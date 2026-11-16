#!/usr/bin/env python3
"""Bound native Cargo HTTP to the canonical public registry TLS endpoints.

This is a TCP CONNECT policy, never a TLS terminator or credential provider.
GitHub's pre-CLI API path is refused locally; Cargo's checked Git CLI remains
the only Git source acquisition path. Agh uses its separate owner transport.
"""
from __future__ import annotations

import errno
import select
import socket
import socketserver
import threading
import time


ALLOWED_TARGETS = frozenset({"index.crates.io:443", "static.crates.io:443"})
MAX_CONNECTIONS = 32
MAX_HEADER_BYTES = 8192
MAX_EVENTS = 10000


class Refused(RuntimeError):
    pass


class RegistryHttpGate:
    def __init__(self, deadline: float, *, offline: bool = False):
        if not deadline > time.monotonic():
            raise Refused("registry HTTP deadline is already exhausted")
        self.deadline = deadline
        self.offline = offline
        self.failure = None
        self.closed = threading.Event()
        self.lock = threading.Lock()
        self.sockets: set[socket.socket] = set()
        self.workers: set[threading.Thread] = set()
        self.events: list[dict] = []
        self.capacity = threading.BoundedSemaphore(MAX_CONNECTIONS)
        gate = self

        class Handler(socketserver.BaseRequestHandler):
            def handle(self):
                gate._handle(self.request)

        class Server(socketserver.TCPServer):
            allow_reuse_address = False

            def process_request(self, request, client_address):
                if gate.closed.is_set() or not gate.capacity.acquire(blocking=False):
                    gate._reply(request, 503)
                    self.shutdown_request(request)
                    return
                try:
                    thread = threading.Thread(target=self.owned_request,
                        args=(request, client_address), name="daily-registry-connect", daemon=True)
                    thread.start()
                except (RuntimeError, OSError):
                    with gate.lock:
                        gate.failure = Refused("registry HTTP worker could not start")
                        gate.closed.set()
                    gate.capacity.release()
                    gate._reply(request, 503)
                    self.shutdown_request(request)
                    return
                # Never expose an unstarted Thread to shutdown/join. The
                # listener completes this transfer before shutdown() returns.
                with gate.lock:
                    if thread.is_alive():
                        gate.workers.add(thread)

            def owned_request(self, request, address):
                try:
                    self.finish_request(request, address)
                except (OSError, ValueError):
                    pass
                finally:
                    self.shutdown_request(request)
                    gate.capacity.release()
                    with gate.lock:
                        gate.workers.discard(threading.current_thread())

        self.server = Server(("127.0.0.1", 0), Handler)
        self.url = "http://127.0.0.1:" + str(self.server.server_address[1])
        self.thread = threading.Thread(target=self.server.serve_forever,
            kwargs={"poll_interval": 0.1}, name="daily-registry-listener", daemon=True)

    @staticmethod
    def _reply(client: socket.socket, status: int):
        try:
            if status == 200:
                client.sendall(b"HTTP/1.1 200 Connection Established\r\n\r\n")
                return
            client.sendall((f"HTTP/1.1 {status} " + ("Connection Established" if status == 200 else "Refused")
                + "\r\nContent-Length: 0\r\nConnection: close\r\n\r\n").encode())
        except OSError:
            pass

    def _register(self, sock):
        with self.lock:
            if self.closed.is_set():
                sock.close()
                return False
            self.sockets.add(sock)
            return True

    def _event(self, target, accepted):
        # Never retain headers, tokens, arbitrary URL paths or userinfo.
        label = target if target in ALLOWED_TARGETS | {"api.github.com:443", "github.com:443"} else "[unsupported]"
        with self.lock:
            if len(self.events) >= MAX_EVENTS:
                self.failure = Refused("registry HTTP event population exceeds its finite bound")
                self.closed.set()
                return
            self.events.append({"target": label, "accepted": accepted})

    def _connect_upstream(self, host):
        # getaddrinfo may block in the platform resolver. It has no outbound
        # connection authority: each dial below is separately guarded AFTER it
        # returns. An unsettled resolver worker still refuses successful exit.
        addresses = socket.getaddrinfo(host, 443, type=socket.SOCK_STREAM)
        if len(addresses) > 64:
            raise OSError("registry resolver address population exceeds its bound")
        last_error = None
        for family, kind, protocol, _canonical, address in addresses:
            upstream, connected = None, False
            try:
                with self.lock:
                    if self.closed.is_set() or time.monotonic() >= self.deadline:
                        return None
                    if family not in {socket.AF_INET, socket.AF_INET6} or kind != socket.SOCK_STREAM:
                        raise OSError("registry resolver returned an unsupported address family")
                    upstream = socket.socket(family, kind, protocol)
                    self.sockets.add(upstream)
                    upstream.setblocking(False)
                    connect_end = min(self.deadline, time.monotonic() + 5)
                    # Nonblocking connect_ex receives an already resolved
                    # numeric address. Shutdown sets closed under THIS lock,
                    # so it cannot race a new dial after taking ownership.
                    code = upstream.connect_ex(address)
                if code not in {0, errno.EISCONN, errno.EINPROGRESS, errno.EWOULDBLOCK, errno.EALREADY, errno.EINTR}:
                    raise OSError(code, "registry upstream connection refused")
                while code not in {0, errno.EISCONN}:
                    now = time.monotonic()
                    if self.closed.is_set() or now >= self.deadline:
                        return None
                    remaining = connect_end - now
                    if remaining <= 0:
                        raise OSError(errno.ETIMEDOUT, "registry upstream connection timed out")
                    _, writable, errors = select.select([], [upstream], [upstream], min(0.25, remaining))
                    if not writable and not errors:
                        continue
                    code = upstream.getsockopt(socket.SOL_SOCKET, socket.SO_ERROR)
                    if code:
                        raise OSError(code, "registry upstream connection failed")
                connected = True
                return upstream
            except OSError as error:
                last_error = error
            finally:
                if upstream is not None and not connected:
                    with self.lock:
                        self.sockets.discard(upstream)
                    upstream.close()
        raise last_error or OSError("registry resolver returned no usable address")

    def _handle(self, client):
        upstream = None
        established = False
        if not self._register(client):
            return
        try:
            client.settimeout(min(3, max(0.01, self.deadline - time.monotonic())))
            header = bytearray()
            while not header.endswith(b"\r\n\r\n"):
                byte = client.recv(1)
                if not byte or len(header) >= MAX_HEADER_BYTES:
                    self._event("[invalid-header]", False)
                    self._reply(client, 403)
                    return
                header.extend(byte)
            line = bytes(header).split(b"\r\n", 1)[0].split(b" ")
            if len(line) != 3:
                self._event("[invalid-header]", False)
                self._reply(client, 403)
                return
            method, authority, protocol = line
            target = authority.decode("ascii", errors="replace")
            if (method != b"CONNECT" or protocol not in {b"HTTP/1.0", b"HTTP/1.1"}
                    or target not in ALLOWED_TARGETS or self.closed.is_set()
                    or self.offline
                    or time.monotonic() >= self.deadline):
                self._event(target, False)
                self._reply(client, 403)
                return
            # No DNS or upstream socket is touched for an unsupported target.
            host = target.removesuffix(":443")
            upstream = self._connect_upstream(host)
            if upstream is None:
                self._event(target, False)
                self._reply(client, 403)
                return
            self._event(target, True)
            self._reply(client, 200)
            established = True
            client.setblocking(False)
            upstream.setblocking(False)
            buffers = {client: bytearray(), upstream: bytearray()}
            peers = {client: upstream, upstream: client}
            open_reads, finish_writes = set(peers), set()
            while (open_reads or any(buffers.values())) and not self.closed.is_set() and time.monotonic() < self.deadline:
                reads = [sock for sock in open_reads if len(buffers[peers[sock]]) < 65536]
                writes = [sock for sock, content in buffers.items() if content]
                readable, writable, _ = select.select(reads, writes, [], 0.25)
                for sock in readable:
                    try:
                        data = sock.recv(65536 - len(buffers[peers[sock]]))
                    except BlockingIOError:
                        continue
                    if not data:
                        open_reads.remove(sock)
                        finish_writes.add(peers[sock])
                    else:
                        buffers[peers[sock]].extend(data)
                for sock in writable:
                    try:
                        sent = sock.send(buffers[sock])
                    except BlockingIOError:
                        continue
                    if sent == 0:
                        raise OSError("registry tunnel peer closed its writer")
                    del buffers[sock][:sent]
                for sock in list(finish_writes):
                    if not buffers[sock]:
                        sock.shutdown(socket.SHUT_WR)
                        finish_writes.remove(sock)
        except (OSError, ValueError):
            if not established:
                self._reply(client, 502)
        finally:
            for sock in (client, upstream):
                if sock is not None:
                    with self.lock:
                        self.sockets.discard(sock)
                    sock.close()

    def environment(self, original):
        result = dict(original)
        for key in list(result):
            if key.lower() in {"http_proxy", "https_proxy", "all_proxy", "no_proxy"}:
                result.pop(key)
        result.update(CARGO_HTTP_PROXY=self.url, CARGO_HTTP_SSL_VERIFY="true",
                      CARGO_HTTP_PROXY_SSL_VERIFY="true", CARGO_HTTP_NO_PROXY="",
                      NO_PROXY="", no_proxy="")
        for key in ("HTTP_PROXY", "HTTPS_PROXY", "ALL_PROXY", "http_proxy", "https_proxy", "all_proxy"):
            result[key] = self.url
        return result

    def __enter__(self):
        try:
            self.thread.start()
        except BaseException:
            with self.lock:
                self.closed.set()
            self.server.server_close()
            raise
        return self

    def __exit__(self, kind, error, tb):
        with self.lock:
            self.closed.set()
        self.server.shutdown()
        self.server.server_close()
        with self.lock:
            sockets, workers = list(self.sockets), list(self.workers)
        for sock in sockets:
            try:
                sock.shutdown(socket.SHUT_RDWR)
            except OSError:
                pass
            sock.close()
        end = time.monotonic() + 5
        for worker in [self.thread, *workers]:
            worker.join(max(0, end - time.monotonic()))
        if any(worker.is_alive() for worker in [self.thread, *workers]):
            self.failure = Refused("registry HTTP gate retains an unsettled worker")
        if self.failure is not None:
            if error is not None:
                error.add_note(str(self.failure))
            else:
                raise self.failure
        return False
