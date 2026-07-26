#!/usr/bin/env python3
# trust-js-regexp: best-effort test262 RegExp triple scraper.
#
# Statically extracts (pattern, flags, input) triples from
# test/built-ins/RegExp/** where they appear as simple literal exec/test
# assertions:
#   /pat/flags.exec("...")     /pat/flags.test('...')
#   new RegExp("pat", "flags").exec("...") / .test("...")
# The extracted triples are NOT trusted for expected values — they are fed
# through the differential harness (tests/regexp_differential.rs), where
# live Node supplies the oracle. Output: tests/data/corpus_triples.json as
# [[pattern_units, flags, input_units], ...] (UTF-16 code units, so lone
# surrogates survive).
#
# Usage: python3 scrape_test262_regexp.py <test262-root> <out.json>
#
# Author: Andrew Yates
# Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

import json
import os
import sys

ROOT, OUT = sys.argv[1], sys.argv[2]
FLAGS = set("dgimsuvy")
MAX_LEN = 200
CAP = 1200


def to_units(s):
    """Python str (may contain lone surrogates) -> UTF-16 code units."""
    units = []
    for ch in s:
        cp = ord(ch)
        if cp > 0xFFFF:
            cp -= 0x10000
            units.append(0xD800 + (cp >> 10))
            units.append(0xDC00 + (cp & 0x3FF))
        else:
            units.append(cp)
    return units


def decode_js_string(text, i, quote):
    """Decode a JS string literal starting after the quote. Returns
    (value, next_index) or None on unsupported escapes/newlines."""
    out = []
    while i < len(text):
        c = text[i]
        if c == quote:
            return "".join(out), i + 1
        if c in "\r\n":
            return None
        if c != "\\":
            out.append(c)
            i += 1
            continue
        i += 1
        if i >= len(text):
            return None
        e = text[i]
        simple = {"n": "\n", "t": "\t", "r": "\r", "b": "\b", "f": "\f",
                  "v": "\v", "\\": "\\", "'": "'", '"': '"', "/": "/", "`": "`"}
        if e in simple:
            out.append(simple[e])
            i += 1
        elif e == "0" and (i + 1 >= len(text) or not text[i + 1].isdigit()):
            out.append("\0")
            i += 1
        elif e == "x":
            h = text[i + 1:i + 3]
            if len(h) != 2:
                return None
            try:
                out.append(chr(int(h, 16)))
            except ValueError:
                return None
            i += 3
        elif e == "u":
            if i + 1 < len(text) and text[i + 1] == "{":
                j = text.find("}", i + 2)
                if j < 0:
                    return None
                try:
                    cp = int(text[i + 2:j], 16)
                except ValueError:
                    return None
                if cp > 0x10FFFF:
                    return None
                out.append(chr(cp))
                i = j + 1
            else:
                h = text[i + 1:i + 5]
                if len(h) != 4:
                    return None
                try:
                    out.append(chr(int(h, 16)))
                except ValueError:
                    return None
                i += 5
        else:
            return None  # octal and friends: skip the case
    return None


def scan_regex_literal(text, i):
    """text[i] == '/': try to read a regex literal. Returns
    (pattern_source, flags, next_index) or None."""
    j = i + 1
    if j < len(text) and text[j] in "/*":  # comment, not a regex
        return None
    in_class = False
    while j < len(text):
        c = text[j]
        if c in "\r\n":
            return None
        if c == "\\":
            j += 2
            continue
        if in_class:
            if c == "]":
                in_class = False
        elif c == "[":
            in_class = True
        elif c == "/":
            break
        j += 1
    if j >= len(text) or text[j] != "/":
        return None
    pattern = text[i + 1:j]
    if not pattern:
        return None
    k = j + 1
    flags = ""
    while k < len(text) and text[k].isalpha():
        flags += text[k]
        k += 1
    if not set(flags) <= FLAGS or len(set(flags)) != len(flags):
        return None
    return pattern, flags, k


def scan_call_arg(text, k):
    """Expect .exec( "..." ) or .test( '...' ) at text[k:]. Returns
    (input_string, ) or None."""
    for name in (".exec(", ".test("):
        if text.startswith(name, k):
            m = k + len(name)
            while m < len(text) and text[m] in " \t":
                m += 1
            if m < len(text) and text[m] in "'\"":
                dec = decode_js_string(text, m + 1, text[m])
                if dec is None:
                    return None
                value, e = dec
                while e < len(text) and text[e] in " \t":
                    e += 1
                if e < len(text) and text[e] == ")":
                    return (value,)
    return None


def extract(text):
    triples = []
    i = 0
    while i < len(text):
        c = text[i]
        if c == "/":
            lit = scan_regex_literal(text, i)
            if lit is not None:
                pattern, flags, k = lit
                arg = scan_call_arg(text, k)
                if arg is not None:
                    triples.append((pattern, flags, arg[0]))
                    i = k
                    continue
        elif text.startswith("new RegExp(", i):
            m = i + len("new RegExp(")
            if m < len(text) and text[m] in "'\"":
                dec = decode_js_string(text, m + 1, text[m])
                if dec is not None:
                    pattern, e = dec
                    flags = ""
                    ok = True
                    while e < len(text) and text[e] in " \t":
                        e += 1
                    if e < len(text) and text[e] == ",":
                        e += 1
                        while e < len(text) and text[e] in " \t":
                            e += 1
                        if e < len(text) and text[e] in "'\"":
                            dec2 = decode_js_string(text, e + 1, text[e])
                            if dec2 is None:
                                ok = False
                            else:
                                flags, e = dec2
                        else:
                            ok = False
                    if ok and e < len(text) and text[e] == ")" and set(flags) <= FLAGS:
                        arg = scan_call_arg(text, e + 1)
                        if arg is not None:
                            triples.append((pattern, flags, arg[0]))
                            i = e
                            continue
        i += 1
    return triples


def pattern_units(source):
    # The regex-literal pattern source is already the pattern text.
    return to_units(source)


seen = set()
rows = []
n_files = 0
for dirpath, _dirs, files in os.walk(os.path.join(ROOT, "test", "built-ins", "RegExp")):
    for fname in sorted(files):
        if not fname.endswith(".js") or "FIXTURE" in fname:
            continue
        n_files += 1
        path = os.path.join(dirpath, fname)
        try:
            text = open(path, encoding="utf-8").read()
        except UnicodeDecodeError:
            continue
        for pattern, flags, inp in extract(text):
            pu, iu = to_units(pattern), to_units(inp)
            if len(pu) > MAX_LEN or len(iu) > MAX_LEN:
                continue
            key = (tuple(pu), flags, tuple(iu))
            if key in seen:
                continue
            seen.add(key)
            rows.append([pu, flags, iu])

rows.sort()
rows = rows[:CAP]
with open(OUT, "w") as f:
    json.dump(rows, f, separators=(",", ":"))
print(f"scanned {n_files} files; extracted {len(rows)} unique triples -> {OUT}")
