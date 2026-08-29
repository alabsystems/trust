#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Derive the Ed25519 EDGE-CASE vectors in `edge_vectors.txt`.

RFC 8032 section 7.1 publishes five valid (key, message, signature) triples and
nothing else. It publishes no vector for any of the cases a verifier is most
likely to get WRONG: a non-canonical `y`, an encoding that is not a curve
point, a malleated `S`, or a small-order public key. Those vectors do not
exist in published form, so this script DERIVES them -- and the whole point of
deriving them here, rather than reading them out of the crate under test, is
that this file shares no code with it.

Independence, concretely:

  * arithmetic is Python's arbitrary-precision `int`, not a 5x51 limb
    representation, so a carry-chain defect in `field.rs` cannot be mirrored
    here;
  * the group law is the AFFINE law of RFC 8032 section 5.1.4, not the extended
    `add-2008-hwcd-3` the crate uses, so a mistranscribed `2d` cannot be
    mirrored here;
  * the scalar reduction is Python's `%`, not restoring long division, so a
    dropped high bit cannot be mirrored here.

Every parameter below is transcribed from RFC 8032 section 5.1 Table 1 as the
RFC prints it -- `p` and the cofactor from the [RFC7748] references, `d` and
`B` from the decimal expansions in the table itself.

Run:  python3 derive_edge_vectors.py [rfc8032_7_1.txt] > edge_vectors.txt
"""

import sys

# --- RFC 8032 section 5.1 Table 1, as printed --------------------------------

# "p of edwards25519 in [RFC7748] (i.e., 2^255 - 19)"
P = 2**255 - 19
# "order of edwards25519 in [RFC7748] (i.e., 2^252+27742317777372353535851937790883648493)"
L = 2**252 + 27742317777372353535851937790883648493
# "base 2 logarithm of cofactor of edwards25519 in [RFC7748] (i.e., 3)"
COFACTOR = 8
# "d of edwards25519 in [RFC7748] (i.e., -121665/121666 = 3709570593466943934...)"
D_DECIMAL = 37095705934669439343138083508754565189542113879843219016388785533085940283555
# "B (X(P),Y(P)) of edwards25519 in [RFC7748]"
BX = 15112221349535400772501151409588531511454012693041857206046113283949847762202
BY = 46316835694926478169428394003475163141307993866256225615783033603165251855960


def check_parameters():
    """The decimal expansions above must satisfy their own definitions."""
    # d = -121665/121666
    assert D_DECIMAL % P == (-121665 * pow(121666, P - 2, P)) % P, "d decimal"
    # B is on the curve.
    assert on_curve(BX, BY), "B is not on the curve"
    # B has order L.
    assert scalar_mul(L, (BX, BY)) == (0, 1), "B does not have order L"


D = D_DECIMAL % P
SQRT_M1 = pow(2, (P - 1) // 4, P)  # section 5.1.1's x * 2^((p-1)/4) correction factor


def on_curve(x, y):
    """RFC 8032 section 5.1: -x^2 + y^2 = 1 + d*x^2*y^2."""
    return (-x * x + y * y - 1 - D * x * x % P * y % P * y) % P == 0


def add(p1, q1):
    """RFC 8032 section 5.1.4, the AFFINE addition law, verbatim:

        (x1,y1) + (x2,y2) = ( (x1*y2 + x2*y1) / (1 + d*x1*x2*y1*y2),
                              (y1*y2 + x1*x2) / (1 - d*x1*x2*y1*y2) )

    with a = -1 folded in as `y1*y2 + x1*x2`. Divisions are modular inverses.
    This is a DIFFERENT formula from the crate's extended coordinates; that is
    deliberate.
    """
    x1, y1 = p1
    x2, y2 = q1
    k = D * x1 * x2 % P * y1 % P * y2 % P
    x3 = (x1 * y2 + x2 * y1) * pow(1 + k, P - 2, P) % P
    y3 = (y1 * y2 + x1 * x2) * pow(1 - k, P - 2, P) % P
    return (x3, y3)


def scalar_mul(k, point):
    """[k]P by double-and-add. Variable time; this is an offline derivation."""
    result = (0, 1)
    addend = point
    while k > 0:
        if k & 1:
            result = add(result, addend)
        addend = add(addend, addend)
        k >>= 1
    return result


def encode_point(point):
    """RFC 8032 section 5.1.2."""
    x, y = point
    return (y | ((x & 1) << 255)).to_bytes(32, "little")


def decode_point(data):
    """RFC 8032 section 5.1.3, following the four numbered steps verbatim.

    Returns the point, or None with the reason the RFC gives for failing.
    """
    n = int.from_bytes(data, "little")
    x_0 = (n >> 255) & 1
    y = n & ((1 << 255) - 1)
    if y >= P:
        return None, "non-canonical y (step 1: 'If the resulting value is >= p, decoding fails')"

    # step 2: x^2 = (y^2 - 1) / (d*y^2 + 1)
    u = (y * y - 1) % P
    v = (D * y % P * y + 1) % P
    x = u * pow(v, 3, P) % P * pow(u * pow(v, 7, P) % P, (P - 5) // 8, P) % P

    # step 3, the three cases
    if v * x % P * x % P == u % P:
        pass
    elif v * x % P * x % P == (-u) % P:
        x = x * SQRT_M1 % P
    else:
        return None, "not a curve point (step 3.3: 'no square root exists ... decoding fails')"

    # step 4
    if x == 0 and x_0 == 1:
        return None, "x = 0 with x_0 = 1 (step 4: 'If x = 0, and x_0 = 1, decoding fails')"
    if x % 2 != x_0:
        x = P - x
    assert on_curve(x, y), "decoded a point that is not on the curve"
    return (x, y), None


def point_order(point):
    """The exact order of a point known to lie in the 8-torsion."""
    q = point
    for order in range(1, 9):
        if q == (0, 1):
            return order
        q = add(q, point)
    return None


def derive_eight_torsion():
    """The 8-torsion subgroup, derived -- no encoding is written down here.

    Every curve point Q satisfies [8L]Q = identity, so [L]Q always lands in the
    8-torsion. Taking small `y` values until one yields a T = [L]Q of full
    order 8 gives a generator, and its multiples are the whole subgroup.
    """
    generator = None
    for y in range(2, 200):
        candidate, _ = decode_point(y.to_bytes(32, "little"))
        if candidate is None:
            continue
        t = scalar_mul(L, candidate)
        if point_order(t) == 8:
            generator = t
            break
    assert generator is not None, "no order-8 point found"

    subgroup = []
    for i in range(COFACTOR):
        q = scalar_mul(i, generator)
        subgroup.append((point_order(q), q))
    # Sanity: a group of exactly 8 distinct points, orders {1,2,4,4,8,8,8,8}.
    assert len({q for _, q in subgroup}) == COFACTOR, "8-torsion has repeats"
    assert sorted(o for o, _ in subgroup) == [1, 2, 4, 4, 8, 8, 8, 8], "wrong order profile"
    return sorted(subgroup, key=lambda entry: (entry[0], encode_point(entry[1])))


def derive_off_curve_y():
    """The smallest `y` values that are canonical but are not curve points.

    These exercise RFC 8032 section 5.1.3 step 3.3 -- the "no square root"
    rejection -- as distinct from the step 1 non-canonical rejection.
    """
    out = []
    for y in range(0, 2000):
        data = y.to_bytes(32, "little")
        point, reason = decode_point(data)
        if point is None:
            assert "not a curve point" in reason, reason
            out.append(y)
        if len(out) == 8:
            break
    return out


def derive_non_canonical_y():
    """Every 255-bit value >= p: exactly the 19 values p .. 2^255-1."""
    return list(range(P, 2**255))


def derive_identity_key_forgery(messages):
    """A signature that verifies under the IDENTITY public key for ANY message.

    This is not a defect in the implementation under test; it is a property of
    RFC 8032 section 5.1.7's group equation, and it is why a verifier must not
    accept a small-order key as a trust anchor.

    Take A = the identity, R = the identity, S = 0. The equation

        [S]B = R + [k]A'

    becomes `identity = identity + [k]identity`, which holds for every value of
    k -- and k is the only part the message influences. So one 64-octet string
    forges every message under that one key, with no secret known.

    Checked below against real messages rather than asserted from the algebra.
    """
    import hashlib

    a_bytes = encode_point((0, 1))
    r_bytes = encode_point((0, 1))
    sig = r_bytes + (0).to_bytes(32, "little")

    a_point, _ = decode_point(a_bytes)
    r_point, _ = decode_point(r_bytes)
    assert a_point == (0, 1) and r_point == (0, 1)
    for m in messages:
        k = int.from_bytes(hashlib.sha512(r_bytes + a_bytes + m).digest(), "little") % L
        assert scalar_mul(0, (BX, BY)) == add(r_point, scalar_mul(k, a_point)), (
            "the identity-key forgery does not satisfy the group equation for %r" % m
        )
    return a_bytes, sig


def derive_zero_key_zero_sig(messages):
    """Per-message verdicts for the ALL-ZEROS key with the ALL-ZEROS signature.

    This one is not a constant answer, and that is why it has to be derived
    rather than guessed. The all-zeros encoding is `y = 0`, whose `x` is
    `+/-sqrt(-1)` -- a point A of order 4, not the identity. With R = A and
    S = 0 the section 5.1.7 equation

        [0]B = R + [k]A'   <=>   identity = [k+1]A

    holds exactly when `k + 1 == 0 (mod 4)`, i.e. `k == 3 (mod 4)`. `k` is a
    SHA-512 digest reduced mod L, so roughly a quarter of all messages are
    accepted -- by a correct implementation.

    Emitting the expected verdict per message turns "what does it do?" into a
    known answer. A test that merely asserted rejection would be WRONG, and was:
    the first draft of `all_zero_signature_is_parsed_and_rejected` asserted that
    no message is accepted and failed on the third one it tried.
    """
    import hashlib

    a_bytes = bytes(32)
    r_bytes = bytes(32)
    a_point, _ = decode_point(a_bytes)
    r_point, _ = decode_point(r_bytes)
    assert point_order(a_point) == 4, "the all-zeros key should have order 4"
    assert r_point == a_point

    out = []
    for m in messages:
        k = int.from_bytes(hashlib.sha512(r_bytes + a_bytes + m).digest(), "little") % L
        holds = scalar_mul(0, (BX, BY)) == add(r_point, scalar_mul(k, a_point))
        # The algebraic shortcut and the full evaluation must agree.
        assert holds == (k % 4 == 3), "k %% 4 == 3 does not characterise acceptance"
        out.append((m, holds, k % 4))
    return out


def main():
    vectors_path = sys.argv[1] if len(sys.argv) > 1 else "rfc8032_7_1.txt"
    check_parameters()

    lines = []
    emit = lines.append
    emit("# Ed25519 EDGE-CASE vectors -- DERIVED, not published.")
    emit("# GENERATED by derive_edge_vectors.py; see PROVENANCE.md. DO NOT HAND-EDIT.")
    emit("# Format: kind | name | hex... (field count varies by kind)")

    # 1. Non-canonical y: every value in [p, 2^255).
    for y in derive_non_canonical_y():
        data = y.to_bytes(32, "little")
        point, reason = decode_point(data)
        assert point is None and "non-canonical" in reason, (y, reason)
        emit("noncanonical_y|p+%d|%s" % (y - P, data.hex()))

    # 2. Canonical y values that are not curve points.
    for y in derive_off_curve_y():
        data = y.to_bytes(32, "little")
        point, reason = decode_point(data)
        assert point is None and "not a curve point" in reason, (y, reason)
        emit("off_curve_y|y=%d|%s" % (y, data.hex()))

    # 3. The 8-torsion, with each point's exact order.
    for order, q in derive_eight_torsion():
        enc = encode_point(q)
        # Must round-trip through the RFC decoder, EXCEPT the identity's
        # sign-bit-set sibling, which is not produced here.
        back, reason = decode_point(enc)
        assert back == q, (order, reason)
        emit("small_order|order=%d|%s" % (order, enc.hex()))

    # 4. Malleated signatures (R, S+L) for every RFC 8032 section 7.1 vector,
    #    each one CHECKED here to satisfy the section 5.1.7 group equation, so
    #    that the only thing left that can reject it is the S range check.
    with open(vectors_path, "r") as handle:
        records = [
            line.strip().split("|")
            for line in handle
            if line.strip() and not line.startswith("#")
        ]
    assert len(records) == 5, "expected the five RFC 8032 section 7.1 vectors"

    import hashlib

    for name, _sk, pk, msg, sig in records:
        sig_bytes = bytes.fromhex(sig)
        a_bytes = bytes.fromhex(pk)
        m = bytes.fromhex(msg)
        r_bytes, s_bytes = sig_bytes[:32], sig_bytes[32:]
        s = int.from_bytes(s_bytes, "little")
        assert s < L, "RFC vector %s already has S >= L" % name

        # The published signature must verify, or the malleation below is
        # being built on top of something already broken.
        a_point, _ = decode_point(a_bytes)
        r_point, _ = decode_point(r_bytes)
        assert a_point is not None and r_point is not None
        k = int.from_bytes(hashlib.sha512(r_bytes + a_bytes + m).digest(), "little") % L
        assert scalar_mul(s, (BX, BY)) == add(r_point, scalar_mul(k, a_point)), (
            "RFC vector %s does not satisfy [S]B = R + [k]A" % name
        )

        # THE MALLEATION. [S+L]B = [S]B because B has order L, so (R, S+L)
        # satisfies the SAME group equation. Asserted, not assumed:
        s_plus_l = s + L
        assert s_plus_l < 2**256, "S+L does not fit 32 octets"
        assert scalar_mul(s_plus_l, (BX, BY)) == add(r_point, scalar_mul(k, a_point)), (
            "(R, S+L) does NOT satisfy the group equation for vector %s -- the "
            "malleability test built on it would be vacuous" % name
        )
        malleated = r_bytes + s_plus_l.to_bytes(32, "little")
        emit("malleated_sig|%s|%s|%s|%s" % (name, pk, msg, malleated.hex()))

    # 5. A universal forgery under the identity public key. Checked against the
    #    five RFC messages plus a few of our own.
    probe_messages = [bytes.fromhex(r[3]) for r in records] + [b"", b"x", b"forge me"]
    a_bytes, forged = derive_identity_key_forgery(probe_messages)
    emit("identity_forgery|any-message|%s|%s" % (a_bytes.hex(), forged.hex()))

    # 6. The all-zeros key with the all-zeros signature: a per-message verdict.
    #    `msg%03d` over a fixed range so both outcomes are certain to appear.
    zero_messages = [b""] + [b"msg%03d" % i for i in range(32)]
    zero_rows = derive_zero_key_zero_sig(zero_messages)
    accepted = sum(1 for _, holds, _ in zero_rows if holds)
    assert 0 < accepted < len(zero_rows), (
        "the zero-key/zero-sig sample is one-sided (%d of %d accepted); a test over it "
        "could not tell an implementation that always accepts from one that never does"
        % (accepted, len(zero_rows))
    )
    for m, holds, k_mod_4 in zero_rows:
        emit("zero_key_zero_sig|%s|%d|%d" % (m.hex(), int(holds), k_mod_4))

    sys.stdout.write("\n".join(lines) + "\n")
    sys.stderr.write(
        "derived: %d non-canonical y, %d off-curve y, %d small-order points, "
        "%d malleated signatures (each verified to satisfy the group equation), "
        "1 identity-key forgery (checked over %d messages)\n"
        % (
            len(derive_non_canonical_y()),
            len(derive_off_curve_y()),
            COFACTOR,
            len(records),
            len(probe_messages),
        )
    )


if __name__ == "__main__":
    main()
