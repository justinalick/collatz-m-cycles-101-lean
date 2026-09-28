"""Windowed two-rise checker (mirror of the planned Lean checker `twoRiseOK`).

For odd n < 2^N write n + 1 = a 2^k0 (a odd), and let l0 be the length of the following descent and
k1 the next rise.  Then a = gamma (mod 2^(l0 + k1)) with gamma = (1 - 2^l0) 3^(-k0) (2-adic), and
a < 2^A, A = max(1, N - k0).  If k0 + k1 > B then gamma mod 2^(B + 1 - k0 + l0) < 2^A.
check(N, B) verifies, for every k0 in [1, N] and every l0 >= 1, that gamma has a set bit in
[A, B + 1 - k0 + l0); hence k0 + k1 <= B for every odd n < 2^N.

Per k0 (c = 3^(-k0) mod 2^W):
  * l0 > zc (zc = lowest set bit of c at or above A): gamma = c mod 2^l0 has the bit zc.
  * A <= l0 <= zc: direct check.
  * 1 <= l0 < A, l0 < E1 - E (E = B + 1 - N): direct check.
  * 1 <= l0 < A, l0 >= E1 - E: pattern check.  If gamma mod 2^(A + E1) < 2^A then the E1-bit window of c
    at i = A - l0 equals P = (c >> A) mod 2^E1 or P - 1 (mod 2^E1).  Bit-parallel search of both patterns
    over i in [1, A - max(1, E1 - E)]; a match falls back to the direct check.
"""
import sys, time

def lowbit_pos(x):
    return (x & -x).bit_length() - 1

def match_mask(X, P, E1, L):
    """bit i (i < L) set iff (X >> i) mod 2^E1 == P"""
    mask = (1 << L) - 1
    acc = mask
    for b in range(E1):
        s = (X >> b) & mask
        if not (P >> b) & 1:
            s ^= mask
        acc &= s
    return acc

def check(N, B, E1=32, W=None, stats=None):
    E = B + 1 - N
    assert E >= 1
    if W is None:
        W = 2 * N + 2 * E1 + 64
    mod = 1 << W
    i3 = pow(3, -1, mod)
    c = 1
    for k0 in range(1, N + 1):
        c = (c * i3) % mod
        A = max(1, N - k0)
        def direct(l):
            wend = B + 1 - k0 + l
            if wend > W:
                return False
            g = (c * (mod + 1 - (1 << l))) % mod
            if stats is not None: stats['direct'] += 1
            return (g % (1 << wend)) >> A != 0
        cz = c >> A
        if cz == 0:
            return False, ('no zc', k0)
        zc = A + lowbit_pos(cz)
        for l in range(A, zc + 1):
            if not direct(l):
                return False, ('direct', k0, l)
        lmin = max(1, E1 - E)
        for l in range(1, min(A, lmin)):
            if not direct(l):
                return False, ('direct', k0, l)
        if A - 1 >= lmin:
            # positions i = A - l in [1, A - lmin]
            L = A - lmin + 1
            X = c % (1 << (A + E1))
            P = (c >> A) % (1 << E1)
            P2 = (P - 1) % (1 << E1)
            rng = ((1 << L) - 1) ^ 1        # bits 1 .. L-1
            mm = (match_mask(X, P, E1, L) | match_mask(X, P2, E1, L)) & rng
            if stats is not None: stats['pattern'] += 1
            while mm:
                i = lowbit_pos(mm)
                mm &= mm - 1
                if stats is not None: stats['fallback'] += 1
                if not direct(A - i):
                    return False, ('fallback', k0, A - i)
    return True, None

def mbar_exact(N):
    """the one-pass bound (tworise.Mbar) computed with the window check: least B >= N accepted"""
    B = N
    while True:
        ok, why = check(N, B)
        if ok:
            return B
        B += 1

if __name__ == "__main__":
    for N in map(int, sys.argv[1:]):
        t = time.time()
        st = {'direct': 0, 'pattern': 0, 'fallback': 0}
        B = mbar_exact(N)
        print(N, B, "%.2fs" % (time.time() - t), flush=True)

def mbar_upper(N, E1=24, LDIR=16):
    """An upper bound for the one-pass two-rise maximum (>= mbar_exact(N), usually equal):
    exact values for l <= LDIR, for l in [A, zc] and at every pattern hit; the bound
    N + E1 - 2 - LDIR for the pairs without a hit (l > LDIR, l < A)."""
    W = 2 * N + 2 * E1 + 64
    W += W % 2
    mod = 1 << W
    i3 = pow(3, -1, mod)
    c = 1
    best = max(N, N + E1 - 2 - LDIR)
    def zval(A, g):
        gz = g >> A
        assert gz != 0
        return A + lowbit_pos(gz)
    for k0 in range(1, N + 1):
        c = (c * i3) % mod
        A = N - k0 if k0 < N else 1
        cz = c >> A
        zc = A + lowbit_pos(cz)
        def exact(l):
            g = (c - (c << l)) % mod
            return zval(A, g) - l + k0
        for l in range(A, zc + 1):
            best = max(best, exact(l))
        for l in range(1, min(A, LDIR + 1)):
            best = max(best, exact(l))
        lmin = LDIR + 1
        if A - 1 >= lmin:
            L = A - lmin + 1
            X = c % (1 << (A + E1))
            P = (c >> A) % (1 << E1)
            P2 = (P - 1) % (1 << E1)
            rng = ((1 << L) - 1) ^ 1
            mm = (match_mask(X, P, E1, L) | match_mask(X, P2, E1, L)) & rng
            while mm:
                i = lowbit_pos(mm)
                mm &= mm - 1
                best = max(best, exact(A - i))
    return best
