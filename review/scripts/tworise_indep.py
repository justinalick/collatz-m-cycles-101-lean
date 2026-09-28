"""Independent (from-scratch) computation of the two-rise maximum M(N):
max over odd n < 2^N of (first rise length k0) + (second rise length k1).
Derivation: n + 1 = 2^k0 a (a odd, a < 2^A, A = N - k0, or A = 1 if k0 = N).
After the rise: 3^k0 a - 1 = 2^l n'' (n'' odd, l >= 1). Next rise k1 = v2(n'' + 1).
a == c (1 - 2^l) (mod 2^(l+k1)) where c = 3^(-k0) (2-adically); so k1 is the largest
value such that gamma mod 2^(l + k1) < 2^A, i.e. l + k1 = A + (zero run of gamma from bit A).
"""
import sys, json, time

def lowest_set_bit(x):
    return (x & -x).bit_length() - 1

def two_rise_max(N):
    W = 2 * N + 128
    mod = 1 << W
    inv3 = pow(3, -1, mod)
    c = 1
    best = (0, None)
    for k0 in range(1, N + 1):
        c = c * inv3 % mod                 # c = 3^{-k0} mod 2^W
        A = N - k0 if k0 < N else 1
        cz = c >> A
        assert cz != 0
        zc = A + lowest_set_bit(cz)        # lowest set bit of c at or above A
        # for l > zc: gamma = c mod 2^l has set bit zc < l, so j_max = zc < l: no k1 >= 1.
        for l in range(1, zc + 1):
            g = (c - (c << l)) % mod       # gamma = c (1 - 2^l) mod 2^W
            gz = g >> A
            assert gz != 0, "W too small"
            jmax = A + lowest_set_bit(gz)
            k1 = jmax - l
            if k1 >= 1 and k0 + k1 > best[0]:
                best = (k0 + k1, (k0, l, k1))
    return best

if __name__ == "__main__":
    cache = json.load(open(sys.argv[1]))
    limit = int(sys.argv[2])
    bad = 0
    for N_s, B in sorted(cache.items(), key=lambda kv: int(kv[0])):
        N = int(N_s)
        if N > limit:
            continue
        t = time.time()
        M, wit = two_rise_max(N)
        ok = M <= B
        exact = (M == B)
        print(f"N={N:6d} B(repo)={B:6d} M(indep)={M:6d} witness(k0,l,k1)={wit} {'OK' if ok else 'VIOLATION'}{' exact' if exact else ' (B larger than max)'} {time.time()-t:.1f}s", flush=True)
        if not ok:
            bad += 1
    print("violations:", bad)
