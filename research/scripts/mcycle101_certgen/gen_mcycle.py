"""Certificate generator for the Lean exclusion of m-cycles, 92 <= m <= 101 (MCycleWalk.lean,
MCycleChain.lean): bootstrap at the floor X0 = 2^71 + 1, the stair of eps values, the Farey walk,
the Rhin ceiling, and one ShapeCert per listed shape.  Exact rational arithmetic throughout; every
function mirrors a Lean checker (epsOKX, stepOKX, walk, mults, uOK, shapeOK)."""
import math, sys
from fractions import Fraction as F
sys.setrecursionlimit(100000)

X0L = 2**71 + 1                      # the Lean floor mX0: every element is >= 2^71 + 1
L2 = F(6931471803, 10**10)
L2hi = F(6931471808, 10**10)
D = F(1584962501, 10**9)            # deltaUp
DLO = F(158496250072115618145373894394781650875981440769248, 10**50)
DHI = F(158496250072115618145373894394781650875981440769249, 10**50)
NCAP = 400

_G = {}
def Ghi(n):
    if n not in _G:
        s = F(0)
        for j in range(n):
            s += D**j
        _G[n] = s
    return _G[n]

def eps_step(Kp, m, m2):
    """(eps, N, M) as checked by epsOKX at the premise K >= Kp, or None"""
    if m2 == 0:
        return F(m, X0L) / (Kp * L2), 0, 0
    N = math.floor(F(m2) * Kp / (m * Ghi(m2)))
    M = math.floor(F(m2) * Kp / (m * (1 + Ghi(m2 - 1))))
    N, M = min(N, NCAP), min(M, NCAP)
    if N < 1 or M < 1:
        return None
    return (F(m - m2, X0L) + F(1, 2**N - 1) + F(m2 - 1, 2**M - 1)) / (Kp * L2), N, M

def best_eps(Kp, m, cands=None):
    best = None
    for m2 in (cands if cands is not None else range(0, m + 1)):
        r = eps_step(F(Kp), m, m2)
        if r is None:
            continue
        if best is None or r[0] < best[0]:
            best = (r[0], m2, r[1], r[2])
    return best

def round_up(fr, sig):
    e = math.floor(math.log10(float(fr)))
    k = sig - 1 - e
    return math.ceil(fr * F(10) ** k), k

def eps_ok(Kp, m, m2, N, M, eps):
    """mirror of epsOKX"""
    if not (Kp > 0 and eps > 0):
        return False
    if m2 == 0:
        return F(m, X0L) <= eps * Kp * L2
    return (m2 <= m and N >= 1 and M >= 1 and N * m * Ghi(m2) <= m2 * Kp and
            M * m * (1 + Ghi(m2 - 1)) <= m2 * Kp and
            F(m - m2, X0L) + F(1, 2**N - 1) + F(m2 - 1, 2**M - 1) <= eps * Kp * L2)

def farey(alpha, beta):
    """Farey neighbours (a, b), (c, d): a/b <= alpha < beta <= c/d, mediant strictly inside"""
    l, r = (1, 1), (2, 1)
    while True:
        md = (l[0] + r[0], l[1] + r[1])
        mf = F(*md)
        if mf <= alpha:
            l = md
        elif mf >= beta:
            r = md
        else:
            return l, r

def rhin_data(m, Kf):
    G = Ghi(m)
    c = 0
    while G > 2**c:
        c += 1
    k = 0
    while 2 * m > 2**k:
        k += 1
    V = math.floor(F(Kf) / G)
    lhs = V * (L2 - F(133, 10 * 4096))
    rhs = F(133, 10) * (12 + c) * L2hi - F(133, 10) + F(133, 10) * F(46057, 100000) + k * L2hi
    return (lhs > rhs and V >= 1), V, c, k

def rhin_ceiling(m):
    lo, hi = 1, 10**40
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if rhin_data(m, mid)[0]:
            hi = mid
        else:
            lo = mid
    return hi

def rounded_step(Kp, m, sig0=3):
    """the best eps at Kp, rounded up to few digits keeping the Farey bound of the exact eps"""
    e, m2, N, M = best_eps(Kp, m)
    (a, b), (c, d) = farey(DLO, DHI + e)
    for sig in range(sig0, 60):
        n_, k_ = round_up(e, sig)
        er = F(n_, 10**k_)
        (a2, b2), (c2, d2) = farey(DLO, DHI + er)
        if b2 + d2 == b + d:
            assert eps_ok(Kp, m, m2, N, M, er)
            return (m2, N, M, n_, k_, er, a2, b2, c2, d2)
    raise RuntimeError

def bootstrap(m):
    """steps [(m2, N, M, n, k, eps, a, b, c, d)], the stall premise Ks and the stall step"""
    K = 1
    steps = []
    while True:
        st = rounded_step(K, m)
        Kn = st[7] + st[9]
        if Kn <= K:
            return steps, K, st
        steps.append(st)
        K = Kn

def stair(m, Ks, Kceil, r=F(11, 10), sig=4):
    """stair entries (Kp, m2, N, M, n, k, eps) for Kp = Ks, Ks r, ..., below Kceil (decreasing Kp)"""
    out = []
    Kp = Ks
    while Kp < Kceil:
        e, m2, N, M = best_eps(Kp, m)
        n_, k_ = round_up(e, sig)
        er = F(n_, 10**k_)
        assert eps_ok(Kp, m, m2, N, M, er)
        out.append((Kp, m2, N, M, n_, k_, er))
        Kp = math.ceil(Kp * r)
    return out[::-1]

def eps_at(K, st):
    for e in st:
        if e[0] <= K:
            return e[6]
    return None

def mults(st, Kceil, Kmin, e, f):
    out = []
    j = 1
    while True:
        if Kceil <= j * f:
            return out
        ep = eps_at(max(j * f, Kmin), st)
        if ep is not None and DHI + ep <= F(e, f):
            return out
        out.append((j * f, j * e))
        j += 1

def walk(st, Kceil, Kmin, a, b, c, d, stats):
    stats[0] += 1
    f = b + d
    e = a + c
    if Kceil <= f:
        return []
    ep = eps_at(max(f, Kmin), st)
    if ep is None:
        return [(0, 0)]
    if F(e, f) <= DLO:
        return walk(st, Kceil, Kmin, e, f, c, d, stats)
    if DHI + ep <= F(e, f):
        return walk(st, Kceil, Kmin, a, b, e, f, stats)
    return (mults(st, Kceil, Kmin, e, f) + walk(st, Kceil, Kmin, a, b, e, f, stats) +
            walk(st, Kceil, Kmin, e, f, c, d, stats))

if __name__ == "__main__":
    for m in map(int, sys.argv[1:]):
        steps, Ks, stall = bootstrap(m)
        Kceil = rhin_ceiling(m)
        ok, V, cexp, kexp = rhin_data(m, Kceil)
        st = [(Ks,) + stall[:6]] + stair(m, math.ceil(Ks * F(11, 10)), Kceil)[::-1]
        st = sorted(st, key=lambda e: -e[0])
        stats = [0]
        a, b, c, d = stall[6:10]
        surv = walk(st, Kceil, Ks, a, b, c, d, stats)
        print(m, "boot", len(steps), "Ks", Ks, "Kceil %.3e" % Kceil, "stair", len(st), "nodes", stats[0],
              "surv", len(surv), sorted(surv)[:40], flush=True)
