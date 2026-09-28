"""The choice of the two-rise grid for m = 97..101 (gridHi): the points of gridLo and the geometric
points ceil(70 * r^i), extended until the chain of every listed shape closes (Sigma Y < K 2^S).

usage: MBAR_CACHE=mbar_cache.json python3 plan_hi_grid.py [r ...]
For each ratio r, prints the least top point (bisection on the extent), the number of points, the sum
of N (first rises for the kernel) and the cost proxy Sigma N^2; B(N) is taken from the cache (the
generator's Mbar) and estimated as N + 16 where it is missing.  With r = 1.1 the grid ends at 23446
(grid_hi.txt); gen_lean.py then recomputes every B and re-verifies every chain."""
import sys, os, json, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_lean as L

HERE = os.path.dirname(os.path.abspath(__file__))
LO = [int(x) for x in open(os.path.join(HERE, "grid_lo.txt")).read().split(",")]

def geo(r, ntop, n0=70):
    Ns, x = [], n0
    while True:
        N = math.ceil(x)
        if not Ns or N > Ns[-1]:
            Ns.append(N)
        if N >= ntop:
            return Ns
        x *= r

def B(N):
    return L._MB.get(N, N + 16)

def closes_all(plans, grid):
    for P in plans:
        for c in P['certs']:
            if not c['small'] and not sum(L.chainSeq(grid, L.Y0_of(c), P['m'])) < c['K'] * L.SC:
                return False
    return True

if __name__ == "__main__":
    rs = [float(x) for x in sys.argv[1:]] or [1.07, 1.1, 1.13, 1.16]
    plans = [L.plan_m(m, need_ns=False) for m in range(97, 102)]
    for r in rs:
        lo, hi = 5000, 60000
        while hi - lo > 50:
            mid = (lo + hi) // 2
            g = sorted((N, B(N)) for N in set(geo(r, mid)) | set(LO))
            lo, hi = (lo, mid) if closes_all(plans, g) else (mid, hi)
        Ns = sorted(set(geo(r, hi)) | set(LO))
        print("r", r, "top", Ns[-1], "points", len(Ns), "sumN", sum(Ns),
              "sumN2 %.2e" % sum(N * N for N in Ns), flush=True)
