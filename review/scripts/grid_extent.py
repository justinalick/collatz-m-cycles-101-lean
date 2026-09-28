"""Estimate: how far would the two-rise grid have to extend (top N) for the chain bound to close
for m = 102..106?  Uses the committed exact B(N) where known and the estimate B = N + 16 for new
geometric points ceil(70*1.1^i) (the same estimate plan_hi_grid.py uses; NOT a proof)."""
import sys, os, json, math
sys.path.insert(0, 'research/scripts/mcycle101_certgen')
os.environ['MBAR_CACHE'] = 'research/scripts/mcycle101_certgen/mbar_cache.json'
import gen_lean as L
cache = {int(k): v for k, v in json.load(open(os.environ['MBAR_CACHE'])).items()}
def geo(top):
    Ns, x = [], 70.0
    while True:
        N = math.ceil(x)
        if not Ns or N > Ns[-1]: Ns.append(N)
        if N >= top: return Ns
        x *= 1.1
def grid_up_to(top):
    Ns = set(geo(top)) | set(cache)
    return sorted((N, cache.get(N, N + 16)) for N in Ns)
def closes(m, P, grid):
    worst = 0
    for c in P['certs']:
        if c['small']: continue
        Ys = L.chainSeq(grid, L.Y0_of(c), m)
        worst = max(worst, sum(Ys) / (c['K'] * L.SC))
    return worst
for m in range(101, 107):
    P = L.plan_m(m, need_ns=False)
    lo, hi = 23446, 4000000
    if closes(m, P, grid_up_to(lo)) < 1:
        print(f"m={m}: closes with the committed grid (top 23446); worst ratio {closes(m,P,grid_up_to(lo)):.3f}", flush=True); continue
    while hi - lo > max(50, lo // 100):
        mid = (lo + hi) // 2
        if closes(m, P, grid_up_to(mid)) < 1: hi = mid
        else: lo = mid
    g = grid_up_to(hi)
    print(f"m={m}: needs grid top about N={hi} ({len(g)} points, sum N^2 = {sum(N*N for N,_ in g):.2e} vs committed {sum(N*N for N,_ in grid_up_to(23446)):.2e}); worst ratio there {closes(m,P,g):.3f}", flush=True)
