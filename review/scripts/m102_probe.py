"""Run the repo's own certificate generator for m = 101 (control) and m = 102, 103 with the
committed two-rise grid (mbar_cache.json), to see where the method stops."""
import sys, os, json, math, time
sys.path.insert(0, 'research/scripts/mcycle101_certgen')
os.environ['MBAR_CACHE'] = 'research/scripts/mcycle101_certgen/mbar_cache.json'
import gen_lean as L
import gen_mcycle as G
grid = sorted((int(k), v) for k, v in json.load(open(os.environ['MBAR_CACHE'])).items())
for m in [int(a) for a in sys.argv[1:]]:
    t = time.time()
    try:
        P = L.plan_m(m, need_ns=False)
    except AssertionError as e:
        print(m, "plan_m assertion failed:", repr(e), flush=True)
        continue
    print(f"m={m} boot={len(P['steps'])} Ks={P['Ks']} Kceil={P['Kceil']} ({P['Kceil']:.3e}) stair={len(P['st'])} nodes={P['nodes']} shapes={len(P['certs'])} fuel={P['fuel']} t={time.time()-t:.1f}s", flush=True)
    nbad = 0
    worst = 0
    for c in P['certs']:
        ok = L.shape_ok(m, grid, c)
        if c['small']:
            ratio = 0.0
        else:
            Ys = L.chainSeq(grid, L.Y0_of(c), m)
            ratio = sum(Ys) / (c['K'] * L.SC)
        worst = max(worst, ratio)
        if not ok:
            nbad += 1
        print(f"   K={c['K']} P={c['P']} m2={c['m2']} N={c['N']} M={c['M']} log2Ub={(math.log2(c['Ub']) if c['Ub']>0 else 0):.2f} small={c['small']} chain/K={ratio:.4f} ok={ok}", flush=True)
    print(f"m={m}: shapes failing with committed grid: {nbad}/{len(P['certs'])}; worst chain ratio {worst:.4f}", flush=True)
