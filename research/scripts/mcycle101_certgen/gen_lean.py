"""Lean data for the exclusion of m-cycles (MCycleWalk.lean / MCycleChain.lean / TwoRiseCheck.lean).

usage: python3 gen_lean.py TAG OUTDIR [--grid N,N,...] [--reuse TAG2:N,N,...] [--parts k] m [m ...]
Writes, for the given m:
  OUTDIR/MCycleTwoRise<TAG><j>.lean  (core Lean only: the two-rise kernel checks AllPairs N B,
                                      split into k modules of about equal kernel cost)
  OUTDIR/MCycleGrid<TAG>.lean        (the grid `grid<TAG>` and `grid<TAG>_ok`)
  OUTDIR/MCycle<m>.lean              (the MData certificate and the kernel check mOK;
                                      MCycle101Data.lean for m = 101)
Without --grid the grid is the set of exact N used by the chains; with --grid it is the given list.
--reuse names grid values already proved in the modules MCycleTwoRise<TAG2>* (imported, not repeated).
All numbers are re-verified here with exact arithmetic that mirrors the Lean checkers
(gen_mcycle.py, tworise_fast.py).

The committed modules are reproduced exactly by
  python3 gen_lean.py Lo OUT 92 93 94 95 96
  MBAR_CACHE=mbar_cache.json python3 gen_lean.py Hi OUT --grid $(cat grid_hi.txt) \
      --reuse Lo:$(cat grid_lo.txt) --parts 6 97 98 99 100 101
(grid_lo.txt: the N of gridLo, the exact N used by the chains of m <= 96; grid_hi.txt: gridLo and
ceil(70 * 1.1^i) up to 23446, chosen by plan_hi_grid.py; mbar_cache.json caches Mbar, about 20
minutes of computation for the N > 1500, and is recomputed if absent)."""
import math, sys, os
from fractions import Fraction as F
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_mcycle as G
import tworise_fast as TR

S = 20
SC = 1 << S
E1 = 16
CHUNK = 3000

# ---------- the chain (mirror of MCycleChain) ----------
def ceil_div(a, b):
    return -((-a) // b)

def chainF(Y):
    return (Y * 1584962501 + 999999999) // 1000000000

def chainG(B, Y):
    return max(0, Y + (584962501 * B * SC + 999999999) // 1000000000 + 1 - 2 * SC)

def gridB(Y, grid):
    for (N, B) in grid:
        if Y <= N * SC:
            return B
    return None

def chainNext(grid, Yp, Yc):
    B = gridB(Yp, grid)
    if B is None:
        return chainF(Yc)
    if 2 * SC <= Yp:
        return min(chainF(Yc), chainG(B, Yp))
    return chainF(Yc)

def chainSeq(grid, Y0, m):
    Ys = [Y0, chainF(Y0)]
    while len(Ys) < m:
        Ys.append(chainNext(grid, Ys[-2], Ys[-1]))
    return Ys[:m]

# ---------- the shape certificate (mirror of uOK / shapeOK) ----------
def room(m, K, P, m2, N, M):
    return (F(P) - K * G.DHI) * G.L2 - F(1, 2**N - 1) - F(m2 - 1, 2**M - 1)

def u_ok(m, K, P, m2, N, M, Ub):
    if not (1 <= m2 <= m and N >= 1 and M >= 1):
        return False
    if not (N * m * G.Ghi(m2) <= m2 * K and M * m * (1 + G.Ghi(m2 - 1)) <= m2 * K):
        return False
    if not (K * G.DHI <= P):
        return False
    r = room(m, K, P, m2, N, M)
    return r > 0 and F(m - m2) <= Ub * r

def u_cert(m, K, P, Q=64):
    best = None
    for m2 in range(1, m + 1):
        N = math.floor(F(m2) * K / (m * G.Ghi(m2)))
        M = math.floor(F(m2) * K / (m * (1 + G.Ghi(m2 - 1))))
        N, M = min(N, G.NCAP), min(M, G.NCAP)
        if N < 1 or M < 1:
            continue
        r = room(m, K, P, m2, N, M)
        if not (K * G.DHI <= P) or r <= 0:
            continue
        Ub = 0 if m2 == m else math.ceil(F(m - m2) / r)
        if best is None or Ub < best[0]:
            best = (Ub, m2, N, M)
    Ub, m2, N, M = best
    assert u_ok(m, K, P, m2, N, M, Ub)
    if Ub <= 2**71 + 1:
        return dict(K=K, P=P, m2=m2, N=N, M=M, Ub=Ub, Pe=0, Q=1, small=True)
    Pe = math.ceil(Q * math.log2(Ub))
    while Ub**Q > 2**Pe:
        Pe += 1
    while Ub**Q <= 2**(Pe - 1):
        Pe -= 1
    return dict(K=K, P=P, m2=m2, N=N, M=M, Ub=Ub, Pe=Pe, Q=Q, small=False)

def Y0_of(c):
    return (c['Pe'] * SC + c['Q'] - 1) // c['Q']

def shape_ok(m, grid, c):
    if not u_ok(m, c['K'], c['P'], c['m2'], c['N'], c['M'], c['Ub']):
        return False
    if c['Ub'] <= 2**71 + 1:
        return True
    if not (c['Q'] >= 1 and c['Ub'] ** c['Q'] <= 2 ** c['Pe']):
        return False
    Ys = chainSeq(grid, Y0_of(c), m)
    return sum(Ys) < c['K'] * SC

# ---------- two-rise bounds ----------
_MB = {}
_MB_FILE = os.environ.get("MBAR_CACHE")          # optional JSON cache {N: B}
if _MB_FILE and os.path.exists(_MB_FILE):
    import json
    _MB.update({int(k): v for k, v in json.load(open(_MB_FILE)).items()})

def Mbar(N):
    """the B used for N: the exact one-pass maximum for N <= 1500, else an upper bound for it (the
    Lean check accepts any B at least the maximum)"""
    if N not in _MB:
        _MB[N] = TR.mbar_exact(N) if N <= 1500 else TR.mbar_upper(N)
        if _MB_FILE:
            import json
            json.dump({str(k): v for k, v in sorted(_MB.items())}, open(_MB_FILE, "w"))
    return _MB[N]

def needed_Ns(m, c, nmax):
    """the N used by the chain of c when every N <= nmax is available (exact ceil(y))"""
    Y0 = Y0_of(c)
    Ys = [Y0, chainF(Y0)]
    used = []
    while len(Ys) < m:
        Yp, Yc = Ys[-2], Ys[-1]
        N = ceil_div(Yp, SC)
        a = chainF(Yc)
        if 2 * SC <= Yp and N <= nmax:
            b = chainG(Mbar(N), Yp)
            if b < a:
                a = b
                used.append(N)
        Ys.append(a)
    return used, sum(Ys) < c['K'] * SC

def min_nmax(m, c):
    nmax = 80
    while True:
        used, ok = needed_Ns(m, c, nmax)
        if ok:
            return nmax, used
        nmax = int(nmax * 1.25) + 1
        assert nmax < 10**6

# ---------- Lean output ----------
def lean_step(st):
    m2, N, M, n_, k_, er, a, b, c, d = st
    return f"⟨{m2}, {N}, {M}, {n_} / 10 ^ {k_}, {a}, {b}, {c}, {d}⟩"

def lean_stair_entry(e):
    Kp, m2, N, M, n_, k_, er = e
    return f"({Kp}, ⟨{m2}, {N}, {M}, {n_} / 10 ^ {k_}, 0, 0, 0, 0⟩)"

def lean_cert(c):
    return f"⟨{c['K']}, {c['P']}, {c['m2']}, {c['N']}, {c['M']}, {c['Ub']}, {c['Pe']}, {c['Q']}⟩"

def Wof(N):
    W = 2 * N + 2 * E1 + 64
    return W + (W % 2)

def walk_depth(st, Kceil, Kmin, a, b, c, d):
    """the recursion depth of G.walk (the fuel of the Lean `walk` bounds it)"""
    f = b + d
    e = a + c
    if Kceil <= f:
        return 1
    ep = G.eps_at(max(f, Kmin), st)
    if ep is None:
        return 1
    if F(e, f) <= G.DLO:
        return 1 + walk_depth(st, Kceil, Kmin, e, f, c, d)
    if G.DHI + ep <= F(e, f):
        return 1 + walk_depth(st, Kceil, Kmin, a, b, e, f)
    return 1 + max(walk_depth(st, Kceil, Kmin, a, b, e, f), walk_depth(st, Kceil, Kmin, e, f, c, d))

def plan_m(m, need_ns=True):
    steps, Ks, stall = G.bootstrap(m)
    Kceil = G.rhin_ceiling(m)
    ok, V, cexp, kexp = G.rhin_data(m, Kceil)
    assert ok
    st = G.stair(m, math.ceil(Ks * F(11, 10)), Kceil)          # decreasing Kp
    pairs = [(e[0], e[6]) for e in st] + [(Ks, stall[5])]
    stats = [0]
    a, b, c, d = stall[6:10]
    shapes = G.walk([(p[0],) + (0,) * 5 + (p[1],) for p in pairs], Kceil, Ks, a, b, c, d, stats)
    assert (0, 0) not in shapes
    certs = [u_cert(m, K, P) for (K, P) in sorted(set(shapes))]
    Ns = set()
    for cc in certs:
        if cc['small'] or not need_ns:
            continue
        nmax, used = min_nmax(m, cc)
        Ns.update(used)
    # the walk's recursion depth: about Kceil / b near a listed shape a/b with small b
    dep = walk_depth([(p[0],) + (0,) * 5 + (p[1],) for p in pairs], Kceil, Ks, a, b, c, d)
    fuel = max(2000, (dep // 500 + 1) * 500)
    assert dep < fuel, dep
    return dict(m=m, steps=steps, Ks=Ks, stall=stall, Kceil=Kceil, V=V, cexp=cexp, kexp=kexp,
                st=st, abcd=(a, b, c, d), nodes=stats[0], certs=certs, Ns=Ns, fuel=fuel)

def chunk_of(N):
    """first rises per kernel theorem: at most about 1 GB of kernel memory (about 60 N bytes per
    first rise at small k0, measured with the core toolchain)"""
    return max(100, min(CHUNK, 12000000 // N))

def tworise_lean(N, B):
    W = Wof(N)
    i3 = f"((2 ^ ({W} + 1) + 1) / 3)"
    lines = []
    names = []
    k = 1
    j = 0
    ch = chunk_of(N)
    while k <= N:
        cnt = min(ch, N + 1 - k)
        c0 = "1" if k == 1 else f"(powMod (2 ^ {W}) 64 {i3} {k - 1} 1)"
        nm = f"tr{N}_{j}"
        lines.append(f"theorem {nm} : rangeOK {N} {B} {E1} {W} {i3} {k} {c0} {cnt} = true := by\n  decide +kernel\n")
        names.append((nm, k, k + cnt))
        k += cnt
        j += 1
    rc = f"(rangeOK_sound {names[0][0]})"
    for nm, lo, hi in names[1:]:
        rc = f"({rc}.trans (rangeOK_sound {nm}))"
    lines.append(f"/-- `k₀ + k₁ ≤ {B}` for the first two rises from every odd `n < 2^{N}`. -/\n"
                 f"theorem allPairs{N} : AllPairs {N} {B} := allPairs_of_range {rc}\n")
    return "\n".join(lines)

def cost(N):
    return N * N

def split_parts(grid, k):
    """k lists of about equal total cost (greedy, largest first)"""
    parts = [[] for _ in range(k)]
    tot = [0] * k
    for (N, B) in sorted(grid, key=lambda e: -cost(e[0])):
        i = tot.index(min(tot))
        parts[i].append((N, B))
        tot[i] += cost(N)
    return [sorted(p) for p in parts if p]

def write_tworise(outdir, name, grid):
    with open(os.path.join(outdir, f"{name}.lean"), "w") as f:
        f.write("import Collatz.TwoRiseCheck\n\n")
        f.write(f"/-!\n# Two-rise bounds for the chains of the `m`-cycle exclusions (kernel checks)\n\n"
                f"Generated by `research/scripts/mcycle101_certgen/gen_lean.py`. Each `AllPairs N B` is\n"
                f"`rangeOK` evaluated by the kernel on chunks of at most {CHUNK} first rises\n"
                f"(`N` = {', '.join(str(N) for N, _ in grid)}).\n-/\n\n")
        # without this the kernel checks of the chunks run as asynchronous tasks whose memory is
        # kept until the end of the file (several GB for the large `N`)
        f.write("set_option Elab.async false\n\n")
        f.write("namespace Collatz.TwoRise\n\n")
        for (N, B) in grid:
            f.write(tworise_lean(N, B) + "\n")
        f.write("end Collatz.TwoRise\n")

def write_grid(outdir, tag, grid, trmods):
    gname = f"grid{tag}"
    with open(os.path.join(outdir, f"MCycleGrid{tag}.lean"), "w") as f:
        f.write("import Collatz.MCycleSteps\n")
        for t in trmods:
            f.write(f"import Collatz.{t}\n")
        f.write(f"\n/-!\n# Two-rise bounds for the chains: the grid `{gname}` ({len(grid)} values of `N`)\n\n"
                f"Generated by `research/scripts/mcycle101_certgen/gen_lean.py`.\n-/\n\n")
        f.write("namespace Collatz\n\n")
        gl = ",\n    ".join(f"({N}, {B})" for (N, B) in grid)
        f.write(f"/-- The two-rise bounds `(N, B)` (increasing `N`). -/\n")
        f.write(f"def {gname} : List (ℕ × ℕ) := [{gl}]\n\n")
        f.write(f"theorem {gname}_cons {{e₀ : ℕ × ℕ}} {{l : List (ℕ × ℕ)}} (h₀ : TwoRiseBound e₀.1 e₀.2)\n"
                f"    (hl : ∀ e ∈ l, TwoRiseBound e.1 e.2) : ∀ e ∈ e₀ :: l, TwoRiseBound e.1 e.2 := by\n"
                f"  intro e he\n  rcases List.mem_cons.mp he with h | h\n  · rw [h]; exact h₀\n"
                f"  · exact hl e h\n\n")
        f.write(f"theorem {gname}_nil : ∀ e ∈ ([] : List (ℕ × ℕ)), TwoRiseBound e.1 e.2 := by\n"
                f"  intro e he\n  cases he\n\n")
        f.write(f"theorem {gname}_ok : ∀ e ∈ {gname}, TwoRiseBound e.1 e.2 := by\n")
        f.write(f"  unfold {gname}\n  exact ")
        f.write(" <|\n    ".join(f"{gname}_cons (twoRiseBound_of_allPairs TwoRise.allPairs{N})"
                                  for (N, B) in grid))
        f.write(f" <|\n    {gname}_nil\n")
        f.write("\nend Collatz\n")

def module_of(m):
    """the module of one m (`MCycle101.lean` is the final assembly, so m = 101 gets its own name)"""
    return "MCycle101Data" if m == 101 else f"MCycle{m}"

def write_m(outdir, P, tag):
    m = P['m']
    gname = f"grid{tag}"
    steps, Ks, stall, st, certs = P['steps'], P['Ks'], P['stall'], P['st'], P['certs']
    a, b, c, d = P['abcd']
    fuel = P['fuel']
    with open(os.path.join(outdir, f"{module_of(m)}.lean"), "w") as f:
        f.write(f"import Collatz.MCycleWalk\nimport Collatz.MCycleGrid{tag}\n\n")
        f.write(f"/-!\n# No Collatz {m}-cycle when every `n ≤ 2⁷¹` reaches 1\n\n"
                f"Generated by `research/scripts/mcycle101_certgen/gen_lean.py`: the bootstrap at the floor\n"
                f"`2⁷¹ + 1` ({len(steps)} steps, `K ≥ {Ks}`), the stair ({len(st)} entries), the Rhin\n"
                f"ceiling `K < {P['Kceil']}`, the Farey walk ({P['nodes']} nodes), {len(certs)} listed shape(s)\n"
                f"with their chain certificates (two-rise bounds from `{gname}`).\n-/\n\n")
        f.write("namespace Collatz\n\n")
        boot = ",\n    ".join(lean_step(s_) for s_ in steps)
        stairs = ",\n    ".join(lean_stair_entry(e) for e in st)
        cs = ",\n    ".join(lean_cert(cc) for cc in certs)
        f.write(f"/-- The exclusion data for `m = {m}`. -/\n")
        f.write(f"def data{m} : MData where\n")
        f.write(f"  boot := [{boot}]\n")
        f.write(f"  Ks := {Ks}\n")
        f.write(f"  root := {lean_step(stall)}\n")
        f.write(f"  ra := {a}\n  rb := {b}\n  rc := {c}\n  rd := {d}\n")
        f.write(f"  stair := [{stairs}]\n")
        f.write(f"  Kceil := {P['Kceil']}\n  V := {P['V']}\n  cexp := {P['cexp']}\n  kexp := {P['kexp']}\n")
        f.write(f"  fuel := {fuel}\n")
        f.write(f"  certs := [{cs}]\n\n")
        f.write(f"theorem data{m}_ok : mOK {m} {S} {gname} data{m} = true := by\n  decide +kernel\n\n")
        f.write(f"/-- **No Collatz {m}-cycle** whose elements all exceed `2⁷¹`, given `RhinBound`. -/\n")
        f.write(f"theorem no_{m}_cycle_of_floor (hR : RhinBound) {{x p : ℕ}} (hx : 0 < x) (hp : 0 < p)\n"
                f"    (hcyc : T^[p] x = x) (hx1 : x ≠ 1) (hx2 : x ≠ 2) (hlow : ∀ j, 2 ^ 71 < T^[j] x) :\n"
                f"    numLocalMin x p ≠ {m} := fun hm =>\n"
                f"  mOK_sound hR {gname}_ok (by norm_num) data{m}_ok hx hp hcyc hx1 hx2 hm hlow\n\n")
        f.write("end Collatz\n")

def main():
    args = sys.argv[1:]
    tag, outdir = args[0], args[1]
    args = args[2:]
    gridNs, reuse, parts = None, {}, 1
    while args and args[0].startswith("--"):
        if args[0] == "--grid":
            gridNs = [int(x) for x in args[1].split(",")]
        elif args[0] == "--reuse":
            t2, ns = args[1].split(":")
            reuse = {int(x): t2 for x in ns.split(",")}
        elif args[0] == "--parts":
            parts = int(args[1])
        args = args[2:]
    ms = list(map(int, args))
    plans = []
    Ns = set()
    for m in ms:
        P = plan_m(m, need_ns=gridNs is None)
        plans.append(P)
        Ns |= P['Ns']
        print(m, "boot", len(P['steps']), "stair", len(P['st']), "nodes", P['nodes'],
              "shapes", len(P['certs']), "N", sorted(P['Ns']), flush=True)
    if gridNs is not None:
        Ns = set(gridNs)
    grid = sorted((N, Mbar(N)) for N in Ns)
    for P in plans:
        for cc in P['certs']:
            assert shape_ok(P['m'], grid, cc), (P['m'], cc['K'])
    print("grid", grid, flush=True)
    own = [(N, B) for (N, B) in grid if N not in reuse]
    ps = split_parts(own, parts) if parts > 1 else [own]
    mods = []
    for j, part in enumerate(ps):
        name = f"MCycleTwoRise{tag}" if len(ps) == 1 else f"MCycleTwoRise{tag}{j + 1}"
        write_tworise(outdir, name, part)
        mods.append(name)
        print(name, "N", [N for N, _ in part], "sumN", sum(N for N, _ in part), flush=True)
    reused_mods = sorted(set(f"MCycleTwoRise{reuse[N]}" for N, _ in grid if N in reuse))
    write_grid(outdir, tag, grid, reused_mods + mods)
    for P in plans:
        write_m(outdir, P, tag)

if __name__ == "__main__":
    main()
