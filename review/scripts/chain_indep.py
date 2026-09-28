"""Independent transcription of the Lean shape-certificate check (Collatz/MCycleChain.lean:
chainF, chainG, gridB, chainNext, chainSum, ShapeCert.room, uOK, ShapeCert.Y0, shapeOK) from the
Lean source, NOT from the repo's Python generator, applied to the certificates in the Lean data files.
Also transcribes rhinOK (HercherAll.lean) for the Rhin ceilings."""
from fractions import Fraction as Fr
import re, sys

deltaUp = Fr(1584962501, 10**9)
deltaLo = Fr(158496250072115618145373894394781650875981440769248, 10**50)
deltaHi = Fr(158496250072115618145373894394781650875981440769249, 10**50)
L2LO = Fr(6931471803, 10**10)
L2HI = Fr(6931471808, 10**10)

def geomQ(q, n):                     # Σ_{d<n} q^d
    return sum((q**d for d in range(n)), Fr(0))

def chainF(Y):                       # ⌈1.584962501 Y⌉
    return (Y * 1584962501 + 999999999) // 1000000000

def chainG(S, B, Y):                 # Nat subtraction truncates at 0
    v = Y + (584962501 * B * 2**S + 999999999) // 1000000000 + 1 - 2 * 2**S
    return max(v, 0)

def gridB(S, Y, grid):
    for (N, B) in grid:
        if Y <= N * 2**S:
            return B
    return None

def chainNext(S, grid, Yp, Yc):
    B = gridB(S, Yp, grid)
    if B is None:
        return chainF(Yc)
    return min(chainF(Yc), chainG(S, B, Yp)) if 2 * 2**S <= Yp else chainF(Yc)

def chainSum(S, grid, f, Yp, Yc, acc):
    while f > 0:
        f, Yp, Yc, acc = f - 1, Yc, chainNext(S, grid, Yp, Yc), acc + Yc
    return acc

def room(c):
    K, P, m2, N, M = c['K'], c['P'], c['m2'], c['N'], c['M']
    return (Fr(P) - K * deltaHi) * L2LO - Fr(1, 2**N - 1) - Fr(m2 - 1, 2**M - 1)

def uOK(m, c):
    K, P, m2, N, M, Ub = c['K'], c['P'], c['m2'], c['N'], c['M'], c['Ub']
    r = room(c)
    return (1 <= m2 <= m and 1 <= N and 1 <= M
            and Fr(N) * m * geomQ(deltaUp, m2) <= m2 * K
            and Fr(M) * m * (1 + geomQ(deltaUp, m2 - 1)) <= m2 * K
            and Fr(K) * deltaHi <= P and 0 < r and Fr(max(m - m2, 0)) <= Ub * r)

def Y0(c, S):
    return (c['Pe'] * 2**S + c['Q'] - 1) // c['Q']

def shapeOK(m, S, grid, c):
    if not uOK(m, c):
        return False, None
    if c['Ub'] <= 2**71 + 1:
        return True, 0.0
    if not (1 <= c['Q'] and c['Ub'] ** c['Q'] <= 2 ** c['Pe']):
        return False, None
    y0 = Y0(c, S)
    s = chainSum(S, grid, m - 1, y0, chainF(y0), y0)
    return s < c['K'] * 2**S, s / (c['K'] * 2**S)

def rhinOK(m, Kf, V, c, k):
    return (1 <= m and 1 <= V and Fr(V) * geomQ(deltaUp, m) <= Kf and geomQ(deltaUp, m) <= 2**c
            and 2 * m <= 2**k
            and Fr(133, 10) * (12 + c) * L2HI - Fr(133, 10) + Fr(133, 10) * Fr(46057, 100000) + k * L2HI
                < Fr(V) * (L2LO - Fr(133, 10 * 4096)))

def parse_grid(path, name):
    s = open(path).read()
    body = re.search(r'def ' + name + r' : List \(ℕ × ℕ\) := \[(.*?)\]', s, re.S).group(1)
    return [(int(a), int(b)) for a, b in re.findall(r'\((\d+), (\d+)\)', body)]

def parse_data(path):
    s = open(path).read()
    certs = re.search(r'certs := \[(.*?)\]\n', s, re.S).group(1)
    out = []
    for t in re.findall(r'⟨([^⟩]*)⟩', certs):
        K, P, m2, N, M, Ub, Pe, Q = [int(x) for x in t.split(',')]
        out.append(dict(K=K, P=P, m2=m2, N=N, M=M, Ub=Ub, Pe=Pe, Q=Q))
    m = int(re.search(r'def data(\d+) : MData', s).group(1))
    Kceil = int(re.search(r'Kceil := (\d+)', s).group(1))
    V = int(re.search(r'V := (\d+)', s).group(1)); cexp = int(re.search(r'cexp := (\d+)', s).group(1)); kexp = int(re.search(r'kexp := (\d+)', s).group(1))
    S = int(re.search(r'theorem data\d+_ok : mOK \d+ (\d+) grid(\w+) data', s).group(1))
    gname = re.search(r'theorem data\d+_ok : mOK \d+ \d+ (grid\w+) data', s).group(1)
    return m, S, gname, out, (Kceil, V, cexp, kexp)

gridLo = parse_grid('Collatz/MCycleGridLo.lean', 'gridLo')
gridHi = parse_grid('Collatz/MCycleGridHi.lean', 'gridHi')
grids = {'gridLo': gridLo, 'gridHi': gridHi}
print("gridLo points", len(gridLo), "gridHi points", len(gridHi))
for path in ['Collatz/MCycle92.lean', 'Collatz/MCycle96.lean', 'Collatz/MCycle97.lean', 'Collatz/MCycle101Data.lean']:
    m, S, gname, certs, (Kceil, V, cexp, kexp) = parse_data(path)
    print(f"{path}: m={m} S={S} {gname} certs={len(certs)} rhinOK(Kceil={Kceil})={rhinOK(m, Kceil, V, cexp, kexp)} rhinOK(Kceil-1)={rhinOK(m, Kceil-1, V, cexp, kexp)}")
    worst = 0
    for c in certs:
        ok, ratio = shapeOK(m, S, grids[gname], c)
        if ratio: worst = max(worst, ratio)
        if not ok:
            print("   FAIL", c)
    print(f"   all shapeOK: {all(shapeOK(m, S, grids[gname], c)[0] for c in certs)}; worst chain/K = {worst:.4f}")
