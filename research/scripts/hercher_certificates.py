#!/usr/bin/env python3
"""Certificates for lean/Collatz/HercherBootstrap.lean and lean/Collatz/LogTwoThreeBounds.lean.

Replays the m = 91 chain of Hercher's Theorem 23 at X0 = 695 * 2^60 with the repaired Theorem 21
(research/scripts/hercher_thm23_bootstrap.py, imported unchanged), rounds every eps_j up to a short
rational eps'_j >= eps_j (a larger eps only weakens the hypothesis "delta < (K+L)/K < delta + eps"),
and computes for every step the Farey certificate: Farey neighbours a/b < c/d (c*b - a*d = 1) with
a/b <= delta_lo and delta_hi + eps'_j <= c/d whose mediant (a+c)/(b+d) is the simplest fraction in
(delta_lo, delta_hi + eps'_j).  Every fraction strictly between a/b and c/d has denominator >= b + d
(Eliahou 1993, Lemma 3.1; Hercher's Lemma 22), so every 91-cycle with K >= K_{j-1} has K >= b + d = K_j.
Here [delta_lo, delta_hi] is the enclosure of delta = log2 3 that LogTwoThreeBounds.lean proves:
  log 2         = sum_{i<n2} (1/2)^(i+1)/(i+1) + r2,   |r2| <= 2^-n2           (Mathlib's
  log 3 - log 2 = sum_{i<n3} (1/3)^(i+1)/(i+1) + r3,   |r3| <= 1/(2 * 3^n3)     abs_log_sub_add_sum_range_le)
with n2 = 175 and n3 = 110, so that both remainders are below 2.5e-53, and
  delta_lo = floor(10^50 * l3/u2) / 10^50,  delta_hi = ceil(10^50 * u3/l2) / 10^50,
where l2 < log 2 < u2 and l3 < log 3 < u3 are the resulting rational bounds.
Everything is exact rational arithmetic (fractions.Fraction); mpmath is used only as a cross-check.

The Simons-de Weger seed K > 7.5311e11 is itself replaced by two chain steps from the trivial K >= 1
(section 2a): step 0 uses Theorem 14 with m1 = m (Theorem 21's premise fails for every m2 >= 1 when K is
small, and sum_i T(n_i) < (97 m + 73)/(54 X0) holds for every m-cycle), step 0' uses Theorem 21 with m2 = 36.

Usage: python3 research/scripts/hercher_certificates.py            (the certificates)
       python3 research/scripts/hercher_certificates.py --roadmap  (also the three checks of
       docs/hercher_formalization_roadmap.md: the vertex-free chain, all m <= 91 against the Lemma-14
       ceiling K1(m), and the one-variable bound Phi(u) against the corrigendum's vertex value; needs mpmath)
"""
from __future__ import annotations

import importlib.util
import math
import os
from decimal import Decimal, getcontext
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("hb", os.path.join(HERE, "hercher_thm23_bootstrap.py"))
hb = importlib.util.module_from_spec(spec)
spec.loader.exec_module(hb)
getcontext().prec = 200

M = 91
X0 = 695 * 2 ** 60
K_START = Fraction(753110000000)        # Simons-de Weger, Corollary 11 / Theorem 3(d): K > 7.5311e11
N2, N3 = 175, 110                        # series lengths for log 2 (x = 1/2) and log 3 - log 2 (x = 1/3)
DIGITS = 50                              # decimal digits of the delta enclosure


def log_series(x: Fraction, n: int) -> Fraction:
    """sum_{i<n} x^(i+1)/(i+1), exactly."""
    s, p = Fraction(0), x
    for i in range(n):
        s += p / (i + 1)
        p *= x
    return s


def delta_enclosure():
    s2 = log_series(Fraction(1, 2), N2)
    s3 = log_series(Fraction(1, 3), N3)
    t2 = Fraction(1, 2 ** N2)
    t3 = Fraction(1, 2 * 3 ** N3)
    l2, u2 = s2 - t2, s2 + t2
    l3, u3 = s2 + s3 - t2 - t3, s2 + s3 + t2 + t3
    scale = 10 ** DIGITS
    lo_num, hi_num = math.floor(l3 / u2 * scale), math.ceil(u3 / l2 * scale)
    d_lo, d_hi = Fraction(lo_num, scale), Fraction(hi_num, scale)
    # the two inequalities that LogTwoThreeBounds.lean checks by kernel evaluation, strict
    assert d_lo * u2 < l3 and u3 < d_hi * l2
    return s2, s3, t2, t3, l2, u2, l3, u3, d_lo, d_hi, lo_num, hi_num


def round_up(fr: Fraction, sig: int):
    """Smallest rational with `sig` significant decimal digits that is >= fr, as (n, k) with value n / 10^k."""
    e = math.floor(math.log10(float(fr)))
    k = sig - 1 - e
    return math.ceil(fr * Fraction(10) ** k), k


def farey_certificate(alpha: Fraction, beta: Fraction):
    """Farey neighbours l = a/b <= alpha < beta <= c/d = r with the mediant inside (alpha, beta)."""
    assert Fraction(1) <= alpha < beta <= Fraction(2)
    l, r = (1, 1), (2, 1)
    while True:
        m = (l[0] + r[0], l[1] + r[1])
        mf = Fraction(*m)
        if mf <= alpha:
            l = m
        elif mf >= beta:
            r = m
        else:
            return l, r


def eps_thm14(K: Fraction, m: int, X0: int) -> Fraction:
    """Theorem 16 with Theorem 14 (m1 = m): (K+L)/K < delta + (97 m + 73)/(54 X0 * 3 K log 2), rounded up."""
    Kd = Decimal(K.numerator) / Decimal(K.denominator)
    e = Decimal(97 * m + 73) / (Decimal(54) * Decimal(X0)) / (3 * Kd * hb.LN2)
    return Fraction(str(e * (1 + Decimal(10) ** -40)))


def certified_step(K: Fraction, eps: Fraction, d_lo: Fraction, d_hi: Fraction):
    """Round eps up to a short decimal without changing the denominator bound; return the Farey certificate."""
    K_ref = Fraction(hb.simplest_between(hb.DELTA_LO, hb.DELTA_HI + eps).denominator)
    for sig in range(4, 40):
        eps_n, eps_k = round_up(eps, sig)
        eps_r = Fraction(eps_n, 10 ** eps_k)
        if Fraction(hb.simplest_between(d_lo, d_hi + eps_r).denominator) == K_ref:
            break
    else:
        raise RuntimeError("could not round eps without changing the denominator bound")
    (a, b), (c, d) = farey_certificate(d_lo, d_hi + eps_r)
    assert c * b - a * d == 1 and Fraction(a, b) <= d_lo and d_hi + eps_r <= Fraction(c, d)
    assert b + d == K_ref, (b + d, K_ref)
    return eps_n, eps_k, eps_r, a, b, c, d, K_ref


def main() -> None:
    s2, s3, t2, t3, l2, u2, l3, u3, d_lo, d_hi, lo_num, hi_num = delta_enclosure()
    print("(1) delta enclosure proved by LogTwoThreeBounds.lean")
    print(f"    n2 = {N2}: |log 2 - S2| <= 2^-{N2} = {float(t2):.3e}")
    print(f"    n3 = {N3}: |log 3 - log 2 - S3| <= 1/(2*3^{N3}) = {float(t3):.3e}")
    print(f"    deltaLo = {lo_num} / 10^{DIGITS}")
    print(f"    deltaHi = {hi_num} / 10^{DIGITS}")
    print(f"    width   = {float(d_hi - d_lo):.3e}")
    try:
        import mpmath
        mpmath.mp.dps = 90
        d = mpmath.log(3) / mpmath.log(2)
        ok = mpmath.mpf(lo_num) / mpmath.mpf(10 ** DIGITS) < d < mpmath.mpf(hi_num) / mpmath.mpf(10 ** DIGITS)
        print(f"    mpmath cross-check (90 digits): deltaLo < log2(3) < deltaHi is {ok}; log2 3 = {mpmath.nstr(d, 60)}")
    except ImportError:
        print("    (mpmath not available for the cross-check)")
    print(f"    ceiling check: 1.4784 * 91 * (8/5)^91 = {1.4784 * 91 * 1.6 ** 91:.4e}")

    print("\n(2a) the seed from K >= 1 (Theorem 14, then Theorem 21 with m2 = 36) in place of Simons-de Weger")
    K = Fraction(1)
    seed_steps = []
    for j in ("0", "0'"):
        m2 = hb.m2_of(K, M, X0)
        eps = eps_thm14(K, M, X0) if m2 == 0 else hb.eps_of(K, M, m2, X0)
        eps_n, eps_k, eps_r, a, b, c, d, K_ref = certified_step(K, eps, d_lo, d_hi)
        seed_steps.append((j, m2, K, eps_n, eps_k, a, b, c, d, K_ref))
        print(f"    step {j}: premise K >= {int(K)}; {'Theorem 14, m1 = m' if m2 == 0 else f'm2 = {m2}'}; "
              f"eps = {float(eps):.4e} rounded up to {eps_n} / 10^{eps_k}")
        print(f"        certificate a/b = {a}/{b}, c/d = {c}/{d}; b + d = {b + d}")
        K = K_ref
    assert K >= K_START, "the seed steps must reach the Simons-de Weger level"
    print(f"    K >= {int(K)} >= {int(K_START)}: the chain of (2) applies")

    print("\n(2) the m = 91 chain at X0 = 695 * 2^60 with rounded-up eps and Farey certificates")
    K = K_START
    steps = []
    for j in range(1, 20):
        m2 = hb.m2_of(K, M, X0)
        assert m2 > 0
        eps = hb.eps_of(K, M, m2, X0)
        eps_n, eps_k, eps_r, a, b, c, d, K_ref = certified_step(K, eps, d_lo, d_hi)
        margin_lo = float(d_lo - Fraction(a, b))
        margin_hi = float(Fraction(c, d) - (d_hi + eps_r))
        steps.append((j, m2, K, eps_n, eps_k, a, b, c, d, K_ref))
        print(f"    step {j}: premise K >= {int(K)}; m2 = {m2}; eps = {float(eps):.4e} rounded up to "
              f"{eps_n} / 10^{eps_k} = {float(eps_r):.4e}")
        print(f"        certificate a/b = {a}/{b}, c/d = {c}/{d}; b + d = {b + d} = K_{j}")
        print(f"        margins: deltaLo - a/b = {margin_lo:.3e}, c/d - (deltaHi + eps) = {margin_hi:.3e}")
        K = K_ref
        if K > hb.K_upper_sdw(M):
            print(f"    K_{j} = {int(K)} exceeds the ceiling 1.4784 * 91 * delta^91 = {float(hb.K_upper_sdw(M)):.4e}: excluded")
            break

    print("\n(3) Lean-ready data (HercherBootstrap.lean)")
    for (j, m2, Kprev, eps_n, eps_k, a, b, c, d, Knew) in seed_steps + steps:
        print(f"    -- step {j}: {'Theorem 14 (m1 = m)' if m2 == 0 else f'm2 = {m2}'}, premise {int(Kprev)} <= K")
        print(f"    def eps{j} : ℚ := {eps_n} / 10 ^ {eps_k}")
        print(f"    -- certificate {j}: a = {a}, b = {b}, c = {c}, d = {d}, b + d = {Knew}")


# ----------------------------------------------------------------------------------------------------
# The three computations quoted in docs/hercher_formalization_roadmap.md (Sections 4 and 5a).

def _premise_ok(K: Fraction, m: int, m2: int, X0: int) -> bool:
    L = (Decimal(162) * Decimal(X0) / Decimal(97)).ln() / hb.LN2
    Kd = Decimal(K.numerator) / Decimal(K.denominator)
    return (hb.DELTA_D ** m2 - 1) / (hb.DELTA_D - 1) * L <= Decimal(m2) / Decimal(m) * Kd


def eps_vertex_free(K: Fraction, m: int, m2: int, X0: int) -> Fraction:
    """Theorem 21 with step (e') only: every window minimum has x_i >= v, so the window contributes
    3 m2/(2^v - 1) instead of 3/(2^v - 1) + 3 (m2 - 1)/(2^v - 1)^delta.  m2 = 0 means Theorem 14."""
    Kd = Decimal(K.numerator) / Decimal(K.denominator)
    if m2 == 0:
        A, tail = Decimal(97 * m + 73) / (Decimal(54) * Decimal(X0)), Decimal(0)
    else:
        v = Decimal(m2) / Decimal(m) * Kd * (hb.DELTA_D - 1) / (hb.DELTA_D ** m2 - 1)
        two_v = (min(v, Decimal(2000)) * hb.LN2).exp()          # 2^v - 1 >= 2^min(v, 2000) - 1: still an upper bound
        A = Decimal(0) if m2 == m else (Decimal(3) / Decimal(X0) if m2 == m - 1
                                         else Decimal(97 * (m - m2) + 73) / (Decimal(54) * Decimal(X0)))
        tail = Decimal(3) * m2 / (two_v - 1)
    return Fraction(str((A + tail) / (3 * Kd * hb.LN2) * (1 + Decimal(10) ** -40)))


def chain(m: int, X0: int, ceiling: Fraction, eps_fn, optimise_m2: bool):
    """Bootstrap from K >= 1; eps_fn(K, m, m2, X0) with m2 = 0 meaning Theorem 14.  Returns (excluded, steps, K)."""
    K = Fraction(1)
    for steps in range(1, 60):
        cands = [m2 for m2 in range(0, m + 1) if m2 == 0 or _premise_ok(K, m, m2, X0)]
        if optimise_m2:
            m2, eps = min(((m2, eps_fn(K, m, m2, X0)) for m2 in cands), key=lambda t: t[1])
        else:
            m2 = max(cands)
            eps = eps_fn(K, m, m2, X0)
        K_new = Fraction(hb.simplest_between(hb.DELTA_LO, hb.DELTA_HI + eps).denominator)
        if K_new > ceiling:
            return True, steps, K_new
        if K_new <= K:
            return False, steps, K_new
        K = K_new
    return False, 60, K


def eps_hercher(K: Fraction, m: int, m2: int, X0: int) -> Fraction:
    return eps_thm14(K, m, X0) if m2 == 0 else hb.eps_of(K, m, m2, X0)


def roadmap_checks() -> None:
    import mpmath
    mp = mpmath.mp
    mp.dps = 50
    d = mpmath.log(3) / mpmath.log(2)
    print("\n(4) roadmap check 1: the vertex-free Theorem 21 (step (e') only), best admissible m2 at each step")
    for m in range(84, 92):
        ok, steps, Kf = chain(m, X0, hb.K_upper_sdw(m), eps_vertex_free, optimise_m2=True)
        print(f"    m = {m}: {'excluded' if ok else 'survives'} after {steps} steps, final K >= {float(Kf):.3e}"
              f" (ceiling 1.4784 m delta^m = {float(hb.K_upper_sdw(m)):.3e})")

    print("\n(5) roadmap check 2: every m <= 91 against the Lemma-14 ceiling K1(m) of Simons-de Weger")
    b = (1 + 1 / mpmath.mpf(X0)) / mpmath.power(2, 1 / d)

    def c_m(m):
        return mpmath.power(2, mpmath.mpf(m) / d * (d - 1) / (mpmath.power(d, m) - 1)) * \
            mpmath.power(b, d / (d - 1) - mpmath.mpf(m) / (mpmath.power(d, m) - 1))

    def K1(m):
        cm = c_m(m)
        g = lambda x: -mpmath.mpf('13.3') * (mpmath.mpf('0.46057') + mpmath.log(x)) - mpmath.log(m * cm) \
            + (d - 1) / (mpmath.power(d, m) - 1) * x * mpmath.log(2)
        xs = [mpmath.power(10, k / mpmath.mpf(4)) for k in range(0, 160)]
        vals = [g(x) for x in xs]
        for i in range(len(xs) - 1, 0, -1):
            if vals[i] > 0 and vals[i - 1] <= 0:
                return mpmath.findroot(g, (xs[i - 1], xs[i]), solver='bisect')
        raise RuntimeError("no root")

    all_ok = True
    for m in range(1, 92):
        k1 = K1(m)
        ok, steps, Kf = chain(m, X0, Fraction(str(k1)), eps_hercher, optimise_m2=False)
        all_ok = all_ok and ok
        if m in (1, 2, 40, 70, 85, 90, 91) or not ok:
            print(f"    m = {m:2d}: K1(m) = {float(k1):.3e}; chain from K >= 1: {'excluded' if ok else 'SURVIVES'} "
                  f"after {steps} steps, final K >= {float(Kf):.3e}")
    print(f"    every m <= 91 excluded against K1(m): {all_ok}")

    print("\n(6) roadmap check 3: the one-variable bound Phi(u) against the corrigendum's vertex value")

    def f(x):
        return 3 / (mpmath.power(2, x) - 1)

    for (m, m2, K) in ((91, 91, 205632218873398596256), (91, 47, 753110000000), (91, 67, 5267319278509397),
                       (91, 36, 6586818670)):
        v = mpmath.mpf(m2) / m * K * (d - 1) / (mpmath.power(d, m2) - 1)
        vertex = f(v) + sum(f(mpmath.power(d, r) * v) for r in range(1, m2))
        umax = (v * (mpmath.power(d, m2) - 1) - (d - 1)) / (mpmath.power(d, m2 - 1) - 1)
        worst = mpmath.mpf(0)
        for t in range(0, 401):
            u = v + (umax - v) * t / mpmath.mpf(400)
            s = f(u)
            for r in range(1, m2):
                L = (v * (mpmath.power(d, m2) - 1) - u * (mpmath.power(d, r) - 1)) / (mpmath.power(d, m2 - r) - 1)
                B = u / mpmath.power(d, m2 - r)
                s += f(max(L, B))
            worst = max(worst, s)
        print(f"    m2 = {m2}, K = {K}: v = {float(v):.4f}, vertex value = {float(vertex):.4e}, "
              f"max_u Phi(u) = {float(worst):.4e}, ratio = {float(worst / vertex):.6f}")


if __name__ == "__main__":
    import sys
    main()
    if "--roadmap" in sys.argv[1:]:
        roadmap_checks()
