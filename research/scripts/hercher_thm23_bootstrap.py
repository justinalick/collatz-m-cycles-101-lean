#!/usr/bin/env python3
"""Hercher's Theorem 23 bootstrap (m-cycles) with the repaired Theorem 21, at any verification bound X0.

Inputs (all from Hercher, J. Integer Seq. 26 (2023) Art. 23.3.5, with the corrigendum of 14 June 2026, and
Simons-de Weger v1.44):
  Theorem 21 (repaired).  For an m-cycle with K odd and L even elements, and m2 <= m with
      ((delta^m2 - 1)/(delta - 1)) * log2(162 X0 / 97) <= (m2/m) K,     v := (m2/m) K (delta-1)/(delta^m2 - 1),
      delta < (K+L)/K < delta + eps,   eps = [A + 3/(2^v - 1) + 3 (m2-1)/(2^v - 1)^delta] / (3 K log 2),
      A = (97 (m - m2) + 73)/(54 X0)  in general,  A = 3/X0 if m2 = m-1,  A = 0 if m2 = m.
  Lemma 22.  Every fraction in the open interval (delta, delta + eps) has denominator at least that of the
      simplest fraction in the interval (Stern-Brocot).  Since (K+L)/K lies there, K is at least that denominator.
  Simons-de Weger, Corollary 11 / Theorem 3(d):  K > 7.5311e11 for 91 <= m <= 648 401, and
      K < 1.4784 m delta^m for 91 <= m <= 515 619 (their Lemma 16 with the champion table).
The bootstrap iterates: K_low -> m2(K_low) -> eps(K_low) -> new K_low := simplest denominator in
(delta, delta + eps); an m is excluded when K_low exceeds the upper bound.  eps is decreasing in K, so each
step is valid for every K >= K_low.  delta is replaced by a rational enclosure [delta_lo, delta_hi] of width
1e-150 and the interval widened to (delta_lo, delta_hi + eps), which can only lower the denominator bound.

Validation: with X0 = 695 * 2^60 (the JIS Definition 4) and m = 91 the printed sequence of Theorem 23 is
m2 = 47, 67, 77, 82, 86, 88, 91 and K > 5.2e15, 3.97e17, 4.64e18, 2.74e19, 7.76e19, 2.05e20, 7.94e21 > 2.2e20.

Usage: python3 research/scripts/hercher_thm23_bootstrap.py
"""
from __future__ import annotations

from decimal import Decimal, getcontext
from fractions import Fraction
import math

getcontext().prec = 200
LN2, LN3 = Decimal(2).ln(), Decimal(3).ln()
DELTA_D = LN3 / LN2
DELTA_LO = Fraction(str(DELTA_D.quantize(Decimal(10) ** -150)))          # truncation error < 1e-150 either way
DELTA_HI = DELTA_LO + Fraction(1, 10 ** 149)
DELTA = float(DELTA_D)


def simplest_between(a: Fraction, b: Fraction) -> Fraction:
    """The fraction with the smallest denominator strictly inside (a, b), a < b (Stern-Brocot descent)."""
    fl = a.numerator // a.denominator
    if fl + 1 < b:
        return Fraction(fl + 1)
    if a == fl:
        inv = 1 / (b - fl)
        return fl + Fraction(1, inv.numerator // inv.denominator + 1)
    return fl + 1 / simplest_between(1 / (b - fl), 1 / (a - fl))


def m2_of(K: Fraction, m: int, X0: int) -> int:
    """Largest m2 <= m with ((delta^m2 - 1)/(delta - 1)) log2(162 X0/97) <= (m2/m) K (0 if none)."""
    L = (Decimal(162) * Decimal(X0) / Decimal(97)).ln() / LN2
    Kd = Decimal(K.numerator) / Decimal(K.denominator)
    best = 0
    for m2 in range(1, m + 1):
        lhs = (DELTA_D ** m2 - 1) / (DELTA_D - 1) * L
        if lhs <= Decimal(m2) / Decimal(m) * Kd:
            best = m2
    return best


def eps_of(K: Fraction, m: int, m2: int, X0: int) -> Fraction:
    """Theorem 21's eps at K (an upper bound, rounded up to a rational)."""
    Kd = Decimal(K.numerator) / Decimal(K.denominator)
    v = Decimal(m2) / Decimal(m) * Kd * (DELTA_D - 1) / (DELTA_D ** m2 - 1)
    two_v = (v * LN2).exp()
    if m2 == m:
        A = Decimal(0)
    elif m2 == m - 1:
        A = Decimal(3) / Decimal(X0)
    else:
        A = Decimal(97 * (m - m2) + 73) / (Decimal(54) * Decimal(X0))
    tail = Decimal(3) / (two_v - 1) + Decimal(3) * (m2 - 1) / ((two_v - 1) ** DELTA_D)
    e = (A + tail) / (3 * Kd * LN2)
    e_up = e * (1 + Decimal(10) ** -40)
    return Fraction(str(e_up))


def bootstrap(m: int, X0: int, K_start: Fraction, K_upper: Fraction, verbose: bool = True):
    K = K_start
    history = []
    for it in range(60):
        m2 = m2_of(K, m, X0)
        if m2 == 0:
            if verbose:
                print(f"    m = {m}: premise of Theorem 21 fails at K = {float(K):.3e}; stop")
            return False, history
        eps = eps_of(K, m, m2, X0)
        frac = simplest_between(DELTA_LO, DELTA_HI + eps)
        K_new = Fraction(frac.denominator)
        history.append((m2, float(eps), int(K_new)))
        if verbose:
            print(f"    m = {m}: m2 = {m2:3d}, eps = {float(eps):.3e}, K > {int(K_new):.3e}"
                  + ("  (exceeds the upper bound)" if K_new > K_upper else ""))
        if K_new > K_upper:
            return True, history
        if K_new <= K:
            return False, history
        K = K_new
    return False, history


def K_upper_sdw(m: int) -> Fraction:
    return Fraction(str(Decimal("1.4784") * m * DELTA_D ** m))


def main() -> None:
    K_start = Fraction(753110000000)             # Simons-de Weger Corollary 11: K > 7.5311e11 for 91 <= m <= 648401
    print("(1) validation: X0 = 695 * 2^60, m = 91 (Hercher's Theorem 23 with the repaired Theorem 21)")
    ok, _ = bootstrap(91, 695 * 2 ** 60, K_start, K_upper_sdw(91))
    print("    excluded" if ok else "    NOT excluded")
    print("\n(2) X0 = 2^71 (Barina): largest m excluded by the same bootstrap")
    X0 = 2 ** 71
    last_ok = None
    for m in range(91, 140):
        ok, hist = bootstrap(m, X0, K_start, K_upper_sdw(m), verbose=False)
        Kfin = hist[-1][2] if hist else 0
        print(f"    m = {m:3d}: {'excluded' if ok else 'survives'}; iterations {len(hist)}, "
              f"final K > {Kfin:.3e}, upper bound 1.4784 m delta^m = {float(K_upper_sdw(m)):.3e}")
        if ok:
            last_ok = m
        elif last_ok is not None and m > last_ok + 1:
            break
    print(f"\n    conclusion: no m-cycle with m <= {last_ok} at X0 = 2^71, if the bootstrap excludes every m up to it")
    print("\n(3) the same at X0 = 695 * 2^60 for comparison")
    for m in range(91, 96):
        ok, hist = bootstrap(m, 695 * 2 ** 60, K_start, K_upper_sdw(m), verbose=False)
        print(f"    m = {m}: {'excluded' if ok else 'survives'}; final K > {hist[-1][2]:.3e}")
    print("\n(4) roadmap: least verification bound X0 (binary search on log2 X0, 0.01 steps) at which the")
    print("    bootstrap excludes m, for m = 92 .. 100; compare the Corollary-17 route of the m <= 86 note (about 2^79)")
    for m in range(92, 101):
        lo, hi = 71.0, 90.0
        if not bootstrap(m, int(2 ** hi), K_start, K_upper_sdw(m), verbose=False)[0]:
            print(f"    m = {m}: not excluded even at X0 = 2^90")
            continue
        while hi - lo > 0.01:
            mid = (lo + hi) / 2
            if bootstrap(m, int(2 ** mid), K_start, K_upper_sdw(m), verbose=False)[0]:
                hi = mid
            else:
                lo = mid
        print(f"    m = {m:3d}: excluded once X0 >= 2^{hi:.2f} = {2 ** hi / 2 ** 60:.0f} * 2^60")


if __name__ == "__main__":
    main()
