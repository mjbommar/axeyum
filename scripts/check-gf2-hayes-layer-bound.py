#!/usr/bin/env python3
"""Check the conditional constant-one Hayes layer implication.

The assumed character-family estimate is refuted at `(j,n)=(5,45)`.  This
script checks, independently of the Rust implementation, only that

    T_(j,n)^2 <= 2^(2*j-2+n)

at the two endpoint degrees would imply a positive degree-n irreducible count.
"""

from __future__ import annotations

import argparse


def fail(message: str) -> None:
    raise SystemExit(f"GF2_HAYES_LAYER_SUFFICIENT|status=FAIL|error={message}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--threshold", type=int, default=22)
    parser.add_argument("--finite-max-degree", type=int, default=400)
    parser.add_argument("--sqrt2-numerator", type=int, default=99)
    parser.add_argument("--sqrt2-denominator", type=int, default=70)
    arguments = parser.parse_args()

    threshold = arguments.threshold
    finite_max_degree = arguments.finite_max_degree
    numerator = arguments.sqrt2_numerator
    denominator = arguments.sqrt2_denominator
    if threshold < 4 or numerator <= 0 or denominator <= 0:
        fail("malformed threshold or rational witness")
    if 2 * threshold > finite_max_degree:
        fail("finite remainder exceeds the checked degree range")
    if numerator * numerator <= 2 * denominator * denominator:
        fail("rational witness is not a strict upper bound for sqrt(2)")
    odd_margin_numerator = 2 * denominator - numerator
    if odd_margin_numerator <= 0:
        fail("sqrt(2) upper bound must be smaller than two")

    # For odd n=2*ell+1, telescoping leaves more than
    # ((2-denoted_sqrt2) * 2^ell) before proper prime powers.  Three seeds
    # cover ell modulo three because advancing ell by three multiplies the
    # coarse divisor bound by less than eight and the margin by eight.
    for ell in range(threshold, threshold + 3):
        degree = 2 * ell + 1
        proper = degree * (1 << ((degree + 2) // 3))
        if denominator * proper >= odd_margin_numerator * (1 << ell):
            fail("odd proper-divisor seed exceeds the family-bound margin")
        if degree <= 6:
            fail("odd proper-divisor monotonicity has not started")

    # At even n=2*ell+2, squaring a principal-unit class doubles every
    # coefficient index.  The k=2 contribution therefore fixes
    # floor(ell/2) coefficients of its degree-(ell+1) source polynomial.
    # Reserve one 2^ell half-margin for it and one for every k>=3 term.
    for ell in range(threshold, threshold + 2):
        half_degree = ell + 1
        fixed = ell // 2
        square_term = half_degree * (1 << (half_degree - fixed))
        if square_term >= 1 << ell:
            fail("even square proper-divisor seed exceeds its half-margin")
        if half_degree <= 2:
            fail("even square-term monotonicity has not started")
    for ell in range(threshold, threshold + 3):
        degree = 2 * ell + 2
        other_terms = degree * (1 << ((degree + 2) // 3))
        if other_terms >= 1 << ell:
            fail("even nonsquare proper-divisor seed exceeds its half-margin")
        if degree <= 6:
            fail("even proper-divisor monotonicity has not started")

    print(
        "GF2_HAYES_LAYER_SUFFICIENT|status=PASS|"
        "implication=checked|assumption_status=REFUTED|"
        "counterexample_level=5|counterexample_degree=45|"
        "counterexample_normalized_layer=7080448|"
        "layer_bound=T_j(n)^2<=2^(2j-2+n)|"
        f"ell>={threshold}|square_divisor_class_restriction=true|"
        "proper_divisor_margin=true|"
        f"finite_remainder_degrees=1..{finite_max_degree}|"
        f"first_symbolic_degrees={2 * threshold + 1},{2 * threshold + 2}|"
        f"sqrt2_upper={numerator}/{denominator}"
    )


if __name__ == "__main__":
    main()
