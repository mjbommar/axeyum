#!/usr/bin/env python3
"""Check the arithmetic reduction from a conductor bound to Lemire's endpoint bound.

This does not prove the conductor bound.  It verifies, with integer arithmetic,
that the explicit proposed bound would imply the required endpoint discrepancy
from ell=194 onward; the committed degree-1-through-400 certificates cover the
remaining endpoint degrees.
"""

from __future__ import annotations

import argparse


DEFAULT_CONSTANT = 8
DEFAULT_POWER = 12
DEFAULT_THRESHOLD = 194
FOURTH_MOMENT_CONSTANT = 64
FOURTH_MOMENT_POWER = 2
FOURTH_MOMENT_THRESHOLD = 200


def fail(message: str) -> None:
    raise SystemExit(f"GF2_HAYES_SUFFICIENT|status=FAIL|error={message}")


def rounded_geometric_sum(ell: int, power: int) -> int:
    """An integer upper bound for sum j^power * 2^(j/2)."""
    return sum(j**power * (1 << ((j + 1) // 2)) for j in range(1, ell + 1))


def induction_term_holds(ell: int, constant: int, power: int) -> bool:
    """The new term at ell+1 fits in the slack of doubling 2^ell."""
    left = 2 * constant * (ell + 1) ** power * (1 << ((ell + 2) // 2))
    return left <= 1 << ell


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--constant", type=int, default=DEFAULT_CONSTANT)
    parser.add_argument("--power", type=int, default=DEFAULT_POWER)
    parser.add_argument("--threshold", type=int, default=DEFAULT_THRESHOLD)
    arguments = parser.parse_args()
    constant = arguments.constant
    power = arguments.power
    threshold = arguments.threshold
    if constant <= 0 or power < 0 or threshold <= 0:
        fail("constant and threshold must be positive and power nonnegative")
    if 2 * threshold > 400:
        fail("finite remainder exceeds the checked degree-400 range")

    # At n <= 2 ell+2, the proposed conductor estimate and telescoping give
    #   |Delta| <= 2*C*sum_j j^a 2^(j/2).
    # Rounding each half power upward keeps this check integral.
    base_left = 2 * constant * rounded_geometric_sum(threshold, power)
    base_right = 1 << threshold
    if base_left > base_right:
        fail("base endpoint inequality does not hold")

    # For each parity, the ratio of right side to the next induction term
    # increases every two steps once
    #   2 (ell+1)^POWER >= (ell+3)^POWER.
    # Checking the two parity seeds and that monotonicity inequality at the
    # first seed proves the integer inequality for every ell >= THRESHOLD.
    if not induction_term_holds(threshold, constant, power):
        fail("even induction seed does not hold")
    if not induction_term_holds(threshold + 1, constant, power):
        fail("odd induction seed does not hold")
    if 2 * (threshold + 1) ** power < (threshold + 3) ** power:
        fail("two-step induction ratio is not monotone at the threshold")

    # Proper-divisor terms in Hayes inversion are bounded by n*2^(n/3)
    # after separating the square term when n is even.  At the two first
    # endpoint degrees, the following sixth-power forms are exact integer
    # versions of the required strict inequalities:
    #
    #   odd:  n*2^(n/3) < 2^((n-1)/2)  iff  n^6 < 2^(n-3)
    #   even: n*2^(n/3) < 2^((n-2)/2)  iff  n^6 < 2^(n-6).
    odd_degree = 2 * threshold + 1
    even_degree = 2 * threshold + 2
    if odd_degree**6 >= 1 << (odd_degree - 3):
        fail("odd proper-divisor margin does not hold")
    if even_degree**6 >= 1 << (even_degree - 6):
        fail("even proper-divisor margin does not hold")
    # Advancing within either parity multiplies the exponential side by four;
    # this seed inequality proves the polynomial side grows by less than four,
    # and the ratio only decreases thereafter.
    if (odd_degree + 2) ** 6 >= 4 * odd_degree**6:
        fail("proper-divisor induction ratio is not monotone")

    print(
        "GF2_HAYES_SUFFICIENT|status=PASS|"
        f"conductor_bound={constant}*j^{power}*2^((n+j)/2)|ell>={threshold}|"
        "endpoint_abs_discrepancy_le_2powell=true|"
        "proper_divisor_margin=true|"
        "finite_remainder_degrees=1..400"
    )

    # Independently check the newer fourth-moment implication.  The assumed
    # endpoint estimate is M_4 <= C*ell^a*2^(3ell).  Since
    # max |Delta_e|^4 <= M_4, it gives max |Delta_e| <= 2^ell whenever
    # C*ell^a <= 2^ell.  This is an implication check, not a proof of M_4.
    fm_constant = FOURTH_MOMENT_CONSTANT
    fm_power = FOURTH_MOMENT_POWER
    fm_threshold = FOURTH_MOMENT_THRESHOLD
    if 2 * fm_threshold > 400:
        fail("fourth-moment finite remainder exceeds degree 400")
    if fm_constant * fm_threshold**fm_power > 1 << fm_threshold:
        fail("fourth-moment envelope does not imply the discrepancy bound")
    if (fm_threshold + 1) ** fm_power > 2 * fm_threshold**fm_power:
        fail("fourth-moment induction ratio is not monotone")

    fm_odd_degree = 2 * fm_threshold + 1
    fm_even_degree = 2 * fm_threshold + 2
    if fm_odd_degree**6 >= 1 << (fm_odd_degree - 3):
        fail("fourth-moment odd proper-divisor margin does not hold")
    if fm_even_degree**6 >= 1 << (fm_even_degree - 6):
        fail("fourth-moment even proper-divisor margin does not hold")
    if (fm_odd_degree + 2) ** 6 >= 4 * fm_odd_degree**6:
        fail("fourth-moment proper-divisor induction ratio is not monotone")

    print(
        "GF2_HAYES_FOURTH_MOMENT_SUFFICIENT|status=PASS|"
        "implication=checked|assumption_status=OPEN|"
        f"moment_bound={fm_constant}*ell^{fm_power}*2^(3ell)|"
        f"ell>={fm_threshold}|endpoint_abs_discrepancy_le_2powell=true|"
        "proper_divisor_margin=true|finite_remainder_degrees=1..400|"
        f"first_symbolic_degrees={fm_odd_degree},{fm_even_degree}"
    )


if __name__ == "__main__":
    main()
