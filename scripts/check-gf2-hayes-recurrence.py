#!/usr/bin/env python3
"""Cross-check the exact type-II Hayes recurrence against direct GF(2) search.

This is deliberately a small research oracle, not a universal existence proof.
It uses integer group-ring arithmetic for principal units and an algebraically
separate bit-polynomial Rabin test for the target short intervals.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction


EXPECTED = (1, 1, 1, 2, 3, 2, 4, 7, 4, 12, 6, 19, 20, 28, 33, 59, 49, 101)


def fail(message: str) -> None:
    raise SystemExit(f"GF2_HAYES|status=FAIL|error={message}")


def polynomial_degree(value: int) -> int:
    return value.bit_length() - 1


def polynomial_remainder(dividend: int, divisor: int) -> int:
    while polynomial_degree(dividend) >= polynomial_degree(divisor):
        dividend ^= divisor << (polynomial_degree(dividend) - polynomial_degree(divisor))
    return dividend


def polynomial_gcd(left: int, right: int) -> int:
    while right:
        left, right = right, polynomial_remainder(left, right)
    return left


def polynomial_multiply_mod(left: int, right: int, modulus: int) -> int:
    result = 0
    modulus_degree = polynomial_degree(modulus)
    while right:
        if right & 1:
            result ^= left
        right >>= 1
        left <<= 1
        if polynomial_degree(left) >= modulus_degree:
            left ^= modulus
    return result


def distinct_prime_divisors(value: int) -> list[int]:
    divisors: list[int] = []
    candidate = 2
    while candidate * candidate <= value:
        if value % candidate == 0:
            divisors.append(candidate)
            while value % candidate == 0:
                value //= candidate
        candidate += 1
    if value > 1:
        divisors.append(value)
    return divisors


def is_irreducible(polynomial: int, degree: int) -> bool:
    x = 0b10
    frobenius = [x]
    for _ in range(degree):
        frobenius.append(
            polynomial_multiply_mod(frobenius[-1], frobenius[-1], polynomial)
        )
    if frobenius[degree] != x:
        return False
    return all(
        polynomial_gcd(polynomial, frobenius[degree // prime] ^ x) == 1
        for prime in distinct_prime_divisors(degree)
    )


def direct_interval_count(degree: int) -> int:
    tail_degree = degree // 2
    return sum(
        is_irreducible((1 << degree) | tail, degree)
        for tail in range(1 << (tail_degree + 1))
    )


def unit_multiply(left: int, right: int, ell: int) -> int:
    """Multiply coefficient bitsets modulo x^(ell+1)."""
    product = 0
    for left_degree in range(ell + 1):
        if not (left >> left_degree) & 1:
            continue
        for right_degree in range(ell + 1 - left_degree):
            if (right >> right_degree) & 1:
                product ^= 1 << (left_degree + right_degree)
    return product


@dataclass(frozen=True)
class PrincipalUnitGroup:
    ell: int
    elements: tuple[int, ...]
    product: tuple[tuple[int, ...], ...]
    identity: int

    @classmethod
    def construct(cls, ell: int) -> PrincipalUnitGroup:
        generators: list[int] = []
        orders: list[int] = []
        for odd_degree in range(1, ell + 1, 2):
            order = 1
            while odd_degree * order <= ell:
                order *= 2
            generators.append(1 | (1 << odd_degree))
            orders.append(order)

        elements: list[int] = []

        def enumerate_products(index: int, value: int) -> None:
            if index == len(generators):
                elements.append(value)
                return
            power = value
            for _ in range(orders[index]):
                enumerate_products(index + 1, power)
                power = unit_multiply(power, generators[index], ell)

        enumerate_products(0, 1)
        if len(elements) != 1 << ell or len(set(elements)) != len(elements):
            fail(f"E_{ell} generator decomposition is not bijective")
        element_index = {element: index for index, element in enumerate(elements)}
        product = tuple(
            tuple(
                element_index[unit_multiply(left, right, ell)] for right in elements
            )
            for left in elements
        )
        return cls(ell, tuple(elements), product, element_index[1])

    def convolution(self, left: list[int], right: list[int]) -> list[int]:
        result = [0] * len(self.elements)
        for left_index, left_count in enumerate(left):
            if left_count == 0:
                continue
            for right_index, right_count in enumerate(right):
                if right_count:
                    result[self.product[left_index][right_index]] += (
                        left_count * right_count
                    )
        return result


def monic_class_sum(group: PrincipalUnitGroup, degree: int) -> list[int]:
    size = len(group.elements)
    if degree >= group.ell:
        return [1 << (degree - group.ell)] * size

    element_index = {element: index for index, element in enumerate(group.elements)}
    result = [0] * size
    for tail in range(1 << degree):
        reciprocal = 1
        for coefficient_index in range(1, degree + 1):
            if (tail >> (degree - coefficient_index)) & 1:
                reciprocal |= 1 << coefficient_index
        result[element_index[reciprocal]] += 1
    if sum(result) != 1 << degree:
        fail(f"A_{degree} does not contain every monic polynomial")
    return result


def identity_irreducible_count(ell: int, target_degree: int) -> int:
    group = PrincipalUnitGroup.construct(ell)
    class_sums = [
        monic_class_sum(group, degree) for degree in range(target_degree + 1)
    ]
    mangoldt = [[0] * len(group.elements) for _ in range(target_degree + 1)]
    irreducibles = [[0] * len(group.elements) for _ in range(target_degree + 1)]

    for degree in range(1, target_degree + 1):
        current = [degree * value for value in class_sums[degree]]
        for earlier in range(1, degree):
            correction = group.convolution(mangoldt[earlier], class_sums[degree - earlier])
            current = [left - right for left, right in zip(current, correction, strict=True)]
        mangoldt[degree] = current

        primitive = current.copy()
        for divisor in range(1, degree):
            if degree % divisor:
                continue
            exponent = degree // divisor
            for class_index, count in enumerate(irreducibles[divisor]):
                if count == 0:
                    continue
                powered = group.identity
                for _ in range(exponent):
                    powered = group.product[powered][class_index]
                primitive[powered] -= divisor * count
        if any(value % degree for value in primitive):
            fail(f"degree {degree} Mobius recovery is not integral")
        irreducibles[degree] = [value // degree for value in primitive]

    return irreducibles[target_degree][group.identity]


def mangoldt_class_distribution(
    ell: int, target_degree: int
) -> tuple[PrincipalUnitGroup, list[int]]:
    """Return every exact characteristic-polynomial class population."""
    group = PrincipalUnitGroup.construct(ell)
    class_sums = [
        monic_class_sum(group, degree) for degree in range(target_degree + 1)
    ]
    mangoldt = [[0] * len(group.elements) for _ in range(target_degree + 1)]
    for degree in range(1, target_degree + 1):
        current = [degree * value for value in class_sums[degree]]
        for earlier in range(1, degree):
            correction = group.convolution(
                mangoldt[earlier], class_sums[degree - earlier]
            )
            current = [
                left - right for left, right in zip(current, correction, strict=True)
            ]
        mangoldt[degree] = current
    return group, mangoldt[target_degree]


def exact_conductor_second_moment(level: int, degree: int) -> int:
    """Integer group-ring/Parseval calculation independent of the Rust NTT."""
    current_group, current = mangoldt_class_distribution(level, degree)
    previous_group, previous = mangoldt_class_distribution(level - 1, degree)
    current_energy = len(current_group.elements) * sum(value * value for value in current)
    previous_energy = len(previous_group.elements) * sum(
        value * value for value in previous
    )
    return current_energy - previous_energy


def identity_class_fourier_variance(ell: int, degree: int) -> tuple[int, int]:
    """Return the uniform mean and full squared deviation via Parseval."""
    energy = sum(
        exact_conductor_second_moment(level, degree)
        for level in range(1, ell + 1)
    )
    group_order = 1 << ell
    if energy % group_order:
        fail("full-family Fourier energy is not divisible by the group order")
    return 1 << (degree - ell), energy // group_order


def fourth_moment_conductor_filtration(
    ell: int, degree: int
) -> tuple[int, int, tuple[int, ...]]:
    """Project D^2 by polynomial truncation and return exact Fourier layers.

    This deliberately does not use the Rust mixed-radix coordinate map.  The
    independently enumerated principal-unit representatives are truncated as
    coefficient bitsets and looked up in a freshly constructed quotient group.
    """
    group, distribution = mangoldt_class_distribution(ell, degree)
    mean = 1 << (degree - ell)
    squared = [
        (population - mean) ** 2 for population in distribution
    ]
    second_moment = sum(squared)
    fourth_moment = sum(value * value for value in squared)
    previous = second_moment * second_moment
    exact_layers: list[int] = []
    for level in range(1, ell + 1):
        quotient = PrincipalUnitGroup.construct(level)
        quotient_index = {
            element: index for index, element in enumerate(quotient.elements)
        }
        buckets = [0] * len(quotient.elements)
        mask = (1 << (level + 1)) - 1
        for element, value in zip(group.elements, squared, strict=True):
            buckets[quotient_index[element & mask]] += value
        cumulative = (1 << level) * sum(value * value for value in buckets)
        if cumulative < previous:
            fail(f"fourth-moment Fourier energy decreases at level {level}")
        exact_layers.append(cumulative - previous)
        previous = cumulative
    if previous != (1 << ell) * fourth_moment:
        fail("fourth-moment filtration does not recover 2^ell M_4")
    return second_moment, fourth_moment, tuple(exact_layers)


def translation_paired_conductor_level(degree: int) -> int:
    """Return 2^v_2(degree), the layer paired by alpha -> alpha + 1."""
    if degree <= 0:
        fail("translation pairing requires positive degree")
    return degree & -degree


def low_conductor_weil_split(ell: int) -> tuple[int, int, int, int]:
    """Independently check the endpoint low-conductor triangle budget."""
    if ell < 2:
        fail("low-conductor splitting requires ell at least two")
    unresolved_top_levels = min(ell, (ell - 1).bit_length() + 2)
    cutoff = ell - unresolved_top_levels
    layer_sum = 0 if cutoff < 2 else (cutoff - 2) * (1 << cutoff) + 2
    scaled_bound = 2 * layer_sum
    half_budget = 1 << (ell - 1)
    if scaled_bound > half_budget:
        fail(
            f"ell={ell}: low-conductor bound {scaled_bound} exceeds "
            f"half-budget {half_budget}"
        )
    return cutoff, unresolved_top_levels, scaled_bound, half_budget


def cumulative_discrepancy(level: int, degree: int) -> int:
    """Return 2^level Delta_(level,degree) from the integer recurrence."""
    if level == 0:
        return 0
    group, distribution = mangoldt_class_distribution(level, degree)
    return (1 << level) * (
        distribution[group.identity] - (1 << (degree - level))
    )


def centered_log_discrepancy(
    ell: int, degree: int
) -> tuple[int, int, tuple[Fraction, ...]]:
    """Recover Delta from the nonuniform logarithm, with exact rationals.

    If U is the uniform idempotent and B_d=A_d-2^d U, then the nonuniform
    factor is (1-U)+C(z), where C(z)=sum_{1<=d<ell} B_d z^d.  Hence

        Delta_(ell,n) = n [1,z^n] sum_{k>=1} (-1)^(k+1) C(z)^k/k.

    The maximum z-degree of C is ell-1, so all orders below
    ceil(n/(ell-1)) vanish before any class arithmetic is performed.
    """
    if ell < 2:
        fail("centered logarithm requires ell >= 2")
    group = PrincipalUnitGroup.construct(ell)
    size = len(group.elements)
    uniform_denominator = 1 << ell
    centered = [[Fraction(0) for _ in range(size)] for _ in range(degree + 1)]
    for row_degree in range(1, ell):
        class_sum = monic_class_sum(group, row_degree)
        uniform = Fraction(1 << row_degree, uniform_denominator)
        centered[row_degree] = [Fraction(value) - uniform for value in class_sum]

    def series_product(
        left: list[list[Fraction]], right: list[list[Fraction]]
    ) -> list[list[Fraction]]:
        result = [
            [Fraction(0) for _ in range(size)] for _ in range(degree + 1)
        ]
        for left_degree, left_row in enumerate(left):
            if left_degree > degree or not any(left_row):
                continue
            retained_right = right[: degree - left_degree + 1]
            for right_degree, right_row in enumerate(retained_right):
                if not any(right_row):
                    continue
                product = group.convolution(left_row, right_row)
                target = result[left_degree + right_degree]
                result[left_degree + right_degree] = [
                    old + value for old, value in zip(target, product, strict=True)
                ]
        return result

    minimum_order = (degree + ell - 2) // (ell - 1)
    power = centered
    discrepancy = Fraction(0)
    contributions: list[Fraction] = []
    for order in range(1, degree + 1):
        coefficient = power[degree][group.identity]
        if order < minimum_order and coefficient:
            fail(
                f"ell={ell} degree={degree}: centered order {order} "
                "appears below its degree support"
            )
        sign = 1 if order % 2 else -1
        contribution = sign * Fraction(degree, order) * coefficient
        contributions.append(contribution)
        discrepancy += contribution
        if order != degree:
            power = series_product(power, centered)
    if discrepancy.denominator != 1:
        fail(
            f"ell={ell} degree={degree}: centered discrepancy is nonintegral "
            f"({discrepancy})"
        )
    return discrepancy.numerator, minimum_order, tuple(contributions)


def main() -> None:
    observed: list[int] = []
    for degree in range(3, 21):
        ell = (degree + 1) // 2 - 1
        recurrence_count = identity_irreducible_count(ell, degree)
        direct_count = direct_interval_count(degree)
        if recurrence_count != direct_count:
            fail(
                f"degree {degree} recurrence={recurrence_count} direct={direct_count}"
            )
        observed.append(recurrence_count)

    if tuple(observed) != EXPECTED:
        fail(f"count vector differs: {observed}")
    translation_controls: list[str] = []
    for degree in range(3, 21):
        ell = (degree + 1) // 2 - 1
        paired_level = translation_paired_conductor_level(degree)
        if paired_level > ell:
            continue
        layer = cumulative_discrepancy(
            paired_level, degree
        ) - cumulative_discrepancy(paired_level - 1, degree)
        if layer != 0:
            fail(
                f"degree={degree}: translation-paired layer "
                f"{paired_level} is {layer}, expected zero"
            )
        translation_controls.append(f"{degree}:{paired_level}")
    for ell in range(2, 4_001):
        cutoff, unresolved, _, _ = low_conductor_weil_split(ell)
        if cutoff + unresolved != ell:
            fail(f"ell={ell}: low/top conductor partition does not recover ell")
    low_split_control = low_conductor_weil_split(199)
    if low_split_control[:2] != (189, 10):
        fail(f"ell=199 low-conductor split differs: {low_split_control}")
    moment = exact_conductor_second_moment(8, 17)
    if moment != 86_200_320:
        fail(f"level-8 degree-17 second moment differs: {moment}")
    cauchy_bound = 1 << (8 - 1 + 17)
    if moment <= cauchy_bound:
        fail("second-moment falsifier no longer exceeds the Cauchy bound")
    variance_controls = []
    fourth_moment_controls = []
    fourth_filtration_controls = []
    _, low_even_distribution = mangoldt_class_distribution(5, 12)
    low_even_mean = 1 << (12 - 5)
    low_even_fourth_moment = sum(
        (value - low_even_mean) ** 4 for value in low_even_distribution
    )
    low_even_candidate_bound = 64 * 5**2 * 2 ** (3 * 5)
    if low_even_fourth_moment != 73_638_400:
        fail(f"ell=5 degree=12 fourth moment differs: {low_even_fourth_moment}")
    if low_even_fourth_moment <= low_even_candidate_bound:
        fail("ell=5 degree=12 no longer refutes the fourth-moment candidate")
    for degree, expected_mean, expected_deviation in (
        (17, 512, 693_360),
        (18, 1_024, 1_861_136),
    ):
        mean, deviation = identity_class_fourier_variance(8, degree)
        if (mean, deviation) != (expected_mean, expected_deviation):
            fail(
                f"ell=8 degree={degree} Parseval diagnostic differs: "
                f"{mean}, {deviation}"
            )
        if deviation < mean * mean:
            fail("full-family Parseval unexpectedly proves identity positivity")
        _, distribution = mangoldt_class_distribution(8, degree)
        maximum_deviation = max(abs(value - mean) for value in distribution)
        expected_maximum = {17: 155, 18: 290}[degree]
        if maximum_deviation != expected_maximum:
            fail(
                f"ell=8 degree={degree} maximum class deviation differs: "
                f"{maximum_deviation}"
            )
        if min(distribution) <= 0:
            fail("ell=8 endpoint unexpectedly contains an empty Mangoldt class")
        fourth_moment = sum((value - mean) ** 4 for value in distribution)
        expected_fourth_moment = {
            17: 5_447_397_264,
            18: 54_144_813_200,
        }[degree]
        if fourth_moment != expected_fourth_moment:
            fail(
                f"ell=8 degree={degree} fourth moment differs: "
                f"{fourth_moment}"
            )
        fourth_cumulant_numerator = 256 * fourth_moment - 3 * deviation**2
        expected_cumulant = {
            17: -47_710_569_216,
            18: 3_469_590_547_712,
        }[degree]
        if fourth_cumulant_numerator != expected_cumulant:
            fail(
                f"ell=8 degree={degree} fourth cumulant differs: "
                f"{fourth_cumulant_numerator}"
            )
        fourth_moment_candidate_bound = 64 * 8**2 * 2 ** (3 * 8)
        if fourth_moment > fourth_moment_candidate_bound:
            fail("ell=8 endpoint refutes the fourth-moment candidate")
        variance_controls.append(
            f"{degree}:{mean}:{deviation}:{maximum_deviation}"
        )
        fourth_moment_controls.append(
            f"{degree}:{fourth_moment}:{fourth_cumulant_numerator}"
        )
        filtration_second, filtration_fourth, exact_layers = (
            fourth_moment_conductor_filtration(8, degree)
        )
        expected_layers = {
            17: (
                0,
                15_904_236_544,
                39_316_443_392,
                9_589_782_016,
                27_393_511_424,
                134_382_961_664,
                280_918_622_208,
                406_280_052_736,
            ),
            18: (
                45_168_150_784,
                44_340_037_632,
                188_109_840_896,
                208_663_687_168,
                1_005_923_738_624,
                1_113_833_144_320,
                3_490_103_330_816,
                4_301_103_038_464,
            ),
        }[degree]
        if (filtration_second, filtration_fourth, exact_layers) != (
            deviation,
            fourth_moment,
            expected_layers,
        ):
            fail(f"ell=8 degree={degree} fourth-moment filtration differs")
        fourth_filtration_controls.append(
            f"{degree}:{','.join(str(value) for value in exact_layers)}"
        )
    _, level_five = mangoldt_class_distribution(5, 45)
    _, level_four = mangoldt_class_distribution(4, 45)
    normalized_layer = 2 * level_five[0] - level_four[0]
    if normalized_layer != 7_080_448:
        fail(f"level-5 degree-45 normalized layer differs: {normalized_layer}")
    if normalized_layer * normalized_layer <= 1 << 45:
        fail("constant-one layer target is no longer refuted")
    centered_controls: list[str] = []
    endpoint_order_contributions: tuple[Fraction, ...] | None = None
    for ell in range(2, 6):
        for degree in (2 * ell + 1, 2 * ell + 2):
            group, distribution = mangoldt_class_distribution(ell, degree)
            expected = distribution[group.identity] - (1 << (degree - ell))
            (
                observed_discrepancy,
                minimum_order,
                order_contributions,
            ) = centered_log_discrepancy(ell, degree)
            if observed_discrepancy != expected:
                fail(
                    f"ell={ell} degree={degree}: centered={observed_discrepancy} "
                    f"recurrence={expected}"
                )
            if minimum_order < 3:
                fail(
                    f"ell={ell} degree={degree}: endpoint logarithm has order "
                    f"{minimum_order}, expected at least three"
                )
            centered_controls.append(
                f"{ell}:{degree}:{observed_discrepancy}:{minimum_order}"
            )
            if (ell, degree) == (5, 12):
                endpoint_order_contributions = order_contributions
    if endpoint_order_contributions is None:
        fail("centered order-cancellation control was not evaluated")
    nonzero_order_contributions = tuple(
        value for value in endpoint_order_contributions if value
    )
    expected_order_contributions = (
        Fraction(32),
        Fraction(-744),
        Fraction(6_144),
        Fraction(-20_736),
        Fraction(37_056),
        Fraction(-39_480),
        Fraction(26_624),
        Fraction(-11_472),
        Fraction(2_976),
        Fraction(-368),
    )
    if nonzero_order_contributions != expected_order_contributions:
        fail(
            "ell=5 degree=12 centered order contributions differ: "
            f"{nonzero_order_contributions}"
        )
    order_triangle_bound = sum(abs(value) for value in nonzero_order_contributions)
    if order_triangle_bound != 145_632:
        fail(f"centered order triangle control differs: {order_triangle_bound}")
    print(
        "GF2_HAYES|status=PASS|degrees=3..20|"
        f"counts={','.join(str(value) for value in observed)}|"
        f"level8_degree17_second_moment={moment}|"
        "generic_cauchy_route=false|"
        f"full_family_parseval_controls={','.join(variance_controls)}|"
        "full_family_parseval_route=false|"
        f"fourth_moment_controls={','.join(fourth_moment_controls)}|"
        f"fourth_filtration_controls={';'.join(fourth_filtration_controls)}|"
        f"fourth_moment_low_control=5:12:{low_even_fourth_moment}:false|"
        "fourth_moment_candidate=OPEN|"
        f"level5_degree45_normalized_layer={normalized_layer}|"
        "constant_one_layer_target=false|"
        "centered_endpoint_log=PASS|"
        "translation_pairing=PASS|"
        "low_conductor_weil_split=PASS|"
        "ell199_low_cutoff=189|ell199_unresolved_top_levels=10|"
        f"translation_controls={','.join(translation_controls)}|"
        f"centered_controls={','.join(centered_controls)}|"
        "centered_order_triangle_route=false|"
        f"ell5_degree12_order_abs_sum={order_triangle_bound}|"
        "ell5_degree12_full_discrepancy=32"
    )


if __name__ == "__main__":
    main()
