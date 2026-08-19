#!/usr/bin/env python3
"""Cross-check the exact type-II Hayes recurrence against direct GF(2) search.

This is deliberately a small research oracle, not a universal existence proof.
It uses integer group-ring arithmetic for principal units and an algebraically
separate bit-polynomial Rabin test for the target short intervals.
"""

from __future__ import annotations

from dataclasses import dataclass


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
    moment = exact_conductor_second_moment(8, 17)
    if moment != 86_200_320:
        fail(f"level-8 degree-17 second moment differs: {moment}")
    cauchy_bound = 1 << (8 - 1 + 17)
    if moment <= cauchy_bound:
        fail("second-moment falsifier no longer exceeds the Cauchy bound")
    _, level_five = mangoldt_class_distribution(5, 45)
    _, level_four = mangoldt_class_distribution(4, 45)
    normalized_layer = 2 * level_five[0] - level_four[0]
    if normalized_layer != 7_080_448:
        fail(f"level-5 degree-45 normalized layer differs: {normalized_layer}")
    if normalized_layer * normalized_layer <= 1 << 45:
        fail("constant-one layer target is no longer refuted")
    print(
        "GF2_HAYES|status=PASS|degrees=3..20|"
        f"counts={','.join(str(value) for value in observed)}|"
        f"level8_degree17_second_moment={moment}|"
        "generic_cauchy_route=false|"
        f"level5_degree45_normalized_layer={normalized_layer}|"
        "constant_one_layer_target=false"
    )


if __name__ == "__main__":
    main()
