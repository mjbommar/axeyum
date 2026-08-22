"""Check the exact Adams/Liouville identity for Hayes character sums.

For a Hayes character ``chi`` and the completely multiplicative polynomial
Liouville function ``lambda(P^r) = (-1)^r``, Euler products give

    L(lambda*chi, u) = L(chi^2, u^2) / L(chi, u).

Thus their logarithmic derivatives obey

    S_m(lambda*chi) + S_m(chi)
        = 0                         (m odd),
        = 2 S_(m/2)(chi^2)          (m even).

This is an exact identity, but not a recursive estimate: lambda is not a
ray-class character, and its sum is precisely the extra term needed to turn
the claimed degree-doubling relation into a tautology.  The checks below sum
prime powers directly, independently of the population/Fourier code.
"""
from __future__ import annotations

import cmath

from lemire_anchor import Characters, cls, irreducibles


def character_value(character: Characters, coefficients: dict[int, int], f: int, degree: int) -> complex:
    """Evaluate chi on the reversed Hayes class of a monic polynomial."""
    theta = character.value_phase(coefficients, cls(f, degree, character.j))
    return cmath.exp(2j * cmath.pi * float(theta))


def adams_sum(character: Characters, coefficients: dict[int, int], degree: int, liouville: bool = False) -> complex:
    """sum_{deg F=degree} Lambda(F) chi(<F>) lambda(F)^liouville."""
    total = 0j
    for prime_degree in range(1, degree + 1):
        if degree % prime_degree:
            continue
        exponent = degree // prime_degree
        sign = -1 if liouville and exponent % 2 else 1
        for prime in irreducibles(prime_degree, procs=1):
            total += sign * prime_degree * character_value(
                character, coefficients, prime, prime_degree
            ) ** exponent
    return total


def square_character(character: Characters, coefficients: dict[int, int]) -> dict[int, int]:
    return {
        k: (2 * coefficients[k]) % (1 << character.es[k])
        for k in character.gens
    }


def main() -> None:
    # Small enough for the pure-Python irreducibility fallback, while covering
    # odd/even degrees and characters of orders 2, 4, 8 and 16.
    checks = 0
    for j in range(1, 6):
        characters = Characters(j)
        for coefficients in characters.all_c():
            squared = square_character(characters, coefficients)
            for m in range(1, 11):
                lhs = adams_sum(characters, coefficients, m, liouville=True)
                lhs += adams_sum(characters, coefficients, m)
                rhs = 0j
                if m % 2 == 0:
                    rhs = 2 * adams_sum(characters, squared, m // 2)
                assert abs(lhs - rhs) < 1e-7, (j, coefficients, m, lhs, rhs)
                checks += 1
    print(f"ADAMS/LIOUVILLE CHECKS PASSED ({checks} identities)")


if __name__ == "__main__":
    main()
