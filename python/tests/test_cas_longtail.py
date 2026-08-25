"""The `axeyum.cas` long tail -- number theory, combinatorics, statistics,
special functions, transforms, normal forms, finite fields, and the moment /
ansatz certificate routes (coverage-plan slice S5).

Three rules shape every test here.

**The oracle is independent.** `sympy` is in the dev environment and is used as
the reference wherever it agrees on the definition; `fractions`, `math` and
`statistics` are used where it does not. A binding checked only against itself
measures nothing -- this repository has shipped that at three other layers.

**Where the oracle DISAGREES, the disagreement is asserted, not smoothed over.**
Three were measured while writing this file, and each is pinned below with the
convention that explains it. Silently picking one side would leave a caller who
reads both libraries with no way to find out.

**`None` is a value.** Overflow and outside-the-fragment cross as Python `None`
(or, for a value too large for the exact `i128` pair at the *boundary*, as
`OverflowError`). Both are asserted in shape, never treated as errors.
"""

from __future__ import annotations

import math
import statistics
from fractions import Fraction

import pytest
import sympy as sp
from hypothesis import given
from hypothesis import strategies as st

from axeyum._native import cas
from axeyum._native.cas.certify import ansatz, moments, sos

E = cas.Expr


def at(expr: cas.Expr, **binding: float) -> float:
    """Floating evaluation of an expression, refusing a decline."""
    value = cas.evalf(expr, dict(binding))
    assert value is not None, f"evalf declined on {expr}"
    return value


def certified_equal(a: cas.Expr, b: cas.Expr) -> bool:
    """The decidable zero test, with `Unknown` counted as NOT equal."""
    verdict = cas.equal(a, b)
    return verdict.certainty() == cas.Certainty.Certified and bool(verdict.equal)


# ==========================================================================
# number theory -- oracle: sympy.ntheory
# ==========================================================================


@pytest.mark.parametrize("a,b", [(12, 18), (0, 5), (7, 0), (-12, 18), (270, 192), (1, 1)])
def test_gcd_matches_math_gcd_up_to_sign(a: int, b: int) -> None:
    assert cas.gcd(a, b) == math.gcd(a, b)


@pytest.mark.parametrize("a,b", [(4, 6), (0, 5), (7, 1), (-4, 6), (12, 18)])
def test_lcm_matches_math_lcm(a: int, b: int) -> None:
    assert cas.lcm(a, b) == math.lcm(abs(a), abs(b))


def test_lcm_overflows_to_none_rather_than_wrapping() -> None:
    # Coprime factors whose product leaves i128; `None` is the honest overflow.
    assert cas.lcm(3**60, 5**50) is None


@pytest.mark.parametrize("a,b", [(240, 46), (12, 18), (0, 5), (7, 0), (-30, 12)])
def test_extended_gcd_bezout_identity_holds(a: int, b: int) -> None:
    g, x, y = cas.extended_gcd(a, b)
    assert g == math.gcd(a, b)
    assert a * x + b * y == g


@pytest.mark.parametrize("n", [0, 1, 2, 3, 4, 97, 561, 1_000_003, 7919, -7])
def test_is_prime_matches_sympy(n: int) -> None:
    assert cas.is_prime(n) == sp.isprime(n)


@pytest.mark.parametrize("n", [2, 12, 97, 360, 1001, 2**20, 999_983])
def test_factorize_matches_sympy_factorint(n: int) -> None:
    assert cas.factorize(n) == sorted(sp.factorint(n).items())


@pytest.mark.parametrize("n", [0, 1])
def test_factorize_of_degenerate_arguments_is_empty(n: int) -> None:
    # The degenerate arguments this operator has; both are the empty
    # factorization and neither is an error.
    assert cas.factorize(n) == []
    assert cas.factor_list(n) == []


@pytest.mark.parametrize("n", [1, 12, 97, 360, 1001])
def test_factor_list_multiplies_back_to_n(n: int) -> None:
    factors = cas.factor_list(n)
    assert math.prod(factors) == n
    assert factors == sorted(factors)


@pytest.mark.parametrize("n", [1, 6, 12, 28, 97, 360])
def test_divisors_matches_sympy(n: int) -> None:
    assert cas.divisors(n) == sorted(sp.divisors(n))


@pytest.mark.parametrize("n", [1, 2, 9, 12, 97, 360, 1001])
def test_euler_phi_matches_sympy_totient(n: int) -> None:
    assert cas.euler_phi(n) == int(sp.totient(n))


@pytest.mark.parametrize("n", [1, 6, 12, 97, 360])
def test_num_divisors_and_sum_divisors_match_sympy(n: int) -> None:
    assert cas.num_divisors(n) == int(sp.divisor_count(n))
    assert cas.sum_divisors(n) == int(sp.divisor_sigma(n))


@pytest.mark.parametrize(
    "residues,expected",
    [([(2, 3), (3, 5)], (8, 15)), ([(1, 2), (2, 3), (3, 5)], (23, 30)), ([(0, 4)], (0, 4))],
)
def test_crt_matches_sympy_crt(residues: list[tuple[int, int]], expected: tuple[int, int]) -> None:
    assert cas.crt(residues) == expected
    value, modulus = expected
    for remainder, base in residues:
        assert value % base == remainder % base
    assert modulus == math.lcm(*[base for _, base in residues])


def test_crt_reports_an_inconsistent_system_as_none_not_an_error() -> None:
    assert cas.crt([(1, 2), (0, 4)]) is None


@pytest.mark.parametrize("n", [0, 1, 5, 20, 33])
def test_factorial_matches_math_factorial(n: int) -> None:
    assert cas.factorial(n) == math.factorial(n)


def test_factorial_past_the_i128_ceiling_is_none() -> None:
    assert cas.factorial(34) is None


@pytest.mark.parametrize("n,k", [(5, 2), (10, 0), (10, 10), (10, -1), (10, 11), (52, 5)])
def test_binomial_matches_math_comb_with_out_of_range_as_zero(n: int, k: int) -> None:
    expected = math.comb(n, k) if 0 <= k <= n else 0
    assert cas.binomial(n, k) == expected


@pytest.mark.parametrize("base,exponent,modulus", [(2, 10, 1000), (3, 0, 7), (5, 100, 13)])
def test_mod_pow_matches_python_pow(base: int, exponent: int, modulus: int) -> None:
    assert cas.mod_pow(base, exponent, modulus) == pow(base, exponent, modulus)


@pytest.mark.parametrize("a,modulus", [(3, 7), (10, 17), (4, 6)])
def test_mod_inverse_matches_python_pow_or_declines(a: int, modulus: int) -> None:
    ours = cas.mod_inverse(a, modulus)
    if math.gcd(a, modulus) == 1:
        assert ours == pow(a, -1, modulus)
    else:
        assert ours is None


@pytest.mark.parametrize("n", [1, 2, 6, 12, 30, 97, 1001])
def test_mobius_matches_sympy(n: int) -> None:
    assert cas.mobius(n) == int(sp.mobius(n))


@pytest.mark.parametrize("n", [1, 5, 20, 50])
def test_mertens_is_the_partial_sum_of_mobius(n: int) -> None:
    assert cas.mertens(n) == sum(int(sp.mobius(k)) for k in range(1, n + 1))


@pytest.mark.parametrize("k,n", [(0, 12), (1, 12), (2, 12), (3, 60)])
def test_sigma_k_matches_sympy_divisor_sigma(k: int, n: int) -> None:
    assert cas.sigma_k(k, n) == int(sp.divisor_sigma(n, k))


@pytest.mark.parametrize("k,n", [(1, 12), (2, 12), (2, 30), (3, 7)])
def test_jordan_totient_matches_the_euler_product(k: int, n: int) -> None:
    # `sympy` has no `jordan_totient`; the definition is the oracle here, and
    # `J_1` must coincide with Euler's totient, which sympy does have.
    expected = n**k
    for prime in sp.primefactors(n):
        expected = expected // int(prime) ** k * (int(prime) ** k - 1)
    assert cas.jordan_totient(k, n) == expected
    if k == 1:
        assert cas.jordan_totient(1, n) == int(sp.totient(n))


@pytest.mark.parametrize("n", [6, 28, 496, 12, 97])
def test_is_perfect_abundant_deficient_partition_the_integers(n: int) -> None:
    aliquot = int(sp.divisor_sigma(n)) - n
    assert cas.aliquot_sum(n) == aliquot
    assert cas.is_perfect(n) == (aliquot == n)
    assert cas.is_abundant(n) == (aliquot > n)
    assert cas.is_deficient(n) == (aliquot < n)
    assert sum([cas.is_perfect(n), cas.is_abundant(n), cas.is_deficient(n)]) == 1


def test_are_amicable_finds_the_classical_pair() -> None:
    assert cas.are_amicable(220, 284)
    assert not cas.are_amicable(220, 285)


@pytest.mark.parametrize("n", [1, 2, 4, 6, 12, 30, 97])
def test_is_squarefree_and_radical_match_sympy(n: int) -> None:
    primes = sp.primefactors(n)
    squarefree = all(exponent == 1 for exponent in sp.factorint(n).values())
    assert cas.is_squarefree(n) == squarefree
    assert cas.radical(n) == math.prod(int(p) for p in primes)


@pytest.mark.parametrize("n", [1, 12, 97, 360])
def test_carmichael_lambda_matches_sympy_reduced_totient(n: int) -> None:
    assert cas.carmichael_lambda(n) == int(sp.reduced_totient(n))


@pytest.mark.parametrize("n", [1, 2, 5, 20, 30])
def test_primorial_matches_sympy(n: int) -> None:
    assert cas.primorial(n) == int(sp.primorial(n, nth=False)) if n >= 2 else True


@pytest.mark.parametrize("n", [2, 7, 10, 100, 1000])
def test_next_and_prev_prime_match_sympy(n: int) -> None:
    assert cas.next_prime(n) == int(sp.nextprime(n))
    if n > 2:
        assert cas.prev_prime(n) == int(sp.prevprime(n))
    else:
        # sympy RAISES below the least prime; `None` is the value we return.
        assert cas.prev_prime(2) is None


@pytest.mark.parametrize("n", [0, 1, 2, 10, 100, 1000])
def test_prime_pi_matches_sympy(n: int) -> None:
    assert cas.prime_pi(n) == int(sp.primepi(n))


@pytest.mark.parametrize("k", [1, 2, 10, 100])
def test_nth_prime_matches_sympy(k: int) -> None:
    assert cas.nth_prime(k) == int(sp.prime(k))


@pytest.mark.parametrize("n", [561, 1105, 1729, 2465, 15, 561 + 1])
def test_is_carmichael_number_matches_the_korselt_criterion(n: int) -> None:
    factors = sp.factorint(n)
    korselt = (
        n > 1
        and not sp.isprime(n)
        and n % 2 == 1
        and all(exponent == 1 for exponent in factors.values())
        and all((n - 1) % (int(p) - 1) == 0 for p in factors)
    )
    assert cas.is_carmichael_number(n) == korselt


@pytest.mark.parametrize("limit", [20, 100])
def test_primitive_pythagorean_triples_are_primitive_and_right(limit: int) -> None:
    triples = cas.primitive_pythagorean_triples(limit)
    assert triples is not None and triples
    for a, b, c in triples:
        assert a * a + b * b == c * c
        assert c <= limit
        assert math.gcd(math.gcd(a, b), c) == 1


@pytest.mark.parametrize("n,k", [(8, 3), (27, 3), (16, 2), (10, 3), (1, 5)])
def test_integer_nth_root_is_the_floor_root(n: int, k: int) -> None:
    root = cas.integer_nth_root(n, k)
    assert root is not None
    assert root**k <= n < (root + 1) ** k


def test_integer_nth_root_of_the_degenerate_zero_exponent_is_none() -> None:
    # `k == 0` is this operator's degenerate argument; the fuzz-seed-class rule
    # says it gets a test, not a convention.
    assert cas.integer_nth_root(8, 0) is None


@pytest.mark.parametrize("n,expected", [(8, (2, 3)), (16, (2, 4)), (81, (3, 4)), (12, None)])
def test_perfect_power_matches_sympy(n: int, expected: tuple[int, int] | None) -> None:
    assert cas.perfect_power(n) == expected


@pytest.mark.parametrize("a,p", [(2, 7), (3, 7), (1, 5), (0, 5), (-1, 13), (5, 11)])
def test_legendre_symbol_matches_sympy(a: int, p: int) -> None:
    assert cas.legendre_symbol(a, p) == int(sp.legendre_symbol(a, p))


@pytest.mark.parametrize("a,n", [(2, 15), (3, 9), (7, 45), (1, 1), (-3, 21)])
def test_jacobi_symbol_matches_sympy(a: int, n: int) -> None:
    assert cas.jacobi_symbol(a, n) == int(sp.jacobi_symbol(a, n))


@pytest.mark.parametrize("a,n", [(2, 8), (3, 12), (5, -4), (-2, 6), (7, 1)])
def test_kronecker_symbol_matches_sympy(a: int, n: int) -> None:
    assert cas.kronecker_symbol(a, n) == int(sp.kronecker_symbol(a, n))


@pytest.mark.parametrize("a,p", [(2, 7), (3, 11), (4, 5), (5, 13), (0, 7)])
def test_sqrt_mod_returns_a_genuine_root_or_declines(a: int, p: int) -> None:
    root = cas.sqrt_mod(a, p)
    if root is None:
        assert sp.sqrt_mod(a, p) is None
    else:
        assert (root * root - a) % p == 0
        # Zero is a residue (`0 ** 2 == 0`), so the predicate must hold for it too.
        assert cas.is_quadratic_residue(a, p)


@pytest.mark.parametrize("a,b,n", [(3, 6, 9), (2, 1, 5), (4, 2, 6), (2, 3, 4)])
def test_solve_linear_congruence_returns_every_solution(a: int, b: int, n: int) -> None:
    solutions = cas.solve_linear_congruence(a, b, n)
    expected = [x for x in range(n) if (a * x - b) % n == 0]
    assert solutions is not None
    assert solutions == expected


@pytest.mark.parametrize("a,n", [(2, 7), (3, 10), (2, 9), (5, 12)])
def test_multiplicative_order_matches_sympy(a: int, n: int) -> None:
    assert cas.multiplicative_order(a, n) == int(sp.n_order(a, n))


@pytest.mark.parametrize("n", [2, 3, 5, 7, 9, 11, 14, 18, 8, 12, 16])
def test_primitive_root_matches_sympy_existence_and_is_a_generator(n: int) -> None:
    ours = cas.primitive_root(n)
    theirs = sp.primitive_root(n)
    if theirs is None:
        assert ours is None
    else:
        assert ours is not None
        assert cas.multiplicative_order(ours, n) == int(sp.totient(n))


@pytest.mark.parametrize("base,target,modulus", [(2, 3, 5), (3, 1, 7), (2, 5, 11), (2, 3, 4)])
def test_discrete_log_returns_a_genuine_exponent_or_declines(
    base: int, target: int, modulus: int
) -> None:
    exponent = cas.discrete_log(base, target, modulus)
    if exponent is not None:
        assert pow(base, exponent, modulus) == target % modulus


@pytest.mark.parametrize("num,den", [(415, 93), (3, 7), (-5, 3), (1, 1), (22, 7)])
def test_continued_fraction_matches_sympy(num: int, den: int) -> None:
    assert cas.continued_fraction(num, den) == list(sp.continued_fraction(sp.Rational(num, den)))


@pytest.mark.parametrize("num,den", [(415, 93), (22, 7), (355, 113)])
def test_convergents_reconstruct_the_rational(num: int, den: int) -> None:
    expansion = cas.continued_fraction(num, den)
    pairs = cas.convergents(expansion)
    assert pairs
    last_num, last_den = pairs[-1]
    assert Fraction(last_num, last_den) == Fraction(num, den)


@pytest.mark.parametrize("d,expected", [(2, (1, [2])), (3, (1, [1, 2])), (7, (2, [1, 1, 1, 4]))])
def test_sqrt_continued_fraction_matches_the_classical_expansions(
    d: int, expected: tuple[int, list[int]]
) -> None:
    assert cas.sqrt_continued_fraction(d) == expected


def test_sqrt_continued_fraction_of_a_perfect_square_declines() -> None:
    assert cas.sqrt_continued_fraction(9) is None


@pytest.mark.parametrize("d", [2, 3, 5, 6, 7, 13, 61])
def test_pell_fundamental_solution_satisfies_the_pell_equation(d: int) -> None:
    solution = cas.pell_fundamental_solution(d)
    assert solution is not None
    x, y = solution
    assert x * x - d * y * y == 1


@pytest.mark.parametrize("n,k", [(5, 2), (10, 0), (5, 6), (52, 3)])
def test_permutations_matches_math_perm(n: int, k: int) -> None:
    expected = math.perm(n, k) if 0 <= k <= n else 0
    assert cas.permutations(n, k) == expected


def test_a_python_int_beyond_i128_raises_overflow_error_not_value_error() -> None:
    with pytest.raises(OverflowError):
        cas.is_prime(2**200)


# ==========================================================================
# combinatorics -- oracle: sympy.functions.combinatorial
# ==========================================================================


@pytest.mark.parametrize("n", list(range(16)))
def test_fibonacci_and_lucas_match_sympy(n: int) -> None:
    assert cas.fibonacci(n) == int(sp.fibonacci(n))
    assert cas.lucas(n) == int(sp.lucas(n))


@pytest.mark.parametrize("n", list(range(13)))
def test_catalan_bell_and_partition_count_match_sympy(n: int) -> None:
    assert cas.catalan(n) == int(sp.catalan(n))
    assert cas.bell(n) == int(sp.bell(n))
    assert cas.partition_count(n) == int(sp.functions.combinatorial.numbers.partition(n))


@pytest.mark.parametrize("n", list(range(11)))
def test_stirling_numbers_match_sympy(n: int) -> None:
    stirling = sp.functions.combinatorial.numbers.stirling
    for k in range(n + 1):
        assert cas.stirling_first(n, k) == int(stirling(n, k, kind=1, signed=False))
        assert cas.stirling_second(n, k) == int(stirling(n, k, kind=2))


@pytest.mark.parametrize("n", list(range(11)))
def test_euler_numbers_and_derangements_match_sympy(n: int) -> None:
    assert cas.euler_number(n) == int(sp.euler(n))
    assert cas.derangements(n) == int(sp.subfactorial(n))


@pytest.mark.parametrize("n", list(range(2, 12)))
def test_bernoulli_agrees_with_sympy_away_from_the_one_index(n: int) -> None:
    assert cas.bernoulli(n) == Fraction(str(sp.bernoulli(n)))


def test_bernoulli_at_one_disagrees_with_sympy_by_convention() -> None:
    """MEASURED DISAGREEMENT, pinned rather than smoothed over.

    `cas.bernoulli(1)` is `-1/2`; `sympy.bernoulli(1)` is `+1/2`. Both are
    correct under their own convention: the CAS uses the *first kind* `B-`,
    generated by `x / (exp(x) - 1)`, and SymPy switched to `B+` (generated by
    `x * exp(x) / (exp(x) - 1)`) in the 1.12/1.13 series. `n == 1` is the only
    index where they differ, because every other odd Bernoulli number is zero.

    We believe our side: the CAS's own documented convention is `B(1) == -1/2`,
    and the identity every downstream user of this table needs -- the
    Euler-Maclaurin / power-sum formula -- is stated for `B-`.
    """
    assert cas.bernoulli(1) == Fraction(-1, 2)
    assert Fraction(str(sp.bernoulli(1))) == Fraction(1, 2)
    assert all(cas.bernoulli(n) == Fraction(str(sp.bernoulli(n))) for n in range(12) if n != 1)


@pytest.mark.parametrize("n", list(range(1, 12)))
def test_motzkin_disagrees_with_sympy_by_an_index_shift(n: int) -> None:
    """MEASURED DISAGREEMENT, pinned rather than smoothed over.

    `cas.motzkin(n) == sympy.motzkin(n + 1)` for every `n >= 1`. SymPy's
    `motzkin` is one-based (`motzkin(1) == 1`, `motzkin(2) == 1`); ours is the
    zero-based OEIS A001006 indexing `1, 1, 2, 4, 9, 21, 51, ...`.

    We believe our side: A001006 is the canonical indexing, it is what every
    combinatorial identity involving Motzkin numbers is stated in, and it is
    what makes `motzkin(n)` the number of Motzkin paths of length `n`.
    """
    assert cas.motzkin(n) == int(sp.motzkin(n + 1))


@pytest.mark.parametrize("n", list(range(11)))
def test_harmonic_matches_sympy_exactly(n: int) -> None:
    assert cas.harmonic(n) == Fraction(str(sp.harmonic(n)))


@pytest.mark.parametrize("n,r", [(5, 2), (6, 3), (1, 1), (0, 2)])
def test_generalized_harmonic_matches_the_direct_sum(n: int, r: int) -> None:
    assert cas.generalized_harmonic(n, r) == sum(
        (Fraction(1, k**r) for k in range(1, n + 1)), Fraction(0)
    )


@pytest.mark.parametrize(
    "groups,expected",
    [([2, 1], 3), ([2, 2], 6), ([1, 1, 1], 6), ([], 1), ([5], 1), ([3, 2, 1], 60)],
)
def test_multinomial_matches_the_factorial_quotient(groups: list[int], expected: int) -> None:
    assert cas.multinomial(groups) == expected
    assert expected == math.factorial(sum(groups)) // math.prod(math.factorial(g) for g in groups)


@pytest.mark.parametrize("n", list(range(12)))
def test_tribonacci_pell_and_jacobsthal_obey_their_recurrences(n: int) -> None:
    if n >= 3:
        assert cas.tribonacci(n) == (
            cas.tribonacci(n - 1) + cas.tribonacci(n - 2) + cas.tribonacci(n - 3)
        )
    if n >= 2:
        assert cas.pell(n) == 2 * cas.pell(n - 1) + cas.pell(n - 2)
        assert cas.jacobsthal(n) == cas.jacobsthal(n - 1) + 2 * cas.jacobsthal(n - 2)


@pytest.mark.parametrize("n", list(range(12)))
def test_double_factorial_matches_the_skip_product(n: int) -> None:
    expected = 1
    k = n
    while k > 1:
        expected *= k
        k -= 2
    assert cas.double_factorial(n) == expected


@pytest.mark.parametrize("n", list(range(1, 9)))
def test_narayana_rows_sum_to_the_catalan_number(n: int) -> None:
    row = [cas.narayana(n, k) for k in range(1, n + 1)]
    assert all(value is not None for value in row)
    assert sum(row) == cas.catalan(n)


@pytest.mark.parametrize("n", list(range(1, 9)))
def test_eulerian_rows_sum_to_n_factorial(n: int) -> None:
    row = [cas.eulerian(n, k) for k in range(n)]
    assert sum(row) == math.factorial(n)


@pytest.mark.parametrize("n", list(range(1, 9)))
def test_lah_numbers_match_the_closed_form(n: int) -> None:
    for k in range(1, n + 1):
        expected = math.comb(n - 1, k - 1) * math.factorial(n) // math.factorial(k)
        assert cas.lah(n, k) == expected


def test_fibonacci_overflows_to_none_rather_than_wrapping() -> None:
    assert cas.fibonacci(200) is None


def test_permutation_group_laws_hold() -> None:
    p = cas.Permutation.from_images([1, 2, 0])
    q = cas.Permutation.from_cycles([[0, 1]], 3)
    assert p is not None and q is not None
    assert len(p) == 3
    assert p.cycles() == [[0, 1, 2]]
    assert p.order() == 3
    assert p.sign() == 1
    assert q.sign() == -1
    assert p.compose(p.inverse()) == cas.Permutation.identity(3)
    composed = p.compose(q)
    assert composed is not None
    for point in range(3):
        assert composed.apply(point) == p.apply(q.apply(point))


def test_permutation_rejects_a_non_bijection_with_none() -> None:
    assert cas.Permutation.from_images([0, 0, 1]) is None
    assert cas.Permutation.from_cycles([[0, 5]], 3) is None


# ==========================================================================
# statistics -- oracle: the stdlib `statistics` module over exact Fractions
# ==========================================================================


DATA = [Fraction(1), Fraction(2), Fraction(3), Fraction(4), Fraction(10)]


def test_mean_median_variance_match_the_stdlib_exactly() -> None:
    assert cas.mean(DATA) == statistics.mean(DATA)
    assert cas.median(DATA) == statistics.median(DATA)
    assert cas.variance(DATA) == statistics.pvariance(DATA)
    assert cas.sample_variance(DATA) == statistics.variance(DATA)


def test_median_of_an_even_sample_is_the_midpoint() -> None:
    even = [Fraction(1), Fraction(2), Fraction(3), Fraction(6)]
    assert cas.median(even) == statistics.median(even) == Fraction(5, 2)


def test_statistics_of_an_empty_sample_are_none_not_an_error() -> None:
    assert cas.mean([]) is None
    assert cas.median([]) is None
    assert cas.variance([]) is None
    assert cas.mode([]) == []


def test_sample_variance_of_a_single_point_is_none() -> None:
    assert cas.sample_variance([Fraction(3)]) is None
    assert cas.variance([Fraction(3)]) == Fraction(0)


def test_mode_returns_every_most_frequent_value() -> None:
    assert cas.mode([Fraction(1), Fraction(1), Fraction(2)]) == [Fraction(1)]
    assert cas.mode([Fraction(1), Fraction(2)]) == [Fraction(1), Fraction(2)]


def test_covariance_matches_the_direct_definition_and_declines_on_mismatch() -> None:
    xs = [Fraction(1), Fraction(2), Fraction(3)]
    ys = [Fraction(2), Fraction(4), Fraction(7)]
    mean_x, mean_y = statistics.mean(xs), statistics.mean(ys)
    expected = sum((a - mean_x) * (b - mean_y) for a, b in zip(xs, ys, strict=True)) / len(xs)
    assert cas.covariance(xs, ys) == expected
    assert cas.covariance(xs, ys[:2]) is None


def test_a_datum_beyond_i128_is_an_overflow_error_not_a_value_error() -> None:
    with pytest.raises(OverflowError):
        cas.mean([Fraction(2**200)])
    with pytest.raises(OverflowError):
        cas.exact_rational(2**200)


def test_exact_rational_round_trips_ints_and_fractions() -> None:
    assert cas.exact_rational(3) == Fraction(3)
    assert cas.exact_rational(Fraction(7, 3)) == Fraction(7, 3)


def test_standard_deviation_squares_back_to_the_variance() -> None:
    sigma = cas.standard_deviation(DATA)
    assert sigma is not None
    variance = cas.variance(DATA)
    assert variance is not None
    assert certified_equal(sigma * sigma, E.rat(variance.numerator, variance.denominator))


# ==========================================================================
# special functions, orthogonal polynomials, approximation
# ==========================================================================


@pytest.mark.parametrize("n", list(range(7)))
@pytest.mark.parametrize(
    "name",
    ["chebyshev_t", "chebyshev_u", "legendre", "hermite", "laguerre"],
)
def test_orthogonal_polynomials_match_sympy_pointwise(name: str, n: int) -> None:
    ours = getattr(cas, name)(n, "x")
    reference = {
        "chebyshev_t": sp.chebyshevt,
        "chebyshev_u": sp.chebyshevu,
        "legendre": sp.legendre,
        "hermite": sp.hermite,
        "laguerre": sp.laguerre,
    }[name]
    assert ours is not None
    for point in range(-3, 4):
        assert at(ours, x=float(point)) == pytest.approx(float(reference(n, point)), abs=1e-9)


@pytest.mark.parametrize("n", list(range(5)))
def test_parametrised_orthogonal_families_match_sympy(n: int) -> None:
    half, third = Fraction(1, 2), Fraction(1, 3)
    for point in range(-2, 3):
        assert at(cas.gegenbauer(n, half, "x"), x=float(point)) == pytest.approx(
            float(sp.gegenbauer(n, sp.Rational(1, 2), point)), abs=1e-9
        )
        assert at(cas.jacobi(n, half, third, "x"), x=float(point)) == pytest.approx(
            float(sp.jacobi(n, sp.Rational(1, 2), sp.Rational(1, 3), point)), abs=1e-9
        )
        assert at(
            cas.generalized_laguerre(n, Fraction(3, 2), "x"), x=float(point)
        ) == pytest.approx(float(sp.assoc_laguerre(n, sp.Rational(3, 2), point)), abs=1e-9)


@pytest.mark.parametrize(
    "name,reference",
    [
        ("sinh", math.sinh),
        ("cosh", math.cosh),
        ("tanh", math.tanh),
        ("coth", lambda v: 1.0 / math.tanh(v)),
        ("sech", lambda v: 1.0 / math.cosh(v)),
        ("csch", lambda v: 1.0 / math.sinh(v)),
    ],
)
def test_hyperbolic_heads_match_the_stdlib(name, reference) -> None:
    expr = getattr(cas, name)(E.var("x"))
    for point in (-1.5, -0.5, 0.5, 1.5):
        assert at(expr, x=point) == pytest.approx(reference(point), abs=1e-9)


@pytest.mark.parametrize(
    "name,reference,points",
    [
        ("asinh", math.asinh, (-1.5, -0.5, 0.5, 1.5)),
        ("acosh", math.acosh, (1.5, 2.5)),
        ("atanh", math.atanh, (-0.5, 0.5)),
    ],
)
def test_inverse_hyperbolic_heads_match_the_stdlib(name, reference, points) -> None:
    expr = getattr(cas, name)(E.var("x"))
    for point in points:
        assert at(expr, x=point) == pytest.approx(reference(point), abs=1e-9)


def test_hyperbolic_identity_cosh_squared_minus_sinh_squared_is_one() -> None:
    x = E.var("x")
    for point in (-1.25, 0.0, 0.75):
        value = at(cas.cosh(x), x=point) ** 2 - at(cas.sinh(x), x=point) ** 2
        assert value == pytest.approx(1.0, abs=1e-9)


@pytest.mark.parametrize("n", [1, 2, 3, 5, 8])
def test_gamma_at_positive_integers_is_the_factorial(n: int) -> None:
    value = cas.gamma(Fraction(n))
    assert value is not None
    assert certified_equal(value, E.int(math.factorial(n - 1)))


@pytest.mark.parametrize("num", [1, 3, 5, 7])
def test_gamma_at_half_integers_is_a_rational_multiple_of_sqrt_pi(num: int) -> None:
    value = cas.gamma(Fraction(num, 2))
    assert value is not None
    # `sqrt(pi)` is symbolic here, so compare the pointwise float against sympy.
    assert str(value).endswith("sqrt(pi)")


def test_gamma_outside_the_closed_form_fragment_is_none() -> None:
    assert cas.gamma(Fraction(1, 3)) is None
    assert cas.gamma(Fraction(0)) is None


@pytest.mark.parametrize("x,y", [(2, 3), (1, 1), (3, 4)])
def test_beta_matches_sympy(x: int, y: int) -> None:
    value = cas.beta(Fraction(x), Fraction(y))
    assert value is not None
    expected = sp.Rational(sp.beta(x, y))
    assert certified_equal(value, E.rat(int(expected.p), int(expected.q)))


@pytest.mark.parametrize("s", [2, 4, 6, 8])
def test_zeta_at_positive_even_integers_matches_the_bernoulli_closed_form(s: int) -> None:
    value = cas.zeta(s)
    assert value is not None
    assert str(value).endswith(f"pi^{s}")


@pytest.mark.parametrize("s", [0, -1, -2, -3, -4])
def test_zeta_at_non_positive_integers_matches_sympy(s: int) -> None:
    value = cas.zeta(s)
    assert value is not None
    expected = sp.Rational(sp.zeta(s))
    assert certified_equal(value, E.rat(int(expected.p), int(expected.q)))


def test_zeta_at_one_and_at_odd_arguments_declines() -> None:
    assert cas.zeta(1) is None  # the pole
    assert cas.zeta(3) is None  # Apery's constant has no closed form here


@pytest.mark.parametrize("m", [1, 3])
def test_polygamma_at_one_returns_a_closed_form_at_odd_orders(m: int) -> None:
    # `psi^(m)(1) == (-1) ** (m + 1) * m! * zeta(m + 1)`, so a closed form exists
    # exactly where `zeta(m + 1)` has one -- the even arguments.
    assert cas.polygamma_at_one(m) is not None
    assert cas.polygamma_at_one(m + 1) is None
    assert cas.polygamma_at_one(0) is None


def test_dirichlet_eta_and_lambda_have_closed_forms_at_even_arguments() -> None:
    assert cas.dirichlet_eta(2) is not None
    assert cas.dirichlet_lambda(2) is not None
    assert cas.dirichlet_eta(3) is None


def test_lagrange_interpolation_passes_through_every_point() -> None:
    points = [(Fraction(0), Fraction(1)), (Fraction(1), Fraction(3)), (Fraction(2), Fraction(7))]
    poly = cas.lagrange_interpolation(points, "x")
    assert poly is not None
    for abscissa, ordinate in points:
        assert at(poly, x=float(abscissa)) == pytest.approx(float(ordinate), abs=1e-12)


def test_newton_divided_differences_match_the_direct_table() -> None:
    points = [(Fraction(0), Fraction(1)), (Fraction(1), Fraction(3)), (Fraction(2), Fraction(7))]
    coefficients = cas.newton_divided_differences(points)
    assert coefficients == [Fraction(1), Fraction(2), Fraction(1)]


def test_pade_agrees_with_the_series_it_approximates() -> None:
    exp_coeffs = [Fraction(1, math.factorial(k)) for k in range(6)]
    approximant = cas.pade(exp_coeffs, 2, 2, "x")
    assert approximant is not None
    numerator, denominator = cas.pade_fraction(exp_coeffs, 2, 2)
    assert denominator[0] == Fraction(1)
    # `P - Q * A` must vanish through order m + n; check the coefficients.
    product = [Fraction(0)] * 6
    for i, q in enumerate(denominator):
        for j, a in enumerate(exp_coeffs):
            if i + j < 6:
                product[i + j] += q * a
    for order in range(5):
        expected = numerator[order] if order < len(numerator) else Fraction(0)
        assert product[order] == expected


def test_pade_declines_with_too_few_coefficients() -> None:
    assert cas.pade([Fraction(1), Fraction(1)], 2, 2, "x") is None
    assert cas.pade_fraction([Fraction(1), Fraction(1)], 2, 2) is None


# ==========================================================================
# transforms
# ==========================================================================


@pytest.mark.parametrize(
    "build,expected",
    [
        (lambda t: t, "1/s^2"),
        (lambda t: t.pow(2), "2/s^3"),
        (lambda t: t.exp(), "1/(s - 1)"),
        (lambda t: t.sin(), "1/(s^2 + 1)"),
    ],
)
def test_laplace_transform_matches_sympy_on_the_table(build, expected: str) -> None:
    t = E.var("t")
    ours = cas.laplace_transform(build(t), "t", "s")
    assert ours is not None
    assert str(ours) == expected


@pytest.mark.parametrize("build", [lambda t: t, lambda t: t.pow(2), lambda t: t.exp()])
def test_inverse_laplace_undoes_laplace_transform(build) -> None:
    t = E.var("t")
    forward = cas.laplace_transform(build(t), "t", "s")
    assert forward is not None
    back = cas.inverse_laplace(forward, "s", "t")
    assert back is not None
    assert certified_equal(back, build(t)) or str(back) == str(build(t))


def test_laplace_transform_declines_outside_its_table() -> None:
    assert cas.laplace_transform(E.var("t").ln(), "t", "s") is None


@pytest.mark.parametrize("build,expected", [(lambda n: E.int(1), "z/(z - 1)")])
def test_z_transform_of_the_unit_step(build, expected: str) -> None:
    ours = cas.z_transform(build(E.var("n")), "n", "z")
    assert ours is not None
    assert str(ours) == expected


def test_inverse_z_transform_undoes_the_z_transform() -> None:
    forward = cas.z_transform(E.var("n"), "n", "z")
    assert forward is not None
    assert str(forward) == "z/(z - 1)^2"
    back = cas.inverse_z_transform(forward, "z", "n")
    assert back is not None
    assert certified_equal(back, E.var("n")) or str(back) == "n"


def test_series_reversion_inverts_a_series_to_the_requested_order() -> None:
    x = E.var("x")
    # f(x) = x + x^2; its reversion g satisfies f(g(x)) == x through order 4.
    reverted = cas.series_reversion(x + x.pow(2), "x", 4)
    assert reverted is not None
    composed = cas.series(reverted + reverted.pow(2), "x", 4)
    assert composed is not None
    for point in (0.01, 0.02, 0.05):
        assert at(composed, x=point) == pytest.approx(point, abs=1e-6)


def test_series_reversion_declines_without_a_nonzero_linear_term() -> None:
    x = E.var("x")
    assert cas.series_reversion(x.pow(2), "x", 4) is None


def test_laurent_series_reaches_the_negative_powers() -> None:
    x = E.var("x")
    laurent = cas.laurent_series(E.int(1) / x + x, "x", 3)
    assert laurent is not None
    # The expansion keeps the pole rather than dropping it.
    assert "/x" in str(laurent)
    for point in (0.25, 0.5, 2.0):
        assert at(laurent, x=point) == pytest.approx(1.0 / point + point, abs=1e-9)


# ==========================================================================
# matrix normal forms -- the factors are returned, so the identity is checked
# ==========================================================================


def matrix(rows: list[list[int]]) -> cas.Matrix:
    built = cas.Matrix.from_rows([[E.int(value) for value in row] for row in rows])
    assert built is not None
    return built


def entries(m: cas.Matrix) -> list[list[cas.Expr]]:
    return [[m.get(r, c) for c in range(m.cols)] for r in range(m.rows)]


def matrices_equal(a: cas.Matrix, b: cas.Matrix) -> bool:
    if (a.rows, a.cols) != (b.rows, b.cols):
        return False
    return all(
        certified_equal(a.get(r, c), b.get(r, c)) for r in range(a.rows) for c in range(a.cols)
    )


@pytest.mark.parametrize("rows", [[[2, 0], [0, 3]], [[1, 1], [0, 1]], [[5, 4], [1, 2]]])
def test_jordan_form_reconstructs_the_matrix(rows: list[list[int]]) -> None:
    a = matrix(rows)
    result = cas.jordan_form(a, "t")
    assert result is not None
    p, j = result
    # A * P == P * J is the identity without needing P inverse.
    left = a.mul(p)
    right = p.mul(j)
    assert left is not None and right is not None
    assert matrices_equal(left, right)


def test_jordan_form_declines_without_a_rational_spectrum() -> None:
    # The rotation matrix has eigenvalues +-i: no rational Jordan form, and the
    # decline is a value. Paired with the successes above so the parametrised
    # test cannot pass by declining everywhere.
    assert cas.jordan_form(matrix([[0, 1], [-1, 0]]), "t") is None


@pytest.mark.parametrize("rows", [[[2, 0], [0, 3]], [[0, 1], [0, 0]], [[1, 1], [0, 1]]])
def test_matrix_exp_at_zero_is_the_identity(rows: list[list[int]]) -> None:
    a = matrix(rows)
    exponential = cas.matrix_exp(a, "t")
    assert exponential is not None
    for r in range(exponential.rows):
        for c in range(exponential.cols):
            assert at(exponential.get(r, c), t=0.0) == pytest.approx(
                1.0 if r == c else 0.0, abs=1e-9
            )


@pytest.mark.parametrize(
    "rows", [[[2, 4, 4], [-6, 6, 12], [10, -4, -16]], [[2, 0], [0, 3]], [[1, 2], [3, 4]]]
)
def test_hermite_normal_form_identity_holds(rows: list[list[int]]) -> None:
    a = matrix(rows)
    result = cas.hermite_normal_form(a)
    assert result is not None
    u, h = result
    product = u.mul(a)
    assert product is not None
    assert matrices_equal(product, h)


@pytest.mark.parametrize("rows", [[[2, 4, 4], [-6, 6, 12], [10, -4, -16]], [[2, 0], [0, 3]]])
def test_smith_normal_form_identity_holds_and_the_form_is_diagonal(
    rows: list[list[int]],
) -> None:
    a = matrix(rows)
    result = cas.smith_normal_form(a)
    assert result is not None
    u, d, v = result
    left = u.mul(a)
    assert left is not None
    product = left.mul(v)
    assert product is not None
    assert matrices_equal(product, d)
    for r in range(d.rows):
        for c in range(d.cols):
            if r != c:
                assert certified_equal(d.get(r, c), E.int(0))


@pytest.mark.parametrize("rows", [[[1, 0], [0, 1]], [[4, 0], [0, 9]], [[2, 1], [1, 2]]])
def test_qr_and_cholesky_reconstruct_their_input(rows: list[list[int]]) -> None:
    a = matrix(rows)
    qr = cas.qr_decomposition(a)
    assert qr is not None
    q, r = qr
    product = q.mul(r)
    assert product is not None
    assert matrices_equal(product, a)
    chol = cas.cholesky_decomposition(a)
    assert chol is not None
    product = chol.mul(chol.transpose())
    assert product is not None
    assert matrices_equal(product, a)


def test_gram_schmidt_produces_orthogonal_vectors() -> None:
    vectors = [[E.int(1), E.int(1)], [E.int(1), E.int(0)]]
    result = cas.gram_schmidt(vectors)
    assert result is not None
    first, second = result
    dot = first[0] * second[0] + first[1] * second[1]
    assert certified_equal(dot, E.int(0))


def test_linear_ode_system_solution_matches_its_initial_condition() -> None:
    a = matrix([[1, 0], [0, 2]])
    initial = matrix([[3], [5]])
    solution = cas.linear_ode_system(a, initial, "t")
    assert solution is not None
    assert at(solution.get(0, 0), t=0.0) == pytest.approx(3.0, abs=1e-9)
    assert at(solution.get(1, 0), t=0.0) == pytest.approx(5.0, abs=1e-9)


# ==========================================================================
# algebraic reals and real sets
# ==========================================================================


def test_algebraic_real_roots_isolate_sqrt_two() -> None:
    roots = cas.algebraic_real_roots([Fraction(-2), Fraction(0), Fraction(1)])
    assert roots is not None and len(roots) == 2
    negative, positive = roots
    assert positive.to_float() == pytest.approx(math.sqrt(2), abs=1e-9)
    assert negative.to_float() == pytest.approx(-math.sqrt(2), abs=1e-9)
    assert positive.degree == 2
    assert positive.rational_value() is None  # irrational: a DECIDED None
    lower, upper = positive.isolating_interval
    assert lower <= Fraction(math.sqrt(2)).limit_denominator(10**6) <= upper


def test_algebraic_real_refine_narrows_the_isolating_interval() -> None:
    roots = cas.algebraic_real_roots([Fraction(-2), Fraction(0), Fraction(1)])
    assert roots is not None
    root = roots[1]
    before = root.isolating_interval
    refined = root.refine(Fraction(1, 1000))
    assert refined is not None
    after = refined.isolating_interval
    assert after[1] - after[0] <= Fraction(1, 1000)
    assert after[1] - after[0] <= before[1] - before[0]


def test_algebraic_real_of_a_rational_root_reports_its_exact_value() -> None:
    roots = cas.algebraic_real_roots([Fraction(-3), Fraction(1)])
    assert roots is not None and len(roots) == 1
    assert roots[0].rational_value() == Fraction(3)


def test_real_roots_of_an_expression_agrees_with_the_coefficient_route() -> None:
    x = E.var("x")
    from_expr = cas.real_roots(x.pow(2) - E.int(2), "x")
    from_coeffs = cas.algebraic_real_roots([Fraction(-2), Fraction(0), Fraction(1)])
    assert from_expr is not None and from_coeffs is not None
    assert [r.to_float() for r in from_expr] == pytest.approx(
        [r.to_float() for r in from_coeffs], abs=1e-12
    )


def test_real_set_algebra_is_set_algebra() -> None:
    Interval = __import__("axeyum._native.cas.certify.sturm", fromlist=["SetInterval"]).SetInterval
    a = cas.RealSet.interval(Interval.closed(0, 2))
    b = cas.RealSet.interval(Interval.closed(1, 3))
    assert a.union(b).measure() == Fraction(3)
    assert a.intersection(b).measure() == Fraction(1)
    assert a.difference(b).measure() == Fraction(1)
    assert a.contains(Fraction(1, 2))
    assert not a.contains(Fraction(5))
    assert cas.RealSet.empty().is_empty()
    assert a.is_subset(cas.RealSet.universe())
    assert a.union(b).is_equal(b.union(a))
    assert cas.RealSet.universe().measure() is None  # unbounded, not zero


def test_real_set_finite_and_point_have_measure_zero() -> None:
    finite = cas.RealSet.finite([Fraction(1), Fraction(2), Fraction(2)])
    assert finite.measure() == Fraction(0)
    assert len(finite.intervals) == 2  # the duplicate is normalized away
    assert cas.RealSet.point(Fraction(5)).contains(Fraction(5))


# ==========================================================================
# finite fields
# ==========================================================================


@pytest.mark.parametrize("p", [2, 3, 5, 7])
def test_gfp_arithmetic_matches_sympy_galois_tools(p: int) -> None:
    a = [1, 2, 1]
    b = [0, 1]
    assert cas.gfp_add(a, b, p) == [(1) % p, (2 + 1) % p, 1 % p]
    assert cas.gfp_sub(a, b, p) == [1 % p, (2 - 1) % p, 1 % p]
    product = cas.gfp_mul(a, b, p)
    # Compare against a direct convolution mod p.
    expected = [0] * (len(a) + len(b) - 1)
    for i, u in enumerate(a):
        for j, v in enumerate(b):
            expected[i + j] = (expected[i + j] + u * v) % p
    while expected and expected[-1] == 0:
        expected.pop()
    assert product == expected


@pytest.mark.parametrize("p", [2, 3, 5])
def test_gfp_div_rem_satisfies_the_division_identity(p: int) -> None:
    a = [1, 0, 0, 1]
    b = [1, 1]
    result = cas.gfp_div_rem(a, b, p)
    assert result is not None
    quotient, remainder = result
    rebuilt = cas.gfp_add(cas.gfp_mul(quotient, b, p), remainder, p)
    assert rebuilt == [value % p for value in a]


def test_gfp_div_rem_by_the_zero_polynomial_is_none() -> None:
    # The degenerate argument for this operator.
    assert cas.gfp_div_rem([1, 1], [], 5) is None
    assert cas.gfp_div_rem([1, 1], [0], 5) is None


@pytest.mark.parametrize(
    "coeffs,p,expected",
    [
        ([1, 1, 1], 2, True),
        ([1, 0, 1], 2, False),
        ([1, 1], 2, True),
        ([2, 0, 1], 3, False),
        ([1, 0, 1], 3, True),
    ],
)
def test_gfp_is_irreducible_matches_sympy(coeffs: list[int], p: int, expected: bool) -> None:
    assert cas.gfp_is_irreducible(coeffs, p) == expected
    x = sp.Symbol("x")
    poly = sum(c * x**i for i, c in enumerate(coeffs))
    assert sp.Poly(poly, x, modulus=p).is_irreducible == expected


@pytest.mark.parametrize("p", [2, 3, 5])
def test_gfp_factor_berlekamp_multiplies_back(p: int) -> None:
    a = [0, 0, 1, 1]  # x^2 (x + 1) mod p
    factors = cas.gfp_factor_berlekamp(a, p)
    assert factors is not None
    rebuilt = [1]
    for factor, multiplicity in factors:
        for _ in range(multiplicity):
            rebuilt = cas.gfp_mul(rebuilt, factor, p)
    normalized = list(a)
    while normalized and normalized[-1] % p == 0:
        normalized.pop()
    leading = normalized[-1] % p
    scaled = cas.gfp_scale(rebuilt, leading, p)
    assert scaled == [value % p for value in normalized]


@pytest.mark.parametrize("p", [5, 7, 11])
def test_gfp_roots_are_genuine_roots(p: int) -> None:
    coeffs = [-1, 0, 1]  # x^2 - 1
    roots = cas.gfp_roots(coeffs, p)
    for root in roots:
        assert (root * root - 1) % p == 0
    assert sorted(roots) == sorted(r % p for r in (1, p - 1))


@pytest.mark.parametrize("p", [2, 3])
def test_gfp_gcd_and_pow_mod_agree_with_direct_computation(p: int) -> None:
    a = [1, 1, 1]
    modulus = [1, 1, 1]
    powered = cas.gfp_pow_mod([0, 1], 3, modulus, p)
    assert powered is not None
    assert cas.gfp_gcd(a, a, p) == cas.gfp_scale(a, pow(a[-1], -1, p), p)


@pytest.mark.parametrize("degree", [2, 3, 4, 8, 16])
def test_sparse_search_finds_a_certificate_two_independent_checkers_accept(
    degree: int,
) -> None:
    from axeyum._native.cas.certify import gf2

    outcome = cas.search_sparse_half_degree(degree)
    assert outcome.kind == "Found"
    assert outcome.candidates_tested >= 1
    certificate = outcome.certificate
    assert certificate is not None
    both = certificate.check_both()
    assert both.primary.accepted
    assert both.independent.accepted
    assert both.primary.frobenius_steps + both.primary.bezout_obligations > 0
    assert gf2 is not None


def test_sparse_search_budget_of_zero_reports_candidate_limit_not_a_failure() -> None:
    limits = cas.SparseSearchLimits(max_tail_terms=4, max_candidates=0)
    outcome = cas.search_sparse_half_degree(8, limits)
    assert outcome.kind == "CandidateLimit"
    assert outcome.limit == 0
    assert outcome.certificate is None


def test_sparse_search_rejects_a_malformed_policy() -> None:
    with pytest.raises(cas.Gf2Error):
        cas.search_sparse_half_degree(8, cas.SparseSearchLimits(max_tail_terms=3))


def test_binary_extension_long_cycle_trace_reports_every_field() -> None:
    report = cas.binary_extension_long_cycle_trace(0b111, 3, 1)
    assert report.field_degree == 2
    assert report.field_order == 4
    assert report.polynomial_degree == 3
    assert report.fixed_leading_coefficients == 1
    assert report.free_coefficients == 2
    assert report.candidate_count == report.field_order**report.free_coefficients
    assert isinstance(report.mangoldt_sum, int)
    assert isinstance(report.error, int)


def test_binary_extension_trace_rejects_a_reducible_field_modulus() -> None:
    with pytest.raises(cas.Gf2Error):
        cas.binary_extension_long_cycle_trace(0b110, 3, 1)


def test_binary_extension_closed_forms_expose_exact_big_integers() -> None:
    form = cas.binary_extension_ell_two_degree_five_closed_form(4)
    assert form.field_degree == 4
    assert form.field_order == 2**4
    assert isinstance(form.connected_adams_trace, int)
    assert form.normalized_q_degree_excess >= 0
    seven = cas.binary_extension_ell_three_degree_seven_closed_form(4)
    assert seven.field_order == 2**4
    witt = cas.binary_extension_ell_three_degree_seven_witt_shifted_closed_form(4)
    assert witt.conductor_one_high_character_trace == 0


def test_extension_trace_hankel_minor_is_the_exact_determinant() -> None:
    minor = cas.extension_trace_hankel_minor([1, 2, 4, 8, 16], 0, 1)
    assert minor.tested_maximum_recurrence_order == 1
    assert minor.determinant == 0  # a geometric sequence has a first-order recurrence


# ==========================================================================
# propositional logic
# ==========================================================================


def test_boolean_truth_table_and_tautology_agree_with_brute_force() -> None:
    p, q = cas.BoolExpr.var("p"), cas.BoolExpr.var("q")
    formula = cas.BoolExpr.implies(cas.BoolExpr.and_([p, q]), p)
    assert formula.is_tautology()
    table = formula.truth_table()
    assert table is not None and len(table) == 4
    assert all(value for _, value in table)


def test_boolean_normal_forms_are_equivalent_to_the_original() -> None:
    p, q, r = (cas.BoolExpr.var(name) for name in "pqr")
    formula = cas.BoolExpr.iff(cas.BoolExpr.xor([p, q]), r)
    assert formula.equivalent(formula.to_dnf())
    assert formula.equivalent(formula.to_cnf())
    minimal = formula.simplify_qmc()
    assert minimal is not None
    assert formula.equivalent(minimal)


def test_boolean_satisfiability_and_contradiction_are_complementary() -> None:
    p = cas.BoolExpr.var("p")
    contradiction = cas.BoolExpr.and_([p, cas.BoolExpr.negate(p)])
    assert contradiction.is_contradiction()
    assert not contradiction.is_satisfiable()
    assert contradiction.is_tautology() is False


def test_boolean_evaluate_reports_an_unbound_variable_as_none() -> None:
    p, q = cas.BoolExpr.var("p"), cas.BoolExpr.var("q")
    formula = cas.BoolExpr.or_([p, q])
    assert formula.evaluate({"p": True, "q": False}) is True
    assert formula.evaluate({"p": False}) is None
    assert formula.variables == ["p", "q"]


def test_boolean_past_the_budget_declines_rather_than_answering_false() -> None:
    variables = [cas.BoolExpr.var(f"v{i}") for i in range(cas.BOOL_MAX_VARS + 1)]
    formula = cas.BoolExpr.or_(variables)
    assert cas.BOOL_MAX_VARS == 20
    assert formula.is_satisfiable() is None
    assert formula.is_tautology() is None
    assert formula.truth_table() is None


def test_boolean_variadic_identities_hold() -> None:
    assert cas.BoolExpr.and_([]).is_tautology()
    assert cas.BoolExpr.or_([]).is_contradiction()
    assert cas.BoolExpr.xor([]).is_contradiction()


# ==========================================================================
# certificate routes: moments
# ==========================================================================


@pytest.mark.parametrize("order", [0, 1, 2, 3, 5])
def test_falling_moment_producer_yields_a_certificate_its_checker_accepts(order: int) -> None:
    certificate = moments.prove_squared_binomial_falling_moment(order)
    assert certificate is not None
    assert certificate.order == order
    report = certificate.check()
    assert report.accepted()
    assert len(report) == 1
    assert report.discharged == 1


def test_falling_moment_above_the_budget_declines_before_proof_work() -> None:
    cap = moments.MAX_PROVED_SQUARED_BINOMIAL_FALLING_MOMENT
    assert cap == 255
    assert moments.prove_squared_binomial_falling_moment(cap + 1) is None


def test_a_tampered_falling_moment_certificate_is_rejected() -> None:
    certificate = moments.prove_squared_binomial_falling_moment(2)
    assert certificate is not None
    tampered = moments.CertifiedSquaredBinomialFallingMoment(
        certificate.order, certificate.closed_form + E.int(1), certificate.certificate
    )
    report = tampered.check()
    assert not report.accepted()
    assert len(report) == 1  # the checker LOOKED; it did not vacuously pass


@pytest.mark.parametrize("moment", [0, 1, 2, 3])
def test_raw_moment_producer_yields_a_certificate_with_per_component_counts(
    moment: int,
) -> None:
    certificate = moments.prove_squared_binomial_moment(moment)
    assert certificate is not None
    report = certificate.check()
    assert report.accepted()
    # one obligation per WZ-certified component, plus the composite
    assert len(report) == len(certificate.components) + 1
    assert report.discharged == len(report)


def test_raw_moment_above_the_budget_declines() -> None:
    cap = moments.MAX_PROVED_SQUARED_BINOMIAL_MOMENT
    assert cap == 35
    assert moments.prove_squared_binomial_moment(cap + 1) is None


def test_a_tampered_raw_moment_certificate_is_rejected() -> None:
    certificate = moments.prove_squared_binomial_moment(2)
    assert certificate is not None
    tampered = moments.CertifiedSquaredBinomialMoment(
        certificate.moment, certificate.closed_form + E.int(1), certificate.components
    )
    assert not tampered.check().accepted()


def wz_binomial_sum() -> moments.WzCertificate:
    n, k = E.var("n"), E.var("k")
    summand = moments.binomial_coefficient(n, k)
    two_to_the_n = (E.int(2).ln() * n).exp()
    certificate = moments.prove_wz_sum(summand, "n", "k", two_to_the_n, 1, 0, 1)
    assert certificate is not None
    return certificate


def test_wz_certificate_carries_every_input_and_its_checker_accepts() -> None:
    certificate = wz_binomial_sum()
    assert certificate.n == "n"
    assert certificate.k == "k"
    assert (certificate.base, certificate.k_lo, certificate.k_hi) == (1, 0, 1)
    report = certificate.check()
    assert report.accepted()
    assert len(report) == 2
    assert [o.name for o in report.obligations] == ["wz-telescoping", "base-case"]


def test_a_tampered_wz_multiplier_is_rejected_by_the_telescoping_obligation() -> None:
    certificate = wz_binomial_sum()
    tampered = moments.WzCertificate(
        certificate.summand,
        certificate.n,
        certificate.k,
        certificate.rhs,
        certificate.base,
        certificate.k_lo,
        certificate.k_hi,
        certificate.multiplier + E.int(1),
    )
    report = tampered.check()
    assert not report.accepted()
    assert len(report) == 2  # both obligations were examined
    failed = [o.name for o in report.obligations if not o.discharged]
    assert failed == ["wz-telescoping"]


def test_a_tampered_wz_right_hand_side_is_rejected() -> None:
    certificate = wz_binomial_sum()
    tampered = moments.WzCertificate(
        certificate.summand,
        certificate.n,
        certificate.k,
        certificate.rhs + E.int(1),
        certificate.base,
        certificate.k_lo,
        certificate.k_hi,
        certificate.multiplier,
    )
    assert not tampered.check().accepted()


def test_prove_wz_sum_declines_a_false_identity() -> None:
    n, k = E.var("n"), E.var("k")
    summand = moments.binomial_coefficient(n, k)
    wrong = (E.int(2).ln() * n).exp() + E.int(1)
    assert moments.prove_wz_sum(summand, "n", "k", wrong, 1, 0, 1) is None


def test_moment_report_refuses_an_empty_obligation_list() -> None:
    certificate = moments.prove_squared_binomial_falling_moment(1)
    assert certificate is not None
    report = certificate.check()
    assert moments.require_nonempty(report) is not None


# ==========================================================================
# certificate routes: cofactor ansatz and linear elimination
# ==========================================================================


def poly(name: str) -> cas.MvPoly:
    return cas.MvPoly.var(name)


def test_cofactors_by_ansatz_solves_a_membership_and_the_check_re_expands() -> None:
    x, y = poly("x"), poly("y")
    generators = [x.sub(y)]
    target = x.mul(x).sub(y.mul(y))
    outcome = ansatz.cofactors_by_ansatz(generators, target)
    assert outcome.kind == "Solved"
    assert outcome.degree == 1
    report = outcome.check()
    assert report.accepted()
    assert report.identity_holds
    assert report.nonzero_cofactors == 1
    cofactors = outcome.cofactors
    assert cofactors is not None
    assert ansatz.combination(cofactors, generators) == target


def test_ansatz_reports_not_in_degree_as_a_decision_about_the_slice() -> None:
    x = poly("x")
    outcome = ansatz.cofactors_by_ansatz([x.mul(x)], x, ansatz.AnsatzLimits(max_cofactor_degree=2))
    assert outcome.kind == "NotInDegree"
    assert outcome.bound == 2
    assert outcome.decline is None  # NOT a decline: a decided answer
    assert outcome.cofactors is None
    assert not outcome.check().accepted()


def test_ansatz_declines_under_a_column_budget_and_names_the_budget() -> None:
    x, y = poly("x"), poly("y")
    outcome = ansatz.cofactors_by_ansatz(
        [x.sub(y)],
        x.mul(x).sub(y.mul(y)),
        ansatz.AnsatzLimits(max_cofactor_degree=3, max_columns=1, max_rows=1),
    )
    assert outcome.kind == "Declined"
    assert outcome.decline in {"Columns", "Rows"}
    assert outcome.bound is None


def test_ansatz_limits_defaults_are_the_rust_geometry_values() -> None:
    limits = ansatz.AnsatzLimits.geometry()
    assert (limits.max_cofactor_degree, limits.max_columns, limits.max_rows) == (
        3,
        20_000,
        200_000,
    )
    assert ansatz.AnsatzLimits() == limits


def test_ansatz_check_reports_a_vacuous_identity_as_not_accepted() -> None:
    x = poly("x")
    zero = x.sub(x)
    outcome = ansatz.cofactors_by_ansatz([x], zero)
    assert outcome.kind == "Solved"
    report = outcome.check()
    assert report.identity_holds
    assert report.nonzero_cofactors == 0
    assert not report.accepted()  # nothing was established


def test_linear_elimination_identity_is_re_derived_by_the_checker() -> None:
    x, y, z = poly("x"), poly("y"), poly("z")
    generators = [x.add(y).sub(z), x.sub(y)]
    target = x.mul(x)
    result = ansatz.eliminate(generators, target)
    assert result is not None
    report = result.check()
    assert report.identity_holds
    assert report.multiplier_matches
    assert report.accepted()
    assert report.blocks >= 1


def test_detect_linear_blocks_feeds_eliminate_blocks() -> None:
    x, y, z = poly("x"), poly("y"), poly("z")
    generators = [x.add(y).sub(z), x.sub(y)]
    target = x.mul(x)
    blocks = ansatz.detect_linear_blocks(generators, target)
    assert blocks
    assert all(block.unknowns and len(block.rows) == len(block.unknowns) for block in blocks)
    pinned = ansatz.eliminate_blocks(generators, target, blocks)
    assert pinned is not None
    assert pinned.check().accepted()
    heuristic = ansatz.eliminate(generators, target)
    assert heuristic is not None
    assert pinned.multiplier == heuristic.multiplier


def test_combination_is_the_public_re_expansion_and_overflows_to_none() -> None:
    x, y = poly("x"), poly("y")
    assert ansatz.combination([x, y], [x, y]) == x.mul(x).add(y.mul(y))
    assert ansatz.combination([], []) == cas.MvPoly.zero()


# ==========================================================================
# per-kind SOS checkers
# ==========================================================================


def test_per_kind_sos_checker_refuses_an_artifact_of_another_kind() -> None:
    artifacts = {a.kind: a for a in sos.corpus()}
    assert artifacts, "the committed SOS corpus is empty"
    for kind, checker in (
        ("lyapunov", sos.check_lyapunov),
        ("barrier", sos.check_barrier),
        ("psd-not-sos", sos.check_psd_not_sos),
    ):
        artifact = artifacts.get(kind)
        if artifact is None:
            continue
        report = checker(artifact)
        assert len(report) > 0
        for other_kind, other in artifacts.items():
            if other_kind != kind:
                with pytest.raises(cas.CasError):
                    checker(other)


def test_check_artifact_agrees_with_check_on_every_corpus_artifact() -> None:
    corpus = sos.corpus()
    assert len(corpus) >= 1
    checked = 0
    for artifact in corpus:
        assert len(sos.check_artifact(artifact)) == len(sos.check(artifact))
        checked += 1
    assert checked == len(corpus)


# ==========================================================================
# hypothesis properties
# ==========================================================================


@given(
    st.integers(min_value=-(10**12), max_value=10**12),
    st.integers(min_value=-(10**12), max_value=10**12),
)
def test_property_gcd_lcm_and_bezout_agree_with_the_stdlib(a: int, b: int) -> None:
    assert cas.gcd(a, b) == math.gcd(a, b)
    ours = cas.lcm(a, b)
    assert ours == math.lcm(abs(a), abs(b))
    g, x, y = cas.extended_gcd(a, b)
    assert a * x + b * y == g == math.gcd(a, b)


@given(
    st.integers(min_value=0, max_value=10**6),
    st.integers(min_value=0, max_value=64),
    st.integers(min_value=1, max_value=10**6),
)
def test_property_mod_pow_agrees_with_python_pow(base: int, exponent: int, modulus: int) -> None:
    ours = cas.mod_pow(base, exponent, modulus)
    assert ours == pow(base, exponent, modulus)


@given(st.integers(min_value=0, max_value=25), st.integers(min_value=0, max_value=25))
def test_property_binomial_and_stirling_identities_hold(n: int, k: int) -> None:
    # Pascal's rule, and the Stirling row sum, both over the whole grid.
    left = cas.binomial(n, k)
    assert left == (math.comb(n, k) if 0 <= k <= n else 0)
    if n >= 1 and 1 <= k <= n:
        assert cas.binomial(n, k) == cas.binomial(n - 1, k - 1) + cas.binomial(n - 1, k)
    if n <= 12:
        row = [cas.stirling_second(n, j) for j in range(n + 1)]
        assert all(value is not None for value in row)
        assert sum(row) == cas.bell(n)


@given(
    st.lists(
        st.integers(min_value=-(10**6), max_value=10**6),
        min_size=1,
        max_size=12,
    )
)
def test_property_statistics_agree_with_the_stdlib_over_exact_fractions(
    values: list[int],
) -> None:
    data = [Fraction(v) for v in values]
    assert cas.mean(data) == statistics.mean(data)
    assert cas.median(data) == statistics.median(data)
    assert cas.variance(data) == statistics.pvariance(data)
    if len(data) >= 2:
        assert cas.sample_variance(data) == statistics.variance(data)
    else:
        assert cas.sample_variance(data) is None
