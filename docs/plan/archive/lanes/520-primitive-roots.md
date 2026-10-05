# Lane: primitive-roots — the multiplicative order of a unit mod n, and primitive roots (W1-7)

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, primitive-roots, 2026-09-04).** Roadmap item W1-7,
the number theorist's first Next Five entry
(`docs/math-department/01-number-theory.md`). ADR-1598 records the design.

**Landed, all eleven admitted by `Kernel::add_declaration` with an empty
`axiom_footprint`** (read from the kernel, not from source text):

| declaration | what it is |
|---|---|
| `Int.one_pow` | `∀ k, pow one k = one` — the one `Int.pow` law that did not exist |
| `Int.IsOrder` | `0 < k ∧ (a^k ≡ 1 [n] ∧ ∀ j, 0<j → j<k → ¬ a^j ≡ 1 [n])` |
| `Int.pow_modeq_one_of_dvd` | `k ∣ m` and `a^k ≡ 1` give `a^m ≡ 1` |
| `Int.order_dvd_of_pow_modeq_one` | the converse, by `Nat.div_mod_exists` against minimality |
| `Int.pow_modeq_one_iff_order_dvd` | **deliverable 3**, the two as one `Iff` |
| `Int.order_unique` | two orders of one unit are equal |
| `Int.order_exists` | **deliverable 1**, by `Nat.lnp_bounded_search` below `φ(n)` |
| `Int.order_dvd_totient` | **deliverable 2**, Lagrange in the concrete case |
| `Int.IsPrimitiveRoot` | **deliverable 4**, a unit whose order is `φ(n)` |
| `Int.order_pow_eq_of_le` | the one-sided half of pairwise incongruence |
| `Int.primitive_root_pow_injective` | **deliverable 4**, the powers enumerate the units |

**Where this stopped, and exactly why.** Deliverable 5 — existence of a
primitive root modulo a prime — did **not** land, and it is not blocked on a
decision. The standard route counts elements of each order using
`∑_{d|n} φ(d) = n`. The obstruction is that identity's left-hand side: it sums
over the **divisor set** of `n`, and no divisor-set aggregate exists in either
prelude. `Nat.sumRange` folds a contiguous `[0,n)`; `Nat.countRange` counts a
`Bool` predicate over a contiguous range; `Int.prodRangeIf` folds a product
over a predicate-restricted contiguous range. The sum can be *expressed* as
`sumRange (fun d => if d ∣ n then φ(d) else 0) (succ n)`, but every step of the
standard proof then needs the divisor-pairing reindexing `d ↦ n/d` of that
restricted sum — and `int_prelude/euler_totient.rs`'s own module doc records
that the analogous restricted-**product** reindexing needed a
remove-one-element induction built from scratch. That is a slice of comparable
size to everything above. It is the honest next task for W1-7.

**Retrieval (step 0).** Fresh `shape_search` build, `declarations=2674`,
positive control `Nat.Finset.pigeonhole` (landed the same day at `f91ded0c2`).
ABSENT for `--name-like primitiveroot`, `--name-like multorder`,
`--name-like ordn`; `--name-like order` returns only the `Alg.OrderedRing`
family, which is *order* in the relational sense. Nothing here is a
re-derivation, and nothing here needed a new `Nat` lemma — every ingredient
existed (`Int.pow_add`/`pow_mul`, the 38-declaration `Int.ModEq` family,
`Int.euler_totient_theorem`, `Nat.lnp_bounded_search`, `Nat.div_mod_exists`,
`Nat.zero_or_succ`, `Nat.le_dest`, `Nat.le_of_dvd`, and
`euler_totient.rs`'s already-`pub(super)` `coprime_of_modeq_inverse`).

**Two design notes worth carrying forward.** (1) The search predicate is
`Q j := a^(succ j) ≡ 1`, not `a^j ≡ 1` — at `j = 0` the latter is true for
every `a`, so the search would always answer `0`. (2) `Coprime (a^i) n` came
out of the order relation itself: `t = i + f` makes `a^f` a modular inverse of
`a^i`, and the Bézout extraction is already a named helper. No
`Coprime`-is-multiplicative lemma was needed.

**Mutation table.** Measured, not predicted; each row is a real build.

| id | mutation | predicted | measured |
|---|---|---|---|
| MUT-A | `three_mod_eight_is_killed_by_exactly_the_even_exponents`: move `m = 3` from the miss list to the hit list | that test alone dies | **that test alone died** |
| MUT-B | `three_has_multiplicative_order_two_mod_eight`: change the refuted claim from `IsOrder 8 3 4` to `IsOrder 8 3 2` (which is TRUE) | that test alone dies | **that test alone died** |
| MUT-C | `declare_is_order`: transpose the positivity conjunct, `Lt 0 k` -> `Lt k 0` | ? | **all 6 die, at `build_int_prelude`** — every failure reads `Int prelude must build: TypeMismatch` |

MUT-A and MUT-B were applied together in one run: 4 of 6 passed and exactly
the two mutated tests failed, so neither mutation leaks into a test it does not
target.

MUT-C is the informative one and its answer is not "exactly one test". A
`Definition` this development's own proofs consume cannot be mutated past
`Kernel::add_declaration`: `Int.order_exists` supplies `Nat.zero_lt_succ` for
the positivity conjunct, so transposing it makes the prelude itself refuse to
build and every test that constructs a kernel dies at line 1. **The trusted
gate, not the test suite, is the guard against a mutated `IsOrder`.** What the
gate cannot see is whether the definition says the intended thing about
concrete values — and that residual is exactly what MUT-A and MUT-B show the
batteries do cover.

<!-- plan-section: landed-changes -->

| 2026-09-04 | primitive-roots | `Int.IsOrder` and the divisibility characterization (`f04f3eaf4`) |
| 2026-09-04 | primitive-roots | `Int.order_exists`/`order_unique`/`order_dvd_totient`, `Int.IsPrimitiveRoot`, `Int.primitive_root_pow_injective` |
| 2026-09-04 | primitive-roots | `mult_order_tests.rs`: the `ord_8(3)=2` / `ord_7(3)=6` evaluation batteries and the `IsPrimitiveRoot 8 3` refutation |
| 2026-09-04 | primitive-roots | ADR-1598, and four curated facts for the named results |
