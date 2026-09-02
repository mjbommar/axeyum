# Lane: eisenstein-lattice

<!-- plan-section: lane-status -->

**Status:** landed, but NOT the briefed target (2026-09-02). Eisenstein's lemma
(ADR-1260 step 1) is **not proved**, and neither is quadratic reciprocity. What
landed is ADR-1260's **residue 2** in general form, plus the piece residue 3 was
actually short of — which is not the piece any prior handoff named. Decision,
mutation table and what the controls cannot catch:
[ADR-1510](../../research/09-decisions/adr-1510-the-side-condition-is-coprimality-and-the-additive-bijection-was-missing.md).

## Prerequisite verification (this lane, in-tree, not inherited)

The brief's picture was stale in both directions.

| the brief said | measured here |
| --- | --- |
| `Int.sumRange`, `sumRange_add`, `sumRange_congr` "have since landed" | correct — `int_prelude/sum.rs`, nine registered names (ADR-1275) |
| the "row-count-is-a-floor lemma" is an open residue to take after step 1 | **already closed** by a sibling lane — ADR-1290, `nat_prelude/floor_count.rs`, three declarations |
| the side condition "is Euclid's lemma and cheap" | cheap, yes; but it is **`Nat.gauss_lemma`**, Euclid with the primality side condition already dropped, so the theorem asks for coprimality and never mentions `PrimeCond` |
| step 1 is blocked on the mod-2 bookkeeping | the bookkeeping is the LAST step, not the binding one. The binding one is that Gauss's lemma runs its bijection **multiplicatively** (`Int.prodRange_permute`) and Eisenstein needs the **same bijection additively** — and no aggregate in this kernel had a `Nat`-valued permutation law |

`Nat.gaussCountBleClosedFormDisj` and `Int.gaussLemmaSignCount` were checked as
the brief asked: the lattice count is **not** a corollary of them. They are the
`a := 2` closed form and the multiplicative assembly; neither reaches an
additive statement.

## Landed

| change | what |
| --- | --- |
| `crates/axeyum-lean-kernel/src/nat_prelude/eisenstein_side.rs` | two declarations, both admitted FIRST attempt, both axiom-free |
| `crates/axeyum-lean-kernel/src/nat_prelude/eisenstein_side_tests.rs` | concrete instantiation with every hypothesis discharged, the false-witness control, footprint, and the declared types pinned character for character |
| `crates/axeyum-lean-kernel/src/nat_prelude/sum_range_permute.rs` | two declarations, both admitted FIRST attempt, both axiom-free |
| `crates/axeyum-lean-kernel/src/nat_prelude/sum_range_permute_tests.rs` | instantiation at a non-`{0,1}` summand, both hypothesis-dropping controls, footprint, type pins |
| `crates/axeyum-lean-kernel/src/nat_prelude.rs` | four name fields, registrations, two build-order calls |
| `crates/axeyum-lean-kernel/src/nat_prelude/nat_prelude_tests.rs` | the four names added to the environment-derived coverage list |
| `docs/research/09-decisions/adr-1510-*.md` | the decision, the mutation table, and the honest report that this table has NO admitted-and-survived instance |
| `docs/research/09-decisions/adr-1510-eisenstein-side-and-sum-permute-checks.py` | 5 claims, 7 controls, 1 recorded survivor; exit status depends on the finding, and 11 of 11 self-mutations exit 1 |
| `artifacts/facts/F-nat-{mul-ne-mul-of-coprime-of-lt,mul-succ-ne-mul-succ-of-coprime,sumrange-point-change,sumrange-permute}.json` | four ledger rows, statements verbatim from `nat_theorem_inventory` |

Declarations:

- `Nat.mul_ne_mul_of_coprime_of_lt : ∀ pp q x y, gcd pp q = 1 → 0 < x → x < pp → pp*y ≠ q*x`
- `Nat.mul_succ_ne_mul_succ_of_coprime : ∀ pp q x y, gcd pp q = 1 → succ x < pp → pp*(y+1) ≠ q*(x+1)`
- `Nat.sumRange_point_change : ∀ a b i0 n, i0 < n → (agree below) → (agree above) → sumRange a n + b i0 = sumRange b n + a i0`
- `Nat.sumRange_permute : ∀ f σ n, InjectiveOn σ n → MapsInto σ n → sumRange f n = sumRange (f ∘ σ) n`

## Checks run

- `cargo test --release -p axeyum-lean-kernel --lib -- nat_prelude:: --test-threads=4` — **335 passed, 0 failed**
- `cargo test --release -p axeyum-lean-kernel --lib -- int_prelude:: --test-threads=4` — **74 passed, 0 failed**
- `cargo clippy --release -p axeyum-lean-kernel --lib --all-targets -- -D warnings` — clean
- `python3 docs/research/09-decisions/adr-1510-eisenstein-side-and-sum-permute-checks.py` — PASS; 11 of 11 self-mutations exit 1
- `python3 scripts/validate-facts.py` — **2580 facts, 0 errors**
- `python3 scripts/check-settled-fact-statements.py` — PASS, 2347 pinned, drifted 0
- `python3 scripts/gen-adr-index.py --check` — PASS
- both fact `checker_command`s run WITH a negative control: the anchored `grep -c` prints `1`/exit 0 for a real name and `0`/exit **1** for a one-character typo
- five kernel mutants, **all five REJECTED** by the trusted gate

## Concrete instantiation table

| declaration | instance | conclusion checked | arithmetic |
| --- | --- | --- | --- |
| `mul_ne_mul_of_coprime_of_lt` | `(pp,q,x,y) = (3,5,2,3)` | `Not (3*3 = 5*2)` | 9 ≠ 10 |
| `mul_ne_mul_of_coprime_of_lt` | `(pp,q,x,y) = (5,7,3,4)` | `Not (5*4 = 7*3)` | 20 ≠ 21 |
| `mul_succ_ne_mul_succ_of_coprime` | `(3,5,1,2)` | `Not (3*3 = 5*2)` | 9 ≠ 10 |
| `mul_succ_ne_mul_succ_of_coprime` | `(5,7,2,3)` | `Not (5*4 = 7*3)` | 20 ≠ 21 |
| `sumRange_point_change` | `a k = k*k`, `b k = k`, `i0 = 2`, `n = 3` | `Sa 3 + b 2 = Sb 3 + a 2` | 5+2 = 3+4 = 7, and `Sa ≠ Sb` (5 vs 3) |
| `sumRange_permute` | `f k = k*k`, `σ k = 2−k`, `n = 3` | `sumRange f 3 = sumRange (f∘σ) 3` | 5 = 5 |

Every hypothesis of the two side-condition instances is discharged, including
the coprimality proof by `Eq.refl` — so `Nat.gcd` really does reduce at both
prime pairs. The permutation instances supply `InjectiveOn`/`MapsInto` as opaque
free variables in a `LocalContext` and check the inferred CONCLUSION; that is a
weaker check and ADR-1510 says so.

## Not proved, and what a next lane takes

Eisenstein's lemma and quadratic reciprocity remain open. The residues, each
verified in-tree:

1. **The additive Gauss bijection, instantiated.** `Nat.sumRange_permute` at
   `σ j := pred (gaussFold pp a (succ j))`. Its two hypotheses are **already
   proved and already `Nat`-typed** — `Nat.gauss_fold_shift_injective_on` and
   `Nat.gauss_fold_shift_maps_into` render as `AxNat.injectiveOn (fun x3 => …) x0`
   and `AxNat.mapsInto (fun x3 => …) x0`, exactly the predicates
   `sumRange_permute` takes. Assembly, not new mathematics.
2. **The residue/fold reconciliation** — `Σ leastResidue = Σ gaussFold + pp·N −
   2·Σ_neg gaussFold`. Wants a conditional sum. `Int.prodRangeIf` exists; **this
   lane did not measure whether a `sumRangeIf` analogue does**, and does not
   claim it is easy.
3. **The mod-2 bookkeeping**, over `Int.sumRange`/`Int.modEq_sumRange`.
4. **Step 2's assembly** — `Nat.countRectangle_partition` at the two strict
   predicates, its per-point hypothesis discharged by this lane's
   `mul_succ_ne_mul_succ_of_coprime` and its row counts named as floors by
   ADR-1290's `countRange_mul_succ_le_eq_floor`. **Every input now exists and
   nobody has run it.** This is the cheapest remaining increment.

Graded family (ADR-0603): all four facts are row 1, the general constructive
form. **Row 2 is UNASSESSED** — the false readings are refuted numerically at
named witnesses (ADR-1510's M1–M5, M7) and asserted as `def_eq` controls in the
test files, but none is stated as a kernel theorem, and no claim is made that
one is impossible.

## Found, not fixed

`scripts/check-shape-duplicates.py` is **RED on this branch and the group is not
this lane's**: `Nat.coprime_factorial_of_lt_prime` (`gauss_lemma.rs`) and
`Nat.prime_coprime_factorial_of_lt` (`prime_dvd_factorial_lcm.rs`) are an
unadjudicated shape duplicate. Neither file is touched by this lane's commits.
It needs adjudication by whoever owns `prime_dvd_factorial_lcm.rs`.
