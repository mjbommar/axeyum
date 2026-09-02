# Lane: eisenstein-2

<!-- plan-section: lane-status -->

**Status:** landed (2026-09-02). Three axiom-free declarations closing
ADR-1540's residues **4** and **1**. **Eisenstein's lemma is still NOT proved,
and neither is quadratic reciprocity** — what landed is step 1's counting
identity and the additive Gauss bijection, not the mod-2 reading and not
step 2. Decision, mutation table and the two recorded survivors:
[ADR-1544](../../research/09-decisions/adr-1544-the-lattice-count-was-assembly-and-the-min-is-not-decoration.md).

## Step 0 — prerequisite verification (this lane, in-tree, not inherited)

`examples/shape_search`, rebuilt on this branch (`declarations=2048` before the
lane's own declarations, so not a stale binary). Every input ADR-1540's residue
4 named was present; the one thing it declined to guess about is genuinely
absent.

| named input | verdict |
| --- | --- |
| `Nat.countRectangle_partition` / `_compl` | FOUND |
| `Nat.countRange_mul_succ_le_eq_floor` / `_min` | FOUND |
| `Nat.gaussFold`, `Nat.leastResidue`, `Nat.gaussNegCount` | FOUND |
| `Nat.gauss_fold_shift_injective_on` / `_maps_into` | FOUND |
| `Nat.sumRange_permute`, `Nat.sumRange_point_change` | FOUND |
| `Nat.mul_succ_ne_mul_succ_of_coprime` | FOUND |
| **`sumRangeIf` (any prelude)** | **ABSENT** |
| `prodRangeIf` — the positive control for that query | FOUND, 12 declarations |
| `Nat.countRectangle_partitionX` — negative control | ABSENT, against `positive control: any-kind=2048` |

So ADR-1540's "every input now exists and nobody has run it" was correct for
residue 4, and its refusal to claim residue 2 was easy was also correct.

## Landed

| change | what |
| --- | --- |
| `crates/axeyum-lean-kernel/src/nat_prelude/eisenstein_lattice.rs` | two declarations, both admitted FIRST attempt, both axiom-free |
| `crates/axeyum-lean-kernel/src/nat_prelude/eisenstein_lattice_tests.rs` | 7 tests: concrete instantiation with both sides evaluated, both hypotheses shown load-bearing at numeric counterexamples, the declared types pinned character for character |
| `crates/axeyum-lean-kernel/src/nat_prelude/gauss_fold_sum.rs` | one declaration, admitted FIRST attempt, axiom-free |
| `crates/axeyum-lean-kernel/src/nat_prelude/gauss_fold_sum_tests.rs` | 5 tests, same three kinds |
| `crates/axeyum-lean-kernel/src/nat_prelude.rs` | three name fields, registrations, two build-order calls, and one `#[allow(clippy::large_stack_arrays)]` (below) |
| `crates/axeyum-lean-kernel/src/nat_prelude/nat_prelude_tests.rs` | the three names added to the environment-derived coverage list |
| `crates/axeyum-py/src/kernel/prelude_fields.rs` | regenerated (`scripts/gen-py-prelude-fields.py`) |
| `docs/research/09-decisions/adr-1544-…md` + `adr-1544-eisenstein-lattice-checks.py` | 5 claims, 10 controls, 2 recorded survivors; 12 of 12 self-mutations exit 1 |
| `artifacts/facts/F-nat-{ble-select-add-of-ne,eisenstein-floor-sum,gauss-fold-sumrange-eq}.json` | three ledger rows, statements verbatim from the kernel's own rendering |

Declarations:

- `Nat.ble_select_add_of_ne : ∀ a b, Not (Eq a b) → sel (ble a b) + sel (ble b a) = 1`
- `Nat.eisenstein_floor_sum : ∀ ap aq m n, gcd (succ ap) (succ aq) = 1 → m < succ ap →
  sumRange (fun x => min n ((succ aq * succ x) / succ ap)) m
  + sumRange (fun y => min m ((succ ap * succ y) / succ aq)) n = n * m`
- `Nat.gauss_fold_sumRange_eq : ∀ m a, gcd a (succ (2*m)) = 1 →
  sumRange succ m = sumRange (fun j => gaussFold (succ (2*m)) a (succ j)) m`

## Three deliberate restatements of ADR-1260's step 1, all argued in ADR-1544

1. **Coprimality plus `Lt m pp`**, not two distinct odd primes with
   `m = (p−1)/2`, `n = (q−1)/2`. A strict generalization: check `C3` verifies
   that Eisenstein's own instances satisfy both hypotheses at all 240 ordered
   pairs of distinct odd primes below 60. `n` is unconstrained.
2. **Divisors given constructively as `succ`**, which is how ADR-1290's floor
   lemma supplies positivity, so no `Lt zero p` hypothesis is formed.
3. **The `min` stays.** Dropping it is **REFUTED** at the generality the
   theorem states (`M4`) and **SURVIVES** only at Eisenstein's own `m`, `n`
   (`M5`, reproducing ADR-1290's `M8`). `floor_count.rs`'s "the consumer never
   sees the min bind" is true and does not license dropping it here.

Also: the internal half-planes are spelled **non-strictly** (`ble`), not
strictly as ADR-1260 describes them, because the non-strict pair IS the floor
lemma's own shape. The headline statement is unchanged — only floors appear in
it — and `M10` records that no numeric check can separate the two spellings.

## Checks run

- `cargo test --release -p axeyum-lean-kernel --lib -- nat_prelude:: --test-threads=4` — **355 passed, 0 failed**
- `cargo test --release -p axeyum-lean-kernel --lib -- int_prelude:: --test-threads=4` — **74 passed, 0 failed**
- `cargo clippy --release -p axeyum-lean-kernel --all-targets -- -D warnings` — clean
- `cargo clippy --release -p axeyum-py --all-targets -- -D warnings` — clean
- `python3 docs/research/09-decisions/adr-1544-eisenstein-lattice-checks.py` — PASS; **12 of 12 self-mutations exit 1**
- `python3 scripts/validate-facts.py` — **2593 facts, 0 errors**
- `python3 scripts/gen-adr-index.py --check` — exit 0
- each fact's `checker_command` run WITH a negative control: the real name prints `1` with both pipeline stages at 0, a one-character typo prints `0` with both stages at **1**
- three kernel declarations, all admitted on the **first** attempt

## Instantiation table

| declaration | instance | checked |
| --- | --- | --- |
| `eisenstein_floor_sum` | `(p,q) = (3,5)`, `m=1`, `n=2` | conclusion inferred and matched; both sides reduce to `2 = n·m`; `3` rejected |
| `eisenstein_floor_sum` | `(p,q) = (5,7)`, `m=2`, `n=3` | both sides reduce to `6 = n·m`; `7` rejected |
| `eisenstein_floor_sum` | `pp = q = 2`, `m = n = 1` (NOT coprime) | floor sum `2`, `n·m = 1` — the identity is FALSE, so coprimality is load-bearing |
| `eisenstein_floor_sum` | `pp = 2`, `q = 1`, `m = 2`, `n = 1` (`m` not `< pp`) | floor sum `3`, `n·m = 2` — FALSE, so the bound is load-bearing |
| `ble_select_add_of_ne` | `(a,b) = (9,10)` and `(10,9)` | selector sum reduces to `1`; instance inferred against `Nat.ne_of_beq_eq_false` |
| `ble_select_add_of_ne` | `a = b = 9` | selector sum reduces to `2` — the hypothesis is load-bearing at exactly one place |
| `gauss_fold_sumRange_eq` | `(m,a) = (1,2)`, `(2,2)`, `(3,3)` (`pp = 3,5,7`) | both sums reduce to `1`, `3`, `6`; the off-by-one rejected |
| `gauss_fold_sumRange_eq` | `(m,a) = (1,3)` (`gcd 3 3 = 3`) | fold sum `0`, triangular sum `1` — FALSE, so coprimality is load-bearing |

Every coprimality hypothesis is discharged by `Eq.refl`, so `Nat.gcd` really
does reduce at each pair; every `Le`/`Lt` hypothesis is built from the two
`Nat.le` constructors only.

## What is still open

1. ~~The additive Gauss bijection, instantiated.~~ **Closed** (ADR-1540
   residue 1).
2. **The residue/fold reconciliation** — `Σ leastResidue = Σ gaussFold + pp·N
   − 2·Σ_neg gaussFold`. Wants a conditional sum, and this lane MEASURED that
   **`sumRangeIf` exists in no prelude** (ABSENT, against a `prodRangeIf`
   control returning 12). The transport from `Nat.prodRangeIf` should be the
   same wrapper-deletion move ADR-1540 used for
   `countRange_permute → sumRange_permute`; nobody has run it, and no claim is
   made here that it is easy.
3. **The mod-2 bookkeeping** over `Int.sumRange`/`Int.modEq_sumRange` — open,
   untouched.
4. ~~Step 2's assembly.~~ **Closed**, in the `min` form.
5. **New:** the `min`-free corollary at `pp = succ (2m)`, `q = succ (2n)`.
   Needs `div (q·(succ x)) pp ≤ n` for `x < m` — true, one arithmetic fact
   about those shapes, not attempted here.

Graded family (ADR-0603): all three facts are row 1. **Row 2 is UNASSESSED**
for all three — the hypothesis-dropping refutations are numeric at named
witnesses and asserted as `def_eq` controls in the test files, but none is
stated as a kernel theorem, and no claim is made that one is impossible. Three
of ADR-1544's seven mutation rows have **no numeric witness at all** and are
caught only by the character-for-character type pins.

## Two things a next lane inherits

- **`NatPrelude` crossed clippy's 16 KiB `large_stack_arrays` threshold** at
  1026 fields on this branch: `derive(Debug)` lowers to
  `debug_struct_fields_finish` over two LOCAL arrays with one entry per field.
  Silenced at the struct with a comment naming the real fix — ADR-1512's
  per-module name registry, already applied to `CRealPrelude` and not to this
  one. The next lane to add a field inherits the allow, not the failure, but
  the growth is real.
- **`scripts/check-settled-fact-statements.py` was already RED on local `main`
  before this lane touched anything**, with 10 unpinned settled facts
  (`F:nat-dvd-prodrange-of-lt`, the `F:nat-multiset-*` family,
  `F:nat-injective-on-or-duplicate`,
  `F:nat-exponent-unique-of-exact-dvd`, …) — each verified present at this
  branch's merge base `73461290f`. This lane's three facts would have made it
  13. `--write` pins all 2360 settled statements and the gate is now exit 0;
  the 10 pre-existing pins are recorded here so the diff is not read as this
  lane's.
