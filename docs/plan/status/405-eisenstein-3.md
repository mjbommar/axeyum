# Lane: eisenstein-3 — `Nat.sumRangeIf`, residues 2 and 3, and Eisenstein's lemma

<!-- plan-section: lane-status -->

**Status: landed (2026-09-02). Eisenstein's lemma is a kernel theorem.**
ADR-1544's three remaining residues — 2, 3 and 5 — all close, and so does the
thing that was blocking them. Nothing ADR-1540 or ADR-1544 left open is still
open. **Quadratic reciprocity is still NOT proved** — its two halves are now
both proved and what is missing is the assembly. Decision, the
correction it forces, and the two recorded survivors:
[ADR-1552](../../research/09-decisions/adr-1552-eisensteins-lemma-was-blocked-on-a-missing-aggregate-and-nothing-else.md).

## Step 0 — prerequisite verification (this lane, in-tree, not inherited)

`examples/shape_search`, rebuilt on this branch (`declarations=2092` before
this lane's own declarations, so not a stale binary reporting a false ABSENT).

| query | verdict |
| --- | --- |
| `--name-like sumRangeIf` | **ABSENT**, against `positive control: any-kind=2092` |
| `--name-like prodRangeIf` (the positive control) | FOUND, 12 declarations |
| `--name-like bnot` (is there a `Bool.not`?) | **ABSENT** |
| `--name-like div_add_mod` / `mod_add_div` | **ABSENT** |
| `--name-like modEq` | FOUND 40, **every one `Int`** — and that verdict is MISLEADING, see below |

## Landed

| change | what |
| --- | --- |
| `crates/axeyum-lean-kernel/src/nat_prelude/subset_sum.rs` | five declarations (one definition, four theorems), all admitted FIRST attempt, all axiom-free |
| `crates/axeyum-lean-kernel/src/nat_prelude/subset_sum_tests.rs` | 9 tests: evaluation-first, three negative controls per instance, the definition's VALUE pinned as well as its type |
| `crates/axeyum-lean-kernel/src/nat_prelude/gauss_residue_reconcile.rs` | one declaration (residue 2), admitted FIRST attempt, axiom-free |
| `crates/axeyum-lean-kernel/src/nat_prelude/gauss_residue_reconcile_tests.rs` | 6 tests: four instances incl. an even composite modulus and a non-coprime pair; three wrong readings refuted numerically |
| `crates/axeyum-lean-kernel/src/nat_prelude/eisenstein_lemma.rs` | four declarations (residue 3 + Eisenstein's lemma + the congruence form), all admitted FIRST attempt, all axiom-free |
| `crates/axeyum-lean-kernel/src/nat_prelude/eisenstein_lemma_tests.rs` | 8 tests; coprimality refuted INSIDE the kernel with a positive control |
| `crates/axeyum-lean-kernel/src/nat_prelude/eisenstein_floor_min_free.rs` | two declarations (residue 5), both admitted FIRST attempt, both axiom-free |
| `crates/axeyum-lean-kernel/src/nat_prelude/eisenstein_floor_min_free_tests.rs` | 5 tests; the restriction to the Eisenstein shape refuted INSIDE the kernel |
| `crates/axeyum-lean-kernel/src/nat_prelude.rs` | twelve name fields, registrations, four build-order calls |
| `crates/axeyum-lean-kernel/src/nat_prelude/nat_prelude_tests.rs` | the twelve names added to the environment-derived coverage list |
| `crates/axeyum-py/src/kernel/prelude_fields.rs` | regenerated (`scripts/gen-py-prelude-fields.py`) |
| `docs/research/09-decisions/adr-1552-…md` + `adr-1552-eisenstein-checks.py` | 6 claims, 11 controls, 2 recorded survivors; 19 of 19 self-mutations exit 1 |
| `artifacts/facts/F-nat-{sumrangeif-zero,sumrangeif-succ,sumrangeif-congr-lt,sumrangeif-compl,leastresidue-sumrange-reconcile,mul-sumrange-div-add-leastresidue,eisenstein-count-identity,eisenstein-lemma,eisenstein-lemma-modeq,div-mul-succ-le-of-le,eisenstein-floor-sum-min-free}.json` | eleven ledger rows, statements verbatim from the kernel's own rendering |

Declarations:

- `Nat.sumRangeIf : (Nat → Bool) → (Nat → Nat) → Nat → Nat`
- `Nat.sumRangeIf_zero` / `Nat.sumRangeIf_succ` — both `Eq.refl`
- `Nat.sumRangeIf_congr_lt` — bounded by `Lt i n`
- `Nat.sumRangeIf_compl : sumRangeIf p f n + sumRangeIf (setCompl p) f n = sumRange f n`
- `Nat.leastResidue_sumRange_reconcile : ∀ ap a m, Σ L + (S + S) = Σ G + pp·N`
- `Nat.mul_sumRange_div_add_leastResidue : ∀ ap a m, a·T = pp·F + Σ L`
- `Nat.eisenstein_count_identity : ∀ m a, gcd a (2m+1) = 1 → a·T + (S+S) = pp·(F+N) + T`
- `Nat.eisenstein_lemma : ∀ m n, gcd (2n+1) (2m+1) = 1 → Even (F + N)`
- `Nat.eisenstein_lemma_modEq : ∀ m n, gcd (2n+1) (2m+1) = 1 → modEq 2 F N`
- `Nat.div_mul_succ_le_of_le : ∀ m n x, Le (succ x) m → Le (div (q·(succ x)) pp) n`
- `Nat.eisenstein_floor_sum_min_free : ∀ m n, gcd pp q = 1 → Σ⌊·⌋ + Σ⌊·⌋ = n·m` (no `min`)

## Five findings a name search does not give you

1. **Residue 2 was never blocked on Gauss's lemma or on coprimality.** Both
   prior ADRs sized it as downstream of the bijection. It is
   **hypothesis-free**: coprimality is what makes the FOLD a bijection, not
   what makes a residue and its reflection add to `pp`. The only side
   condition is `leastResidue < pp`, which `Nat.mod_lt` supplies at the
   constructively positive modulus `succ ap`. The check script verifies the
   identity at 8,450 instances including 5,070 composite-modulus and 3,250
   non-coprime ones. **The only thing standing in front of residue 2 was
   `Nat.sumRangeIf`.**
2. **The division algorithm was already here, under a name nothing points at.**
   There is no `Nat.div_add_mod`. But `Nat.divMod d n q r` unfolds to
   `And (Eq n (add (mul d q) r)) (Lt r d)`, so the LEFT CONJUNCT of
   `Nat.div_mod_exec` is exactly `n = pp·(n/pp) + n mod pp`. No new arithmetic
   was needed for residue 3's first step.
3. **`Nat.modEq` exists**, contrary to the obvious query. `--name-like modEq`
   returns 40 declarations, every one `Int`, because the `Nat` theorems are
   spelled `mod_eq_*` in lower case while the constant they mention is
   `Nat.modEq`. It is the BALANCED form (`∃ u v, a + d·u = b + d·v`), which is
   why the congruence is a five-line corollary of `Even` rather than a second
   proof.
4. **The odd parts come off definitionally.** `Nat.mul` recurses on its RIGHT
   argument, so after one `mul_comm` both `mul T (succ (2n))` and
   `mul X (succ (2m))` ι-reduce to `mul T (2n) + T` and `mul X (2m) + X` with
   no lemma at all. That is what makes the parity step short.
5. **A prebuilt inventory reported a theorem this lane had just declared as
   ABSENT.** `theorem_dependency_inventory` was rebuilt for the first nine
   declarations and NOT for the last two, and it answered *"no theorem matches
   `Nat.div_mul_succ_le_of_le`"* — which its own error text correctly calls a
   failure rather than an empty answer. The fact rows' `checker_command` uses
   `cargo run`, which rebuilds; a prebuilt binary does not.

## Checks run

- `cargo test --release -p axeyum-lean-kernel --lib -- nat_prelude:: --test-threads=4` — **395 passed, 0 failed**
- `cargo clippy --release -p axeyum-lean-kernel --all-targets -- -D warnings` — clean
- `python3 docs/research/09-decisions/adr-1552-eisenstein-checks.py` — PASS; **19 of 19 self-mutations exit 1**
- `python3 scripts/validate-facts.py` — **2617 facts, 0 errors** (after `check-fact-depends-derived.py --fix` added 7 derived edges)
- `python3 scripts/check-settled-fact-statements.py --write` — 2384 pins, unpinned 0
- `scripts/check-merge-hygiene.sh` — PASS
- `python3 scripts/gen-adr-index.py --check` — exit 0
- `nat_axiom_inventory --require-axiom-free nat` — `ok: nat trusted surface = 0`
- the fact `checker_command` run WITH a negative control: the real name prints
  `1` at exit 0, a one-character typo prints `0` at exit **1**
- **twelve kernel declarations, all twelve admitted on the FIRST attempt**

## Instantiation table

| declaration | instance | checked |
| --- | --- | --- |
| `sumRangeIf` | `p i := 3 ≤ i`, `f i := i+1`, `n = 6` | reduces to `15`; rejects `16`, the `prodRangeIf` convention's `18`, and the complement's `6` |
| `sumRangeIf` | `p i := i ≤ 1`, `f i := i·i`, `n = 4` | reduces to `1`; rejects `2`, `3`, `13` |
| `sumRangeIf_succ` | `p i := 3 ≤ i`, `n = 3` | prior sum `0`, new sum `4`; a dropped-term equation would give `0` |
| `sumRangeIf_compl` | both cases above | `15 + 6 = 21`, `1 + 13 = 14`; the selected part alone is NOT the full sum |
| `leastResidue_…_reconcile` | `(pp,a,m) = (7,3,3)` | `11 + (1+1) = 6 + 7·1 = 13`; every aggregate reduces and rejects its neighbour |
| `leastResidue_…_reconcile` | `(5,2,2)`, `(4,3,3)` **even composite**, `(3,3,1)` **non-coprime** | all four aggregates reduce; the theorem needs neither primality nor coprimality |
| `mul_sumRange_div_add_leastResidue` | `(ap,a,m) = (6,3,3)` | `3·6 = 7·1 + 11 = 18`; rejects `19` |
| `eisenstein_count_identity` | `(m,a) = (3,3)` | `3·6 + 2·1 = 7·(1+1) + 6 = 20`; rejects `21` |
| `eisenstein_count_identity` | `(m,a) = (4,3)` (`gcd 3 9 = 3`) | 36 vs 37 — FALSE, so coprimality is load-bearing |
| `eisenstein_lemma` | `(pp,q) = (7,3)`, `(5,3)`, `(7,5)` | `F+N` reduces to `2`, `2`, `4`; each rejects its neighbour |
| `eisenstein_lemma` | `(pp,q) = (9,3)` (`gcd 3 9 = 3`) | `F+N` reduces to `3`, and `3` is refuted as `k+k` for every reachable `k` INSIDE the kernel, with a positive control on `2 = 1+1` |
| `eisenstein_lemma_modEq` | the same three coprime pairs | conclusion inferred and matched against `modEq 2 F N` |
| `div_mul_succ_le_of_le` | every `x < m` at `(m,n) = (3,2)`, `(2,1)`, `(3,1)` | the bound is inferred and the quotient reduces at each index |
| `eisenstein_floor_sum_min_free` | the same three pairs | both sides reduce to `n·m` = `6`, `2`, `3`; each rejects its neighbour |
| `eisenstein_floor_sum_min_free` | `pp = 2`, `q = 5`, `m = 1`, `n = 0` (the cap BINDS) | bare row sum `2`, capped row sum `0`, `def_eq` rejects — so the min-free reading is FALSE at a general instance `eisenstein_floor_sum` reaches |

Every coprimality hypothesis is discharged by `Eq.refl`, so `Nat.gcd` really
does reduce at each pair.

## What is still open, sized

1. **Quadratic reciprocity.** Both halves are proved. The remaining assembly is
   two steps, and the first is `Nat`-side and cheap: instantiate
   `Nat.eisenstein_lemma` at `(m,n)` and at `(n,m)` and combine the two parity
   statements with `Nat.eisenstein_floor_sum`'s `F_p + F_q = n·m` to get
   `N_p + N_q ≡ n·m (mod 2)`. **Every input exists and nobody has run it.**
   The second step is `Int`-side: turn that into Legendre symbols through
   `Int.gaussLemmaSignCount`, which needs a `(−1)^(a+b) = (−1)^a·(−1)^b` step
   over `Int.pow_neg_one_of_even`/`_of_odd`, both of which exist.
2. ~~ADR-1544's residue 5, the `min`-free corollary.~~ **Closed** —
   `Nat.eisenstein_floor_sum_min_free`. The `min` is removable at
   `pp = 2m+1`, `q = 2n+1` and NOT in general, and both halves are tested.

## Two things a next lane inherits

- **`Nat.sumRangeIf` is now the third corner of the subset-fold triangle**
  (`countRange` counts, `prodRangeIf` multiplies, `sumRangeIf` sums). Anything
  that wanted a conditional sum and worked around it should now go through it.
- **A name-search verdict of "all `Int`" is not a `Nat` absence.** The `Nat`
  side of this prelude spells theorems in lower snake case even when the
  constant they mention is camel case, so `--name-like modEq` misses
  `Nat.mod_eq_symm`, `Nat.mod_eq_trans`, `Nat.mod_eq_refl` and the rest.
  Search for the CONSTANT (`--const Nat.modEq`) when the name query comes back
  one-sided.

<!-- plan-section: landed-changes -->

| 2026-09-02 | eisenstein-3 | `Nat.sumRangeIf` + defining equations + bounded congruence + the `setCompl` split (5 declarations, `subset_sum.rs`) |
| 2026-09-02 | eisenstein-3 | residue 2: `Nat.leastResidue_sumRange_reconcile`, hypothesis-free (`gauss_residue_reconcile.rs`) |
| 2026-09-02 | eisenstein-3 | residue 3 and **Eisenstein's lemma**, plus the congruence form (4 declarations, `eisenstein_lemma.rs`) |
| 2026-09-02 | eisenstein-3 | residue 5: `Nat.eisenstein_floor_sum_min_free` and its bound lemma (`eisenstein_floor_min_free.rs`) |
| 2026-09-02 | eisenstein-3 | ADR-1552 + its check script (6 claims, 11 controls, 19/19 self-mutations exit 1) and eleven ledger rows |
