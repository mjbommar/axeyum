# Lane: quadratic-reciprocity-2 — the two steps ADR-1552 named, both run

<!-- plan-section: lane-status -->

**Status: landed (2026-09-02). The law of quadratic reciprocity is a kernel
theorem, axiom-free.** ADR-1552's two remaining steps were both correct and
both cheap. Five declarations, every one admitted on the FIRST kernel attempt,
every one with an empty `Kernel::axiom_footprint`. Decision, the mutation
table, and three recorded survivors:
[ADR-1557](../../research/09-decisions/adr-1557-quadratic-reciprocity-is-proved-and-the-legendre-symbol-is-defined-by-gausss-count.md).

```text
Int.quadraticReciprocity : ∀ m n, gcd (2n+1) (2m+1) = 1 →
  legendreSym m (2n+1) · legendreSym n (2m+1) = (−1)^(n·m)
```

## Step 0 — prerequisite verification (this lane, in-tree, not inherited)

`examples/shape_search`, rebuilt on this branch (`declarations=2133` before this
lane's own declarations, so not a stale binary reporting a false ABSENT).

| named input | verdict |
| --- | --- |
| `Nat.eisenstein_lemma`, `Nat.eisenstein_lemma_modEq` | FOUND (2 matches on one query) |
| `Nat.eisenstein_floor_sum_min_free` | FOUND |
| `Int.gaussLemmaSignCount` | FOUND |
| `Int.pow_neg_one_of_even` / `_of_odd` | FOUND |
| `Int.is_quadratic_residue` + `_one` / `_mul` / `_of_modEq` | FOUND, 4 |
| `Int.firstSupplementaryLawResidue` (the shape template) | FOUND |
| `Nat.gaussNegCount` | FOUND, 9 |
| `Int.pow_add`, `Int.mul_assoc`/`mul_one`/`one_mul`, `Nat.gcd_comm`, `Nat.even_or_odd` | FOUND |
| **any Legendre symbol** (`--name-like legendre`) | **ABSENT**, against `positive control: any-kind=2133` |
| `--name-like quadraticReciprocity` / `reciprocity` / `legendreSym` | **ABSENT**, same control |

ADR-1552's "every input exists and nobody has run it" was correct for step 1.
What it did not say is that there is **no Legendre symbol in this kernel at
all**, which is what made step 2 a design decision rather than an assembly.

## Landed

| change | what |
| --- | --- |
| `crates/axeyum-lean-kernel/src/nat_prelude/quadratic_reciprocity_count.rs` | two declarations (step 1), both admitted FIRST attempt, both axiom-free |
| `crates/axeyum-lean-kernel/src/nat_prelude/quadratic_reciprocity_count_tests.rs` | 6 tests: the arithmetic re-derived in Rust first, concrete instantiation at five prime pairs, the non-coprime refutation with its recorded survivor, footprint, type pins |
| `crates/axeyum-lean-kernel/src/int_prelude/quadratic_reciprocity.rs` | three declarations (step 2), all admitted FIRST attempt, all axiom-free |
| `crates/axeyum-lean-kernel/src/int_prelude/quadratic_reciprocity_tests.rs` | 7 tests, in their own file rather than appended to the 6,000-line `int_prelude_tests.rs` |
| `crates/axeyum-lean-kernel/src/nat_prelude/eisenstein_lemma.rs` | `two_mul` and `regroup_four` exported `pub(super)` rather than copied a third time |
| `crates/axeyum-lean-kernel/src/nat_prelude.rs`, `src/int_prelude.rs` | five name fields, registrations, two build-order calls, two test-module registrations |
| `crates/axeyum-lean-kernel/src/{nat,int}_prelude/*_prelude_tests.rs` | the five names added to the environment-derived coverage lists; `Int.legendreSym` filed under `definition_names` (31) not `derived_laws` (265), because that list asserts `Declaration::Theorem` |
| `crates/axeyum-py/src/kernel/prelude_fields.rs` | regenerated (`scripts/gen-py-prelude-fields.py`) |
| `docs/research/09-decisions/adr-1557-…md` + `adr-1557-quadratic-reciprocity-checks.py` | 6 claims, 8 controls, 3 recorded survivors; 18 of 18 self-mutations exit 1 |
| `artifacts/facts/F-{nat-gausscount-sum-even,nat-gausscount-sum-modeq,int-legendre-sym-modeq-pow,int-quadratic-reciprocity}.json` | four ledger rows, statements verbatim from the kernel's own rendering |

Declarations:

- `Nat.gaussCount_sum_even : ∀ m n, gcd (2n+1) (2m+1) = 1 → Even ((N_p + N_q) + n·m)`
- `Nat.gaussCount_sum_modEq : ∀ m n, gcd (2n+1) (2m+1) = 1 → modEq 2 (N_p + N_q) (n·m)`
- `Int.legendreSym : Nat → Nat → Int := fun m a => (−1)^(gaussNegCount (2m+1) a m)`
- `Int.legendreSym_modEq_pow : ∀ m a, PrimeCond (2m+1) → gcd a (2m+1) = 1 → ModEq (2m+1) (a^m) (legendreSym m a)`
- `Int.quadraticReciprocity : ∀ m n, gcd (2n+1) (2m+1) = 1 → legendreSym m (2n+1) · legendreSym n (2m+1) = (−1)^(n·m)`

with `N_p := gaussNegCount (2m+1) (2n+1) m` and `N_q := gaussNegCount (2n+1) (2m+1) n`.

## Four decisions, all argued in ADR-1557

1. **The Legendre symbol is DEFINED by Gauss's counting exponent**, not by the
   residue indicator, because `qr_criterion.rs` records that the converse of
   Euler's criterion has no statable form here. The name is justified by
   `Int.legendreSym_modEq_pow`. **`legendreSym m a = 1 ↔ is_quadratic_residue`
   is NOT proved in either direction**, and both the module doc and the ledger
   row say so.
2. **The proof multiplies by the self-inverse `(−1)^(n·m)` rather than
   splitting on parity.** The case-split route needs `Even (a+b) → Even a →
   Even b` and its odd twin, neither of which exists here. Cancelling needs only
   `Int.pow_add`, `Int.pow_neg_one_of_even` and three ring lemmas, all landed.
3. **Only coprimality is assumed, never primality** — strictly stronger than the
   textbook law, the same generalization ADR-1544 recorded for
   `Nat.eisenstein_floor_sum`. Primality appears once, in the symbol's
   specification, because Gauss's lemma needs it to cancel `m!`.
4. **`two_mul`/`regroup_four` exported rather than copied.** The per-file-copy
   convention is right for a helper two files apart; a third copy of the same
   two moves is not.

## Checks run

- `cargo test --release -p axeyum-lean-kernel --lib -- nat_prelude:: --test-threads=4` — **401 passed, 0 failed** (was 395)
- `cargo test --release -p axeyum-lean-kernel --lib -- int_prelude:: --test-threads=4` — **81 passed, 0 failed** (was 74)
- `cargo clippy --release -p axeyum-lean-kernel --all-targets -- -D warnings` — clean
- `cargo clippy --release -p axeyum-py --all-targets -- -D warnings` — clean
- `python3 docs/research/09-decisions/adr-1557-quadratic-reciprocity-checks.py` — PASS; **18 of 18 self-mutations exit 1**
- `python3 scripts/validate-facts.py` — exit 0 (after `check-fact-depends-derived.py --fix` added 4 derived edges)
- `python3 scripts/check-settled-fact-statements.py --write` then re-run — PASS, 2393 pinned, drifted 0
- `python3 scripts/gen-adr-index.py --check` — exit 0
- `nat_axiom_inventory --require-axiom-free nat` and `-- integer` — both exit 0, with `-- axreal` exiting 1 at 30 as the control that the flag CAN fail
- each fact's `checker_command` run WITH a negative control: the real name prints `1` at exit 0, a one-character typo prints `0` at exit **1**
- `scripts/recount-pinned-inventory.py --check` on `int_prelude_tests.rs` — 4 arrays, all declared == counted
- **five kernel declarations, all five admitted on the FIRST attempt**

## Instantiation table

`N_p := gaussNegCount p q m`, `N_q := gaussNegCount q p n`, `m = (p−1)/2`,
`n = (q−1)/2`. Computed in Python before any kernel term was built and
re-derived independently in Rust inside both test files.

| `p` | `q` | `m` | `n` | `N_p` | `N_q` | `n·m` | law | checked |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 3 | 5 | 1 | 2 | 1 | 1 | 2 | `+1` | conclusion inferred and matched; both sides reduce; `−1` rejected |
| 5 | 7 | 2 | 3 | 1 | 1 | 6 | `+1` | same |
| 3 | 7 | 1 | 3 | 0 | 1 | 3 | `−1` | same — the only `−1` row in `PAIRS` |
| 5 | 13 | 2 | 6 | 1 | 3 | 12 | `+1` | same |
| 13 | 17 | 6 | 8 | 4 | 4 | 48 | `+1` | same; largest magnitude formed is `17·6 = 102` |
| 7 | 11 | 3 | 5 | 2 | 3 | 15 | `−1` | a SECOND `−1` instance, so the sign is not carried by one row |
| 3 | 3 | 1 | 1 | 0 | 0 | 1 | — | NON-COPRIME: `+1` against `−1`, so the hypothesis is load-bearing |
| 5 | 5 | 2 | 2 | 0 | 0 | 4 | — | recorded SURVIVOR: equally non-coprime and the two sides AGREE |

`Int.legendreSym` is a `Definition`, so it is also reduced on its own at
`(m, a) = (3,3)`, `(3,2)`, `(6,17)`, `(1,3)` — two multipliers at `p = 7` with
counts of OPPOSITE parity, so a wrong body cannot agree by luck — and each
instance rejects the opposite sign.

Every coprimality hypothesis is discharged by `Eq.refl`, so `Nat.gcd` really
does reduce at each pair.

## The correction this lane owes its brief

**The brief's expected signs were wrong at two of its five pairs.** It asked
for `(3,5) → −1` and `(5,7) → −1`; both are `+1`. The Legendre product is `−1`
exactly when BOTH primes are `3 mod 4`, and `5 ≡ 1 (mod 4)`. Only `(3,7)` in
that list is the `−1` case, which is why `(7,11)` was added. Caught by
recomputing the table in Python before writing any Rust — the "arithmetic
first" step, doing exactly what it exists for.

## Mutation table

Eight kernel mutants, each rebuilt and run against the 13 tests of the two
reciprocity modules, with the file restored afterwards: **six REJECTED by the
trusted gate, two ADMITTED and caught only by the type pins.** Two rows are
worth more than the count:

- **M5/M6 mutate the `Definition`'s body and are REJECTED.** `CLAUDE.md`'s rule
  that the trusted gate cannot tell you a definition is wrong does not apply
  unconditionally: `Int.quadraticReciprocity`'s proof is built on the unfolded
  body, so the definition is **pinned from above** and a wrong body makes the
  LAW fail to type-check (`DeclarationValueMismatch`). This lane read the actual
  message rather than trusting the runner's classifier. The evaluation tests are
  therefore NOT what catches M5/M6 — they are the guard that would matter if
  the law above the definition were removed.
- **M7/M8 are ADR-1260's admitted-and-survived binder swap, and here they do
  not survive.** Both are caught by the character-for-character type pins and by
  nothing else in the suite.

## What is still open, sized

1. **The bridge `legendreSym m a = 1 ↔ is_quadratic_residue`.** The `⟸`
   direction is reachable from `Int.euler_criterion_residue_imp_one` plus
   `1 ≢ −1` at `p > 2`, and is NOT built. The `⟹` direction is the missing
   converse of Euler's criterion and is not reachable without a primitive root
   or a root-counting argument. State the reachable half as an implication.
2. **The Jacobi symbol.** No `legendre`-shaped declaration existed before this
   lane; Jacobi was not separately measured, so check before building. Its
   reciprocity law wants a product over a factorization, and
   `nat_prelude/factorization.rs` supplies existence but not canonicity — the
   ADR-1552-era "evaluate versus induct" distinction applies.
3. **Row 4 of the graded family (ADR-0603), the labeled Mathlib import**
   (`Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity`), **is a
   separate lane** and is not attempted here. All four of this lane's ledger
   rows are row 1, the general constructive form; nothing here is an import.
4. **Row 2 is stated numerically and inside the kernel, not as a theorem.** The
   non-coprime refutation is asserted as a `def_eq` control in both test files
   and swept in the check script; no claim is made that a kernel-level
   refutation is impossible.

## Two things a next lane inherits

- **A definition under a theorem is pinned by that theorem.** A lane citing
  "the trusted gate cannot tell you a `Definition` is wrong" should first check
  whether anything above the definition consumes its unfolded body. The rule
  survives — it is about a definition with nothing proved over it.
- **`Nat.gcd_comm` has no fact row**, so `depends_on` on this lane's rows is an
  intersection that omits it. That is `check-fact-depends-derived.py`'s
  documented behaviour, not a curation gap.

<!-- plan-section: landed-changes -->

| 2026-09-02 | quadratic-reciprocity-2 | step 1: `Nat.gaussCount_sum_even` and `Nat.gaussCount_sum_modEq` (`quadratic_reciprocity_count.rs`), both axiom-free |
| 2026-09-02 | quadratic-reciprocity-2 | step 2: **`Int.quadraticReciprocity`**, `Int.legendreSym` and `Int.legendreSym_modEq_pow` (`quadratic_reciprocity.rs`), all axiom-free |
| 2026-09-02 | quadratic-reciprocity-2 | ADR-1557 + its check script (6 claims, 8 controls, 3 recorded survivors, 18/18 self-mutations exit 1) and four ledger rows |
