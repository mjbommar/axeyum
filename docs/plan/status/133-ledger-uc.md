# Lane: ledger-uc — register the fourth batch (uniform convergence, alternating series, polynomials, crossing)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, ledger-uc, 2026-08-27).** Registered 26 new
facts in `artifacts/facts/`. `python3 scripts/validate-facts.py` is green:
**776 facts checked, 0 errors** (750 pre-existing + 26 new).

**Ch.24 (uniform convergence, new chapter):** `F:creal-uniformconvergeson`
(the CARRIER — a one-constructor `Type` in `Sort (1)`, not `Prop`: its
`--require-kind` is `inductive`, not `definition`), `F:creal-uniform-converges-id`,
`F:creal-uniform-converges-geom-half` (the two concrete instances),
`F:creal-uniform-limit-uniformly-continuous` (the headline theorem). Every
fact's `statement` records that `UniformConvergesOn` must be `Type`-valued
because the headline theorem *constructs* a `UniformlyContinuousOn` witness
from the rate as literal `Nat` data, and `Exists.rec` is `Prop`-only. No
pointwise-not-uniform counterexample is claimed or checked; the guarantee is
recorded as a type-level argument (`rate : Nat`, not `CReal -> Nat`).

**Ch.22-23 (alternating series):** `F:creal-negonepowdouble`,
`F:creal-alternatingeleo`, `F:creal-alternatingbracket`. **NOT registered**
(do not exist in the merged tree): `CReal.alternatingBracketUpper`,
`CReal.alternatingLowerBound`, `CReal.alternatingUpperBound` — see Findings
below. *(Since landed — all three now exist in the kernel; historical record.)*
<!-- was-absent: CReal.alternatingBracketUpper, CReal.alternatingLowerBound, CReal.alternatingUpperBound -- this status note's snapshot of the merged tree; all three since landed -->

**Ch.20 (`CReal` polynomials):** `F:creal-polyeval` (+`-zero`/`-succ`),
`F:creal-polyadd`, `F:creal-polyeval-polyadd`, `F:creal-polyscale`,
`F:creal-polyeval-polyscale`, `F:creal-polydegreelt` (recorded as a
PROPOSITION, not a computed degree — `CReal.Equiv`/`CReal.le` are
undecidable) (+`-polyadd`/`-polyscale`).

**Ch.25-27 (`Complex` polynomials, factor theorem):**
`F:complex-polydegreelt-polymul`, `F:complex-hornerfromtop`
(+`-zero`/`-succzero`/`-succsucc`), `F:complex-factorquotient` (a COMPUTED
quotient via a nested `Nat.rec`, never `Exists`-elimination — its own notes
record the forced-`zero`-prepend boundary bug the natural reindexing hits),
`F:complex-factorquotient-degreelt`.

**Ch.14 (integral machinery):** `F:creal-meshscaledleofge`,
`F:creal-crossingclose` — registered as what the theorem STATES, with its
`statement` and `notes` explicit that `hap`/`hpb` (`samplePt`'s domain
membership) are UNDISCHARGED hypotheses of the theorem itself, not a proof
gap; the theorem the kernel admitted is fully and soundly proved but not
usable as a closed result until those two hypotheses are separately
discharged.

## Checker forms used

- Definitions/inductives:
  `cargo run -q --release -p axeyum-lean-kernel --example kernel_declaration_projection
  -- --require-declaration <Name> --require-kind {definition|inductive} 2>/dev/null
  | grep -cE '^found[[:space:]]<prelude>[[:space:]]<kind>[[:space:]]<Name>[[:space:]]'`
- Theorems:
  `cargo run -q --release -p axeyum-lean-kernel --example theorem_dependency_inventory
  -- <Name> 2>/dev/null | grep -cE '^<Name>[[:space:]]'`
- Axiom footprint (all 26 facts, prelude `creal` or `complex`):
  `cargo run -q --release -p axeyum-lean-kernel --example nat_axiom_inventory
  -- --include-constructed --require-axiom-free {creal|complex}`
  Re-measured on this tree: `creal: axiom=0 opaque=0 quotient=0 total_trusted=0`,
  `complex: axiom=0 opaque=0 quotient=0 total_trusted=0`, `nat: axiom=0 opaque=0
  quotient=0 total_trusted=0`.

## Mutation testing (isolated snapshot, never the shared checkout)

Used `scripts/lane-snapshot.sh HEAD` (`/data0/axeyum/scratch/snap-ledger-uc-*`,
reclaimed after use) with a private `CARGO_TARGET_DIR`
(`/data0/axeyum/target/ledger-uc`, removed after use). Three declarations
mutated (display-name string only, one line each), rebuilt in `--release`,
re-run against the exact `checker_command`s above:

- `Complex.hornerFromTop` -> `Complex.hornerFromTop_MUTATED`
  (`complex.rs:1713`): `kernel_declaration_projection --require-declaration
  Complex.hornerFromTop` count **0**, exit **1**. Control in the SAME rebuild,
  `Complex.polyMul`: count **1**, exit **0**.
- `CReal.negOnePowDouble` -> `CReal.negOnePowDouble_MUTATED`
  (`creal.rs:4715`): `theorem_dependency_inventory CReal.negOnePowDouble`
  count **0**, exit **1**. Control `CReal.alternatingELeO` (which depends on
  `negOnePowDouble` via the `NameId`, not the string, so it still builds and
  is found unaffected): count **1**, exit **0**.
- `Nat.succ_add` -> `Nat.succ_add_MUTATED` (`nat_prelude.rs:1909`, a
  pre-existing dependency fact `F:nat-succ-add` this batch cites, not a new
  registration — this batch has no NEW `Nat.*` fact since `Nat.even_or_odd`
  does not exist): `theorem_dependency_inventory Nat.succ_add` count **0**,
  exit **1**. Control `Nat.add_comm`: count **1**, exit **0**.

All three mutated builds compiled and type-checked cleanly (renaming a
declaration's *display* string does not change any `NameId` reference used
internally, so dependent proofs continue to build) — the checkers'
discrimination is entirely on the printed name, as intended.

## Findings — NOT registered, with reasons

Checked against local `main` @ `aee64cc17` merged into this worktree
(`git merge --no-edit main`, fast-forward):

- **`CReal.uniform_converges_add`** — does not exist. No `CRealPrelude`
  field, no `declare_uniform_converges_add`. Exists as a commit
  (`aa347788f`) on unmerged branch `worktree-agent-a2562e3631adc1bf2` only.
- **`Nat.even_or_odd`** — does not exist. Confirmed three ways: no source
  match, `theorem_dependency_inventory Nat.even_or_odd` exits 1, and
  `nat_prelude/fibonacci.rs`'s own doc comment says a parity case-split
  "is NOT attempted in this [declaration]... substantial new machinery".
  Exists as a commit (`88c516432`, "computed even/odd split") on unmerged
  branches `worktree-agent-a71ce0189ae2e5688` / `worktree-agent-aa7767a7d63d9446e`
  only.
- **`CReal.alternatingBracketUpper`**, **`CReal.alternatingLowerBound`**,
  **`CReal.alternatingUpperBound`** — none exist. `creal/alternating.rs` has
  exactly three `declare_*` functions (`neg_one_pow_double`,
  `alternating_e_le_o`, `alternating_bracket`); no dual/upper-bound variant
  anywhere in `creal/`.
*(All five names above are since landed — `CReal.uniform_converges_add`,
`Nat.even_or_odd`, and the three `CReal.alternating*` declarations all now
exist in the kernel. This section is a historical record of the merged-tree
snapshot checked at the time, not a live claim.)*
<!-- was-absent: CReal.uniform_converges_add, Nat.even_or_odd, CReal.alternatingBracketUpper, CReal.alternatingLowerBound, CReal.alternatingUpperBound -- this findings section's snapshot; all five since landed -->

Per this lane's scope (`crates/` read-only; "if a declaration does not
exist, that is a finding to report, not a thing to build"), none of the
above were built, and none of the unmerged sibling branches were merged in
to source them — `main`/`origin/main` do not contain these commits as of
this run.
