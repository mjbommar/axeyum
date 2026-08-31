# ADR-1060: declare `Nat.avg`/`Nat.pair` and `Max.max`/`Min.min`/`Nat.instMax`/`instMinNat` — draw 12's unblock, both taken

Status: accepted
Date: 2026-08-31
Index-summary: ADR-1045 (draw 12, declined) named `Nat.avg`/`Nat.pair` as
the one verified-clean, floor-clearing held-out family unblock and flagged
a SECOND one, `Init.Data.Nat.MinMax`, as the largest remaining opportunity
but a harder route (Mathlib states every MinMax lemma through the
`Max`/`Min` typeclass, and this kernel has no typeclasses). Both are
declared here, construction-only (ADR-0653): `Nat.avg`/`Nat.pair` exactly
as ADR-1045 specified, and `Max.max`/`Min.min`/`Nat.instMax`/`instMinNat`
as four bare-root/cross-namespace names matching Mathlib's literal
constant tokens (extending the `Squarefree`/`nth.rs` bare-root precedent
to a typeclass-method/instance-argument pair rather than a `Prop`). Both
re-screened against the REAL post-build kernel environment (not a
simulation): R9 0/10 for each, R11 clean for each, R5's two-new-family
minimum satisfied. Holdout isolation unaffected (146, PASS, before and
after -- `artifacts/autogenesis/` was never touched by this lane).

Related: ADR-1045 (draw 12, declined; the finding and the exact unblock
this ADR executes), ADR-0653 (construction-only discipline), ADR-0910
(`Nat.nthRoot`/`Squarefree`, the search-then-simulate-then-build
methodology and the bare-root-name precedent this ADR follows and
extends), ADR-0900 (draw 10 declined, the same territory-exhaustion
finding ADR-1045 reproduces)

## Context

ADR-1045 measured the dispatch queue at (nominally) 10 against a floor of
10 and declined draw 12: every below-floor un-owned Nat/Int module either
topically or vocabulary-collides with an already-published development/
train family, reproducing ADR-0900's finding on a tree with twelve draws'
worth of families claimed. It found exactly ONE genuinely clean,
floor-clearing construction target by simulation -- `Nat.avg`/`Nat.pair`,
opening `Batteries.Data.Nat.Bisect` + `Mathlib.Data.Nat.Pairing` as one
15-candidate held-out family (R9 0/10, R11 fully clean) -- but R5 requires
TWO new held-out families per draw, and a comparably clean second was not
found within that session's budget. `Init.Data.Nat.MinMax` (30 candidates)
was named as the largest remaining opportunity, but flagged as needing
typeclass-name bridging (`Max.max`, `Min.min`, `Nat.instMax`, `instMinNat`
are the missing constants) -- a chicken-and-egg gap in the normal bridge
mechanism (which derives from constants of already-SETTLED mirrors; none
uses that syntax yet) -- or declaring literal kernel constants under those
unconventional names directly, named as the harder route and not pursued.

This lane's task: declare both, construction-only, and re-verify by
re-running the real screen rather than trusting ADR-1045's numbers, since
a readiness figure measured before the unblock exists is a figure about a
different tree (the standing lesson from the `Nat.dist` incident this
crate's CLAUDE.md records).

## Decision

Declare both:

1. **`Nat.avg (a b : Nat) : Nat := div (add a b) 2`** and **`Nat.pair (a b
   : Nat) : Nat := if a < b then add (mul b b) a else add (add (mul a a)
   a) b`** -- exactly ADR-1045's Step 4 specification, over this prelude's
   existing `Nat.add`/`Nat.mul`/`Nat.div`/`Nat.ble`/`Nat.succ`. Neither
   uses a recursor. `crates/axeyum-lean-kernel/src/nat_prelude/avg_pair.rs`.

2. **`Max.max (a b : Nat) : Nat := if a <= b then b else a`**, **`Min.min
   (a b : Nat) : Nat := if a <= b then a else b`** (bare-root namespaces
   `Max`/`Min`, matching Mathlib's typeclass method names literally), and
   **`Nat.instMax`/`instMinNat`** as same-value aliases of `Max.max`/
   `Min.min` under the exact names Mathlib's elaborated statements apply
   as the instance argument. This kernel has no typeclasses (the complete
   inductive list, per this crate's CLAUDE.md, is fixed and does not
   include a `Max`/`Min` class), so `Nat.instMax`/`instMinNat` are NOT
   real typeclass instances -- they are ordinary `Nat -> Nat -> Nat`
   functions, chosen because the autogenesis screen's admissibility test
   is purely SYNTACTIC (a literal-constant-token membership check against
   `kernel.environment()`), so what unblocks it is a declaration whose
   RENDERED NAME matches the token, independent of whether its type
   mirrors Mathlib's typeclass-polymorphic signature. This is not a new
   technique: `squarefree.rs` already declares the bare-root `Squarefree`
   (not `Nat.squarefree`) for exactly this reason, and `nth.rs` already
   declares `Nat.nth` at a genuinely different type than Mathlib's own.
   This ADR extends the same move from one bare-root `Prop`-vs-`Bool` case
   to four names spanning a typeclass method/instance pair.
   `crates/axeyum-lean-kernel/src/nat_prelude/minmax.rs`.

Both are construction-only (ADR-0653): each file declares its
definition(s) and nothing else. No theorem, equation lemma, or mirror
statement is declared. Evaluation tests live in sibling files
(`avg_pair_tests.rs`, `minmax_tests.rs`), each new file rather than an
addition to the dense `nat_prelude_tests.rs`, per this repository's
standing merge-hazard note.

## Verification

### Step 1 -- re-run ADR-1045's `Nat.avg`/`Nat.pair` simulation in the CURRENT tree, before building anything

Before writing any Rust, re-ran the real `select()`/`admissible()` against
the committed inventory/vocabulary/registry with `cand-avg-pair` added to
a copy of `FAMILY_MODULES` (never written to disk) -- reproducing exactly
what ADR-1045 reports: 10 candidates selected (the pool is `>= 15`;
`select()` caps at `PER_FAMILY = 10`, same as every other family), R9
0/10, R11 clean. Confirmed before building.

### Step 2 -- build, with the discipline check as a live gate

`avg_pair.rs` built first, committed within the first ten tool calls (the
process rule -- see git log). The kernel cannot tell a `Definition` is
wrong (a function of the right type computing the wrong value is admitted
just as happily as a correct one), so both files carry evaluation tests at
concrete, DISCRIMINATING arguments:

- `Nat.avg`: `avg 3 4 = 3` (floor, not the ceiling `4`; `Nat.div` and
  `Nat.sub` both truncate silently), plus `avg 0 1 = 0` and `avg 2 7 = 4`
  at the same boundary.
- `Nat.pair`: `pair 1 2 = 5`, chosen to discriminate THREE plausible wrong
  formulas at once -- `1 + 2 = 3` (the symmetric-sum formula), a
  transposed `<` branch (`1*1 + 1 + 2 = 4`), and the textbook
  two-multiplication Cantor pairing `(3)*(4)/2 + 1 = 7` -- and `7` is not
  arbitrary: it is exactly `pair 2 1`, so the same check confirms `pair`
  is not symmetric (which any injective two-argument pairing function
  must not be).

`every_nat_declaration_is_checked_and_axiom_free` (which derives its
coverage from `kernel.environment()`, not a hand list -- see this crate's
CLAUDE.md on why that distinction matters) caught both names as
uncovered on the first build; added to `definition_names`. One Rust field
name collision was also caught by the compiler, not by inspection:
`Nat.Pair` (the product type `binary_rec.rs` added) already owns the Rust
identifier `pair` -- renamed the new field to `pair_fn` (the KERNEL names
`Nat.Pair`/`Nat.pair` differ by case and do not actually collide, only
the Rust identifiers did).

### Step 3 -- MinMax: judged tractable by simulation, then built

Simulated the same way before writing any Rust: added `{"Max.max",
"Min.min", "Nat.instMax", "instMinNat"}` to the environment set and
re-ran `select()`/`admissible()` with `cand-minmax` -> `("Init.Data.Nat.
MinMax",)`. Result: of 32 total module rows, 30 become admissible with
all four names present (matching ADR-1045's count exactly), `select()`
takes the first 10 (`PER_FAMILY` cap), R9 0/10 against the real
environment, R11 clean with **zero** environment-sweep hits (cleaner than
`avg_pair`'s own screen, which has one advisory hit on the stem `avg`
against its own declaration -- expected and non-blocking). Judged
tractable and built.

### Step 4 -- FULL nat_prelude:: sweep and clippy, both files

```
cargo test -p axeyum-lean-kernel --lib nat_prelude::
  268 passed; 0 failed; 0 ignored; 940 filtered out
cargo clippy -p axeyum-lean-kernel --all-targets --all-features -- -D warnings
  0 errors in avg_pair.rs / avg_pair_tests.rs / minmax.rs / minmax_tests.rs
  (7 pre-existing errors remain elsewhere in the crate -- exists_gcd_one.rs,
  nat_prelude.rs:1492, gauss_lemma.rs -- untouched by this lane, out of scope)
```

Confirmed with `--list` on each new test module that every `#[test]` is
actually registered (not silently swallowed by a misplaced anchor, per
this crate's own standing gotcha): `avg_pair_tests` 2/2, `minmax_tests`
3/3.

### Step 5 -- re-screen AFTER declaring, against the REAL (not simulated) environment

Rebuilt `shape_search --release` fresh and dumped
`kernel.environment()` directly (2572 declarations, up from the tree's
prior 2568/2552; confirmed all six new names -- `Nat.avg`, `Nat.pair`,
`Max.max`, `Min.min`, `Nat.instMax`, `instMinNat` -- present by name in
the dump, not inferred). Re-ran the real `select()`/`screen_family` with
BOTH candidate families present simultaneously, exactly as a draw would:

```
natural-avg-pair: 10 candidates, R9 0/10, R11 clean, env_hits=[('avg','Nat.avg',1)]
natural-minmax:   10 candidates, R9 0/10, R11 clean, env_hits=[]
R5 check: 2 new families with candidates (>= 2 required)
```

Neither `artifacts/autogenesis/nursery-v1.json`,
`mathlib-nursery-split-policy-v1.json`, `kernel-environment-snapshot-v1.json`,
nor any other file under `artifacts/autogenesis/` was touched by this
lane (verified: `git diff --stat` over the whole range against those
paths is empty). `check-autogenesis-holdout-isolation.py` reports
`held_out=146|files_scanned=1110|settled=0|references=0|verdict=PASS`,
identical before and after this lane's work (necessarily, since the
inputs it reads were never touched).

`gen-autogenesis-nursery-refill.py --check` (against the COMMITTED
snapshot, unaffected by the live kernel build) still reports
`entries=380|env=2552|...`, byte-identical to ADR-1045's own report --
confirming this lane changed nothing the committed manifest generator
reads. `check-dispatchable-frontier.py` reads **4** dispatchable against
the floor of 10 at the time of this ADR (not ADR-1045's 10 -- theorem
lanes have since consumed six of those ten; this number is unaffected by
and independent of this ADR's work, which is about SUPPLY for a future
draw, not the current dispatch queue).

## Consequences

- **The next draw (draw 13) can authenticate itself against a REAL, not
  simulated, environment.** Both families are confirmed clean by
  construction, not merely by plan. The lane authoring draw 13 still owns
  `gen-autogenesis-nursery-refill.py`'s `FAMILY_MODULES`/`FAMILY_ROUTES`
  edits, the manifest regeneration, and the fact-ledger reconciliation --
  none of that is touched here, deliberately (this lane enables a draw;
  it does not author one).
- **The bare-root/cross-namespace technique generalizes past `Squarefree`.**
  `minmax.rs` is the first case declaring FOUR names across three
  different namespace roots purely to satisfy the syntactic admissibility
  screen, including two (`Nat.instMax`, `instMinNat`) that stand for a
  typeclass-instance argument with no corresponding structure in this
  kernel. Whether this is the right general answer to "Mathlib states it
  through a typeclass we don't model" is worth a wider look before it
  becomes routine -- `Init.Data.Nat.MinMax` is not the only typeclass-
  elaborated module in the un-owned supply, and each future case should
  re-derive (not assume) that a same-value alias under the instance name
  is honest for that specific typeclass, the same way this ADR verified
  it for `Max`/`Min` rather than asserting it as a pattern.
- **The held-out population is still shrinking under its own success**
  (ADR-1045's own observation, unaffected by this ADR): the two families
  opened here are a one-time addition of 20 new held-out rows against a
  144-row population that keeps draining as ordinary development spends
  families. This buys draw 13, not runway beyond it.
