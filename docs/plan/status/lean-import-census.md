# Lane: lean-import-census -- the statement-import blocker was never the `variable` block

<!-- plan-section: lane-status -->

**Lane block (`DONE -- ADR-1662 accepted; census published; screen shipped and
mutation-verified`, lean-import-census, 2026-09-05).**

Owned *Next Ten item 5* of
[`docs/math-department/14-lean-lang.md`](../../math-department/14-lean-lang.md):
run every pinned Mathlib mirror through the statement-only import route, count
the decline reasons, and ship the extraction-time screen.

## Headline

**The count changed the answer.** Two documents said the 257 open mirrors are
blocked because statement-only extraction drops Mathlib's enclosing `variable`
block. Measured over all 756 mirrors through the real route, that class is
**5 rows**, one of them open. The blocker is somewhere else and it is one class:
**361 statements reach a proof-bearing declaration inside their own definition
closure**, so the proof-isolation gate refuses the stream.

| class | stage | rows | open | proved | Nat | Int | held out |
|---|---|---:|---:|---:|---:|---:|---:|
| `admitted` | — | 390 | 132 | 258 | 245 | 145 | 110 |
| `trusted-declaration-in-closure` | import | 361 | 123 | 238 | 301 | 60 | 93 |
| `coercion-variable-block` | elaboration | 3 | 1 | 2 | 1 | 2 | 1 |
| `field-notation-variable-block` | elaboration | 1 | 0 | 1 | 1 | 0 | 0 |
| `elided-proof-glyph` | elaboration | 1 | 1 | 0 | 1 | 0 | 1 |

Zero rows in every other class the census looked for: unsupported construct
(three registered decline codes), universe/level, target cardinality,
goal-not-Prop, stream limit, malformed stream, export timeout, resource. 751 of
751 exports succeeded, so nothing is unaccounted for.

Nine distinct declarations block the 361: `eq_self` 97, `Nat.mod_lt` 90, `Quot`
73, `dif_pos` 34, `Nat.le_of_lt_add_one` 24, `em` 23, `And.left` 12, `Eq.subst`
7, `propext` 1 (287 Theorem / 73 Quotient / 1 Axiom, first blocker per stream).
So C4's first demand-gated feature is an **admission** feature -- extend the
independently reconstructed `trusted_substitution` set over the seven
constructive names (337 rows), with `em` and `propext` held back as a separate
decision because substituting them would enlarge the trusted surface rather than
reconstruct it.

## What was verified before building

- `scripts/provision-lean-import-toolchain.sh --verify` PASSES on the dev box,
  but its Mathlib checkout is a partial cache: 2,006 oleans and **no**
  `Mathlib.olean`, so `import Mathlib` fails there in 3.2 s with
  `object file ... does not exist`. A PASS from that script means the pinned
  checkout and the exporter are present, not that Mathlib is built. s5 has the
  real thing (6.2 GB `.lake/build`), so the Lean half runs there and the importer
  half runs in this checkout.
- `python3 scripts/check-autogenesis-holdout-isolation.py` **before**:
  `held_out=216 files_scanned=1132 references=0 verdict=PASS`.
  **After**: identical, `PASS`. No held-out id is named in the published
  artifact (551 ids named, 0 of them held out); held-out membership comes from
  `check-dispatchable-frontier.py --json`, never a hand list.

## Method

Four phases in `scripts/run-statement-import-blocker-census.py`. Each statement
becomes the value of a transparent `def _ : Prop` after `import Mathlib`; Lean
4.30.0 elaborates it (5.7 s for 756); `lean4export` emits that definition's own
declaration closure (2,256 s for 751 streams); `import_statement_ndjson` admits
or declines (410 s). Nothing is proved and no proof value is read.

Controls the run cannot pass without: a negative-control statement naming a
constant that does not exist (the run aborts if it elaborates -- it was
rejected); a diagnostic regex whose `error(lean.unknownIdentifier):` tag group is
OPTIONAL, because demanding a bare `error:` matches nothing and reports every row
as elaborated; the phase-2 olean build, which recompiles a module made only of
rows phase 1 called clean and is therefore the parser-desync control; and the 499
proved mirrors as the positive-control population -- 238 of them hit the SAME
single blocker, which is what makes "this is the route, not the mathematics" a
measurement.

## The screen

`scripts/lean_surface_screen.py` classifies a statement from its text alone, on
any host, with no Lean. Over the same 756 statements it flags 5 and Lean rejects
5 -- **the sets are equal**, 0 flagged-but-elaborated and 0 rejected-but-unflagged.

The discriminating decision is that a `coerced-projection` requires EVERY
top-level operand of the group to be `↑`-coerced. 54 statements carry a coercion
arrow and 51 elaborate, so a `↑` grep would be wrong about 51 of them and would
still pass a positive-only test suite.

Wired into `scripts/attest-nursery-surface.py`, which runs it before Lean and
gained `--screen-only` (no ssh, no Mathlib; exit status depends on the finding).
A flagged row is FLAGGED, never dropped and never rewritten -- ADR-0615 forbids
editing a preregistered `formal.statement`.

Controls: `scripts/tests/test_lean_surface_screen.py`, 10 tests, every fixture a
real pinned statement with a measured Lean verdict, including two negative
controls a coercion grep would fail. Mutation suite `lean-surface-screen`: five
mutations, each removing one guard, **each killing exactly one test**.

## Not repaired, and not caused here

- `python3 scripts/gen-autogenesis-nursery-refill.py --check` is RED on `main`
  (`nursery-v2-extension.json does not match its own extension_sha256`); 3 of the
  61 tests in `test_gen_autogenesis_nursery_refill` + `test_propose_nursery_refill`
  error for that one reason. `git diff main` over that manifest and both scripts
  is empty, so this lane did not cause it. It IS why the screen went into
  attestation rather than into the draw.
- `scripts.tests.test_create_autogenesis_nursery_dispatch_baseline` fails 2 of
  its tests; the subject, its test file and `artifacts/autogenesis/` are all
  identical to `main` here.
- The three Lean gates `14-lean-lang.md` records as red since the pin moved are
  untouched.

## What did not run

Nothing in the census was skipped. `cargo test --workspace` was not run (not this
lane's gate); `cargo check -p axeyum-lean-import --all-targets` and
`cargo clippy -p axeyum-lean-import --all-targets -- -D warnings` both pass.

<!-- plan-section: landed-changes -->

| 2026-09-05 | Population builder and batch statement-import census example | `87a6b8609` |
| 2026-09-05 | The four-phase census driver, piloted end to end on 8 rows | `68c235ed5` |
| 2026-09-05 | `scripts/lean_surface_screen.py`, its 10-test control suite, mutation suite `lean-surface-screen`, and the `--screen-only` wiring in `attest-nursery-surface.py` | `d95a30125` |
| 2026-09-05 | Merge of `main` (resolved a two-lane append conflict in `scripts/tests/mutation_controls.py`; both suites kept and both re-run) | `84147ec7b` |
