# ADR-1662: The statement-import blocker is a proof inside the definition closure, not the `variable` block

Status: accepted
Date: 2026-09-05
Index-summary: Statement-import blocker census over all 756 pinned Mathlib mirrors -- 390 cross, 361 are stopped by a proof-bearing declaration inside the STATEMENT's own definition closure and 5 by elaboration; C4's first demand-gated feature is therefore an admission feature, not an elaboration one, and a text-only screen reproduces Lean's elaboration verdict 5 for 5

## Context

[`docs/math-department/14-lean-lang.md`](../../math-department/14-lean-lang.md)
puts the same obstruction in two places. Reviewer 01 (number theory) says the
257 open Mathlib mirrors are blocked because "statement extraction loses
Mathlib's enclosing `variable` block, so a coercion-carrying statement re-parses
as nothing (**no screen exists**); typeclass-headed statements have no
record-spine target".
[`docs/plan/status/315-attestation-ceiling.md`](../../plan/status/315-attestation-ceiling.md)
item 3 says the same thing in the same words. Neither gives a count, and nothing
had run the route over the population to find one.

That matters more than a missing number. C4 of the
[library-artifact compatibility roadmap](../../plan/library-artifact-compatibility-roadmap-2026-08-30.md)
admits a source or elaboration feature "only when it is the smallest shared
blocker for a preregistered high-value population". Without a census, C4 has no
input and the queue picks a feature by taste. Two guesses were already on the
table -- typeclass-headed statements, and coercions -- and they imply very
different work.

The route itself is not in question:
[ADR-0604](adr-0604-lean-is-the-surface-syntax.md) §2 makes
`import_statement_ndjson` the front door for posing a Lean-authored statement as
a goal, and `examples/statement_goal_record.rs` is the worked example. What was
missing is the measurement across it.

## Decision

**The census is run, published, and re-runnable; and the largest shared blocker
is not on the elaboration side at all.**

Over all 756 `F:ml430-*` mirrors, statement-only import admits 390 and declines
366. Of the 366, **361 are one class**: the statement's own definition closure
reaches a proof-bearing declaration, so the proof-isolation gate refuses the
stream. Only **5** are elaboration failures, and every one of those five is the
dropped `variable` block or a printer glyph.

So C4's first demand-gated feature, chosen by count, is an **admission** feature:
extend `import_statement_ndjson`'s independently reconstructed
`trusted_substitution` set to cover the nine declarations that block those 361
rows. It is not an elaboration feature, and it is not the coercion work the two
documents pointed at -- that class is three rows.

**Second, both elaboration classes now have an extraction-time screen that needs
no Lean.** `scripts/lean_surface_screen.py` classifies a statement from its text
alone; it is wired into `scripts/attest-nursery-surface.py`, which runs it before
Lean and gains a `--screen-only` mode that runs on any host. A screened row is
FLAGGED with its class, never dropped and never rewritten
([ADR-0615](adr-0615-the-evaluation-envelope-is-per-cohort-and-a-draw-is-incremental.md)
forbids editing a preregistered `formal.statement`).

## Evidence

`artifacts/measurements/statement-import-blocker-census-2026-09-05.json`, run at
`84147ec7b` against Mathlib `c5ea00351c28` and Lean 4.30.0 on s5.

### The class table

| class | stage | rows | open | proved | Nat | Int | held out |
|---|---|---:|---:|---:|---:|---:|---:|
| `admitted` | — | 390 | 132 | 258 | 245 | 145 | 110 |
| `trusted-declaration-in-closure` | import | 361 | 123 | 238 | 301 | 60 | 93 |
| `coercion-variable-block` | elaboration | 3 | 1 | 2 | 1 | 2 | 1 |
| `field-notation-variable-block` | elaboration | 1 | 0 | 1 | 1 | 0 | 0 |
| `elided-proof-glyph` | elaboration | 1 | 1 | 0 | 1 | 0 | 1 |

Restricted to the 257 OPEN mirrors -- the population reviewer 01 was talking
about -- it is 132 admitted, 123 `trusted-declaration-in-closure`, 1 coercion,
1 glyph.

Classes the census looked for and found **zero** of: unsupported construct (the
importer's three registered decline codes), universe/level, target cardinality,
goal-not-Prop, stream limit, malformed stream, export timeout, resource. Every
export succeeded (751 of 751, rc 0, no empty stream), so no row is unaccounted
for.

### What actually blocks the 361

`import_statement_ndjson` reports the FIRST trusted declaration it meets, so this
is a distribution over first blockers, not over all of them. Nine distinct
declarations, in three kinds:

| declaration | kind | rows |
|---|---|---:|
| `eq_self` | Theorem | 97 |
| `Nat.mod_lt` | Theorem | 90 |
| `Quot` | Quotient | 73 |
| `dif_pos` | Theorem | 34 |
| `Nat.le_of_lt_add_one` | Theorem | 24 |
| `em` | Theorem | 23 |
| `And.left` | Theorem | 12 |
| `Eq.subst` | Theorem | 7 |
| `propext` | Axiom | 1 |

287 Theorem, 73 Quotient, 1 Axiom. These are not proofs of the mirrored
proposition -- the target is a `def _ : Prop` and its proof was never exported.
They are proofs sitting inside the VALUE of a definition the statement mentions:
Mathlib's `Nat` division and modulo are well-founded recursions whose
definitions carry `Nat.mod_lt`, `dif_pos` guards a `Decidable` branch, `Quot`
appears through quotient-carried structures.

That distinction is the whole point and it is why the fix is bounded: nine
names, reconstructible independently, versus "support typeclasses". It is also
why the fix is not free -- `em` and `propext` are classical, and admitting them
by substitution would enlarge the trusted surface rather than reconstruct it.
The 24 rows behind those two are a separate decision from the 337 behind the
other seven, and this ADR does not take it.

### Method

`scripts/gen-statement-import-blocker-census.py` builds the population: every
`F:ml430-*` fact, its pinned Mathlib source name (read from the title and
cross-checked against `provenance.source` -- **not** `formal.kernel_theorem`,
which on a proved mirror is OUR declaration and can be spelled differently
upstream; that cross-check found `Int.dvd_coe_gcd` mirrored as `Int.dvd_gcd`),
its fragment, its status, and its held-out membership taken from
`scripts/check-dispatchable-frontier.py --json`.

`scripts/run-statement-import-blocker-census.py` then runs four phases:

1. **elaborate.** One Lean module, `import Mathlib` plus one
   `def axeyumCensusGoalNNNN : Prop := <statement>` per row, each on its own line
   so a `file:LINE:COL:` diagnostic maps back to its row with no guessing.
   5.7 s on s5 for 756 statements.
2. **export.** The module is rebuilt from the rows that elaborated, compiled to
   an olean, and `lean4export Mathlib <module> -- <goal>` emits one stream per
   goal: that definition's own declaration closure and nothing else. No theorem
   value is exported, because the target is a `def`, not a `theorem`. 2,256 s
   for 751 streams.
3. **import.** `import_statement_ndjson` on each stream, through the new
   `crates/axeyum-lean-import/examples/statement_import_census.rs`, which records
   a typed decline as a row and continues rather than exiting on the first one.
   410 s.
4. **classify / publish.**

### Controls

- **A negative control statement** naming a constant that does not exist. The run
  aborts if it ELABORATES, because a run in which nothing elaborated -- a stub
  `lean`, an empty module, a swallowed error stream -- is otherwise identical to
  a clean pass. It was rejected.
- **The diagnostic regex makes Lean 4.30's `error(lean.unknownIdentifier):` tag
  group optional.** Demanding a bare `error:` matches nothing and reports every
  row as elaborated; that is exactly how `attest-nursery-surface.py`'s first run
  read as 160/160.
- **The olean build is the parser-desync control.** A parse error can swallow the
  lines after it and report them as elaborated. Phase 2 recompiles a module built
  only from the rows phase 1 called clean; a row that was never really read would
  fail there. It compiled.
- **The 499 PROVED mirrors are the positive-control population.** They are
  already established here, so a blocker on one is a property of the ROUTE and
  never of the proposition's difficulty. 238 of them are blocked, all in the same
  single class -- which is what makes "this is the route, not the mathematics" a
  measurement rather than an assertion.

### The screen, measured against the same run

`scripts/lean_surface_screen.py` flags 5 of the 756 statements from text alone.
Lean rejects 5 at elaboration. **The two sets are equal**: 5 agreeing, 0
flagged-but-elaborated, 0 rejected-but-unflagged. Both sides are derived over the
same population -- the screen from each statement's text, Lean from this run --
and neither is a literal.

Three signatures:

- `printer-glyph`: `⋯`, `✝` or `…` in the statement.
- `coerced-projection`: dot notation on a parenthesized group in which EVERY
  top-level operand is `↑`-coerced, e.g. `(↑a - ↑b).natAbs`.
- `unascribed-lambda-projection`: field notation on a lambda binder with no type
  ascription, e.g. `fun a => a.choose b`.

The "every top-level operand" condition is what makes this a screen rather than a
`↑` grep: 54 of the 756 statements carry a coercion arrow and 51 elaborate,
because a sibling operand of known type fixes the target.

Controls: `scripts/tests/test_lean_surface_screen.py`, 10 tests, every fixture a
real pinned statement with a measured Lean verdict, including two negative
controls a coercion grep would fail (`(i / ↑(i.gcd j)).gcd …` elaborates,
`fun (a : ℕ) => a.choose b` elaborates). Registered as mutation suite
`lean-surface-screen`: five mutations, each removing one guard, **each killing
exactly one test**.

## Alternatives

**Read the statements and classify them by hand.** Rejected on the standing rule:
prose about a blocker is not a measurement of it, and the two documents that
already described this blocker in words gave no count, no population -- and, as
it turns out, the wrong class.

**Screen on `↑` anywhere in the statement.** Rejected, and it is the reason the
screen has negative controls: it would flag 54 rows and be wrong about 51, while
passing a positive-only test suite.

**Screen by elaborating each candidate in real Lean.** That is the ground truth
and it is what the census does, but it cannot be the screen: it needs a 6 GB
built Mathlib that exists on one fleet host, so a screen built that way is
unrunnable where draws are authored. The text-only screen is not a weaker version
of it -- on this population it agrees exactly -- and it runs anywhere.

**Put the screen in `gen-autogenesis-nursery-refill.py::select()`, the draw.**
Rejected for now, and the reason is recorded rather than repaired: that
generator's `--check` is ALREADY RED on `main` (`nursery-v2-extension.json does
not match its own extension_sha256`), its drawn families are frozen by ADR-1445
and re-emitted rather than re-screened, and adding a field or a filter there
would rewrite a preregistered manifest. `propose-nursery-refill.py`, the headroom
snapshot, reads a tracked measurement whose digests would go stale and whose
`--remeasure` needs a 39 MB inventory on `/nas3`. Attestation is where these two
classes are discovered today, and it is where the screen went.

**Drop or rewrite a flagged statement.** ADR-0615 forbids editing a preregistered
`formal.statement`, and a row silently removed from a run is a coverage change
nobody recorded. A flagged row is labelled and still elaborated.

## Consequences

**C4 now has an input, and it points somewhere else than the roadmap guessed.**
The first demand-gated feature is the trusted-substitution extension for seven
constructive declarations (337 rows), with the two classical ones held back as a
separate decision. C4's exit criterion -- before/after population survival -- is
this census re-run.

**Two documents need correcting, not repairing.** `14-lean-lang.md`'s chair-01
row and `315-attestation-ceiling.md` item 3 both say "no screen exists", and
both imply the `variable` block is the reason the 257 are stuck. One is now
false and the other is 1 row of 257. Corrections are appended, per this
repository's convention for a stale claim.

**A draw can be screened on any host.** Before this, the only way to learn that a
statement would not re-parse was to elaborate it against a built Mathlib on one
fleet host over ssh. `attest-nursery-surface.py --screen-only` does the same
classification anywhere in under a second, and its exit status depends on the
finding.

**What this does NOT establish.** The screen agrees with Lean on THIS population;
that is a measurement over 756 statements, not a theorem, and a statement family
outside the pinned Nat/Int mirrors can break it in either direction. The census
measures whether a statement CROSSES, never whether it is provable here: an
admitted goal is an open fact with a kernel goal, and nothing in this run moves
any fact's status. The blocker distribution is over FIRST blockers, so unblocking
`eq_self` will expose whatever is behind it and the census must be re-run rather
than subtracted from. And everything here is bound to one pin pair (Mathlib
`c5ea0035`, Lean 4.30.0); a pin move invalidates the numbers, which is why the
artifact records both.

**Two gates were red before this lane and are still red.**
`gen-autogenesis-nursery-refill.py --check` fails on the
`extension_sha256` mismatch (3 of its 61 control tests error for that one
reason), and the three Lean gates `14-lean-lang.md` records as red on `main`
since the pin moved are untouched. Recorded so the next lane does not attribute
them to this work.

## Related

- [ADR-0604](adr-0604-lean-is-the-surface-syntax.md) — the statement-only import
  route this census runs
- [ADR-0615](adr-0615-the-evaluation-envelope-is-per-cohort-and-a-draw-is-incremental.md)
  — why a screened row is flagged and never rewritten
- [ADR-0603](adr-0603-classical-theorems-land-as-graded-statement-families.md) —
  the graded-family frame the mirrors sit in
- [`docs/math-department/14-lean-lang.md`](../../math-department/14-lean-lang.md)
  — Next Ten item 5, which this closes
- [`docs/plan/library-artifact-compatibility-roadmap-2026-08-30.md`](../../plan/library-artifact-compatibility-roadmap-2026-08-30.md)
  — C4
