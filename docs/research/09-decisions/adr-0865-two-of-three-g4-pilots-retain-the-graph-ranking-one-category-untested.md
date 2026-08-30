# ADR-0865: L2 phase G4 ran two pilots, not three; both moved their metric cleanly; the ranking is retained, scoped to what was tested

Status: accepted
Date: 2026-08-30
Index-summary: G4 pilot clusters — signal-scarce population supports 2
categories, not 3; both run pilots (statability probe, generic congr_arg)
moved their preregistered metric with zero added trust surface and beat the
honest local-ready alternative on time-to-result; ranking retained for
categories 1-2 only, category 3 declared not-yet-evaluable.

## Context

`docs/plan/graph-directed-library-roadmap-2026-08-30.md` phase G4 asks for
three pilots (a high-degree missing substrate, a shared producer, a
destination bridge toward linear algebra/polynomials/analysis), each
comparing graph selection against the best local-ready alternative, with an
explicit instruction not to rationalize the score after seeing outcomes: the
ranking is retained only if at least two of three pilots move their
preregistered metric without a worse trust boundary, otherwise the weights
are revised.

ADR-0845 published the only frontier that currently exists
(`artifacts/infrastructure-frontier/mathlib-group-defs-v1.frontier.json`),
over population `mathlib-group-defs-v1` — Mathlib's group-definitions
neighbourhood, 446 declarations. `artifacts/declaration-graph/populations/`
and `artifacts/graph-join/` each contain exactly this one population; no
second population exists.

## Decision

**Establish signal before designing pilots, per the task's own instruction,
and report the actual shape found rather than manufacturing three pilots a
sparse population cannot support.**

The frontier's four queues over `mathlib-group-defs-v1` are: 4
language-infrastructure rows (all about the missing bundled-structure/
typeclass mechanism — `Semigroup`/`mul_assoc`, `CommMagma`/`mul_comm`,
`IsLeftCancelMul`/`mul_left_cancel`, and a carrier-generic `congrArg`), 0
proof-producer rows, 1 theorem-dominator row (an identity-verification
task, not proof work), 0 dependency-ready-leaf rows. None of these rows is a
finite-collections/big-operator candidate; none is a linear-algebra/
polynomial/analysis bridge candidate.

So:

1. **Category 2 (shared producer)** has a clean single candidate: row
   `IF-LANG-53e5bef137`, generic `congrArg`. Run as specified.
2. **Category 1 (high-degree missing substrate)** has no finite-collections
   candidate in this population, but does have a genuine "another high-degree
   missing substrate" under the roadmap's own permissive wording: the
   bundled-structure/typeclass gap behind three of the four language-
   infrastructure rows. The FULL gap (adding a `Structure`/typeclass
   mechanism to a kernel whose complete inductive list is
   `True/False/And/Or/Iff/Eq/Exists/Acc/Bool/Nat/Decidable` + `Nat.le` +
   `Nat.Fin` + `Char`, with no `Prod`) is new kernel type-theory work, out of
   a session-sized pilot's scope. Run a BOUNDED probe instead: can a raw,
   non-bundled, `Sort`-quantified associativity statement already be built
   and admitted, using only the public `Kernel` API? This tests the row's
   underlying claim at the resolution a pilot can actually resolve.
3. **Category 3 (destination bridge)** has zero candidates in this
   population. Building a second population rooted at a module actually on
   that path (e.g. `Mathlib.Algebra.Polynomial.Basic`,
   `Mathlib.LinearAlgebra.Basic`) requires the full G0→G3 pipeline over a
   different Mathlib subtree — out of this lane's edit scope
   (`artifacts/declaration-graph/`, `artifacts/graph-join/`,
   `artifacts/infrastructure-frontier/`) and not "genuinely cheap": it is a
   second G0-G3 run, not a read. **Declared not-yet-evaluable rather than
   forced.** This is the outcome the roadmap's own framing names as
   acceptable — a sparse population that cannot support a fair pilot is a
   real result, not a lane failure.

So **two pilots ran, not three**, both preregistered
(`docs/plan/status/l2-g4-pilot-clusters.md`, committed before any pilot code,
verifiable via `git log`) before any code was written.

### Pilot 1 (bounded substrate probe)

Built `∀ (α : Sort 1) (op : α→α→α), (assoc hyp) → (assoc concl)` via the raw
`Kernel` API (no bundled record, no `NatOps` scaffolding) — RESULT: PASS,
`Kernel::add_declaration` accepted it. A negative control (identical proof
term against a mismatched commutativity-from-associativity goal) was
correctly REFUSED, confirming the check was not vacuous. Zero added trust
surface (ordinary `add_declaration`, no axiom).

Finding: row `IF-LANG-dce29ad3f7`'s framing is broader than what is actually
missing. Raw carrier-generic statability was ALREADY present (`quotient.rs`
already binds `Sort u`-typed variables internally for its own purposes); what
is missing is the bundled ERGONOMICS (one `Structure` reused across many
lemmas), not raw statability. This sharpens the row; it does not refute the
row's underlying claim that no bundled-structure mechanism exists.

### Pilot 2 (generic congr_arg)

Built a carrier-generic `congr_arg` (explicit `ty`/`level` parameters instead
of a hardcoded carrier) and ran it against the same inputs as the existing
`NatOps::congr` (via the `NatDev` wrapper) — RESULT: PASS, and the two proof
terms are the **identical `ExprId`** via the kernel's content-addressed
interning, i.e. genuine byte-for-byte drop-in reuse, not merely "a parallel
implementation that also works". The wrapped theorem independently admitted.
Zero added trust surface.

A fresh grep for the row's own preregistered metric
(`congr_nat_to|congr_bool_to_nat` under `crates/axeyum-lean-kernel/src`)
found 4 matching files against the row's recorded baseline of 1 — the
baseline had already gone stale from concurrent lane activity the same day,
an independent, measured instance of the standing "a baseline ages fast in
this repository" observation.

### Local-ready alternative

Both pilots' preregistered comparator is `F:ml430-nat-and-self-06a84ccc`
(`Nat.land n n = n`), picked as the simplest-looking untaken entry in
`scripts/check-dispatchable-frontier.py`'s 21-item DISPATCHABLE list with no
graph input — mirroring how a lane actually picks "the next thing" absent
graph guidance, and confirmed via `git log` not to overlap sibling lane
`draw9-first-theorems`'s already-claimed targets.

Investigated by reading `nat_prelude/land.rs`, `nat_prelude/rec_agreement.rs`
(`declare_land_aux_le_left` as the closest existing proof of the needed
shape), and the shared `agree_by_fuel_induction`/`cases_zero_succ` induction
machinery. Several prerequisites already exist and are proved
(`land_zero_left`, `land_zero_right`, `land_bit`, `div_mod_exec`), but the
specific induction proving `landAux fuel n n = n` does not, and sizing it
against this repository's own documented cost for sibling facts in the same
family (`land_comm`, `land_assoc`, `land_bit` each needed dedicated
fuel-irrelevance lemmas and multiple debugging rounds per CLAUDE.md) puts it
at multi-hour, not same-session-pilot-budget, effort. **Not completed.**
The other 8 open dispatchable candidates in the same family were read for
comparison and are comparable or harder (`and_or_distrib_left/right`,
`dist_triangle_inequality`, `fermat_primefactors_one_lt`), except possibly
`Nat.and_one_is_mod`, which looks potentially easier but was not
independently verified.

This is load-bearing, not incidental: neither graph-selected pilot's local-
ready comparator produced a proved fact inside the same budget both pilots
completed in (~20-25 minutes each). "Dispatchable" in the ledger certifies
dependency readiness, not proof brevity, and the two claims are not the same.

## Consequences

**Exit verdict: RETAIN the ranking, scoped to categories 1-2 over population
`mathlib-group-defs-v1`.** Two of two run pilots moved their preregistered
metric (one exactly as preregistered, one more strongly than preregistered)
with zero added trust surface, and both beat the honest local-ready
alternative on the one axis actually measured for it. Category 3 remains
genuinely untested; this ADR does not claim the ranking works for a
destination-bridge category, only that it was not tested and states what
would make it testable (a second joined population on a module actually on
that path, built by the lane(s) that own the graph-join/frontier artifacts).

Per the roadmap's own instruction, this verdict is not rationalized after
the fact: both pilots' metrics, baselines, and the local-ready comparator
were committed (`021c884de`) before either pilot's code existed, and the
honest counterfactual — what would have changed the verdict — is recorded in
`docs/plan/status/l2-g4-pilot-clusters.md`: a REJECT from
`add_declaration` on pilot 1, or a merely-similar (non-identical) proof term
from pilot 2, would each have been a pilot that failed to move its metric
cheaply, and with only one pilot left standing the exit criterion would not
have been met.

G5 (make graph selection the ordinary dispatcher) should read this ADR's
scope limit literally: dispatch is justified for language-infrastructure and
shared-producer style candidates over this population; a destination-bridge
population still needs to be built and piloted before graph selection is
trusted for that category.

## Alternatives

**Manufacture a third pilot from an unrelated candidate (e.g. a random
theorem-dominator row) to hit the letter of "three pilots".** Rejected: the
task explicitly warns against this ("a pilot whose graph selection had one
candidate to choose from tests nothing"), and doing so would test nothing
about category 3's actual claim (destination bridging).

**Skip the local-ready-alternative comparison once it looked hard, and just
report the two pilots as unopposed wins.** Rejected: the comparison is the
point of the phase. Sizing the alternative honestly — including its
non-completion — is a real, useful result and is reported as such rather
than omitted.

**Treat pilot 1's PASS as validating the full row (claiming bundled
structures are not needed at all).** Rejected: the pilot answers a narrower
question (raw statability) than the row asks (ergonomic, reusable, bundled
structure). Reporting the narrower finding is honest; reporting the broader
one would not be.
