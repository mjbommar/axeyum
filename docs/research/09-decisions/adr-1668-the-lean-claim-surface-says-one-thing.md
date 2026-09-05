# ADR-1668: The Lean claim surface says one thing

Status: accepted
Date: 2026-09-05
Lane: `lean-claim-surface`

Index-summary: One 120-word paragraph on what "Lean compatible" means here
(the K profile, the two pins, the replay census, the import tier, the
Lean-side tactic, the carrier ledger) is reused verbatim on every claim
surface named below; the K3 matrix row is decided (native producers are
K3-shaped over this kernel, not over Lean goals) without changing any
assurance field; and the three July Lean roadmap documents are marked
historical under the C-series ordering.

## Context

`docs/math-department/14-lean-lang.md` Next Ten item 10 named the problem:
"the K profile, the replay census, the import tier and the two pins" were
scattered across claim surfaces that each said something different, and two
of them said something false. Measured 2026-09-05, before this lane:

1. `docs/plan/global/10-status.md`'s Lean paragraph reported "a retained
   local Lean 4.30 result of 70/70 accepted" and "Lean language, ecosystem,
   and complete native compatibility remain far beyond the current K0/K1
   slices" — a July number and a July framing, copied forward unchanged into
   the generated `PLAN.md` through several landings that changed the real
   figures (`creal` replay is 1,972/2,045, not a pass/fail 70/70; two more
   pins now exist, ADR-1660; two Next Ten items landed same-day, ADR-1662
   and ADR-1666).
2. `docs/plan/global/20-next-actions.md` action A9 opened with "the local
   host currently has neither `lean` nor `elan`" — false. Both Lean 4.30.0
   (the Mathlib corpus pin) and 4.34.0-rc1 (the cross-check pin, ADR-1594,
   moved further by ADR-1660) are installed under `~/.elan/toolchains/` on
   the fleet; `command -v lean` is empty only because `elan` does not modify
   `PATH`. `scripts/check-lean-gate.sh --print-toolchain` resolves it. A9's
   entire "provision Lean" framing was solving an already-solved problem
   while missing the four Next Ten items that are actually still open.
3. `docs/plan/lean-compatibility-v1.json`'s K3 row
   (`planned-native-proof-profile`, "Native goal, hole, unification, and
   tactic profile") carries every assurance field `not_attempted`, and nine
   reviewers in `14-lean-lang.md` independently note that this reads as
   "nothing native exists" when in fact `linarith`, `ring`, `simp`, `decide`,
   and the tactic combinator are 18,497 lines emitting kernel-checked proof
   terms over this kernel's own preludes, and `by axeyum` (ADR-1666) now
   closes real Lean goals for the quantifier-free ℕ fragment by handing Lean
   its own parser, elaborator and kernel a checked term.
4. Three documents dated 2026-07-21/22 —
   [`lean-system-compatibility-roadmap-2026-07-21.md`](../../plan/lean-system-compatibility-roadmap-2026-07-21.md),
   [`lean-system-implementation-plan-2026-07-21.md`](../../plan/lean-system-implementation-plan-2026-07-21.md),
   [`lean4-complete-parity-roadmap-2026-07-22.md`](../../plan/lean4-complete-parity-roadmap-2026-07-22.md)
   — still carried a `Status:` line reading "active" while their own tallies
   (21 done / 5 partial / 96 to do) had not moved since 2026-08-13, and the
   ordering `docs/math-department/14-lean-lang.md` adopted (interoperate at
   the artifacts that carry mathematical meaning before imitating the
   language) supersedes theirs. The terminal
   [complete-parity contract](../../plan/lean4-complete-parity-contract-2026-07-22.md)
   and its [registry](../../plan/lean-complete-parity-v1.json) were correct
   and current throughout, and are not part of this problem.

## Decision

**One paragraph, written once, and every future Lean claim on a claim
surface is either a verbatim quote of it or a measured edit to it — never a
fresh, independently-drifting sentence.**

The paragraph (120 words, reused character-for-character in every location
below):

> "Lean compatible" means what the compatibility matrix measures: K0 1/1 and
> K1 6/6 (an independent checker and a versioned import route), K2 through K6
> at 0 — no native source, tactics, workflow, runtime, or ecosystem yet. Two
> pins are distinct and every claim names which: `lean-toolchain`, the
> cross-check pin (currently 4.34.0-rc1, ADR-1594/1660), and the Mathlib
> corpus pin (Lean 4.30.0, mathlib4 `c5ea0035`, lean4export `a3e35a58`).
> Independent checkability is measured by replay in pinned Lean: `creal`
> only, 1,972 of 2,045 theorems, 48 `Type`-valued theorems Lean refuses, 25
> blocked behind them (ADR-0760). Imports are a labeled tier, never the
> axiom-free headline (ADR-0601, ADR-1664). `by axeyum` lets Lean check
> axeyum-produced terms as a tactic (ADR-1666). Cross-library statement
> identity runs through the carrier correspondence ledger (ADR-1665).

It appears, verbatim, in:

- `docs/plan/global/10-status.md` (replacing the stale "70/70 accepted"
  paragraph)
- `README.md` (the Lean-checker section, §2)
- `docs/PROJECT-STATE.md` (replacing the stale closing sentence of "Evidence
  and Lean")

Each of these is a claim surface named in `docs/plan/lean-complete-parity-v1.json`'s
`claim_surfaces` list. The full detail — the per-chair breakdown, the
measured "red today" row, and the open Next Ten items — stays in
`docs/math-department/14-lean-lang.md`, which each location links to rather
than re-deriving. **The rule, going forward:** a Lean status sentence on any
claim surface is either this paragraph unchanged, or a dated re-measurement
that updates the paragraph *and* this ADR together — never a standalone
number quoted from memory. This is the same discipline ADR-0509 already
applies to the trusted-surface count ("declared is not reached; both are
published"); this ADR extends it to the compatibility narrative as a whole.

**A9 in `docs/plan/global/20-next-actions.md` is rewritten**, not patched:
the false "neither lean nor elan" premise is corrected, and the action now
points at `14-lean-lang.md`'s four still-open Next Ten items (2: extend the
replay census to every prelude with `missing=0`; 3: publish `creal` as a
Lean library; 7: the public conformance corpus and divergence ledger; 9: a
native reader for the kernel-core statement rendering), in the priority
order that file gives them.

**The K3 row's assurance fields are unchanged.** Every field in
`planned-native-proof-profile` stays `not_attempted`: the profile's
`requires` are `admitted` and `proof_checked` credit toward *Lean goals*, and
the native producers are not that — they are K3-*shaped* work over this
kernel's own preludes, a different and already-real thing, not partial
credit toward the Lean-goal row. The row's `residual` field gains one
sentence recording exactly this distinction and pointing at ADR-1666 for
where the Lean-goal-facing half of the same work (`by axeyum`) is tracked
instead. `python3 scripts/gen-lean-compatibility.py --check` and (through
`derive_matrix_rows`) `python3 scripts/gen-lean-complete-parity.py --check`
both pass after the regeneration this residual-only edit requires.

**The three July documents are marked historical, in place, without
rewriting their bodies.** Each gets a dated status block appended
immediately after its own header metadata: historical as of 2026-09-05;
ordering superseded by ADR-0717's C-series
(`docs/plan/library-artifact-compatibility-roadmap-2026-08-30.md`) and by
`docs/math-department/14-lean-lang.md`; the complete-parity contract and its
registry are explicitly **not** superseded and remain the terminal
definition. The parity roadmap's block additionally marks the U2
official-execution programme (3,723 CTest cases, 111 not-run attempts, zero
credit since July) historical rather than resumed, since that roadmap is
where U2 is described.

## Evidence

- `docs/math-department/14-lean-lang.md`, "What the Lean boundary has today"
  table and the Next Ten list, measured 2026-09-05 at `f67ce41d2` — the
  source of every figure quoted in the paragraph above.
- ADR-1660 (the two pins), ADR-0760 (the `creal` replay census grading),
  ADR-0601 and ADR-1664 (imports never headline), ADR-1666 (`by axeyum`),
  ADR-1665 (the carrier correspondence ledger).
- `scripts/check-lean-gate.sh --print-toolchain` — resolves both installed
  toolchains despite `command -v lean` returning nothing.
- `python3 scripts/gen-lean-compatibility.py --check` and
  `python3 scripts/gen-lean-complete-parity.py --check` — both exit 0 after
  the K3 residual edit and regeneration.

## Alternatives

- **Rewrite each claim surface independently, in its own words.** Rejected:
  this is exactly the failure mode that produced the "70/70" and "neither
  lean nor elan" claims in the first place — restated by hand, each surface
  drifts from the measured tree at its own rate and by its own amount.
- **Change the K3 row's assurance fields to `succeeded` or add a partial
  state for the native producers.** Rejected: `proof_checked`/`admitted` in
  this contract mean credit toward a **Lean goal**, and the native producers
  do not check a Lean goal — `by axeyum` does that, on a distinct route
  (ADR-1666), and the row's own `requires` already describe what would need
  to be true. Blurring the field would let a non-Lean-goal result read as
  Lean-goal credit, which is the confusion the matrix exists to prevent.
- **Delete the three July documents instead of marking them historical.**
  Rejected: they carry an evidence audit and a completion audit that are
  still cited by name from other documents; deleting them breaks those
  citations for no benefit over a status block that tells a reader not to
  trust the ordering.

## Consequences

- Every future Lean-status edit to `10-status.md`, `README.md`, or
  `docs/PROJECT-STATE.md` is checkable against one paragraph rather than
  three independently-worded ones; a reviewer who finds a fourth wording
  knows it is wrong by construction.
- `docs/math-department/14-lean-lang.md` remains the single place detail
  lives; the claim surfaces link to it instead of re-deriving its numbers,
  which is what let two of them go stale for weeks without anyone noticing.
- The K3 row keeps its honest "nothing here yet" reading for the Lean-goal
  question it actually asks, while the residual sentence stops it from being
  misread as "the native producers do not exist."
- The three July documents stop being cited as an active roadmap; the next
  Next Ten item (2, 3, 7, or 9) is planned against `14-lean-lang.md` and
  ADR-0717's C-series, not against a July tally frozen since 2026-08-13.

## Related

- [`docs/math-department/14-lean-lang.md`](../../math-department/14-lean-lang.md)
  — Next Ten item 10, which this closes
- [ADR-1660](adr-1660-there-are-two-lean-pins-and-every-claim-names-which-one-it-means.md) —
  the two pins the paragraph names
- [ADR-1662](adr-1662-the-statement-import-blocker-is-a-proof-inside-the-definition-closure-not-the-variable-block.md),
  [ADR-1664](adr-1664-an-originated-theorem-may-rest-on-an-import-on-a-route-of-its-own.md),
  [ADR-1665](adr-1665-the-carrier-correspondence-ledger-and-its-five-grade-enum.md),
  [ADR-1666](adr-1666-by-axeyum-is-a-lean-tactic-and-lean-checks-the-term.md) —
  the landed items the paragraph cites
- [ADR-0509](adr-0509-the-trusted-surface-is-measured-as-reached-not-only-declared.md) —
  the same "declared is not reached" discipline, extended here to the
  narrative rather than a single count
- [`docs/plan/library-artifact-compatibility-roadmap-2026-08-30.md`](../../plan/library-artifact-compatibility-roadmap-2026-08-30.md) —
  ADR-0717's C-series, the ordering the July documents are superseded by
