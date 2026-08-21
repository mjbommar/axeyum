# ADR-0539: The example inventory COUNT is generated; the per-example prose is not

Status: accepted
Index-summary: Split `docs/reference/examples.md`'s gate into a mechanical half and a judgement half — `scripts/gen-example-inventory.py` writes the `all N … Cargo examples` markers from `git ls-files`, while the requirement that every example carry a hand-written row stays. Motivated by the marker going stale FIVE times in one day (108 → 113 → 118 → 119 → 121 → 122 → 123 → 124), each time reddening `check-parity-docs.py` for whichever lane pushed next.
Index-status: accepted
Date: 2026-08-21

## Context

`scripts/check-parity-docs.py` enforces two things about the example catalogue:

1. every tracked file under `crates/*/examples/` has a link in
   `docs/reference/examples.md`;
2. `docs/documentation-plan.md` and `PLAN.md` (via
   `docs/plan/global/30-workstream-state.md`) contain the literal string
   `all N … Cargo examples` for the current N.

Both are good rules and they have caught real omissions. But they are not the
same KIND of rule, and bundling them costs.

**Measured 2026-08-21.** The count went stale eight times in one working day —
108 → 113 → 118 → 119 → 121 → 122 → 123 → 124 — as concurrent lanes added
examples. Each time, the next lane to push found `check-parity-docs.py` red for
a reason that had nothing to do with its change, and paid a context switch to
fix someone else's bookkeeping. One lane (this one) paid it five times and
mis-set the number twice: once bumping 123 → 124 after adding a catalogue row
for an already-tracked file, which is not a new file.

The second failure is the diagnostic one. **A human maintaining a derived
integer will get it wrong**, because the rule for deriving it ("count tracked
files, but a catalogue row is not a file") lives nowhere except the gate.

## Decision

Split the gate along the line between mechanism and judgement.

- **The count is generated.** `scripts/gen-example-inventory.py` derives N from
  `git ls-files` over `crates/*/examples/**.rs` — the same population
  `check-parity-docs.py` uses — and rewrites the marker in the two source files.
  `--check` fails when they disagree, and is wired into `scripts/check.sh` and
  the `justfile`. `PLAN.md` continues to be produced by `gen-plan.py` from
  `30-workstream-state.md`, so the count reaches it the way every other
  generated number does.
- **The prose is not generated, and the per-example row requirement stays.** A
  catalogue row says what an example is FOR, which section it belongs in
  (learning example / artifact generator / maintainer diagnostic), and whether
  it writes files. None of that is derivable. Measured the same day: of eight
  examples catalogued by hand, **five were named `*_audit` or `*_census` and
  wrote nothing**, so the name does not even predict the section. Generating a
  stub row would make the gate green over a description nobody wrote, which is
  strictly worse than the gate being red.

## Consequences

- A lane adding an example still has to write its row. That is the part worth a
  human's time and it is unchanged.
- A lane that adds an example and forgets the count no longer reddens the gate
  for everyone else; regeneration fixes it, and `--check` catches a stale one.
- The population is defined in exactly one place. If the two scripts ever
  disagree about what counts as an example, that is now a visible contradiction
  between two `--check` gates rather than a number a human guessed.
- **This does not fix the shared-append-point problem**, only this instance of
  it. `PLAN.md` and the ADR index are generated for the same reason; this is the
  third file to join them, and the pattern — per-lane state in per-lane paths,
  derived values in generators — is the one CLAUDE.md already states.

## Alternatives rejected

- **Generate the whole catalogue.** Rejected: it would fabricate descriptions,
  and the descriptions are the reason the file exists.
- **Drop the count markers.** Rejected: the count is the only thing tying the
  prose file to the tracked population. Without it, a catalogue can quietly fall
  behind and nothing says so.
- **Let the gate warn instead of fail.** Rejected on this repository's own
  evidence: a check that cannot fail is one nobody reads, and the parity ledger
  went fifteen days stale behind exactly that reasoning.
