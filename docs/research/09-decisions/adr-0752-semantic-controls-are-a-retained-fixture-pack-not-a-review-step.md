# ADR-0752: semantic controls are a retained fixture pack, and zero executed cases is failure

Status: accepted
Date: 2026-08-30
Index-summary: S3's semantic falsification lands as a versioned pack of known-false, known-vacuous and known-valid fixtures that the gate executes; a load-bearing control is one a killed mutation demonstrates can fail, and by that definition 8 of 2,117 proved facts have one.
Index-status: accepted

Phase: ADR-0717 L0, roadmap phase **S3**
Lane: `l0-s3-semantic-controls`
Builds on: [ADR-0746](adr-0746-the-safety-matrix-is-generated-and-gated.md) (S0's census)

## Context

ADR-0717 names vacuity as risk 3 and says plainly that an empty axiom footprint
does not touch it. S0 then measured how far the ledger's protections actually
reach: **91 of 2,117** proved facts carry semantic-falsification evidence and
**14** name any mutation or negative control.

S0 also found the trap that makes this phase easy to get wrong. **1,901
evidence rows declare `kind: exhaustive-enumeration` or `instance-pin` while
their `supports` records an axiom footprint.** Nothing was enumerated. Reading
`kind` at face value turns the true semantic-falsification count of 91 into
1,992 — a nineteenfold over-report of exactly the protection this phase exists
to supply.

And the session that produced this phase also produced an unusually good
corpus of the defect. Six real cases, each of which passed something before it
was caught:

- a control that "succeeded" on a **sort mismatch**, applying a theorem to a
  `Prop` where a `Nat → Prop` was wanted, so it never tested the property;
- a control **vacuous by mathematics rather than by types**: `φ(x) ∣ φ(x·q)`
  holds at composite `q` too, so a composite control fails at *zero*
  composites — while the same-shaped control over the neighbouring prime-power
  formula genuinely discriminates;
- a traced plan asserting an identity was coprimality-independent, "verified
  numerically at (4,6),(6,9)", **false at 26 of 26** non-coprime pairs;
- a primality certificate for **91** that passes Fermat, passes the order
  check, and whose claimed factor is genuinely prime — only completeness
  rejects it;
- a Chinese-remainder certificate **(9, 24)** for a system whose answer is
  9 mod 12: every guard passes but leastness;
- an NRA certificate recording a bound's **constant but not its strictness**,
  so the independent re-validator accepted a forged refutation of a
  *satisfiable* query — while nine guards in that module were each killed by
  exactly one test.

That last one carries the methodological point, and the roadmap agrees with
it: **mutation testing measures the guards you have, never the ones you are
missing.** A guard that was never written has nothing to delete.

## Decision

### 1. The pack is retained, executed, and pinned

`scripts/semantic_control_fixtures.py` holds the fixtures; every one is a real
defect above, or the valid control that sits one line away from it.
`scripts/check-semantic-control-fixtures.py` executes them and gates.

Three classes, and the distinction is the decision:

| class | must hold | why it is separate |
|---|---|---|
| `false` | at least one counterexample | a control finding none is measuring nothing |
| `vacuous` | **zero** discriminating instances | the fixture asserts the zero rather than its own greenness |
| `valid` | no counterexamples, ≥1 discriminating instance, **≥1 killed mutation** | greenness is not evidence; a killed mutation is |

A `vacuous` fixture is not a bug to be fixed. It is a *retained specimen*: the
shape a control takes when it cannot fail, kept executable so the shape stays
recognisable.

### 2. Zero executed cases is always failure

Per fixture and for the pack, whatever the class, and for an empty pack. This
is the repository's signature defect and it is a guard, not a sentence: the
mutation that removes it kills exactly one test.

### 3. A load-bearing control is one that has been shown to fail

Not one that is present. Not one whose `kind` says so. A control counts only
when this gate has *demonstrated* it fails when the property fails — a killed
mutation, or an in-tree numerics script that asserts its own negative controls
genuinely fail and does.

By that definition, over the whole ledger:

    load_bearing=8|semantic_falsification=91|proved=2117

**8 of 2,117.** 91 is the upper bound — facts carrying a semantic evidence row,
whether or not it discriminates. 1,992 is the number `kind` would give, and the
census never reads `kind`: it reads S0's generated column, which classifies
from `supports`. That is also why S0 keeps ownership of the column and this
lane reads rather than recomputes it.

The 84-fact difference between 91 and 8 is **not** a claim that 84 controls are
vacuous. It is the honest statement that 84 have not been demonstrated either
way. Those are different findings and the summary keeps them apart.

### 4. A mutation that is not falsified is classified, never failed

The roadmap is explicit: *some mutations are also true*. A `Mutation` carries an
`also_true` flag; an unfalsified mutation so declared is reported `also-true`
for review, and an undeclared one is reported `survived` and listed. Neither
reds the gate.

This is a design constraint, not a leniency. A gate that fails on a true
mutation is a gate somebody turns off, which is the same outcome as not having
one — and worse than not having one, because the turning-off is invisible.

Measured on the committed pack: 19 mutations, **18 killed, 1 `also-true`, 0
survived**. The `also-true` case is `eq-to-le` on the totient identity, where
the weakened statement is simply true.

### 5. A fixture may not name a fact that does not exist, is not proved, or is held out

Three guards, each mutation-verified. The third matters most: a control aimed
at a blind evaluation population spends the family it was measuring.
`check-autogenesis-holdout-isolation.py` reports
`held_out=116|files_scanned=1109|settled=0|references=0|verdict=PASS`.

## Consequences

- 13 fixtures, 9,742 executed cases, 19 mutations, four in-tree numerics
  scripts re-executed on every gate run (~2 s total).
- 21 guards, each verified by `mutation_controls.py` to kill exactly one of 28
  controls. No survivors, nothing unmeasured.
- Registered in both `scripts/check.sh` and the justfile.
- The pack's shape is pinned in `artifacts/semantic-controls/fixture-pack.json`,
  so a silent change to a model is drift rather than a fresh baseline.

## What this ADR does not claim

- **The pack does not cover the ledger.** 8 of 2,117 is the honest number, and
  growing it is per-family work, not a generator.
- **The `vacuous` class is judgement, not a measurement of the ledger.** Both
  vacuous fixtures are controls that really shipped here; nothing asserts they
  are the only two.
- **Nothing here inspects a proof term.** These are semantic checks over small
  domains, which is what makes them cheap and is also their ceiling. S4's Lean
  replay and S5's kernel differential are the checks that reach the term.

## Two defects the gate found in its own first run

Both are recorded because each is the failure this phase exists to catch,
arriving in the tool built to catch it.

1. **The numerics-script detector matched the literal string `NEGATIVE
   CONTROL`** and reported two in-tree scripts as carrying none. Both carry
   several, spelled `GENUINELY FAILS`. A gate manufacturing a finding about its
   own subject; the counts went 0 → 14 and 0 → 6 once the pattern covered both
   spellings.
2. **A mutation named `drop-congruence-check` never removed the guard it
   names** — it re-ran the unmutated checker and reported `survived`. It is now
   killed at 1,174 instances. A "survivor" is as easily a broken mutation as a
   weak guard, and only reading the mutation tells you which.

A third belongs to the control suite rather than the gate:
`test_a_fixture_that_executed_nothing_is_refused` needed a *second* fixture
with a nonzero count. Without it the pack-total clause covers for a deleted
per-fixture clause, the mutation survives, and a passing test measures nothing
about the guard it names.
