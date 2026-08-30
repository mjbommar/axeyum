# L0/S1 — Bind statement identity

<!-- plan-section: lane-status -->

Lane: `l0-s1-statement-identity`
Phase: S1 of the trusted-library safety roadmap (ADR-0717, selected by ADR-0746)
Decision: [ADR-0763](../../research/09-decisions/adr-0763-statement-identity-is-pinned-for-every-settled-fact-and-absence-is-a-violation.md)
Status: **COMPLETE.** S1's exit criterion holds and is executed on every merge.

## The gap S0 measured, re-measured from the ledger

`artifacts/safety-matrix/safety-matrix.tsv` reported `exact_statement`
142 / 2117 — the thinnest column. Split by population, read from the facts
directly so the two measurements are independent:

| population | settled | pinned before | pinned after |
|---|---:|---:|---:|
| all settled facts | 2120 | 144 | **2120** |
| `F:ml430-*` mirrors | 375 | 27 | 375 |
| native (non-mirror) | 1745 | 117 | 1745 |

Mirrors already had a stronger guard — `check-mirror-statement-fidelity.py`
hashes `formal.statement` against a preregistered catalog, 502 of 514 verified.
**The native 1,745 were the real gap**, and they are the half of S1's
specification that had nothing behind it.

### The old gate could not fail on absence, and that is measured

`check-settled-fact-statements.py` had `if pin is None: continue` — absence read
as "newly settled", never as a gap. Loading `HEAD~2`'s checker with `HEAD~2`'s
144-pin manifest against the live facts:

```
clean                                        -> exit 0
SWAPPED BINDERS on F:creal-ivt-approx        -> exit 0   ACCEPTED
same mutation on a fact it DID pin (control) -> exit 1   rejected
```

The control is what makes this a finding rather than a bug report: the gate
worked correctly and simply had no opinion about 1,976 facts.

## What landed

**Statement identity for every settled fact.** Manifest schema 2 pins, per
fact, the kernel rendering (`formal.statement`), the reader-facing prose
(top-level `statement`), and the declaration it names (`formal.kernel_theorem`),
with superseded digests preserved in `history`. Pinning the prose is new: a
native fact makes two claims, and the field most readers see was unwatched.

**Absence is a violation, and the ratchet cannot be loosened.**
`coverage_floor` bounds unpinned facts (0), identity bindings (1,294) and
headerless statements (30) — and **slack is itself a violation**. Raising an
allowance to sneak something past makes the next run fail because the actual
count is then below the raised allowance. Loosening is self-reverting rather
than merely discouraged.

**`--write` can no longer launder drift.** It used to rebuild the pins from
current state unconditionally, so running it after a drift re-pinned the damage
and the gate went green.

**A structural bind needing no pin.** A `render_lean` statement opens
`theorem <name> :` and that name must equal `kernel_theorem`. 1,158 of 1,188
satisfy it, 0 violate it. A hash says "changed"; this says "changed into a
rendering of a different declaration".

```
before: settled=2120|pinned=144|drifted=0                                PASS
after:  settled=2120|pinned=2120|unpinned=0|identity_bound=1294
        |header_exempt=30|drifted=0|floor_unpinned=0|floor_identity=1294 PASS
```

## S1's exit, executed on every merge

`scripts/check-statement-identity-mutations.py`, ~2s, no cargo. Records which
gate rejected each row, because "something failed" is not evidence that the
right thing failed.

```
control|clean-tree|statement=0|mirror=0
1 swapped binders     F-creal-ivt-approx   REJECTED by=statement-pin
2 changed constant    F-creal-ivt-approx   REJECTED by=statement-pin
3 altered relation    F-creal-ivt-approx   REJECTED by=statement-pin
4 source drift        totient-dvd-of-dvd   REJECTED by=statement-pin+mirror-fidelity
5 our own rendering   both totient mirrors REJECTED by=statement-pin+mirror-fidelity
PASS|5/5 rejected|tree restored
```

Rows 1–3 rest on the statement pin **alone**, which is the measurable S1 delta —
before this lane, `F:creal-ivt-approx` was unpinned and all three were accepted.
Mutation 5 replays the two real damaged forms from `e79804fdd` rather than an
invented one.

## Priority population (coordinator-flagged, verified here)

`exact_statement` **0 / 20** across the IVT/EVT rows, none in the pin manifest,
against a ledger-wide control of 142/2117. Now **20/20 pinned, 14/20
identity-bound** — the six `cas-*` rows name no `kernel_theorem`.
`CReal.ivt_approx` and both ADR-0603 row-2 impossibility results are fully
bound, against their corrected prose. They needed no special machinery: full
coverage reaches them by construction, and `CReal.ivt_approx` is the subject of
exit mutations 1–3.

## Mutation kill sets — 19 guards, 19 killed exactly one, 0 survived

`settled-fact-statement-identity` (13 new) and `settled-fact-statements` (6
pre-existing, one anchor re-pointed after the refactor).

Three needed a second pass, and each failure is the same defect in miniature — a
control that passes for a reason other than the guard it names:

- **repointing** and **identity floor** each SURVIVED their first run, masked by
  a neighbouring guard firing on the same fixture. Fixed by isolating: the
  repointing fixture is `cas-term` (header check inert) and carries a second
  stable fact so `identity_bound` does not also fall; the identity fixture
  licenses the repoint with an amendment, leaving the lost binding as the only
  complaint. An amended repoint IS still a lost binding, so that is the right
  semantics as well as the isolating one.
- **the amendment digest check** survived because its two `or` clauses were only
  ever exercised together. Added a fixture with the `from` digest wrong and the
  `to` digest right.

## Non-negotiables, verified

- No fact's `epistemic_status`, `proof_route`, `axiom_footprint`, evidence or
  statement text was edited. A pin asserts only that a claim will not change
  silently; it asserts nothing about whether the claim is right.
- No `formal.statement` was found misdescribing its theorem — but note this lane
  performed **no semantic audit**, only integrity binding. That is S3's job, and
  reading this coverage as review coverage would be exactly wrong.
- `check-autogenesis-holdout-isolation.py`:
  `held_out=116|files_scanned=1109|settled=0|references=0|verdict=PASS`
- `check-mirror-statement-fidelity.py`:
  `facts=2270|mirrors=514|hash_verified=502|unpinned=12|violations=0|verdict=PASS`
- Registered in BOTH `scripts/check.sh` and the justfile;
  `check-aggregate-scope.sh` still reports 64 recorded divergences.

## For the next lane

- **Landing a settled fact now requires `--write` and committing the manifest.**
  One command. The failure message names it.
- **The manifest is machine-written** (~14,900 lines). `--write` is the only
  supported writer; hand-editing the floor is caught by the slack check.
- **S2 (circularity) inherits a usable hook**: `kernel_theorem` is now pinned per
  fact, so the authored declaration identity S2 must compare against observed
  dependencies is already bound and cannot drift underneath it.
- **The 30 headerless `lean4` statements are the remaining structural gap** in
  this column. Each carries a bare type with no `theorem <name> :` header, so
  nothing ties it to the declaration it claims beyond `kernel_theorem` itself.
  Bounded by `max_header_exempt` so it cannot grow; reducing it is ordinary work.
