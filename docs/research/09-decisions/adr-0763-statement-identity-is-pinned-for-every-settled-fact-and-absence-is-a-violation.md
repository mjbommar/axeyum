# ADR-0763: statement identity is pinned for every settled fact, and absence is a violation

Status: accepted
Date: 2026-08-30
Index-summary: S1 of ADR-0717. The statement gate could not fail on the
commonest way a statement goes unwatched — never being pinned — so 1,976 of
2,120 settled facts were unprotected and the gate printed `drifted=0` and
exited 0. Measured, not assumed: the pre-S1 gate ACCEPTS a swapped-binder
mutation on `CReal.ivt_approx`. Now every settled fact pins its kernel
rendering, its reader-facing prose and the declaration it names; absence is
bounded by a ratchet the gate re-derives, so a loosened floor is
self-reverting; `--write` can no longer launder drift. All five S1 exit
mutations reject, with the rejecting gate recorded per row. 19 guards,
19 mutation-verified to kill exactly one test.
Lane: `l0-s1-statement-identity`

Implements: [ADR-0717](adr-0717-library-construction-is-graph-directed-through-an-artifact-compatible-trust-anchor.md) phase S1,
specified in
[`docs/plan/trusted-library-safety-roadmap-2026-08-30.md`](../../plan/trusted-library-safety-roadmap-2026-08-30.md),
selected by [ADR-0746](adr-0746-the-safety-matrix-is-generated-and-gated.md)

## Context

ADR-0746's census measured `exact_statement` at **142 of 2117** proved facts —
the thinnest column in the matrix — and found the sharper version of the same
point: the 1,038 `generated-unreviewed` facts are the *best*-protected
population, each carrying a discriminating checker that names its own
declaration, and **the one thing none of them protects is `formal.statement`**.
Their checkers match a declaration NAME, never its TYPE.

So the gap was never "unreviewed prose". It was that a fact's formal statement
could be rewritten and nothing failed.

`scripts/check-settled-fact-statements.py` existed for exactly this and could
not do it. One line:

```python
if pin is None:
    continue  # newly settled: pinned below, not drift
```

Absence from the pin manifest read as "newly settled", never as a gap. The gate
printed `settled=2120|pinned=144|drifted=0` and exited **0** — this
repository's signature defect, a checker that cannot fail, sitting on its own
statement-integrity check.

Two `ml430` totient mirrors had `formal.statement` replaced with our own
`render_lean` output earlier the same day (`e79804fdd`). Those were caught,
because mirrors are hash-pinned against a preregistered catalog. Native facts
had no equivalent.

## The measurement that scopes it

Read from the ledger directly rather than from the matrix, so the two are
independent:

| population | settled | pinned |
|---|---:|---:|
| all settled facts | 2120 | 144 |
| `F:ml430-*` mirrors | 375 | 27 |
| native (non-mirror) | 1745 | 117 |

Mirrors carry a second, stronger guard already
(`check-mirror-statement-fidelity.py`, 502 of 514 hash-verified against the
catalog). **The native 1,745 are the actual gap**, and they are the half of S1's
specification — "for native claims, bind a canonical kernel rendering and
intended reader-facing statement" — that had nothing behind it.

### The pre-S1 gate accepts the mutation

Not inferred from reading the code. Measured, by loading `HEAD~2`'s checker
with `HEAD~2`'s 144-pin manifest and pointing both at the live facts:

```
clean                                        -> exit 0
SWAPPED BINDERS on F:creal-ivt-approx        -> exit 0   ACCEPTED
same mutation on a fact it DID pin (control) -> exit 1   rejected
```

The control matters. Without it the first result reads as "the gate is broken",
which is wrong and would have sent the fix in the wrong direction. The gate
worked; it simply had no opinion about 1,976 facts, and an empty opinion is
indistinguishable from a clean bill of health.

## Decision

### 1. Every settled fact pins three things

`artifacts/ontology/settled-fact-statement-pins.json`, schema 2, one row per
settled fact:

- `statement_sha256` — `formal.statement`, which for a native `lean4` row *is*
  the canonical kernel rendering;
- `prose_sha256` — the top-level reader-facing `statement`;
- `kernel_theorem` — the declaration the fact claims to be about;
- `history` — superseded digests, preserved when an amendment corrects a row.

The prose half is new and is the point. A native fact makes two claims, and
pinning only the formal one leaves the field most readers actually see free to
be rewritten to describe a different theorem while the formal side sits still.

2,120 pinned, of which **1,294 are fully identity-bound** (they also name a
`kernel_theorem`; the remainder are `cas-term` / `smtlib2` rows that name no
declaration).

### 2. Absence is a violation, bounded by a ratchet the gate re-derives

`coverage_floor` carries three counters. The important property is not that
they are monotone — it is that **slack is itself a violation**:

- `max_unpinned_settled` (0) — more unpinned than this fails; *fewer* also
  fails, telling you to run `--write`;
- `min_identity_bound` (1,294) — fewer bindings fails; more fails as slack;
- `max_header_exempt` (30) — see below.

A hand-editable floor is decoration. Raising `max_unpinned_settled` to sneak an
unpinned fact past makes the *next* run fail, because the actual count is then
below the raised allowance. Loosening is self-reverting rather than merely
discouraged.

The floors start at coverage already achieved, so the ratchet never demands
work that has not been done — it only forbids regression. That is the same
shape as the frontier gate's `--floor`.

### 3. A structural bind that needs no pin

A `render_lean` statement opens `theorem <name> :`, and that name must equal the
fact's `kernel_theorem`. 1,158 of 1,188 `lean4` settled facts satisfy it and
**0 violate it**; the 30 that carry a bare type with no header are exempt and
counted, so a 31st cannot appear quietly.

This catches something no content hash can express. A hash says "changed"; this
says "changed into a rendering of a *different declaration*".

### 4. `--write` cannot launder drift

It used to rebuild `pins` from current state unconditionally, so anyone who ran
it after a drift re-pinned the damage and the gate went green. It now refuses
any pin whose digests moved without an amendment, and when an amendment does
license the change it pushes the superseded digests into `history` — the
roadmap's "preserve previous statements when correcting a row".

### 5. The exit criterion is executed, not asserted

`scripts/check-statement-identity-mutations.py` constructs all five S1 mutations
against the live ledger on every merge (~2s, no cargo), records **which gate
rejected each**, and restores every touched file byte-exactly.

```
control|clean-tree|statement=0|mirror=0
1 swapped binders     F-creal-ivt-approx   REJECTED by=statement-pin
2 changed constant    F-creal-ivt-approx   REJECTED by=statement-pin
3 altered relation    F-creal-ivt-approx   REJECTED by=statement-pin
4 source drift        totient-dvd-of-dvd   REJECTED by=statement-pin+mirror-fidelity
5 our own rendering   both totient mirrors REJECTED by=statement-pin+mirror-fidelity
PASS|5/5 rejected|tree restored
```

Recording the attributing gate is not decoration: "something failed" is not
evidence that the right thing failed, and rows 1–3 resting on the statement pin
*alone* is precisely the measurable S1 delta.

Mutation 5 replays the two real damaged forms from `e79804fdd` rather than an
invented one. It is the sharpest of the five because it makes nothing false —
both theorems are real and axiom-free. It makes the mirror's claim
*unfalsifiable from the fact*, since with our rendering in the field that should
hold Mathlib's proposition, both sides agree by construction.

Exit 2 is reserved for a STALE fixture — a renamed fact, a statement no longer
containing the token a mutation edits — because a fixture that quietly stops
matching its subject is how this kind of check rots into a formality.

## Priority population

The coordinator flagged the 20 IVT/EVT facts, verified here independently
against the matrix: `exact_statement` **0 / 20**, and none in the pin manifest,
against a ledger-wide control of 142/2117. They are now **20/20 pinned and
14/20 identity-bound** (the six `cas-*` rows name no `kernel_theorem`).
`CReal.ivt_approx` and both ADR-0603 row-2 impossibility results are fully
bound, against their corrected prose rather than the earlier boilerplate. They
required no special machinery — full coverage reaches them by construction —
and `CReal.ivt_approx` is the subject of exit mutations 1–3.

## What a pin does NOT assert

A pin says a claim will not change silently. It says nothing about whether the
claim is right. No fact's `epistemic_status`, `proof_route`, `axiom_footprint`,
evidence or statement text was touched by this lane, and no semantic audit of
any `formal.statement` was performed — that is S3's job, and conflating the two
would let integrity coverage be read as review coverage.

## Consequences

- Landing a settled fact now requires running
  `check-settled-fact-statements.py --write` and committing the manifest. That
  is one command, and it is the cost of the gate being able to fail at all.
- The manifest is ~14,900 lines and is machine-written. Do not hand-edit it;
  `--write` is the only supported writer.
- Correcting a statement now requires an amendment row naming both digests and
  a reason. Legitimate corrections happen and are not blocked — they are made
  visible, which was always the intent.

## Verification

- 19 guards across two mutation suites, **19 killed exactly one test, 0
  survived**. Three needed a second pass and each failure is recorded in the
  commit that fixed it: two guards were masked by a neighbouring guard firing on
  the same fixture, and one clause of an `or` had never been exercised alone.
- `check-mirror-statement-fidelity.py` unchanged and still
  `hash_verified=502|violations=0|verdict=PASS`.
- `check-autogenesis-holdout-isolation.py` still
  `settled=0|references=0|verdict=PASS`.
- Registered in both `scripts/check.sh` and the justfile;
  `check-aggregate-scope.sh` still reports 64 recorded divergences.

## Alternatives rejected

**A second manifest for native identity, beside the existing pins.** Two files
holding a digest of the same field is the "two proofs of one fact that must stay
in sync" hazard; the existing manifest was extended instead.

**A monotone floor without the slack check.** This is what a ratchet usually
means here, and it is not enough: the floor lives in a hand-editable JSON file,
so a lane that loosens it once keeps the loosened value forever. Re-deriving the
floor and rejecting slack is what makes the edit self-reverting.

**Leaving the floor below achievable coverage, on the reasoning that a strict
gate gets turned off.** The floor never demands undone work — it starts where
coverage already is. Setting it lower would leave exactly the slack the previous
paragraph rejects, and pinning is mechanical: a fact arriving unpinned is one
`--write` away from compliance, not a research task.
