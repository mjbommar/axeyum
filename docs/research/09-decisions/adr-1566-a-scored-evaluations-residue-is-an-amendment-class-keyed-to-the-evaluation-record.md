# ADR-1566: a scored evaluation's residue is an amendment class, keyed to the evaluation record and never to a fact id

Status: accepted
Date: 2026-09-02
Lane: `scored-residue-class`

Index-summary: ADR-1565 identified the last red partition gate's whole subject
— one component spanning `development`/`held-out`/`train`, fused by six
`held-out -> train`/`held-out -> development` edges from ONE family — and
measured that they are not a leak: the family was sealed 2026-08-29, its rows
were created `open` with `depends_on: []`, the scoring protocol was
preregistered 2026-09-01 14:03, and all six edges enter at 2026-09-01 14:58,
the commit that SCORED the family. It then offered two repairs. This ADR takes
the second: a **component-level analogue of ADR-1563's per-edge amendment
class, keyed to the evaluation record**. The new class
`scored-evaluation-residue` is honoured only when `class_complaint`
re-derives, from the live manifests, `holdout-evaluation-v1.json` and git,
that (a) the crossing edge's blind endpoint belongs to the family a record
names AND appears in that record's outcomes, (b) the record is `scored` and
its preregistration commit is a STRICT git ancestor of the commit that
introduced the edge, and (c) the edge runs FROM the blind row, never INTO it.
The amendment names the record's `record_id`; it may not name a held-out fact
id, and does not — the blind endpoint is stored as the baseline's salted
digest and resolved back through the live manifests, so
`check-autogenesis-holdout-isolation.py` still scans the artifact and still
reports `references=0`. **Baseline 6 -> 0.**
`check-autogenesis-nursery.py` contracts the same amendments through the edge
gate's own `load_amendments` (one implementation, as ADR-1563 required) and
goes from **1 crossing component to 0** — the last red partition gate is
green. What stays a leak is stated and driven: an edge INTO a blind row, an
edge from a blind row the record does not score, and an edge whose introducing
commit predates the preregistration each still fail both gates, on three
written controls. Four new mutants, one kill each.

Index-status: accepted

## Context

[ADR-1550](adr-1550-gate-the-producer-the-crossing-edge-is-the-unit.md) made
the crossing `depends_on` EDGE the unit of a partition-leak finding and froze
today's set into a shrink-only baseline.
[ADR-1563](adr-1563-the-bootstrap-lemma-is-not-a-leak-and-the-stale-exemption-is-retired.md)
added the first amendment **class**, `depends-on-longitudinal-bootstrap`, with
three properties that keep a class from degenerating into ADR-1546's growing
exemption: the class is **re-derived** from the live manifests rather than
asserted, the **direction is half the rule**, and `--record-baseline`
**excludes honoured amendments** so deleting one turns its edge back into a
violation. Baseline 198 -> 153.

[ADR-1564](adr-1564-train-is-the-training-partition-not-an-evaluation-partition.md)
made `train` the training partition, which retired 147 of those 153.
[ADR-1565](adr-1565-the-six-crossings-are-a-scored-evaluations-residue-and-the-nursery-gate-had-lost-the-blind-seal.md)
measured what the remaining six are, refused to move any family, restored a
blind seal the nursery gate had silently lost, and left the gate red with a
written cause and two named repairs:

> either an ADR accepting a scored family's residue as a permanent
> cause-recorded crossing, or a component-level analogue of ADR-1563's
> per-edge amendment class keyed to the evaluation record — an exemption may
> never name a held-out row.

**This ADR takes the second.** The first would have been a sentence; the
second is a rule a later reader can re-derive and a later lane can break.

## The decision

A new amendment class, `scored-evaluation-residue`, in
`scripts/check-partition-edges.py`.

> **A crossing edge is not a leak when it is the residue of an evaluation that
> was scored under a protocol committed before the edge existed.**

An amendment claiming the class carries an `evaluation_record` — the
`record_id` of a record in
`artifacts/autogenesis/holdout-evaluation-v1.json` — and is honoured only if
every one of the following is re-derived and holds. None of them is taken on
the author's word, and none of them is stated in the artifact.

| # | clause | re-derived from |
| --- | --- | --- |
| a | the edge's blind endpoint belongs to the family the record names, **and** appears in that record's `outcomes` | the live nursery manifests (`family`), and the record |
| b | the record's `state` is `scored`, and its `protocol_commit` is a **strict git ancestor** of the commit that introduced this edge | `git merge-base --is-ancestor`, plus the same first-parent pickaxe `introducing_commit` already uses |
| c | the edge runs **from** the blind row to a non-blind one | the live manifests and the policy's own `blind_partitions` |
| d | the amendment is keyed to `evaluation_record`, an id present in the record file | the record file |

`blind` is read from `policy.blind_partitions`, never spelled as `held-out` in
this rule, for the reason ADR-1564 gives: a second copy of a preregistered
decision is a second place to forget.

### Why the key is the record and not the fact

Clause (d) is the one that makes this a *class* rather than six judgements. If
an amendment were keyed to a fact id, then:

* the artifact would name a held-out row in plain text, which
  `check-autogenesis-holdout-isolation.py` treats as a breach — ADR-1550
  already paid for this once, with six such breaches in its first baseline, and
  it is the exact reason ADR-1563 recorded the six as **structurally
  un-amendable**; and
* the rule would be un-auditable in the direction that matters. "This fact is
  fine" is a judgement. "This edge is the residue of *that* record, and the
  record predates it" is a claim about a committed artifact and a commit graph,
  and either half can be checked by someone who was not here.

So the amendment stores the blind endpoint as the **salted SHA-256 digest**
`redacted_key` already uses for the baseline, with the same committed salt, and
`class_complaint` resolves it back to a live fact id by digesting each blind
row of the live manifests. A reader with the manifests can re-derive every
clause; a producer reading the artifact learns a digest and a record id.

**`check-autogenesis-holdout-isolation.py` still scans this file** — the
amendments artifact was and remains inside its scan set, and it still reports
`references=0`. The redaction is what makes the amendment possible, not an
exemption from the scan.

### What is still a leak

Stated here because a class that cannot be violated is the growing exemption
again. Each of these is a written control (see below), and each fails BOTH
gates:

* **Any edge INTO a blind row.** Spending blindness on a row by making a drawn
  row's proof depend on it is the original breach, and it is not an evaluation
  residue in any direction. Clause (c).
* **Any edge from a blind row the record does not score.** A sibling in a
  spent family is still a row nobody evaluated; the class requires membership
  in `outcomes`, not merely a matching family name. Clause (a).
* **Any edge whose introducing commit predates the preregistration.** This is
  ADR-1565's whole argument, mechanised. An edge older than the protocol was
  not created by the evaluation, so the row was not blind when it was scored,
  and the ADR-1450 / `natural-bit-decode` reclassification is the correct
  instrument instead. Clause (b).
* **An unscored record, or an absent one.** A record whose `state` is not
  `scored` is a preregistration, not a result. Clause (b).

### The one tolerance, and why it is loud rather than silent

Clause (b) is a question about the commit graph, and **three real trees here
do not have one**: `scripts/tests/mutation_controls.py` copies the checkout
with `.git` in its `ignore_patterns` (measured — the nursery suite's baseline
went red on exactly this before the tolerance existed), a lane snapshot from
`git archive | tar -x` carries no history, and every control fixture is built
from scratch.

Both obvious behaviours are wrong:

* **Refuse every amendment there.** The gate then goes red on a fact about
  *where it ran* rather than about the ledger — the failure `exit 2` exists to
  avoid, one level down.
* **Honour them silently.** The reader is told a clause held when it was never
  asked. That is the shape CLAUDE.md names: a checker that cannot fail, in one
  environment, with nothing in its output to say so.

So the clause is **skipped and recorded**. `ClassContext.git_available()` is
the narrow test (`rev-parse --is-inside-work-tree`), the skip lands in
`ClassContext.unverified`, and BOTH gates print it — `CLASS-UNVERIFIED <line>`
plus a `class_unverified=N` field on `check-partition-edges.py`'s summary, and
the same lines from `check-autogenesis-nursery.py` before its OK rows. The
authoritative run is the one in a checkout, and the output says which kind of
run it was. M30 is the mutant that asserts availability instead, and it kills
exactly the control for this.

The note is deliberately NOT in the nursery report dict: that report's digest
is a property of the drawn population, and a fact about where the gate ran
does not belong in it.

### And what does not change

* `--record-baseline` still excludes honoured amendments, so the six edges
  leave the baseline (**6 -> 0**) and deleting an amendment turns its edge
  back into a violation against a baseline it is no longer in. That is the
  ADR-1563 property that makes every clause above observable.
* The ratchet still refuses to grow.
* `check-autogenesis-nursery.py` reads the amendments through
  `check-partition-edges.py`'s own `load_amendments`, by path. There is one
  implementation of what is honoured, not two. The edge-match itself moved into
  a shared `edge_is_amended` for the same reason: matching a live plain fact id
  against a committed digest is a rule, and two copies of it would be two
  gates describing different graphs.
* Nothing is moved between partitions, no row's outcome or id appears in any
  artifact this lane wrote, and `integer-absolute-value` remains held-out and
  remains SPENT exactly as `holdout-evaluation-v1.json` already records.

## Consequences

* `check-partition-edges.py --baseline`: green, baseline **6 -> 0**.
  `--record-baseline` refuses to grow, and a no-op re-record is byte-identical.
* `check-autogenesis-nursery.py`: **green**, 1 crossing component -> 0. This is
  the last red partition gate from ADR-1546's exit criterion.
* The blind seal ADR-1565 restored is intact and is now driven by three
  controls rather than one, each aimed at a different clause of the class.
  Every exemption list behind these numbers is EMPTY: `component_split_
  exemptions` 0, `cross_population_component_split_exemptions` 0, baselined
  edges 0. Nothing is suppressed; 51 edges are amended under two re-derived
  classes and the rest do not cross.
* **Mutation, measured, and the two mutants that kill two.** `partition-edges`:
  42 tests, 28 mutants, 26 single kills. M24 (record key), M25 (scored
  membership), M26 (direction), M27 (preregistration order), M28 (record
  state), M29 (redacted matching) and M30 (the tolerance) are the new ones.
  **M11 kills 2** because `redacted_key` is now one rule with two readers —
  what the baseline records, and which form an amendment may name a blind
  endpoint in; retargeting it at `redacted_row` to force a single kill was
  tried and kills THREE, two of them for a self-inconsistency the shipped code
  cannot have. `nursery-split-exemption-guards`: 26 tests, 11 mutants; **N1
  kills 2** — one contraction, now exercised by two amendment classes, and the
  second kill is the new class's accept case, which is the positive control the
  three seals need.
* The audit question for the NEXT `held-out -> X` edge is unchanged and is now
  executable: which commit introduced it, and does the preregistering commit
  precede it. A lane that answers "yes" writes one amendment; a lane that
  answers "no" has a leak and must repair or reclassify.
