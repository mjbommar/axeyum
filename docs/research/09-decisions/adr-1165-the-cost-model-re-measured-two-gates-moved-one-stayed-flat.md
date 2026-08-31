# ADR-1165: The cost model re-measured — two gates moved, one stayed flat

Status: accepted
Date: 2026-08-31
Index-summary: Re-measured every checkable claim in
`docs/formalized-math-2026-08/07-the-cost-model-and-pareto-position.md`
(dated 2026-08-27) against the current tree rather than inheriting it. The
document holds up in substance — §1-2's strategy framing is unchanged, and
every named "templates compound" example still exists. Three things moved
and are corrected in place, in dated blocks, per doc 08's convention (quote
the old text, do not delete it). The setoid-congruence "producer, waiting to
be written" was built the same day the document was written
(`creal/congruence.rs`, `cb8b54e20`), with one production consumer
(`CReal.mulPowCongr`) and nothing retired — the base congruences the deriver
depends on cannot be re-derived through it without circularity, so the
token-sink reduction is prospective. The sharding gate is closed for the
mechanism named: `creal_tests.rs`'s single pinned array no longer exists,
replaced by 46 per-module shards. The retrieval gate got real machinery
(`shape_search`, ADR-0608, 2026-08-27) but is measurably not closed:
`scripts/brief-step0.py` found it used 4.8% of the time over 272 lane status
docs (vs. 46% for mutation testing, which has both a harness and a gate),
and two more retrieval-failure instances are dated after the tool landed.
The contracts gate is unchanged: `fact-frontier.py --json` still reports 0
admissible, now measured against 170 ready facts and exactly two registered
producer contracts, one of which matches exactly one ready fact — and
declines it.
Index-status: accepted

Related: ADR-0601/0602/0603 (the strategy this document operationalizes),
ADR-0608 (`shape_search`, the retrieval machinery), ADR-0692/0875/0895/1090
(the IVT/EVT worked example's own correction chain, the convention this ADR
follows), `docs/plan/status/136-congruence-deriver.md` (the congruence
producer), `scripts/brief-step0.py` (the retrieval-compliance measurement).

## Context

`docs/formalized-math-2026-08/07-the-cost-model-and-pareto-position.md`
carries this project's Pareto claim and cost model, written 2026-08-27 during
a single ~30-lane day. Its sibling document, doc 08 (IVT/EVT measured against
Mathlib), was found the same week contradicting its own table within ten
lines — a verdict paragraph asserting a structural gap that a table four
lines above it had already closed, plus a citation to prose that occurs zero
times in the file it names. That was not carelessness so much as staleness:
a file that records a state of the tree accumulates drift the moment the tree
moves, and its own authority is what makes the drift expensive.

Four days had passed since doc 07 was written, in a repository that landed
Gauss's lemma, the general-`n` determinant, IVT/EVT row 4 (labeled Mathlib
import), and a re-measured curriculum coverage axis in that window (per the
dispatching lane's own summary). The task: re-measure doc 07's claim and
correct wherever the document and the tree disagree, in either direction —
not advocacy, not a rewrite, a measurement.

## What was re-measured, and how

Every number below was produced by a command run in this lane's own worktree
against local `main`, not quoted from an earlier document.

**§4.1, contracts.** `python3 scripts/fact-frontier.py --json`:

```
selection.ready_fact_ids:       170
selection.admissible_fact_ids:  0
selection.declined_fact_ids:    1
selection.outcome:              "refused-no-admissible-candidate"
```

`ls artifacts/autogenesis/producer-contracts/` lists exactly two contracts
(`nat-coprime-family-v1.json`, `int-modeq-family-v1.json`). Filtering the 170
ready entries for a non-empty `matched_producer_contract_ids` returns exactly
one: `F:ml430-nat-coprime-of-lt-minfac-0f79bdba`, matched against
`producer-contract-nat-coprime-family-v1` — and its own `rejected_by`
includes `declined-via-contract`, so the one fact that reached a contract was
turned away by it. Doc 07 said "was 0"; it is still 0, and the shape of *why*
is now visible: the registry exists and is wired into selection, but 169 of
170 ready facts never reach a contract at all (`no-registered-operation`,
`no-matched-producer-contract`), and the one that does gets declined.

**§4.2, retrieval.** `docs/research/09-decisions/adr-0608-…md` (2026-08-27,
the same day as doc 07) records the audited count at **seventeen** distinct
instances (doc 07's own source, the design-review note it cites, had reported
thirteen mid-day) and lands `shape_search` — a shape-indexed retrieval tool
over every declaration kind in `kernel.environment()`, not just theorems.
`scripts/check-shape-duplicates.py` gates it into `check.sh`/the justfile;
`scripts/shape-duplicates-allowlist.json` still lists exactly 10 adjudicated
groups, unchanged since 2026-08-27, so no *new* accidental duplicate has
reached the tree since the gate landed.

That is real progress, and it is not the whole story. CLAUDE.md's own
retrospective log records two more retrieval-failure instances dated
**after** `shape_search` existed — 2026-08-29 (a module basename, `crt.rs`,
duplicated across two preludes, with the wrong one searched) and 2026-08-30
(the same counting argument reused over a different aggregate in a different
prelude, findable only by shape, not by name) — both by lanes that had the
tool available. `scripts/brief-step0.py` (2026-08-29, `b6f6d5f37`) measured
why, over 272 lane status documents: mutation testing, which is backed by
both a harness and a CI gate, is followed **46%** of the time; `shape_search`,
which as of 2026-08-27 was backed only by prose in CLAUDE.md, was used
**4.8%** of the time. The tool's own conclusion — compliance tracks
mechanization, not emphasis — is why it moves the check into the dispatcher's
own step 0 rather than asking the lane to remember. That tool is two days old
at measurement time and has no before/after instance count of its own yet.

**§4.3, sharding.** `ls crates/axeyum-lean-kernel/src/creal/inventory/ | wc
-l` returns 46. `creal_tests.rs` (11,198 lines) carries no `EXPECTED`/pinned
declaration-count array; `git log --diff-filter=A` on the shard directory
confirms it replaced the single array CLAUDE.md's own retrospective describes
("CURRENT STATE (2026-08-27): `creal_tests.rs` no longer has this pin at
all"). `every_creal_declaration_is_checked_and_axiom_free` (still present,
`creal_tests.rs:124`) is the environment-derived coverage check that replaced
the length pin. No document tracks a cross-lane-conflict-rate before/after
number, so that specific metric doc 07 named cannot be quoted; the mechanism
that produced the conflicts — every pair of `creal` lanes editing one shared
file regardless of which declarations they added — no longer exists.

**§3, the congruence producer.** `git log --diff-filter=A -- \
crates/axeyum-lean-kernel/src/creal/congruence.rs` shows it landed
2026-08-27 (`cb8b54e20`), the same day doc 07 called it "waiting to be
written". Read in full: a six-entry registry of base congruence lemmas, a
`CongruExpr` term representation chosen so the deriver can inspect a node
without running it, and `derive`/`declare_derived_congr`, pure structural
recursion returning `Result<(ExprId, ExprId), CongrError>`. One permanent
production registration, `CReal.mulPowCongr`, dispatched from
`build_creal_prelude_uncached`. Its own status doc
(`docs/plan/status/136-congruence-deriver.md`) reports the deepest
kernel-checked demo — five registered-op nodes — at 7.62 ms derive+check, and
is explicit that nothing existing was retired: `neg_congr`, `add_congr`,
`mul_congr`, `min_congr`/`max_congr`/`abs_congr`, `pow_congr`,
`sum_range_congr` are all base cases the registry depends on, so deriving
them through the deriver would be circular. The reduction this buys is
prospective — for composite congruences not yet written — not a retroactive
saving on what was already hand-assembled.

**§1, the IVT/EVT worked example doc 07 points to.** Re-read doc 08 in full,
including its own correction chain (ADR-0692, ADR-0875, ADR-0895, ADR-1090).
As of 2026-08-31 all four ADR-0603 rows are populated with evidence for both
theorems; IVT is Pareto-positioned under the two-axis test, EVT is not, for a
bookkeeping reason (no fact had named the row-1 supremum theorem, which
already existed under a different name) rather than the structural one an
earlier draft of doc 08 asserted. `CReal.evt_approx_max` is an *approximate*
maximiser, not the classical attaining one — doc 08 states this and doc 07
never claimed otherwise, so no correction to doc 07's own text was needed
here, only a pointer confirming the distinction survives.

**Falsifiability paragraph.** The "~8.5 s incremental for a degree-2 `∀x`
identity" / "~1 s concrete" / "~356 s" triple could not be traced to a
specific committed benchmark this lane could re-run in bounded time. Reported
as unverified rather than silently re-asserted or deleted. A different but
related cost curve — Sturm-isolation cost for the row-3 EVT decidable
fragment, concrete argmax rather than a `∀x` identity — is separately
measured in `docs/plan/status/138-cas-extremum.md` up to degree 22-24
(16 ms-13.7 s sparse, ~24 s for a degree-6 "thick" polynomial, declining
soundly). That is adjacent evidence the surrounding CAS machinery scales
gracefully; it is not a substitute measurement for the specific axis doc 07's
falsifiability bet is about, which remains open at degree 2 as of this
writing.

**Cross-check, unrelated to any specific doc-07 number but load-bearing for
its §1 "quote the pair" instruction.** `python3 scripts/validate-facts.py`:
`routes: cas-certificate=46(kernel-reconstructed=14,cas-internal=32)
imported-kernel-lean=7 kernel-lean=2122 search-certificate=12 smt-clausal=10
smt-term-level=17`. `python3 scripts/gen-lean-axiom-ledger.py --check`:
`total=30|axreal=30|complex=0|cpoint=0|creal=0|integer=0|logic=0|nat=0|rat=0
|string=0`. The axiom-ledger shape doc 07 §1 asks readers to quote as a pair
is unchanged even though every count around it moved. The validator also now
discloses that 1 of the 14 `kernel-reconstructed` `cas-certificate` rows is
non-discriminating (the kernel obligation it checks holds of every
polynomial, not just the produced one) — worth carrying alongside the 14 so
it is not quoted as fourteen independent geometric certificates.

## Decision

Corrected `docs/formalized-math-2026-08/07-the-cost-model-and-pareto-position.md`
in place, following doc 08's own convention: a dated correction block at the
top summarizing what moved, and per-section dated blocks that quote the
original text (struck through where superseded, e.g. the congruence-producer
paragraph) rather than delete it, so a later reader can see what was refuted
or confirmed and when. No claim in the document was found to be fabricated or
unsupported; the corrections are entirely "this has since moved" rather than
"this was wrong when written."

## What this does NOT change

The overall Pareto argument in §1-2 is untouched — it was checked and holds.
No fact was reclassified by this ADR; that is out of scope for a cost-model
audit and belongs to a lane working the ledger directly. The "labeled imports
never headline" invariant (ADR-0601 §3) and the axiom-ledger pair (30, all in
`axreal`) are re-confirmed, not re-derived from a different method.

## Open questions this measurement surfaces, not resolved here

- Whether `shape_search`'s 4.8% brief-time usage rises now that
  `brief-step0.py` runs it for the lane rather than asking; no before/after
  data exists yet because the tool is two days old.
- Whether the producer-contract registry grows past two contracts, and
  whether a wider registry actually raises the `fact-frontier.py`
  `admissible` count from 0, or whether the frontier's `no-registered-
  operation` gate (which 169 of 170 ready facts fail before a contract is
  even consulted) is the actual binding constraint and contracts are not yet
  the limiting factor.
