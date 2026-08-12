# Session diary and roadmap — 2026-08-12

What happened when axeyum was pointed at a real mathematical frontier for a
day, what broke, what got fixed, and what to do next. Written as a diary
because the *order* of the discoveries is the useful part: several of the
most valuable findings only appeared because an earlier belief turned out to
be wrong.

Companions: the [result note](claim-ledger-and-rado-frontier-2026-08-12.md)
and the [findings register](findings-register-2026-08-12.md) (issue-by-issue
table with status).

---

## Part I — Diary

### 1. The premise

The question was whether axeyum could produce a genuinely new mathematical
result, end to end, with no external solver or checker in the trusted path.
Target: four-colour Rado numbers `R_k(a(x-y)=bz)`, where the published table
of Chang–De Loera–Wesley (ISSAC 2022) leaves thirteen coprime entries open,
one of them — `R_4(2(x-y)=3z)` — as a bare `> 225` with every neighbour
exact.

The shape suited the project: the answer is a threshold, so it needs *both*
a colouring (replayable by hand) and a refutation (only checkable by
machine). Exactly the untrusted-search / trusted-checking split.

### 2. First mistake: reaching for the sharpest external tool

The first working pipeline used **kissat and drat-trim**. It produced
`R_4(2(x-y)=3z) = 226` quickly, and a summary that said, approvingly, that
if you deleted `crates/` the result would still stand.

That was the wrong instinct, and it inverted the project's own ADR-0002:
external solvers are differential oracles, not the product. Everything after
this was redone through axeyum. The kissat/drat-trim runs survive only as
corroboration rows.

**Lesson:** the sharpest available tool is not the right tool when the
question is *what can this system do*.

### 3. The first real capability gap

Running the native proof core on the same instance, the process was
**OOM-killed at 27.6 GiB** after two and a half hours. The core retained its
entire DRAT proof in memory; reference solvers stream to disk.

Fixed the same day: a `DratSink` trait threaded through the core, a
`TextProofSink` proven byte-identical to `write_drat`, and a bounded-memory
streaming checker (**ADR-0381**, 18 tests). Measured on the same instance:
**1.9 GiB resident streaming vs 22.3 GiB in-memory**.

### 4. The finding that became the paper's thesis — and was wrong

Certification, not search, turned out to dominate. Per cube: refuted in
0.3 s, proof checked in 200 s. Another: 2.2 s against 1031 s. Ratios of
**470–670×**, with a plausible structural story (forward DRAT checking
rescans an accumulating clause DB, so cost is superlinear in proof length).

This was written into the paper as a finding: *checking, not solving, sets
the frontier*. An artifact policy was built on top of it — don't distribute
large certificates, because regenerating one costs under 1% of checking it.

Both were wrong, and the correction is §7.

### 5. What the discipline caught, repeatedly

Cross-checking rather than trusting produced most of the day's value:

- **A selection error of mine.** I claimed a closed form verified against
  "15 published values, zero mismatches". I had chosen the 15. The
  counterexample (`S(3,4)=45`, formula gives 41) sits in the source paper's
  own table.
- **A published-1966 result nearly claimed as ours.** A novelty audit traced
  the same formula to Znám (1966) through five later sources and OEIS — and
  established it is *false as an equality*, which two theses state in print.
- **A one-line arithmetic slip** (`ab+1` vs `a²`) propagated to a subagent
  before being caught.
- **Two agents "disagreeing"** — resolved by re-deriving both, not
  adjudicating: they had tested *different constructions*.
- **An unsound bound generator.** `predicted_lower_bound` returned values
  for `b > a` where the construction is invalid — 19/19 parameter triples
  defective. Guarded.
- **A contaminated artifact.** A restarted run appended to a live status
  file: 1093 rows, 69 duplicates. The cover checker caught it because it
  verifies the cover is *exactly* the product with no cell repeated.
- **My own gate refusing my own claim.** I marked a cover `checked` while
  224 of its 1024 cells were deferred. It rejected me. Correct.

### 6. The mathematics

Mining the SAT-found extremal colourings showed they are **a-adic valuation
strata**, not magnitude intervals (the interval hypothesis died on all 78
witnesses). Generalising Chang–De Loera–Wesley's k=3 valuation-plus-shells
colouring to nested two-ended shells gives, for `b = a-1`, an excess over
`a^k` of `a^(k-1) - 2a + 1` — which equals `(a-1)^2` exactly when k=3. The
published correction term was the **k=3 shadow** of something general. At
k=4, a=4 it is 57, matching `R_4 = 313`.

Verified by construction at 11 of 11 attempted points; it reproduces the
published 31, 73, 141, 241, 379, 103 and our 313.

Then it made a falsifiable prediction — `R_5(3,2) = 319` — and the solver
**refuted the tightness in 14.8 seconds** by finding a 5-colouring of [319].
The bound holds (it is a lower bound); its tightness stops at k=5. A failed
prediction, caught by the same machinery that produced it, is the best
illustration of the architecture the day produced.

### 7. The reversal

Late in the day, two things retired the §4 finding.

**First, a scheduling error.** Search and certification were running as one
job, so the slow half throttled the fast half. Separated — search with
checking disabled, proofs dumped to disk — a cover that had been 42% done
after 5.5 hours completed in **152.9 seconds**. About 460×.

**Second, the checker itself.** A backward (core-first) DRAT checker
(**ADR-0382**, 18 tests, differential fuzz against the forward one) measures
**66×** on a 200k-step proof and checks a 1.32M-step proof in 2.9 minutes —
the size class the forward checker could not finish in thirty. Check/solve
went from 470–670× to **2.0–2.6×**.

So the "frontier" was a property of one implementation choice, not of
certified combinatorics. The paper now says so, and **withdraws** the
artifact-distribution argument that depended on it. The forward checker is
retained unchanged as the small auditable reference; the new one is for
speed, not for trust.

**Lesson:** two orders of magnitude of evidence and a plausible mechanism
are not the same as a law.

### 8. Where it ended

Both values fully certified by axeyum alone — 8192 cells, ~250M proof steps,
zero failures, about eleven minutes of checking. The paper's completeness
gate, which had failed all afternoon by design, passes.

---

## Part II — Roadmap

Ordered by value per unit of work. Items reference the
[findings register](findings-register-2026-08-12.md).

### R1 — Close the "green gate over nothing" (A3) — *highest*

`Evidence::check` returns `Ok(true)` for `Evidence::Unsat(None)` and
`Unknown(_)`. A bare uncertified result therefore "passes the check". This
is the failure class CLAUDE.md is built around, sitting in the product's own
front door. Make it return a three-valued answer or refuse; audit callers.

### R2 — Promote the session's tooling into the workspace (F1)

The cube-and-conquer harness, the min-conflicts SLS, the certification
driver and the instance generator did most of the day's work and live in
`/tmp`. Nothing reproduces without them. This is the difference between *we
did this once* and *the system does this*. Suggested home: an
`axeyum-search` crate or examples under `axeyum-bench`, with the harness's
two known defects (B1 model flushing, B2 status-file clobbering) fixed on
the way in.

### R3 — Regenerate and re-certify the replication ledger (F6, B8)

Two defects, one fix. 35 of 37 claims record **drat-trim** as their checker,
contradicting the no-external-checker position — and, worse, an attempt to
re-certify them revealed that all 34 stored proofs are in **binary DRAT**,
which axeyum's `parse_drat` cannot read. Those certificates are currently
unverifiable by the system that ships them.

The fix is one job: regenerate each proof with axeyum's own proof-producing
core (which emits text DRAT), then verify with `check_drat_backward`. That
retires the external checker and the unreadable format together. Cost is
minutes now that A2 is fixed; the largest instances solved in ~130 s.

**This is a good argument for making the ledger's certificate format part
of the validated contract** rather than whatever the producing tool happened
to emit — the validator checks hashes and paths, but never that a stored
proof is in a dialect the checker accepts.

### R4 — Fix ground `IntDiv`/`IntMod` constant folding (A6)

Up to **49×** measured on semantically identical queries; converts solved
instances into timeouts. Also the direct cause of the quantified layer's
failure, so it likely unblocks A7 for free.

### R5 — Deadline and arena defects in the evidence front door (A4, A5)

`produce_qf_bv_evidence` ignores the caller's deadline for proof production;
`produce_evidence_smtlib` drops the arena so consumers cannot check their
own result without re-parsing. Both are small, both are correctness-adjacent.

### R6 — Iterate guarded universal expansion to a fixed point (A7)

Nested `∀x. G(x) ⇒ ∀y. H(x,y) ⇒ …` is refused though each layer is
individually supported. Would open the quantified formulation that failed
today.

### R7 — Backward-checker follow-ons (A8–A10)

Core-first propagation, LRAT emission from backward marking, proof trimming.
All recorded in ADR-0382 with their known obstacles.

### R8 — Wire `just claims` into CI (F2)

Once ADR-0380 is accepted. The ledger's three gates already pass locally.

### R9 — Connect the two knowledge graphs (F4)

math-education has 1,565 concepts with epistemic status and prerequisite
structure; axeyum's curriculum has 23 nodes with decidability classes. The
map is 68× larger than the routing table it should feed. Also: that repo's
148-misconception corpus is an untapped evaluation set for plausible-but-
wrong machine reasoning (F5).

### R10 — The mathematics that remains open (E1–E8)

`R_4(5,4) = 741`? (search-hard, not check-hard). No k=5 upper bound exists
for any member of the family. The general-k proof of the shell bound is
asserted in source and unverified. `b > a` at k ≥ 3 has no construction.

---

## Part III — What to carry forward

1. **Verify against all the data, not the data you chose.** The selection
   error is the most embarrassing thing here and the easiest to repeat.
2. **A plausible mechanism plus two orders of magnitude is still not a
   law.** Ask what would have to be true for the finding to be about your
   implementation rather than the problem.
3. **Separate the jobs that have different cost profiles.** Search and
   certification bundled together looked like a 300-core-hour wall; apart,
   it was minutes plus minutes.
4. **Gates that reject their author are the ones worth having.** Every
   validator that fired today fired on me.
5. **Record failed predictions as evidence.** The k=5 refutation is a
   better argument for the architecture than any success in the log.
