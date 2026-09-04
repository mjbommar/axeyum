# 12 — The chair

Reviewer: the department head, doubling as an external referee
Verdict, 2026-09-04: **would sign the report, and would not let the coverage claim through**
Last measured: 2026-09-04 at `1856cdb3c`

> "Eleven colleagues, four favourable, three blocked on the same door, and one
> saying you have not written down what your kernel assumes. That is a healthy
> report. Now: what do you claim, and can a hostile reader check it?"

> **AUDITED 2026-09-04.** Every absence claim in this file was re-checked
> against a freshly rebuilt kernel index. See
> [AUDIT-2026-09-04.md](AUDIT-2026-09-04.md) for the evidence, and the
> corrections marked **[AUDIT]** below. Across the twelve files, 11 of 76
> absence claims were false and 12 more overstated the gap; the cause is that
> the ledger characterises only 38% of its proved facts and does not cover 430
> kernel theorems at all (ADR-1605).

## The persona

Does not do the mathematics. Reads the report, asks what is being claimed, and
asks whether an unfriendly reviewer could verify or deflate it in an
afternoon. Has seen many projects mistake volume for progress. Their two
questions are always the same: **what is assumed**, and **what did you do that
nobody else did**.

## What the ledger says

| metric | value | how it is read |
|---|---|---|
| proved propositions | 2,487 | `python3 scripts/validate-facts.py` |
| open (declared frontier) | 262 | mostly transcribed Mathlib propositions as a work queue |
| refuted | 4 | boundary refutations, a first-class status |
| conjectured / computed | 3 / 2 | Collatz; two four-colour Rado numbers |
| axiom footprint | empty on every proved row | `Kernel::axiom_footprint`, read from the environment |
| producer retirements | 67 hand proofs in one week (2026-09-03) | each re-admitted at a byte-identical type |
| validation errors | 0 | the ledger's own gate |
| kernel integration suites | 32 | `scripts/check-kernel-suites.sh --list` |

## The two questions

**What is assumed?** Nothing, on 2,487 results, and the claim is checkable in
one command by a hostile reader. That is the strongest thing in the report and
the chair would lead with it. The qualifications they would insist on stating
in the same breath: the kernel itself is a trusted base of about 155k lines
that nobody has proved consistent (see
[10-logic-and-foundations.md](10-logic-and-foundations.md), item 5), and the
empty footprint is a consequence of a design choice — no `Quot.sound`, no
`funext`, no choice — that four of the eleven reviewers identify as the thing
blocking their field. **The metric and the limitation are the same fact.** A
report that quotes one without the other is not honest.

**What did you do that nobody else did?** Three things, in the chair's order:

1. **The production route.** 67 theorems retired to machine producers in a
   week, each re-checked by a small kernel. Other libraries are written by
   people; this one is increasingly written by search and checked by a
   trusted core. That is a *rate*, and rates compound.
2. **The constructive real analysis.** Reviewer 02 says it is among the most
   complete anywhere, and that reviewer is the specialist. It is a genuine
   contribution independent of the tooling.
3. **The metatheory with an audited encoding.** Reviewer 10's point: proving
   excluded middle underivable in IPC, with the rule set read out of the
   kernel rather than assumed, is a real result about a real formal system.

## What they would not let through

- **Any coverage-parity claim against Mathlib.** Four reviewers report near-total
  absence in their fields (topology, algebra, classical analysis, category
  theory), and one reports that a theorem the library shares with Mathlib may
  be a *different statement* because of constructivity
  ([03-classical-analysis.md](03-classical-analysis.md)). The defensible claim
  is per-statement dominance plus uncontested axes, as the cost-model note
  already argues — not coverage.
- **Counting all 2,487 as equivalent.** A generated congruence lemma and
  quadratic reciprocity are one row each. The chair would want a weighted or
  landmark count reported beside the total.
- **The word "complete" about any shelf** other than, arguably, elementary
  number theory and constructive one-variable analysis.
- **Treating `computed` as `proved`.** Two Rado numbers are computed with
  certificates and are not theorems about defined objects. The ledger already
  distinguishes these and the prose must too.

## The department-wide finding

**One decision blocks four reviewers.** Algebra, category theory, and the
algebraic half of geometry are blocked on `Quot.sound` and `funext`; topology,
classical analysis, and probability are blocked on a topology design decision
and a classical-axiom policy. Those are **two ADRs**, and until they are
written, work in six of twelve fields is either impossible or speculative.

The chair's judgement: this is the highest-leverage item in the entire
department, it is a day of writing rather than a quarter of implementation,
and it has been deferred because the current metric does not punish deferring
it.

## Next five, in their priority order

- [ ] **1. The quotient and extensionality ADR.** Add `Quot.sound`, commit to
      setoid quotients, or admit it in a labelled second tier with separately
      reported footprints. Unblocks or scopes reviewers 04, 05, 06, 09.
- [ ] **2. The classical-axiom policy ADR.** Excluded middle as a labelled
      footprint entry, or as an explicit hypothesis discharged at use — the
      route `Nat.em_implies_lnp` already demonstrates. Unblocks or scopes
      reviewers 03, 08, 10.
- [ ] **3. A landmark count beside the total.** Define what counts as a named
      result, count them, and report both numbers. Their view: 2,487 is a real
      number that tells a reader nothing about depth, and the first hostile
      reviewer will say so.
- [ ] **4. Close one `computed` result into a kernel statement.** The Rado
      number is the flagship candidate. It converts the project's thesis from
      an architecture diagram into a demonstrated result.
- [ ] **5. Write down the kernel's own metatheoretic status**, per reviewer
      10. What is trusted, what is cross-checked against official Lean, and
      what a relative consistency result would require. Nobody outside can
      assess the headline metric without it.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: 2,487 proved / 262 open / 4 refuted, empty footprint throughout, 67 producer retirements in one week. Department-wide finding: two unwritten ADRs block six of twelve fields. | ledger snapshot at `1856cdb3c` |
| 2026-09-04 | **Next Five items 1, 3 and 5 landed.** W0-1 decided by measurement (ADR-1595, setoid quotients); the landmark count shipped as a registered checker with its own controls — 1,432 landmarks of 2,487 proved, 57.6%; ADR-1600 records the kernel's metatheoretic status. Item 2, the classical-axiom policy, remains the outstanding decision. Off-roadmap: the safety-matrix gate was found red on main since 2026-08-31 and regenerated. | `8b4f277d4`, `2a640c9b6` |

## How to re-measure

```sh
python3 scripts/validate-facts.py
cargo run --release -p axeyum-lean-kernel --example footprint_closure_audit
scripts/check-kernel-suites.sh --list
git log --since='7 days ago' --format=%s | grep -ciE 'retire|producer'
```

## Related

- [The cost model and Pareto position](../formalized-math-2026-08/07-the-cost-model-and-pareto-position.md)
  — why the claim is per-statement dominance, not coverage
- [README.md](README.md) — the full board and the shared snapshot
- [Computable knowledge](../research/00-orientation/computable-knowledge-world-graph.md)
  — where this library is proposed to go next
