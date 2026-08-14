# agent-f — integration record

**Claim under test:** *in an integrated framework the precondition of a transform
can be enforced where it is applied, rather than living in a document beside it.*

**Verdict: supported, and the margin is larger than I expected — but only for
transforms inside the one registry that has an application point at all.** The
honest version of the claim is narrower than the one I was given, and the
narrowing is the interesting part.

---

## 1. What the conventional pipeline does here

The conventional shape is a preprocessing script — a Python driver, a `sed`
pass over `.smt2`, a bespoke encoder — that rewrites a formula and hands the
result to a solver binary. In that arrangement:

- the transform's assumptions are in the author's head, at best in a comment;
- the solver has no way to learn them, because it receives a *formula*, not a
  formula-plus-justification;
- every downstream stage then certifies the transformed formula perfectly. A
  DRAT proof of the wrong formula is a valid DRAT proof. A model of the wrong
  formula replays against the wrong formula.

That last point is the whole reason this task exists, and it is not a
hypothetical: agent-a hit it today in `axeyum-search`. `ColouringProblem`'s
colour-class ordering is sound only for interchangeable colours; for an
off-diagonal family it turned satisfiable `S(3;3,4,5)` at `n=41` into `unsat`,
and the resulting proof would have checked. The precondition was true and
written down and violated, all at once.

The conventional pipeline has no place to *put* the check. There is no shared
term representation between the script and the solver, so the check would have
to be re-derived from the emitted text. This is why such checks are not written:
not because nobody wants them, but because the seam has no vocabulary.

## 2. What integration actually bought

Three things, and they are separable.

**(a) A single application point.** `grep -n "report.record"` in `canonical.rs`
returns three lines, two of which are rule applications. Every rewrite the
canonicalizer will ever commit passes through those two. A guard placed there is
universal *by construction*, not by a convention someone must keep. This is the
part that is purely structural — it comes from the transform and its consumers
living in one program, and it turned what could have been a 57-site audit into a
two-line change.

**(b) An independent semantic reference in the same address space.** The
denotation guard evaluates `before` and `after` with `axeyum_ir::eval_with_memo`.
That evaluator is a different code path from the rewrite matcher, written for a
different purpose, and it is *right there* — no serialization, no subprocess, no
re-parsing. A split pipeline could do this only by shipping both terms to a
checker process and paying to encode them, which is precisely the cost that makes
people skip it.

**(c) Sharing that makes the check affordable.** This is the one I did not
predict. The naive guard re-evaluates each `before`/`after` pair and is quadratic
in formula size — genuinely too expensive to leave on. It becomes linear because
the term arena is immutable and hash-consed, so one `eval_with_memo` memo per
sample assignment can be carried across every application in the pass, and each
node is evaluated at most 4 times *in total*. The affordability comes from the IR
design (interning, immutability, `Copy` term IDs), not from the guard.

The measured consequence:

| | canonicalize | end-to-end (`qfbv-curated`, sat-bv, 2 s) |
|---|---|---|
| structural only | 0.363 / 0.379 / 0.414 s | 21.55 s, PAR-2 0.964 |
| + denotation guard | 0.806 / 0.853 / 0.883 s | 21.51 s, PAR-2 0.963 |

2.2x on the transform; nothing at all on the answer. Verdicts identical
(sat=9 unsat=24 unknown=10, DISAGREE=0 both ways). Because it was free, it
defaults on in release — which is the only place the wrong `unsat` would actually
ship. In a split pipeline this measurement is not even available: you cannot
compare "with check" and "without check" when the check has nowhere to live.

## 3. Where the claim does not reach — and this is the honest part

**Integration is necessary, not sufficient. The other ~20 transforms in the very
same crate are still unguarded.**

`axeyum-rewrite` exports roughly 20 public transformation entry points outside
the manifest — `eliminate_arrays`, `solve_eqs`, `elim_unconstrained`,
`blast_integers`, `expand_quantifiers`, `eliminate_int_divmod`, and the rest.
They are as integrated as the canonicalizer is: same crate, same arena, same
`TermId`s. They gained nothing from this slice.

The reason is not integration. It is that they have **no shared application
point**. Each is a whole-formula pass with its own traversal and its own commit
discipline; there is no `record()` for a guard to sit behind. Their preconditions
live in module doc comments, unevenly — `elim_unconstrained.rs:1-31` states
precondition, model soundness, termination and an explicit negative scope, while
`eliminate_int_divmod` introduces fresh `q`/`r`/`v` symbols and declares no model
route at all.

So integration supplied the *vocabulary* for the check (shared terms, a shared
evaluator, hash-consing) but the manifest supplied the *hook*. A framework that
is integrated but has no registry with an application point is exactly as
unguarded as a shell script — it just has better types while being unguarded.
That is a real limit on the claim and I would rather record it than round it off.

There is a second limit worth stating. Even inside the manifest, the guard is not
a proof. It samples 4 assignments; the sweep's second judge adds 40 more; a
denotation defect that hides from all 44 is not caught. `RewriteTestRoute::ProofObligation`
still has zero consumers. "Checked" is a long way short of "certified", and
Lean parity for the rewriter means certified.

## 4. The counterfactual, measured rather than asserted

The strongest evidence that the seam matters is what happens when the guard is
removed from it. Neutering `PreconditionCheck::check` and re-running the controls
produced, verbatim:

```
denotation guard did not refuse the wrong rewrite: Ok(CanonicalizeOutcome {
  term: TermId(3), report: RewriteReport { applications: [RuleApplication {
    rule_id: RewriteRuleId("control.denotation_violation.v1"), ... }] ... } })
```

`bvadd(x, 0)` became `bvnot(x)`. Well-formed, well-sorted, and wrong. Downstream,
nothing would have objected — that is the point of the control. 5 of 8 controls
fail this way; the other 3 test manifest data rather than the enforcement point
and fail under a different mutation, which I record because a control that passes
while testing nothing is this campaign's recurring failure mode.

## 5. What I would tell the next agent

- The application point is the asset. Before designing a check, find the line
  every instance of the thing passes through. If there isn't one, making one is
  the task.
- Do not restate the matcher as the guard. A structural precondition written by
  reading the match arms agrees with the match arms' bugs. I kept the operator
  scope deliberately coarse — read off the dispatch, one level up — and pushed
  everything finer onto an evaluator that shares no code with the rewriter.
  `T4.4-rule-ledger-patterns.md:29-30` already names this trap: "Dual
  representations are two sources of truth."
- Measure the guard's own coverage and fail on holes. `PreconditionAudit` reports
  `denotation_unavailable` precisely because a guard that quietly stops checking
  is indistinguishable from a guard that passes. Two controls assert the coverage
  number itself, one of them asserting that an array-sorted rewrite is counted as
  **unchecked** rather than as a pass.
