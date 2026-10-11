# ADR-7100: Ground model evaluation shares deadlines through finite quantifiers

Status: accepted; audited OMT contract adopted, final integration gates remain open
Date: 2026-10-11

Expose eval_within with the existing evaluator semantics plus an optional shared
deadline. Some(Value) is a completed result; None is resource exhaustion, not
false or undefined. Existing eval/eval_with_memo retain their signatures and pass
no deadline. Internal exhaustion uses a private evaluator label converted at the
public bounded boundary; other IR errors retain their existing meaning.

Poll before term visits, completion and finite quantified bindings, passing the
same deadline into fresh quantified sub-evaluations. Do not drop finite Bool/BV/FP
quantifier support to implement a deadline. Primitive arithmetic/string/operator
work is atomic and may overshoot before the next poll; this is cooperative
preemption, not a hard realtime guarantee. OMT portable checks must report budget
exhaustion distinctly and never accept a partially evaluated model.

## Adoption and later composition

The implemented bounded contract is adopted. Later ADR-6301/6302 bind finite
integer optimality evidence to the original query; ADR-7000/7100 carry shared
cooperative deadlines through intake and model replay. Earlier follow-up lists
above record the original increment and are superseded where these later
contracts supply the implementation. See the
[current validation receipts](../../plan/notes/28-wide-real-smtlib-writer.md)
and [completion audit](../../plan/user-feedback-completion-audit-2026-10-11.md).
Current fresh-native OMT suites and full-feature solver regressions cover
feasible/optimal/unknown/unsupported outcomes and changed evidence. A checked
affine recession witness, not search exhaustion, justifies unboundedness.
Gold remains false when strict-better evidence is absent; integer-cut, BV and
other unsupported certificate producers retain explicit declines. Shared
linearization/checking is not advertised as independent implementation or
kernel admission. Final workspace/all-target verification and main integration
remain open.
