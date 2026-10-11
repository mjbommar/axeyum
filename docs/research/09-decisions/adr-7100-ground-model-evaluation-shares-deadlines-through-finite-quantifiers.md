# ADR-7100: Ground model evaluation shares deadlines through finite quantifiers

Status: proposed
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
