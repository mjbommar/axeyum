# axeyum-rewrite

Rewrite manifest contracts and denotation-preserving canonicalization for
Axeyum.

The default Phase 3 canonicalizer enables only exact-denotation rules:
Boolean/BV constant folds, simple Boolean identities, equality/ITE identities,
and BV zero/one/all-ones identities. Every rule is registered with a stable ID,
sort/width precondition, preservation classification, identity projection, and
required evaluator/oracle test routes.

Equisatisfiability-only rewrites may be recorded in a manifest while disabled,
but they must not be enabled by default until model projection is implemented
and replay-tested.
