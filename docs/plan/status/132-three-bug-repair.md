# Lane: three-bug-repair — arithmetic evidence and CAS regressions

<!-- plan-section: lane-status -->

**Three reported bug classes repaired (`DONE`, three-bug-repair, 2026-09-30).**
Reproduced the certified CLI crash with `distinct x y`, `x ≤ y`, `y ≤ x`;
step-integral unbounded enumeration with `floor(x)` over `[0, 10¹²]`; and
repeated-root factorization declining on expanded `(x − 40000)²`. These are
locally constructed reproducers; the original reporter's inputs were not supplied.

Arithmetic evidence checking now rebuilds the Boolean skeleton, atom propositions,
and signed theory literals from the supplied source assertions. Each lemma carries
its deterministic source-atom position, avoiding producer-arena term and symbol
handles. Both theory contradictions and propositional closure are still checked;
removed lemmas, satisfiable singleton cores, and a changed satisfiable source query
are rejected by regression tests. Same-arena `verify` remains a separate entry point.

CAS step splitting now declines before a range exceeds the existing periodic
splitter's 100,000-index span; checked endpoint arithmetic avoids cast-boundary
panics. Integration candidate finders run lazily, stopping at the first certified
antiderivative. Factorization detects exact polynomial squares before bounded
rational-root enumeration, recursively factors the square root, and certifies the
reassembled result without increasing root-search limits.

**Validation:** CAS library: 711 passed, 4 ignored; arithmetic DPLL library slice:
39 passed; independent-reparse evidence suite and negative controls: 3 passed;
CAS/solver clippy across all targets with solver `full` and warnings denied passed;
workspace formatting and diff whitespace checks passed. The original CLI reproducer
returns `unsat` with `certified=1 arena=ok`. Removing the CAS repairs makes the
factor regression fail and leaves the step regression running beyond a five-second
probe (terminated). No `just check`, workspace full gate, push, or remote CI claim.

**Resume:** apply any subsequently supplied original failing inputs as additional
regressions. The repairs cover the concrete cases above, not every integration
resource-exhaustion pattern or every factorization outside the rational fragment.

<!-- plan-section: landed-changes -->

| 2026-09-30 | (this commit) | Repair fresh-arena integer `distinct` evidence checking, bound definite step-integration enumeration and invoke candidate finders lazily, and recover exact repeated-root squares before the rational-root coefficient budget. Reproducer regressions and certificate negative controls pass. |
