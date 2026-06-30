# Model

The model uses finite Boolean assignments over named variables.

The validator checks:

- `and-formula-sat-witness`: the listed assignment satisfies `p and q`;
- `excluded-middle-no-counterexample`: no assignment falsifies `p or not p`;
- `contradiction-unsat`: no assignment satisfies `p and not p`;
- `demorgan-equivalence-no-counterexample`: no assignment separates
  `not (p and q)` from `(not p) or (not q)`;
- `tiny-cnf-refutation`: no assignment satisfies every clause of
  `(p) and (not p or q) and (not q)`.

The validator is a small trusted replay checker for these finite artifacts. It
does not emit proof objects itself. The promoted `tiny-cnf-refutation` row is
also carried by a source-linked DIMACS artifact that the CNF regression uses to
exercise DRAT emission, LRAT elaboration, and independent proof checking.
