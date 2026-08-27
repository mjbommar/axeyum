# Lane: ledger-uc — register the fourth batch (uniform convergence, alternating series, polynomials, crossing)

<!-- plan-section: lane-status -->

**Your lane's block (`IN PROGRESS`, ledger-uc, 2026-08-27).** Registering
facts for Ch.24 (uniform convergence), Ch.22-23 (alternating series), Ch.20
(`CReal` polynomials), Ch.25-27 (`Complex` polynomials, factor theorem), and
Ch.14 (`CReal.meshScaledLeOfGe` / `CReal.crossingClose`) that were built by
sibling lanes but had no ledger entry.

Placeholder commit to satisfy "commit early" — this block is updated with
the final fact list, checker commands, mutation-test results and validator
total once the batch lands.

**Findings so far (existence checked against local `main` @ `aee64cc17`,
merged into this worktree):**

- `CReal.uniform_converges_add`, `Nat.even_or_odd`,
  `CReal.alternatingBracketUpper`, `CReal.alternatingLowerBound`,
  `CReal.alternatingUpperBound` do **not exist** in the merged tree.
  `Nat.even_or_odd` and `CReal.uniform_converges_add` exist as commits on
  OTHER, unmerged sibling branches (`worktree-agent-a71ce0189ae2e5688` /
  `worktree-agent-aa7767a7d63d9446e` for the former,
  `worktree-agent-a2562e3631adc1bf2` for the latter) but are not in `main` or
  `origin/main` as of this run, so per this lane's brief ("read freely, write
  nothing" / "if a declaration does not exist, that is a finding to report")
  they are not registered here.
- Everything else in the brief's list was confirmed present in the merged
  tree by grepping declaration names and, for theorems, by running
  `theorem_dependency_inventory` (exit 0 = found).
