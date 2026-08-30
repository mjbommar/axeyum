# Lane: cas-reconstruct — move ADR-0601's `kernel-reconstructed` count, and size what is left

<!-- plan-section: lane-status -->

**Your lane's block (`DONE this pass`, cas-reconstruct, 2026-08-28).**

`scripts/validate-facts.py`, before and after, run in this worktree:

```
cas-certificate: 29 total -- kernel-reconstructed 1, cas-internal 28
cas-certificate: 31 total -- kernel-reconstructed 3, cas-internal 28
```

**Nothing was relabelled and no checker was weakened.** The two new
`kernel-reconstructed` rows are CAS → kernel bridge tests that were authored,
passed, and were never registered in the ledger:

- `F:cas-ivt-degree4-sign-bracket-kernel-checked-cost-curve` —
  `rat_prelude::cas_ivt_bridge_tests::tests::ivt_sign_bracket_degree_four_kernel_checked`,
  `x^4-2` on `(1,2)`. `F:cas-ivt-sign-bracket-cbrt2-kernel-checked`'s own notes
  already cited this fact id; the fact did not exist.
- `F:cas-difference-of-squares-free-x-kernel-checked` —
  `complex::cas_bridge_tests::cas_verified_difference_of_squares_true_and_false`,
  `(x+1)(x-1) = x^2-1` at a **free** `x`, plus the CAS-refuted variant rejected
  by the same kernel.

Both were re-run here (1 passed each; 5.51 s and 123.77 s), and their
`checker_command`s were executed **verbatim, with `/usr/bin/grep`**, each
returning a count of `1`.

**The degree-4 kernel check was mutation-verified by this lane rather than
taken on the authoring lane's word.** Changing only the kernel-side bound from
the exact `14` to a wrong-but-true-looking `16` — `Nat.le 1 16` is itself a
true proposition, just not the one the reduced term inhabits — makes
`Kernel::add_declaration` reject with
`TypeMismatch { expected: ExprId(1577225), got: ExprId(1577239) }` and the test
FAIL; reverted, it passes again. So the kernel term asserts *what the CAS
computed* (`p(2) = 14`), not merely something well-typed. The mutation was made
and reverted inside this lane's own worktree, and `git status` was confirmed
clean afterwards.

Detail moved to [`../notes/223-cas-reconstruct.md`](../notes/223-cas-reconstruct.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | cas-reconstruct | `cas-certificate` `kernel-reconstructed` 1 → 3: registered two already-passing, unregistered CAS → kernel bridges; mutation-verified the degree-4 kernel check; measured the remaining 28 as a backlog, not a Richardson boundary |
