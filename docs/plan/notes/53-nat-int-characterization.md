# Notes: 53-nat-int-characterization

Detail moved out of [`../status/53-nat-int-characterization.md`](../status/53-nat-int-characterization.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

18 theorems, every axiom footprint measured empty. Two things stop this from
being an unfalsifiable claim: the theorems are instantiated at structures we
actually have (a categoricity theorem whose premises nothing satisfies would be
axiom-free and worthless), and nine `Weakening` variants replace one hypothesis
with `True` and must each be refused **at the declaration they were aimed at**.
A guard-mutation check — disabling one injection — killed exactly one test.

**Also recorded here because it cost another lane 1,514 lines:** the per-lane
index protocol has a gap the written rule does not close. `git read-tree HEAD`
in one shell invocation and `git commit` in the next is not a refresh — HEAD
moved in between (`cf205e9a8`), and the bare commit from the stale private index
reverted it inside a commit whose stat otherwise looked exactly like the eleven
files staged. Repaired in `f532e04d3`. The operative rule: read-tree in the
**same invocation** as the commit, and read `git show --stat` for the file
*count*, not for the diff you were expecting.

**Next:** the ℤ existence half. It needs a map out of `Int` built from a target
ring's own data, which means either parameterising over a small ordered-ring
interface or constructing the comparison map from `natAbs` plus the sign split.
That is the one theorem standing between `F:int-characterization` and an `ℤ`
categoricity fact with the same standing as `F:nat-peano-categoricity`.
