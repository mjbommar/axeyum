# Lane: import-brecon — making official Lean's structural recursion admissible

<!-- plan-section: lane-status -->

**The `brecOn`/`below` blocker is closed, and it was one missing congruence rule
(`WIP`, import-brecon, 2026-08-15).** Taking over
[`formalized-collect`](85-formalized-collect.md)'s finding, the census came
first, because a fail-closed importer reports one blocker per stream and the
handed-over cluster table was 27 first-blocker samples, not a census.
`census_ndjson` (new, diagnostic-only: declines are recorded and the declaration
**skipped**, so the staging kernel still holds only gate-accepted declarations,
and it returns counts — never a `Kernel`) over a corpus that is now *written
down* (`scripts/lean-import-census.sh`, 40 named `Init`/`Std` declarations) said:
**22 of 40 streams clean, 93 declines, but only 10 distinct root blockers** —
61 of the 93 were cascades, and the "5 `noConfusion`" and "5 `HEq`" clusters were
each **one** declaration seen five times.

Then the fix, which was not in the reducer. δ/β/ζ/ι/projection reduction already
handle the whole `brecOn` encoding — `whnf` of `Nat.add n (succ m)` really does
return `Nat.succ ((Nat.rec … m).1 n)`. `def_eq` was missing **`Proj`/`Proj`
congruence** (`a.i ≡ b.i` when `a ≡ b`), which Lean has and our port dropped; two
stuck projections one δ-step apart compared as `false`. After it: **37 of 40
streams clean, 1 distinct root blocker**, and **`Nat.add_comm` imports** (52
declarations, empty Lean axiom footprint). Nine of ten root blockers closed by
one rule, because `noConfusion`, `match_n` and `casesOn` are all compiled through
the same machinery and `below` is built from `PProd`. No new fact:
`F:nat-add-comm` is already ours on `kernel-lean`, so the stream is pinned as a
**capability fixture** (`"fact": null`) with a replay test instead.

Next: **K-like reduction** (`to_cnstr_when_K`), which is the single remaining
root blocker — `eq_of_heq` needs `cast α α h a ≡ a` with `h : α = α` a variable,
and only K-like reduction gets there. Our kernel already computes the predicate
(`is_k_like_inductive`) and uses it **only** to emit the wire `k` flag;
`reduce_rec` never consults it. It is more soundness-sensitive than the
projection rule (a definitional subsingleton, not a congruence), so it needs its
own negative suite: a one-constructor `Prop` *with fields*, a non-`Prop`
structure, and a mutual group must each stay non-reducible. Also recorded, not
blocking: we lack `to_cnstr_when_structure`, and our `reduce_projection` uses
full `whnf` where Lean uses `cheap_proj` (ordering, not correctness).

<!-- plan-section: landed-changes -->

| 2026-08-15 | (pending) | `Proj`/`Proj` congruence in `def_eq` closes 9 of 10 root import blockers (40-stream census: 22→37 clean, 10→1 root); first-class decline census `census_ndjson`; pinned `Nat.add_comm` capability fixture. |
