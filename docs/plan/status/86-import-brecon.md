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
`reduce_rec` never consults it. It is deliberately **not** started here, because
sizing it turned up two things the reference code does not show: (1) the guard
is `is_def_eq(infer_type(major), …)` and the major is an **fvar**, so reduction
needs the `LocalContext` it currently never receives — ~55 internal call sites,
and `pub fn whnf` is public API with users outside the crate; (2) that makes
`whnf_cache`, keyed on `(env revision, ExprId)`, **context-dependent and
unsound** — `LocalContext::new()` restarts fvar ids at 0 and `check_declaration`
builds two fresh contexts with no environment change between them, so the cache
spans both. Settle the cache key before writing the rule. It also needs its own
negative suite (one-constructor `Prop` *with fields*, non-`Prop` structure,
mutual group must each stay non-reducible), since it asserts a definitional
subsingleton rather than a congruence. Recorded, not blocking: we lack
`to_cnstr_when_structure`, and `reduce_projection` uses full `whnf` where Lean
uses `cheap_proj` (ordering, not correctness).

Also fixed here, found in my own tool: `lean4export` **exits 0** on a constant
it cannot find, panicking to stderr and writing a metadata-only stream — which
the census scored as a *clean* stream. Both the script and the census example
now reject a declaration-free export instead of counting it as a pass.

<!-- plan-section: landed-changes -->

| 2026-08-15 | (pending) | `Proj`/`Proj` congruence in `def_eq` closes 9 of 10 root import blockers (40-stream census: 22→37 clean, 10→1 root); first-class decline census `census_ndjson`; pinned `Nat.add_comm` capability fixture. |
