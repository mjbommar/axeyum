# Lane: invariance-of-dimension — the index surgery lands, and the exchange's obstruction moves

<!-- plan-section: lane-status -->

**`AlgS.Index.*` and `AlgS.Exchange.*` — seventeen declarations, every footprint
empty — remove the obstruction ADR-1627 named, and relocate the one that stops
the Steinitz exchange** (`PARTIAL`, invariance-of-dimension, 2026-09-06,
ADR-1657).

## What this slice is

ADR-1627 landed `AlgS.Field`, `AlgS.VectorSpace`, `solve_smul` (the atomic
Steinitz step) and `basis_zero_unique` — invariance of basis number at length
zero — and named one obstruction for the general theorem: the exchange rewrites
the *indexing* of a coefficient family, and at the `AlgS` build position
`Nat.lt` and `Nat.beq` are undeclared.

That obstruction is gone. The exchange lemma itself is not landed, and its
remaining obstruction is a different one.

## Partition check

Run before proving anything.
`artifacts/structural-index/held-out-exclusion-manifest.json`,
`artifacts/autogenesis/nursery-v2-extension.json` and
`corpus/glaurung-proof-populations/` contain **no** occurrence of
`VectorSpace`, `Steinitz`, `dimension`, `exchange`, `linComb` or `basis`.
Coverage confirmed positively rather than by an empty grep: the nursery file
holds 579 `partition` rows (210 development, 220 held-out, 141 train) and both
manifest files were confirmed present and non-empty. **No target of this lane
is in a blind evaluation population.** No `F:ml430-*` id is cited anywhere in
this lane's output.

## What landed

Seventeen declarations across two new files.

`crates/axeyum-lean-kernel/src/nat_prelude/vector_space_exchange.rs` —
`AlgS.Index.*`, built from `Nat.rec` alone:

| name | kind | what it says |
| --- | --- | --- |
| `AlgS.Index.le` | definition | `m ≤ n`, the first order relation that exists at this build position |
| `AlgS.Index.removeAt` | definition | drop index `i`, shift the rest down |
| `AlgS.Index.insertAt` | definition | insert at index `i`, shift the rest up |
| `AlgS.Index.le_zero_eq` | theorem | `i ≤ 0 → i = 0` |
| `AlgS.Index.le_refl` | theorem | `n ≤ n` |
| `AlgS.Index.le_succ_right` | theorem | `p ≤ q → p ≤ succ q` |
| `AlgS.Index.le_dichotomy` | theorem | `(m ≤ n) ∨ (succ n ≤ m)` — totality |
| `AlgS.Index.le_succ_cases` | theorem | `i ≤ succ n → (i ≤ n) ∨ (i = succ n)` |
| `AlgS.Index.insertAt_at` | theorem | the inserted value sits where it was inserted |
| `AlgS.Index.insertAt_below` | theorem | below the insertion point nothing moved |
| `AlgS.Index.insertAt_above` | theorem | at and above it the family reappears shifted |
| `AlgS.Index.removeAt_insertAt` | theorem | delete what you inserted — unconditional |
| `AlgS.Index.insertAt_removeAt` | theorem | put back what you deleted — also unconditional |

`crates/axeyum-lean-kernel/src/nat_prelude/vector_space_steinitz.rs` —
`AlgS.Exchange.*`, where the index calculus meets `AlgS.Module.linComb`:

| name | what it says |
| --- | --- |
| `AlgS.Exchange.op_swap_last` | `(a·b)·c ~ (a·c)·b` in any `AlgS.CommGroup` — no module needed |
| `AlgS.Exchange.linComb_ext_below` | families agreeing below `n` give equivalent sums |
| `AlgS.Exchange.linComb_insertAt` | inserting a term at `i ≤ n` appends it to the sum |
| `AlgS.Exchange.linComb_removeAt_insertAt` | **the split ADR-1627 sized** |

Sixteen of the seventeen were admitted on first submission. Facts:
`F:algs-index-insertat-removeat`, `F:algs-exchange-lincomb-removeat-insertat`.

## The three calls worth reading (ADR-1657)

1. **Route (a) is not a route.** The brief offered "thread `Nat.lt`/`Nat.beq`/
   `Nat.ble` in as explicit `deps`" against "state the surgery over `Nat.rec`".
   A `dep` here is a `NameId` of a declaration already in the environment, and
   those four are interned about sixty lines *after* the whole `AlgS` block.
   Route (a) is a reordering of the shared prelude build, not a parameter.
   Route (b) is additive and gives all ten defining equations as ι-reductions.
2. **The surgery recurses on the INDEX; the fold recurses on the LENGTH.** Only
   the length induction closes; the `removeAt` form leaves
   `removeAt (succ i') c n'` stuck on a variable at every step. So the
   `insertAt` form is what is proved, and the `removeAt` form is a corollary one
   `trans` away because `insertAt_removeAt` is unconditional.
3. **Invariance of dimension is a theorem about TIGHT fields.** See below.

## What did NOT land, and the precise obstruction

**The Steinitz exchange lemma and invariance of dimension are not here.** The
obstruction is no longer index surgery.

The exchange step needs `u_j ~ Σ_{i<n} c_i w_i` together with *some* `c_i`
apart from zero, so `solve_smul` can solve for `w_i`. Independence of `u`
supplies only the negation `¬(∀ i, c_i ~ 0)`, and constructively that does not
yield `∃ i, c_i # 0`. `AlgS.Field.apartCotrans` does not help: it turns an
apartness into a disjunction, and there is no apartness to start from —
`AlgS.CommGroup` carries no apartness relation, so "`u_j` is apart from zero" is
not expressible on the vector side at all.

The route that does work runs the whole bound as a refutation
(`le (succ n) m → False`, resolved back by `AlgS.Index.le_dichotomy`, which was
proved in this lane for exactly that purpose). Inside the refutation one may
assume `∀ i, ¬(c_i # 0)` and must conclude `∀ i, c_i ~ 0` — which is
`AlgS.Field.IsTight`, deliberately a predicate and not a record field
(ADR-1627), because ℚ proves it and `CReal` cannot. So the honest general
statement is

```text
AlgS.Field.IsTight F -> IsVectorSpace F M smul ->
  linearIndependent u m -> spans w n -> AlgS.Index.le m n
```

and ℝ is not an instance of it. That is a mathematical fact about the shelf,
not a budget note.

## Sizing for the next lane

Three pieces, in order:

1. `linComb_smul` and `linComb_add` — linearity of the fold. Two straightforward
   `Nat.rec` inductions over `AlgS.Module.smulAdd`/`addSmul`, each about the
   size of `linComb_ext_below` (~150 lines of builder).
2. The one-step exchange: `spans w n`, `linComb c w n ~ x` and `c i # 0` give
   `spans (insertAt i x (removeAt i w)) n`. This is where
   `linComb_removeAt_insertAt` and `solve_smul` finally meet, and it is the
   largest single piece.
3. The outer induction in refutation form, resolved by `le_dichotomy`.

`AlgS.VectorSpace.dim` should NOT be declared until (2) and (3) land: a `dim`
whose well-definedness is unproved is a name asserting something the kernel has
not checked.

## Landed changes

| commit | what |
| --- | --- |
| `c85a12e8a` | `AlgS.Index.{le, removeAt, insertAt}` and six evaluation tests |
| `43d9d6cfb` | the eight index-surgery lemmas and two kernel-refused negative controls |
| `104e8f0a0` | `AlgS.Exchange.*`, the split, and the per-declaration admission harness |
| `c65c6bc00` | `le_succ_right` and `insertAt_removeAt` |
| `59f0e72e7` | clippy: hoist the `comm_group` index alias above the statements |
| `eed1b1979` | ADR-1657, two facts, and this status file |
| `07a1dbd5f` | rustfmt the index-surgery call site |
| `f268fb519` | merge main (173 commits) -- three conflicts, all in generated files |
| `f37947f12` | regenerate the four generated files after the merge |

## The merge

Main moved 173 commits while this lane was mid-wrap-up. `git merge --no-edit
main` conflicted in exactly three files, **all generated**: the frontier shape
census, the settled-fact statement pins, and the ADR index. Each was resolved by
taking main's side and re-running its generator, so this lane's rows are
re-derived rather than hand-merged into another lane's output -- a hand-merge of
two generators' outputs is how a stale half survives mid-file. `nat_prelude.rs`
auto-merged; both registration points and all four
`vector_space_{exchange,steinitz}` files are intact, and no other lane claimed
`AlgS.Index`, `AlgS.Exchange` or ADR number 1657.

`gen-plan.py` and `gen-py-prelude-fields.py` were re-run and wrote nothing:
PLAN.md had already auto-merged with this lane's block intact, and the
`axeyum-py` mirror is unaffected because these names are deliberately not
threaded into `NatPrelude`.

One correction worth recording. Before the merge, `check-merge-hygiene.sh`
failed on `kernel-dependency-projection staleness` (committed 4635, live 4754,
diff 119 > tolerance 100). That gate was **already red on main** -- this lane's
17 declarations account for 17 of the 119, and main's own drift was 102, over
tolerance on its own. Main regenerated the projection during the 173 commits,
so after the merge the guard reads `kernel_projection=ok` with no action from
this lane. Regenerating it here would have been a large-JSON conflict for
nothing.

## Gates

Every one re-run against the MERGED tree, exit status captured from the command
and not from a pipeline.

| gate | result | exit |
| --- | --- | --- |
| `cargo check --workspace --all-targets` | 0 errors | 0 |
| `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` | 0 errors | 0 |
| `cargo fmt --all --check` | clean | 0 |
| `cargo test --release -p axeyum-lean-kernel --lib -- nat_prelude::vector_space` | **25 passed**, 0 failed | 0 |
| `cargo test --release -p axeyum-lean-kernel --lib -- nat_prelude::nat_prelude_tests` | **249 passed**, 0 failed | 0 |
| `validate-facts.py` | 2956 facts, 0 errors | 0 |
| `check-settled-fact-statements.py` | settled 2682, pinned 2682, drifted 0 | 0 |
| `check-kernel-trusted-core.py` | 5 guards, 0 failures | 0 |
| `check-autogenesis-holdout-isolation.py` | held_out 206, references 0, PASS | 0 |
| `check-links.sh` | all links ok | 0 |
| `check-merge-hygiene.sh` | PASS, `kernel_projection=ok` | 0 |

The two kernel suites are the load-bearing ones and both report a NONZERO
count: a feature-gated suite that compiled to nothing would print
`running 0 tests ... ok` and exit 0.

## Mutation

All three RUN, and re-run a second time against the merged tree with identical
kill counts. Baseline: 25 tests, 25 passed, exit 0. Each mutant was applied,
built, run against the same 25-test collection, and restored byte-for-byte
(`git status` clean after each).

| mutant | change | pre-merge | post-merge |
| --- | --- | --- | --- |
| A | `removeAt`'s base case off by one: `v (succ j)` to `v j` | killed 18/25 | killed 18/25 |
| B | the split lemma's bound reversed: `le i n` to `le n i` | killed 7/25 | killed 7/25 |
| C | `le (succ i) zero` returns `True` instead of `False` | killed 18/25 | killed 18/25 |

No mutant is PREDICTED. Mutants A and C change a **`Definition`**, which the
trusted gate cannot object to -- the mutated `removeAt` still has exactly the
right type -- so their kills come from the evaluation tests and from the
downstream theorems whose `Eq.refl` stops holding. That is why this module has
evaluation tests at all. Mutant B is confined to `AlgS.Exchange` (7 of 25)
because the reversed bound is rejected where the split hands its hypothesis to
`linComb_insertAt`, and nothing in `AlgS.Index` depends on it; the 18 survivors
are the correct ones.
