# Diary — lane `import-brecon`, 2026-08-15

Continuing [`diary-formalized-collect.md`](diary-formalized-collect.md). That
lane measured 13 of 40 official Lean theorems admitted, attributed the largest
blocker cluster to `brecOn`/`below` reduction, and named this as the next task.

## 1. The census first, because the estimate was a guess

The brief carried a four-row table (structural recursion 8, `rfl` equations 7,
`HEq` 5, `noConfusion` 5) and said in as many words that it was that lane's best
reading, not a census. It was not a census, and the difference mattered.

A fail-closed importer reports the *first* blocker in a stream and stops, so the
table was built from 27 first-blocker samples. Two things it could not see:

- **How many of the 27 are the same root cause seen again.** A blocker in
  `Nat.zero_add._f` reappears in every stream that transitively needs
  `Nat.zero_add`.
- **How many are cascades.** When a declaration is refused, everything
  downstream fails with `UnknownConst`, which is not an independent blocker at
  all.

So the first thing I built was `census_ndjson` in `axeyum-lean-import`: the same
records through the same trusted gate, but a kernel decline is recorded and the
declaration **skipped** instead of stopping the stream. That is safe precisely
because it skips: the staging kernel still contains only declarations
`Kernel::add_declaration` accepted, which is *why* dependents of a skipped
declaration then fail with `UnknownConst` and are visible as cascades. Nothing
is published — `census_ndjson` returns counts, never a `Kernel`, never a
`CompletedImport` — so no caller can mistake a censused stream for an imported
one. Only `ImportError::Kernel` is recoverable; malformed bytes stay fatal,
because continuing past those would census a stream we did not read.

The corpus is also now written down (`scripts/lean-import-census.sh`). The
original 40 were not, so "13 of 40" could not be re-measured after a change —
which is the entire point of the exercise. Mine is 40 named `Init`/`Std`
declarations spanning `rfl` equations, recursor-encoded induction, `HEq`,
`noConfusion`, decidability, and a few needing no computation.

**The real census, before any change:**

| | |
|---|---|
| streams admitting completely | **22 of 40** |
| declaration records | 1255 |
| declines | 93 |
| **distinct root blockers** | **10** |
| distinct cascade declarations | 28 |

| cluster | root declines |
|---|---|
| structural-recursion body (`._f`) | 3 (`Nat.zero_add._f`, `Nat.succ_add._f`, `Nat.add_assoc._f`) |
| `rfl` equation of a `brecOn` function | 3 (`Nat.add_succ`, `Nat.mul_succ`, `Nat.pow_succ`) |
| other `TypeMismatch` | 2 (`Nat.succ_sub_succ_eq_sub`, `List.append_assoc`) |
| `noConfusion` auxiliary | 1 (`_private.Init.Prelude.0.noConfusion_of_Nat.aux._f`) |
| `HEq` elimination | 1 (`eq_of_heq`) |

Ten root causes, not twenty-seven blockers. Sixty-one of the ninety-three
declines were cascades. The `noConfusion` cluster the brief sized at 5 is **one**
declaration seen five times, and the `HEq` cluster of 5 is **one** declaration —
`eq_of_heq` — seen five times.

## 2. It was one missing rule, and it was not in the reducer

I expected to implement `brecOn`/`below` reduction. There was nothing to
implement: δ, β, ζ, ι and projection reduction already handle the whole
encoding. The probe (`nat_add_reduction_probe`) says so directly — WHNF of
`Nat.add n (Nat.succ m)` really does come back as

    Nat.succ ((Nat.rec … motive … m).1 n)

with the outer `succ` peeled off exactly as Lean's `brecOn` compilation
intends, and stuck only on `m`, a variable, where it *should* be stuck.

The failure was one level up, in `def_eq`. Narrowing to the smallest refused
pair:

    lhs head:  (Nat.rec … m).1
    rhs head:  (Nat.brecOn.go … m Nat.add._f).1

Two `Proj` nodes, same field, projected values one δ-step apart. Our checker had
`Const`/`Const`, `FVar`/`FVar`, spine congruence, function eta and structure
eta — and **no `Proj`/`Proj` congruence**. `def_eq_app` sees two bare `Proj`
nodes with empty spines and answers `false`. Lean has the rule
(`type_checker.cpp`, `is_proj(t_n) && is_proj(s_n) && proj_idx == proj_idx`);
our port dropped it.

That is the whole fix: `a.i ≡ b.i` when `a ≡ b` and the indices match.

**After, on the same 40:**

| | before | after |
|---|---|---|
| streams admitting completely | 22 | **37** |
| declines | 93 | 13 |
| **distinct root blockers** | **10** | **1** |
| distinct cascades | 28 | 8 |

One rule closed nine of the ten root blockers — every `._f` body, every `rfl`
equation, `noConfusion`, and both of the unclassified `TypeMismatch`es.
**`Nat.add_comm` imports**, with 52 declarations admitted and an empty Lean
axiom footprint. So does `Nat.mul_comm`.

The reason one rule covered clusters that looked unrelated is that they are not
unrelated: `noConfusion`, `match_n` auxiliaries and `casesOn` are all compiled
through the same `brecOn`/`below` machinery, and `below` is built from `PProd`,
so every one of them ends in a projection out of a recursor application.

## 2b. My own census tool had the repository's signature defect in it

One corpus entry, `not_not`, is Mathlib and not core. `lean4export` handles that
by **panicking to stderr and exiting 0**, having written a stream containing the
metadata record and nothing else. My script's `if ! (…)` never fired, the census
read one metadata record, found zero declines, and scored it a **clean stream**.
So the first run of the corrected corpus was 40 streams of which one had never
been exported at all, counted on the passing side.

The conclusion was not affected — the numbers below are re-measured with the
entry replaced by `Classical.not_not`, and before/after are unchanged except the
record count (1161 → 1255) — but the failure mode is exactly the one CLAUDE.md
warns about: *an empty result from a tool that was never pointed at your subject
is indistinguishable from a strong negative result.* It is now checked on both
sides. The script rejects an export whose stderr carries `PANIC` **or** whose
stream has fewer than two records; the census example gives a declaration-free
stream its own `EMPTY-NO-DECLARATIONS` bucket and an `empty_streams=` field, so
it can never land in `clean_streams`.

Worth stating plainly: exit status is not evidence here. `lean4export` returns 0
for a constant it could not find.

## 3. Why widening the trusted gate here is safe, and how that is pinned

This makes `Kernel::add_declaration` accept more, which is where a wrong
`proved` comes from, so the argument has to be stated rather than asserted.

`Proj` is a term former and definitional equality is a congruence: if `a ≡ b`
then `a.i ≡ b.i`. The rule cannot identify two terms that are not already equal
and cannot make a stuck term reduce. Its entire discriminating content is the
field-index comparison — drop that and it *would* identify distinct fields of
one structure.

So the index is what `tests/projection_congruence.rs` attacks. Five tests, and I
ran the control: with the rule disabled, the one positive test fails and **all
four negatives still pass**, which is what makes them soundness guards rather
than artifacts of the new code.

- different field index → refused, at `add_declaration` and not merely at
  `def_eq`;
- different projected value → refused;
- a projection whose recorded structure name is wrong → refused by projection
  *inference*. This one earns its place: `def_eq_proj` deliberately does **not**
  compare the structure name, matching Lean, and the justification is that
  inference already rejects a mislabelled projection so it can never reach
  def-eq inside an admitted declaration. That justification is now a test, not a
  comment.
- a *reducible* projection still selects the right field in both positions.

Unchanged and re-run: `cargo test -p axeyum-lean-kernel` (all suites green),
`nat_theorem_inventory` 119 theorems, `nat: axiom=0 opaque=0 quotient=0`,
`integer: axiom=1`, `scripts/check-lean-gate.sh` 12 suites / 49 tests / 112
real-Lean checks, `validate-facts.py` 96 facts 0 errors.

## 4. No new fact, deliberately

`Nat.add_comm` is the headline, and it is **not** a new fact. We already prove it
(`F:nat-add-comm`, `proof_route: kernel-lean`) and it is one of the 119 theorems
in our own Nat prelude. Landing an imported copy would understate what this
project holds — the same check that made the previous lane withdraw an imported
`Nat.not_succ_le_zero` after writing it.

What the stream is instead is a **capability fixture**:
`artifacts/lean-imports/nat-add-comm.ndjson`, pinned by SHA-256, `"fact": null`
in the manifest with the reason written out, and replayed by
`crates/axeyum-lean-import/tests/brecon_reduction.rs`. A capability regresses
silently; a fact does not need re-asserting.

## 5. The next binding constraint, named precisely

One root blocker remains on the 40: **`eq_of_heq`**, and it is not `HEq`
elimination as such. Reading Lean's proof term out of the export, the minor
premise of the `HEq.rec` requires

    cast α α h a  ≡  a        with `h : α = α` a *variable*

`cast` is `Eq.rec`, and with `h` a variable `Eq.rec` cannot ι-reduce. Lean gets
there by **K-like reduction** (`to_cnstr_when_K`, `kernel/inductive.h`): for a
single-family inductive **predicate** with exactly one constructor that has
**zero fields**, the major premise is replaced by that nullary constructor
whenever the premise's type is def-eq to the constructor's type — so `h`
becomes `Eq.refl α` and ι fires.

Our kernel already computes the predicate: `is_k_like_inductive` exists in
`lean_export.rs` and is used **only** to emit the wire `k` flag. `reduce_rec`
never consults it. So the next slice is small and well-specified: consult it in
`reduce_rec`, with the guard Lean uses (`infer_type` of the major WHNFs to an
application of the recursor's own inductive, build the constructor applied to
the parameters only, and require `def_eq` of the two types).

It is more soundness-sensitive than the projection rule — this one asserts a
definitional subsingleton rather than a congruence — so it wants its own
negative suite: a `Prop` with one constructor that *has* fields must not be
K-reducible, a non-`Prop` single-constructor structure must not be, and a mutual
group must not be (Lean excludes mutuals explicitly, "for simplicity").

**Two obstacles the next lane should know before starting, because I hit both
while sizing it and neither is visible from the reference code.**

*The guard needs a local context that reduction does not have.* Lean's guard is
`is_def_eq(infer_type(major), infer_type(nullary_ctor))`, and in `eq_of_heq` the
major premise is a **free variable** — so `infer_type` needs its type, which
lives in `LocalContext`, not in the environment. Our `whnf` /
`whnf_no_unfolding` / `reduce_rec` chain takes no context (Lean's type checker
carries `m_lctx` as a member; our port passes `ctx` explicitly and stops at the
`def_eq` layer). Without the context K-like reduction silently fails to fire
under binders, which is every case that matters. Threading it reaches ~55
internal call sites across `tc.rs`, `inductive.rs` and `quotient.rs`, and `pub
fn whnf(&mut self, e)` is public API with users in `axeyum-solver` and a dozen
test files, so it must stay and gain a `whnf_in`-style sibling.

*And that makes the WHNF cache context-dependent.* `Kernel::whnf_cache` is keyed
on `(env revision, ExprId)` — sound **today** precisely because nothing in
reduction consults `ctx` (`whnf_local_value` does, and is deliberately outside
the cache). K-like reduction breaks that: the same `ExprId` for an fvar reduces
differently depending on the fvar's type. And the contexts really do collide —
`LocalContext::new()` restarts `next_fvar` at 0, and `check_declaration` builds
**two** fresh contexts (one for the type, one for the value) with no environment
change between them, so the cache spans both. Either the cache key grows a
context identity, or K-reducible spines skip it. This is a soundness question,
not a performance one, and it should be settled before the rule is written.

Two further gaps are visible in the same reference function and are **not**
blocking anything on this corpus, recorded so they are not rediscovered:

- `to_cnstr_when_structure` — eta-expanding a non-constructor major premise of a
  non-recursive structure. We do not have it.
- Lean reduces projections with `whnf_core`/`cheap_proj` first so that `a.i =?= b.i`
  is tried as `a =?= b` *before* forcing either side. We use full `whnf` in
  `reduce_projection`. That is a performance ordering difference, not a
  correctness one, but it means our projection rule fires later than Lean's.

## 6. What I did not do

- No K-like reduction. It is the next task, sized above.
- No re-pin of the toolchain (4.30.0 → current). Still one decision made once,
  still not made.
- No Mathlib clone. The census is now cheap to re-run at any scale, which is the
  precondition that was missing, but the corpus that matters next is whatever
  exercises K-like reduction, not a bigger one.
