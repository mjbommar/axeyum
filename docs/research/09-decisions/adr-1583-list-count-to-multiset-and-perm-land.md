# ADR-1583: `List.count_toMultiset` lands, and `List.Perm` closes the sized negative ADR-1579 left open

Date: 2026-09-03
Status: Accepted
Lane: `list-carrier-2`

Index-summary: ADR-1579 recorded two sized negatives for the new `List`
carrier: `List.count_toMultiset` did not land (the named blocker was a
`Nat.beq`-to-`≠` bridge lemma), and `List.Perm`/`perm_reverse` were not
attempted. Both close here. The named blocker turned out not to exist:
`Nat.Multiset.count_singleton_of_ne` is already stated directly in terms of
`beq`, not `Not (Eq _ _)`, so no bridge lemma was needed at all —
`Nat.ne_of_beq_eq_false`/`Nat.beq_eq_false_of_ne` already existed in
`nat_prelude` (predating this lane) and were not even consumed.
`List.count_toMultiset`, two new prerequisites (`List.count_append`,
`List.count_reverse`), and `List.Perm` as a decidable `Bool` predicate with
all four requested theorems (`perm_refl`, `perm_symm`, `perm_reverse`,
`perm_append_comm`) land, every one with `Kernel::axiom_footprint = []`. Six
direction bugs — all the same `symm_of`'s-`(a,b)`-must-match-its-hypothesis's
-own-direction class this repository's own gotchas already name as the most
common bug here — were found and fixed by instantiating a proof step at free
fvars pushed into an explicit `LocalContext` and comparing `Kernel::infer_in`
against the expected type via `render_lean`, exactly the technique
`kernel-proof-engineering.md` prescribes. `List` is also registered in the
theorem/coverage ledgers and the two `shape_search`-style declaration/
dependency projections for the first time, closing ADR-1579's *other* sized
negative (no inventory registration) along the way.
Index-status: Accepted

## Context

ADR-1579 landed `List.{u}` as an ordinary universe-polymorphic inductive with
`length`/`append`/`map`/`foldr`/`reverse`, nine axiom-free theorems, and the
bridge definitions `List.toMultiset`/`List.count` — but recorded, as its own
"what did NOT land" section, that `List.count_toMultiset` was attempted and
abandoned: `bridge.rs`'s `declare_count_to_multiset` was written to
deliberately return `Err` rather than ship a stub, with the measured
obstruction named as "a bridge lemma from `Nat.beq head a = false` to
`head ≠ a`" to invoke `Nat.Multiset.count_singleton_of_ne`. `List.Perm` and
`perm_reverse` were marked "if time remains" in that lane's brief and not
attempted at all. Neither gap was hypothetical — `docs/plan/status/
460-list-carrier-1.md` names both explicitly as the next lane's starting
point, per this repository's own "a sized negative is a complete
deliverable" convention.

Separately, `List` was invisible to every cross-prelude inventory and search
tool: `prelude_theorem_inventory`'s `build_groups`, `kernel_declaration_
projection`'s group list, and `theorem_dependency_inventory`'s shared kernel
build never called `build_list_nat_bridge`, so `List`'s (then nine)
originated theorems were silently absent from every ledger's `distinct`
count and from `shape_search`-style lookups by name — the same "empty
answer from a tool never pointed at your subject" trap CLAUDE.md's own
gotchas document, just for a whole new prelude rather than an existing one.

## Decision

**Land `List.count_toMultiset`, `List.Perm`, and the four requested `Perm`
theorems, and register `List` in every cross-prelude inventory tool.**

### The named blocker did not exist

The blocker ADR-1579 recorded — a bridge from `Nat.beq head a = false` to
`head ≠ a` — is unnecessary because `Nat.Multiset.count_singleton_of_ne`'s
actual signature is

```text
Nat.Multiset.count_singleton_of_ne : ∀ a x, Eq Bool (beq x a) false →
  Eq (count (singleton a) x) 0
```

directly in terms of `beq`, not `Not (Eq Nat _ _)`. `Nat.ne_of_beq_eq_false`/
`Nat.beq_eq_false_of_ne` (the propositional `≠` bridge ADR-1579's own
"future lane" guidance pointed at) already existed in `nat_prelude`
(`nat_prelude/order_more.rs`, `nat_prelude/totient.rs`), predating this
lane, and this proof does not use either — only `Nat.beq_comm`, to flip the
`cons` case's own `beq head a` case-split hypothesis into the `beq a head`
shape the lemma wants. This is exactly the "before you build anything: does
it already exist?" gotcha, arriving as a blocker that had already dissolved
by the time it was checked rather than as a name search.

### `List.count_toMultiset`

`∀ a l, count a l = Nat.Multiset.count (toMultiset l) a`, by induction on
`l` (`a` fixed). The `nil` case is `Nat.Multiset.count_eq_zero_of_bound_le`
at `Nat.Multiset.zero` — `bound zero` is `0` by ι alone, so `Nat.zero_le a`
already has the type the lemma's hypothesis wants, with no extra step. The
`cons` case case-splits on `Nat.beq head a`, built via a fresh `Bool.rec`-
based `Or` split (`ops::bool_true_or_false_of`/`or_cases_of`, mirroring
`nat_prelude::ops::bool_true_or_false`/`nat_prelude::steps::or_cases`,
rebuilt locally because both are `pub(super)` to `nat_prelude` and not
reachable from `list_prelude`): the `true` branch transports `head = a`
(`Nat.eq_of_beq_eq_true`) through `Nat.Multiset.count_singleton_self`; the
`false` branch flips the hypothesis via `Nat.beq_comm` and applies
`Nat.Multiset.count_singleton_of_ne` directly. Both branches thread
`Nat.Multiset.count_add`, `Nat.succ_add`/`Nat.zero_add` (this prelude's
`Nat.add` recurses on its RIGHT argument, so `add (succ zero) y` and
`add zero y` do not reduce for symbolic `y` by defeq alone), and the
induction hypothesis to close the chain.

### `List.count_append` and `List.count_reverse` — the two prerequisites `List` did not have

Neither existed before this lane and both were needed for `List.Perm`:

- `List.count_append : ∀ a l1 l2, count a (append l1 l2) = add (count a l1)
  (count a l2)`, by induction on `l1`. Same outer shape as `bridge::
  declare_length_append`'s induction, but `count`'s `cons` case carries an
  extra `Bool.rec` on `Nat.beq head a` that `length`'s does not, so the step
  needs the same case split `count_toMultiset` built — unlike that proof, no
  `Nat.beq_comm` flip is needed here, because both sides of the goal split
  on the exact same `beq head a` term (no swapped-argument `Multiset.
  singleton` to reconcile).
- `List.count_reverse : ∀ a l, count a l = count a (reverse l)`, by
  induction on `l`. The `nil` case is `Eq.refl` (`reverse nil` is defeq
  `nil`). The `cons` case unfolds `reverse (cons head tail)` to
  `append (reverse tail) (singleton head)` (`theorems.rs`'s own `reverse`
  unfold), applies `count_append` to split that count into a sum, and closes
  with the same `beq head a` case split (needed again because
  `count a (cons head nil)` is itself `Bool.rec`-shaped) plus the induction
  hypothesis.

### `List.Perm` — reusing `Nat.Finset.allBelow` directly, not rebuilding an equivalent loop

```text
List.Perm l1 l2 := Nat.Finset.allBelow
  (fun a => Nat.beq (List.count a l1) (List.count a l2))
  (Nat.succ (Nat.add (List.max l1) (List.max l2)))
```

`List.max l := List.foldr Max.max Nat.zero l`. ADR-1577 declared `Nat.
Finset.allBelow : (Nat → Bool) → Nat → Bool` — a bounded `Bool`-valued
universal — together with its two reflection theorems (`allBelow_of_
all_true`, `allBelow_true_at`) as plain functions, not tied to `Nat.
Finset`'s own carrier data. `List.Perm` reuses them directly rather than
rebuilding an equivalent loop, which is exactly the "brief asked for the
`Nat.Finset.allBelow` shape" instruction this lane was given, taken
literally: the SAME function, not a lookalike.

**None of the four requested theorems needs `List.max` proved to be an
actual upper bound**, which was not obvious going in:

- `perm_refl`/`perm_reverse`/`perm_append_comm` all reduce to a pointwise
  count identity that holds unconditionally, for every `a` — `beq_refl`,
  `count_reverse`, and `count_append` + `Nat.add_comm` respectively.
  `allBelow_of_all_true`'s hypothesis is `∀ i, Lt i n → …`, and an
  unconditional pointwise proof discharges that for *any* `n` whatsoever, so
  the specific bound value never has to be reasoned about.
- `perm_symm` is the one exception: its hypothesis (via `allBelow_true_at`)
  only gives the pointwise fact below `bound(l1,l2)`, and the goal needs it
  below `bound(l2,l1)` — two different terms (`succ (add (max l1) (max l2))`
  vs. `succ (add (max l2) (max l1))`). Closed with `Nat.add_comm` plus a
  `succ` congruence proving `Eq (bound l1 l2) (bound l2 l1)` OUTRIGHT, then
  a new small combinator, `ops::transport_along` (`h : Eq ty p q`, `px :
  body(p)` ⊢ `body(q)` — the same `Eq.rec` shape `symm_of`/`trans_of`/
  `congr_of` already specialize, exposed directly because none of those
  three cover moving a `Lt a _` hypothesis across a proven bound equality),
  to transport the bound-membership hypothesis across it. This is the only
  place any bound-symmetry reasoning is needed at all.

The bound still has to be a GENUINE upper bound for `Perm` to compute the
right `Bool` at concrete lists, even though no theorem needs it proved so:
`List.max` is a real max-fold (not a placeholder), verified by the
requested negative controls computing correctly — `Perm [1,2] [2,1]` reduces
to `true`, `Perm [1,2] [1,2,2]` reduces to `false` (and explicitly not
`true`) — both by direct `def_eq`, not merely "some proof term type-checks".

### Six direction bugs, one family, found by the prescribed technique

Every `symm_of`/`congr_of`/`trans_of` call in this file takes explicit
`(a, b)` (or `(a, b, c)`) arguments that must match its hypothesis's OWN
`Eq` direction — not the direction the caller wants the *output* to read.
Six calls across `count_append`, `count_reverse`, and `perm_append_comm` had
this backwards (e.g. `symm_of(k, …, count_tail, m_term, hm_false, …)` when
`hm_false`'s actual type was `Eq m_term count_tail`, not the reverse) — the
exact "`x`/`x'` backwards is the single most common bug in this development"
family `kernel-proof-engineering.md` already names, just in `symm_of`'s
`(a,b)` position rather than a lemma instantiation's.

All six were found the way that document prescribes: rather than bisecting
by disabling declarations, `declare_count_append`'s `step` closure's return
value was checked directly, at the genuinely free (not yet abstracted)
`head`/`tail`/`ih`/`a`/`l2` fvars, by pushing each into an explicit
`LocalContext` with `Kernel::infer_in` and comparing the result against the
expected type via `Kernel::render_lean` side by side — the kernel's own
`TypeMismatch { expected: ExprId(…), got: ExprId(…) }` names neither side
by value, so this is the only way to see what actually differed. The first
fix (in `count_append`'s `true` branch) immediately made that specific
`step` type-check; the same technique, applied by hand-tracing every
remaining `symm_of` call's declared `(a,b)` against the ACTUAL type of the
hypothesis it was given, found the other five before ever running the
kernel again.

### `List` joins every cross-prelude inventory tool

`prelude_theorem_inventory.rs` gains an unconditional `list` group
(`build_list_nat_bridge` + `build_list_perm`, after `nat`);
`kernel_declaration_projection.rs` gains the same group, wired into its
`--require-declaration` search array (verified both directions:
`List.count_toMultiset`/`List.perm_symm` found, a nonexistent name errors
and exits 1); `theorem_dependency_inventory.rs` gains the same group into
its shared kernel build — this one mattered specifically for `check-fact-
depends-derived.py --fix`, which reads this tool's graph to derive a fact's
`depends_on` from its proof term: before this addition, `List.count_
reverse`'s direct use of `List.count_append` in its own proof was invisible
to that tool and `--fix` reported `missing_edges=0` for the wrong reason —
not because there was nothing to derive, but because `List` was outside its
coverage entirely, the same "zero from a tool never pointed at the subject"
trap that tool's own module doc already records once (for `Int`/`Rat`/
`Str`/`characterization`) and `prelude_theorem_inventory`'s own doc records
again (for `characterization`). `gen-theorem-production-ledger.py`'s
`EXPECTED_PRELUDES` and `gen-py-prelude-fields.py`'s `PRELUDES` table gain
`list` (alphabetically positioned, following the `ipc` precedent in the
first). `ListNatBridge`/`ListPerm` are deliberately NOT registered in
`gen-py-prelude-fields.py`: `ListNatBridge::count_to_multiset` is
`Option<NameId>`, a field type that generator's `collect()` does not
classify, and teaching it optional fields is out of this lane's scope — only
`ListPrelude` (all plain `NameId` fields) registers, with a matching
`build_list_prelude` PyO3 method added so the generated field-table function
has a real caller (an unregistered `kind` compiles to a `never used`
warning, which `-D warnings` turns into a build failure).

## What did NOT land

Nothing from this lane's assigned scope. The only limitation carried
forward is ADR-1579's own: `List.Perm` is ℕ-only (matches `List` itself,
which is genuinely universe-polymorphic but every operation and theorem in
this prelude fixes `u := 0`), and `List.Perm`'s own semantic correctness
(that the `Bool` it computes actually reflects the existence of a
permutation) is not itself a theorem here — only the four requested
algebraic properties (`refl`/`symm`/`reverse`/`append_comm`) are proved.
Nothing needed that stronger statement.

## Consequences

- `List`'s originated-theorem count rises from 9 (ADR-1579) to 17
  (`docs/plan/generated/theorem-production-ledger.md`); the ledger's own
  `distinct` figure rises 2340 → 2539 (17 of that from `list`, the rest from
  concurrent lanes' merges to `main` since the ledger was last regenerated —
  see `docs/plan/status/460-list-carrier-1.md`'s own note that this number
  was already stale independent of the `List` work).
- `Nat.Multiset` and `Nat.Finset` are unaffected: neither is redefined,
  neither loses a theorem, and `Nat.Finset.allBelow`/its two reflection
  theorems gain a second consumer (`List.Perm`) beyond `Nat.Finset.subsetB`/
  `beq` themselves.
- ADR-1579's "what did NOT land" section is now fully closed: both sized
  negatives recorded there (`count_toMultiset`, and no inventory
  registration) are resolved, and the "if time remains" `Perm` item is
  landed in full (all four requested theorems, not a subset).

## Alternatives considered

- **Represent the beq-to-ne bridge as a NEW lemma anyway**, since the brief
  asked for one. Rejected once measured: `Nat.Multiset.count_singleton_
  of_ne` does not need it, and building an unused lemma would be exactly the
  "re-deriving what existed" waste CLAUDE.md's own gotchas warn against —
  the finding (the blocker does not exist) is the deliverable, not a lemma
  nobody consumes.
- **Take the MAXIMUM of the two lists' maxima for `Perm`'s bound**
  (`Nat.Max.max`), rather than their SUM. Either works for `perm_symm`'s
  bound-symmetry step (`Nat.max_comm` exists alongside `Nat.add_comm`); SUM
  was chosen only because it needed one fewer distinct lemma family and
  matches `Nat.Finset.beq`'s own choice of width (ADR-1577) — not because
  MAX would have failed.

## Evidence

| what | where |
| --- | --- |
| `List.count_toMultiset` | `crates/axeyum-lean-kernel/src/list_prelude/bridge.rs` (`declare_count_to_multiset`) |
| `List.count_append`, `List.count_reverse`, `List.max`, `List.Perm`, and the four `perm_*` theorems | `crates/axeyum-lean-kernel/src/list_prelude/perm.rs` |
| the reused `Bool` case-split helpers, and the new `transport_along` combinator | `crates/axeyum-lean-kernel/src/list_prelude/ops.rs` |
| evaluation tests with negative controls, including `Perm [1,2] [2,1] = true` / `Perm [1,2] [1,2,2] = false` | `crates/axeyum-lean-kernel/src/list_prelude/bridge/bridge_tests.rs`, `crates/axeyum-lean-kernel/src/list_prelude/perm/perm_tests.rs` |
| the reused reflection theorems this bridges to | ADR-1577 (`Nat.Finset.allBelow_of_all_true`/`allBelow_true_at`) |
| the carrier and theorem list this ADR amends | ADR-1579 |
| cross-prelude registration | `crates/axeyum-lean-kernel/examples/{prelude_theorem_inventory,kernel_declaration_projection,theorem_dependency_inventory,list_theorem_inventory}.rs`, `scripts/gen-theorem-production-ledger.py`, `scripts/gen-py-prelude-fields.py`, `crates/axeyum-py/src/kernel.rs` |
| the seven registered facts | `artifacts/facts/F-list-{count-to-multiset,count-append,count-reverse,perm-refl,perm-symm,perm-reverse,perm-append-comm}.json` |

Verification: `cargo test -p axeyum-lean-kernel --lib -- list_prelude::` —
19 passed (was 11 after `count_toMultiset` alone, was 10 before this lane);
`cargo test -p axeyum-lean-kernel --lib -- nat_prelude::` — 422 passed,
confirming no regression; `cargo clippy -p axeyum-lean-kernel --all-targets
-D warnings` and `-p axeyum-py --all-targets -D warnings` both clean
(source-freshness-touched first). Axiom footprint `[]` for all seven new
theorems, read from `Kernel::axiom_footprint` via the tests' own coverage
checks. `python3 scripts/gen-theorem-production-ledger.py --check`,
`scripts/gen-ledger-coverage.py --check`, `scripts/gen-py-prelude-fields.py
--check`, `scripts/check-fact-depends-derived.py --check`, `python3
scripts/validate-facts.py` all exit 0. **Not run:** the full workspace
`--lib`/`--tests` sweep, `cargo deny check`, `just foundational-resources`.
