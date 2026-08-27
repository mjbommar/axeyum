# The ten `shape_search --duplicates` groups, adjudicated

Status: **closed for this pass** — one accidental duplicate found and fixed
(tiny, safe), nine groups confirmed intentional or confirmed a false positive
of the tool's own coarseness. Re-run after any future dedup work; the tool
still reports 10 groups by design (see "What the tool actually measures"
below).

## Why this note exists

ADR-0608's `shape_search --duplicates` mode reports 10 groups where two or
more declarations share an admitted *type shape*. The lane that built the
tool described these as "ten theorem pairs stating literally the same
proposition under two names." That claim is stronger than what the tool
measures — shape-equality is arity + head-symbol equality, not proposition
equality — so it needed checking against the actual statements and proof
terms, not the names or the shape. This is that check, group by group.

Command used throughout (release build, ~13-15s):

```sh
cargo run --release -q -p axeyum-lean-kernel --example shape_search -- \
  --include-constructed --duplicates
```

## Verdicts

| # | Shape | Declarations | Verdict |
|---|---|---|---|
| 1 | `Int.lt` | `Int.Characterization.zero_lt_one`, `Int.zero_lt_one` | (b) |
| 2 | `Rat→Rat→Rat→Nat→Nat→IsDistribution→PairwiseUncorrelated→lt→le` | `Rat.chebyshev_sampleMean_uncorrelated`, `Rat.weak_law_of_large_numbers` | (b) |
| 3 | `CPoint→CPoint→CPoint→CReal.Equiv` | `CPoint.apollonius_from_stewart`, `CPoint.apollonius_median` | (a), intentional |
| 4 | `CReal→Nat→CReal.le` | `CReal.rat_approx_upper`, `CReal.sampleUpperBound` | (a), accidental |
| 5 | `CReal→Nat→CReal.le` | `CReal.rat_approx_lower`, `CReal.sampleLowerBound` | (a), accidental |
| 6 | `Int→Int→Or` | `Int.Characterization.le_total`, `Int.le_total` | (b) |
| 7 | `Int→Not` | `Int.Characterization.discrete`, `Int.no_int_between` | (b) |
| 8 | `Nat→Nat→Eq` | `Nat.succ_sub_succ`, `Nat.succ_sub_succ_eq_sub` | (a), accidental — **fixed this pass** |
| 9 | `Nat→Nat→Eq→Eq` | `Nat.Peano.succ_injective`, `Nat.succ_injective` | (b) |
| 10 | `Nat→Nat→Nat.le→Nat.le` | `Nat.le_succ_succ`, `Nat.succ_le_succ` | (b) |

**4 of 10 are genuine duplicate propositions (a); 6 are deliberate
restatements under a second name (b); 0 are shape-only false positives (c)
in this batch** — every group that shares a *shape* here does turn out to
share the *same proposition*, which was not guaranteed going in (the brief's
own worked example, Chebyshev/WLLN, looked like a strong (c) candidate by
name and shape and is not).

### Groups 1, 6, 7, 9 — `characterization.rs`, deliberate (b)

`crates/axeyum-lean-kernel/src/characterization.rs`'s module doc states its
purpose directly: prove the constructed `Nat`/`Int` are pinned up to
isomorphism (Peano categoricity for `Nat`; no-junk + generation + discreteness
+ order for `Int`), because an empty axiom footprint says nothing about
whether the *objects* are the standard ones. Four of its bundled
`CharacterizationEntry` fields happen to restate ordinary prelude theorems
verbatim as part of that bundle:

```rust
// crates/axeyum-lean-kernel/src/characterization/nat.rs:176
let existing = dev.prelude().succ_injective;
let value = dev.kernel().const_(existing, vec![]);
dev.declare_theorem_u(names.succ_injective, vec![], statement, value)?;
```

```rust
// crates/axeyum-lean-kernel/src/characterization/int.rs:544-567
// discrete, le_total, zero_lt_one -- each: build the statement locally,
// then `let existing = dev.int_prelude().<name>; let value =
// dev.kernel().const_(existing, vec![]);`
```

This is not "two proofs of one fact" — it is **one proof term, re-exported
under a second name**, and the kernel re-typechecks that the independently
*re-derived statement* here matches the existing theorem's type (the point
of the exercise: confirming `Int.lt`, `Int.le`, etc. really do carry the
Peano/order-pinning content, not merely a same-named but weaker claim). Zero
duplicated proof effort, by construction. `--duplicates` cannot see this — it
compares types, and the whole point of `characterization.rs` is that two
different-looking bundles are asserting facts about the *same* type — so it
will always flag these four pairs. That is a tool limitation, not a defect
in the code.

**Group 2 (Chebyshev/WLLN) is the same pattern, not the shape-only
coincidence the brief predicted.** `rat_prelude/probability.rs:5279`'s doc
comment says it outright: *"a renaming, not a new result... The type is
IDENTICAL to `chebyshev_sample_mean_uncorrelated`'s, and the proof is a
direct forward to that theorem."* The proof term confirms it:

```rust
// rat_prelude/probability.rs:5352
let forward = d.lemma(
    p.chebyshev_sample_mean_uncorrelated,
    &[x, eps, pf, n, m, hd, hpw, heps],
);
// ...wrapped in eight nested lam_fv and returned as the whole value.
```

`weak_law_of_large_numbers` exists purely so a reader searching for "the weak
law of large numbers" finds a declaration under that name; it is a zero-cost
alias, same as the characterization pattern. **This is the group the brief
flagged as "almost certainly" a false-positive (c) by name and shape alone,
and it is not one** — worth noting because it shows shape-based guessing
about *which* groups are real duplicates is unreliable in both directions.

**Group 10** (`Nat.le_succ_succ`/`Nat.succ_le_succ`) is the same pattern
again, for a different reason: `nat_prelude/order_extra.rs`'s module doc
explains it restates a fixed set of lemmas under Lean-core's exact flat names
(`F:nat-order-lemma-census`'s twenty-name list), because an imported corpus's
proofs resolve against Lean-core spelling and this kernel's own name differs
(`le_succ_succ` here, `Nat.succ_le_succ` in Lean core). `succ_le_succ`'s body
is `d.lemma(p.le_succ_succ, &[n, m, h])` wrapped in one `lam_fv` — again a
thin alias, not a re-derivation.

### Group 3 — Apollonius, intentional (a)

`CPoint.apollonius_from_stewart` and `CPoint.apollonius_median`
(`crates/axeyum-lean-kernel/src/creal_point.rs`) prove the identical
statement — `∀ A B C, Equiv (add (distSq A B) (distSq A C)) (add (add (distSq
A M) (distSq A M)) (add (distSq B M) (distSq B M)))` — by two genuinely
independent proofs, and the file says so:

> `apollonius_from_stewart`... proved by doubling `stewart_median` and
> eliminating `distSq B M` via `midpoint_dist_sq_quarter`, **not** by
> re-running `declare_apollonius_median`'s own route. The two theorems were
> previously proved by independent algebra with nothing connecting them;
> this is the bridge, landed under its own name rather than replacing
> either.

So this *is* the "two proofs of one fact" shape CLAUDE.md warns about, but
it is deliberate: `apollonius_from_stewart` exists specifically to
cross-check that the `stewart_median`-based route and the direct coordinate
route prove the same thing, and is documented as intentionally landed beside
`apollonius_median` rather than replacing it. Flagging this as a defect and
deleting one side would remove the cross-check that is the point. Left
as-is; noted here so a future dedup pass does not "fix" it.

### Groups 4 & 5 — `rat_approx_{upper,lower}` / `sample{Upper,Lower}Bound`: the predicted case, confirmed

These are the pair the brief called "the one that looks most like a real
(a)," and it is — confirmed by reading both proof terms, not just the
shape:

- `CReal.rat_approx_upper : ∀ x n, CReal.le x (CReal.ofRat (Rat.add
  (CReal.seq x n) (Rat.natDivSucc 1 n)))` — `creal/density.rs:96`, first
  appears in the tree **2026-08-22** (`73b7a468f`).
- `CReal.sampleUpperBound : ∀ x m, CReal.le x (CReal.ofRat (Rat.add
  (CReal.seq x m) (Rat.natDivSucc 1 m)))` — `creal/uniform_continuity.rs:1335`,
  first appears **2026-08-26** (`49fa00986`).

Same proposition up to bound-variable renaming (`n` vs. `m`), each proved by
a genuinely separate derivation (`rat_approx_upper` via a `k`-indexed
regularity argument and `Rat.add_assoc`/`sub_le_of_le`;
`sampleUpperBound` via `regular`, `le_of_sub_le`, and a three-term
reassociation `radd3_move_middle_out`). No shared proof term. The mirror
pair (`rat_approx_lower`/`sampleLowerBound`) is the same shape and the same
finding.

**Both are load-bearing, in different modules:**

- `rat_approx_upper`/`rat_approx_lower` are used by `density.rs` itself
  (`witness_shrinks`), `completeness.rs`, and `ivt.rs` (the intermediate
  value theorem's threshold-crossing argument, twice).
- `sampleUpperBound`/`sampleLowerBound` are used within
  `uniform_continuity.rs`'s bucket-clamp machinery
  (`declare_bucket_clamp_upper`/`_lower`, `mesh`-adjacent lemmas).

This is exactly the documented hazard: a later lane (2026-08-26, building the
uniform-continuity/bucket-clamp apparatus) needed "x never exceeds its own
sample by more than 1/(m+1)" and did not find the four-day-older
`rat_approx_upper` that already states it, so it built an independent proof
under a new name. Per the repository's stated rule, the **older** one
(`rat_approx_upper`/`lower`, `density.rs`) is load-bearing outside its own
file (`ivt.rs`, `completeness.rs`), so it should stay canonical.

**Safe remedy (not applied — `creal/` is out of scope for this lane, six
kernel lanes are live there):** make `sampleUpperBound`/`sampleLowerBound`
thin restatements of `rat_approx_upper`/`rat_approx_lower`, the same pattern
already used four other places in this codebase (`characterization.rs`,
`weak_law_of_large_numbers`, `nat_prelude/order_extra.rs`'s `succ_le_succ`,
and this pass's own fix to `succ_sub_succ_eq_sub`, below):

```rust
// declare_sample_upper_bound, replacing the independent derivation:
let stmt = cle(d, p, x, embedded_target); // unchanged
let value = {
    let with_n = d.lam_fv(n_fv, nat_ty, d.lemma(p.rat_approx_upper, &[x, n]));
    d.lam_fv(x_fv, carrier, with_n)
};
```
(Exact variable names would need matching against `uniform_continuity.rs`'s
existing `m`/`n` usage; sketch only, not verified against the kernel — a
creal-lane task.)

### Group 8 — `Nat.succ_sub_succ`/`Nat.succ_sub_succ_eq_sub`: accidental, and fixed this pass

Unlike group 10 in the same file, `succ_sub_succ_eq_sub`
(`nat_prelude/order_extra.rs`, added to restate Lean-core's flat name for
`succ_sub_succ` — see the file's module doc, which describes exactly this
purpose for exactly this kind of pair) did **not** follow the file's own
established alias pattern. Before this pass its proof was a byte-for-byte
copy of `succ_sub_succ`'s own induction (`nat_prelude/algebra.rs:18`),
independently re-derived rather than reusing the existing proof term — the
"two proofs of one fact" hazard, landed by accident inside the very file
whose job is to avoid it.

`succ_sub_succ` (the older declaration, `algebra.rs`) is heavily load-bearing
(`choose.rs`, `catalan.rs`, `order.rs`, `vandermonde.rs`, `binomial.rs`, and
`algebra.rs` itself). `succ_sub_succ_eq_sub` had **zero** downstream
consumers anywhere in the crate outside its own name-list test entry
(`nat_prelude_tests.rs:814`) — confirmed by grep before touching anything.

**Fixed in this pass** (`crates/axeyum-lean-kernel/src/nat_prelude/order_extra.rs`),
by making it a thin restatement matching the rest of the file, exactly the
pattern `succ_le_succ` in the same file already uses two lemmas above it:

```rust
d.theorem(p.succ_sub_succ_eq_sub, 2, &|d, v| {
    let (n, m) = (v[0], v[1]);
    let sn = d.succ(n);
    let sm = d.succ(m);
    let lhs = d.sub(sn, sm);
    let rhs = d.sub(n, m);
    let stmt = d.eq(lhs, rhs);
    let proof = d.lemma(p.succ_sub_succ, &[n, m]);
    (stmt, proof)
})?;
```

Why this is safe: no signature or public-name change, no downstream
consumer to update (confirmed by grep, above), the admitted statement is
unchanged (`sub (succ n) (succ m) = sub n m`, same as before), and the change
is exactly the pattern three other declarations in this same file already
use for the same reason. Verified: `cargo test -p axeyum-lean-kernel --lib
nat_prelude::` — 95 passed, 0 failed, including
`every_nat_declaration_is_checked_and_axiom_free`; `creal::creal_tests::creal_prelude_builds`
still builds (33.5s, within the 36-41s recent reference range — the change
is outside `creal` so this is a smoke check that nothing global regressed);
`shape_search --duplicates` still reports the pair (expected — see below).

## What the tool actually measures, and what it does not

`--duplicates` matches on admitted *type shape* (conclusion head symbol +
hypothesis head symbols + arity), not on proof terms and not on
alpha-equivalence beyond bound-variable renaming within that shape. Two
consequences, both confirmed empirically this pass rather than assumed:

1. **It cannot distinguish an intentional thin-alias restatement from an
   accidental full re-derivation.** Groups 1, 2, 6, 7, 9, 10 are aliases
   costing one proof each; group 8 was a full re-derivation costing two,
   until this pass. All six report identically. Fixing group 8 does not
   remove it from `--duplicates`' output (confirmed: still 10 groups after
   the fix) — the tool would need to compare proof terms or at least detect
   "this value is `const_app`/`lemma` of that other declared name" to tell
   them apart. That is a real, describable refinement (walk the two
   `Declaration::Theorem.value`s and check whether one is a saturating
   application of the other's name) but it touches `shape_index.rs`, which
   carries 18 mutation-verified guards and is out of this lane's scope to
   churn — describing it here rather than building it, per the brief.
2. **Shape-equal did not turn out to mean proposition-unequal anywhere in
   this batch**, which is itself worth recording: the tool's positive
   predictive value on this run was 10/10 for "these two declarations state
   the same fact," even though shape equality alone cannot guarantee that
   in general (the brief's own hypothetical, "`CReal→Nat→CReal.le` is a
   very generic shape," is empirically two hits and zero misses here, not
   because the shape is narrow but because both real-analysis pairs
   happened to be literal duplicates).

## Does ADR-0608 or the design-review appendix overstate this?

The framing quoted in the brief — "ten theorem pairs stating literally the
same proposition under two names" — undersells the (b) cases rather than
overstating them: six of the ten are not proof duplication at all, they are
deliberate, zero-cost aliasing (a design pattern used independently in three
different files for three different reasons: categoricity bundling,
discoverability, and corpus-name matching). Calling all ten "duplication" to
a reader would suggest six declarations' worth of proof-maintenance burden
that does not exist. It is accurate that all ten pairs do state the same
proposition (verified above, group by group) — the overstatement, if there
is one, is treating "same proposition, two names" as inherently a hazard,
when six of the ten instances are exactly the safe form of that (one proof,
two names) and only three ever were the unsafe form (two independent
proofs: Apollonius by design, `rat_approx`/`sample*Bound` and
`succ_sub_succ_eq_sub` by accident, the latter now fixed).
