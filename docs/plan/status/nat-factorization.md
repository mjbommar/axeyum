# Lane: nat-factorization — the computed prime factorization

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-factorization, 2026-09-02).**

`docs/plan/status/nat-multiset.md` handed off the COMPUTED form of prime
factorization and named one blocker: `prod (add m₁ m₂) = prod m₁ * prod m₂`.
All four targets landed, every declaration admitted on the FIRST attempt, all
axiom-free (`theorem_axiom_footprint`: `nat` is 905 theorems, 905 axiom-free,
footprint max 0).

**`Nat.Multiset.prod_add` (`multiset_prod.rs`).** The handoff named
`Int.prodRange_split` and `Nat.prodRangeIf` as untested candidates. **Neither
transports, and the reason is worth keeping**: `prodRange_split` splits ONE
function's fold at a point and leaves a *shifted* fold of the same function
behind, where what is needed is the upper half of each factor collapsing to
`1`; `prodRangeIf` is a selector whose only theorems are `_zero`, `_succ` and
`_congr_lt`, and none of them relates two bounds. So all three `prodRange` laws
are new: `prodRange_congr` (the Nat twin of `Int.prodRange_congr` — this kernel
has no `funext`, so a pointwise identity cannot be pushed under the fold by
rewriting the function argument), `prodRange_mul`, and
`prodRange_add_of_one_above`. The last is stated with the bound as `add k j`
rather than under a `Le k n` hypothesis because **`Nat.add` recurses on its
RIGHT argument**: `add k (succ m)` is `succ`-shaped for symbolic `k`, so the
induction goes on `j` and needs no `le_dest`.

**`Nat.minFac` divides, is at least 2, and is prime (`min_fac_dvd.rs`).** The
brief assumed `minFac_dvd` existed. It did not — `min_fac.rs` proved
MINIMALITY only, which a `minFac` returning a non-divisor satisfies VACUOUSLY,
and `shape_search --const Nat.minFac` returned exactly two theorems. Five
declarations closed the gap. Two things generalize:

- **State a fuel recursion's candidate as `succ cp`, not as a bare variable.**
  `Nat.div_mod_exec` requires its divisor expressed as a successor, and a bare
  fvar is stuck. `min_fac.rs` pays for this with a `pos_implies_succ_pred`
  unfold plus a transport back; quantifying over the predecessor from the start
  removes both.
- **`minFacAuxDvd`'s `add (succ cp) fuel = n` premise is load-bearing.** It is
  `min_fac.rs`'s module-doc argument turned into a hypothesis. Without it the
  statement is FALSE: `minFacAux 0 6 4 = 4`, and 4 does not divide 6.

**`Nat.factorization` and its two correctness theorems
(`factorization_multiset.rs`).** Trial division through `minFac` with fuel `n`.
Both hypotheses of `prodFactorizationAux` are load-bearing: `0 < n` rules out
`n = 0` (where the guard `n ≤ 1` is TRUE and the answer would be
`prod zero = 1`, so the statement is false without it), and `n ≤ fuel` makes the
fuel-exhaustion case VACUOUS rather than wrong. The pattern to reuse: **split
on `n` first and DERIVE the guard's Boolean value in each branch**, then
transport the goal along that one equation — splitting on the guard instead
demands a proof in the branch that cannot occur.

**Evaluation table**, every positive paired with the wrong value it rules out
(the trusted gate cannot tell a `Definition` is wrong, and `factorizationAux`
is one):

| term | value | negative control |
| --- | --- | --- |
| `count (factorization 12) 2` | 2 | NOT 1 (each prime divided out once) |
| `count (factorization 12) 3` | 1 | NOT 0 (stopped after the first) |
| `count (factorization 12) 5` | 0 | |
| `card (factorization 12)` | 3 | NOT 2 |
| `factorization 1` | `Multiset.zero` | NOT `singleton 1` (`minFac 1 = 1`) |
| `count (factorization 7) 7` | 1 | NOT 0 |
| `card (factorization 7)` | 1 | |
| `prod (singleton 3)` | 3 | NOT 0 |
| `prod {2,2,3}` | 12 | NOT 6 (repeat dropped) |
| `prod (add {2,2,3} {3})` | 36 | NOT 12 |

`prod_add ({2,2,3}, {3})` INFERS to `36 = 12 * 3` (not `12 = 12 * 3`);
`prod_factorization 12` to `12 = 12` (not `6 = 12`);
`factorization_prime (12, 2)` to primality of 2 (not of 4);
`min_fac_dvd 15` to `3 ∣ 15` (not `2 ∣ 15`, so the failed candidate really is
skipped); `min_fac_prime 15` to primality of 3 (not of 5 — 5 is prime AND
divides 15, so that control separates "the least factor" from "some prime
factor").

**Measurements.** `nat_prelude::` 353 passed, 0 failed (`--release`,
`--test-threads=4`). `python3 scripts/validate-facts.py` 2601 facts, 0 errors.
`scripts/check-fact-depends-derived.py` clean, `missing_edges=0` (9 facts,
41 edges derived). Clippy `-D warnings` clean on `axeyum-lean-kernel` and
`axeyum-py`.

**One incidental find worth knowing about.** `#[derive(Debug)]` on
`NatPrelude` crossed clippy's `large_stack_arrays` ceiling when this lane's 19
fields took the table past 1024. The derive lowers to
`Formatter::debug_struct_fields_finish`, which takes a `&[&dyn Debug; N]` —
N FAT pointers, 16 bytes each, so 1024 fields is exactly 16 KiB. The struct
itself is 4 bytes per field (`NameId` is a `u32`), so the `Copy` this table is
passed by is ~4 KiB; the 16 KiB frame exists only inside a `{:?}` call.
Suppressed at the derive with that reasoning written down. **Every other
prelude field table will hit this at its own 1024th field**, and `creal` is at
606 + 69.

**Not attempted.** `Nat.factorization` agreeing with any Mathlib definition
(ours is fuel-recursive linear search, so the `ml430` mirror-flip criterion
says no); a `prodRange_congr_lt` (bounded pointwise congruence — not needed
here); `Nat.Multiset.card` of a sum; and the multiplicity of a given prime in
`factorization n` as a closed form.

<!-- plan-section: landed-changes -->

| 2026-09-02 | nat-factorization | `Nat.Multiset.prod_add` plus the three general `Nat.prodRange` laws (`multiset_prod.rs`), the blocker `nat-multiset` handed off |
| 2026-09-02 | nat-factorization | `Nat.minFac` divides, is `>= 2`, and is prime — five declarations `min_fac.rs` did not have (`min_fac_dvd.rs`) |
| 2026-09-02 | nat-factorization | **`Nat.factorization` by trial division**, with `prod_factorization` and `factorization_prime` (`factorization_multiset.rs`) |
| 2026-09-02 | nat-factorization | eleven facts, each checker pinning the arity and the FULL rendered type (a name-only pattern is population-only) |
