# ADR-1070: Gauss's lemma piece 3 -- two of five connecting-theorem items land, one shared with Euler's theorem

Status: accepted
Date: 2026-08-31
Index-summary: Three theorems land axiom-free toward Gauss's lemma's
connecting theorem (`a^m ≡ (-1)^gaussNegCount [pp]`, ADR-0970/ADR-0985/
ADR-0990's five-item piece-3 sizing): `Int.prodRange_const_pow` and
`Int.prodRange_scaledIndexEqPowMulFactorial` close item A
(`∏(a·k) = a^m·m!`) in full. The "product of signs equals `(-1)^count`"
item ADR-0990 flagged as having "no existing analogue found" closes via
`Int.gaussSignProdEqPowNegOneOfCount`, a one-line corollary of
`Int.prodRangeIf_const_eq_pow_count` -- this lane built that lemma
independently (as `Int.prodRangeIf_constEqPowCount` in `euler_theorem.rs`)
before discovering the `euler-spine` lane had landed the SAME proposition
on `main` first, in its own file `euler_prod_pow.rs`; the two statements
were confirmed identical (same arity, same `pred`/`a`/`n` binder order,
same `selector`/`prodRange` construction) and this lane's duplicate was
dropped in favor of the already-landed, already fact-registered one -- see
"Merge resolution" below. The remaining three items (a per-term `Nat`/`Int`
congruence bridge, `gcd(m!,pp)=1`, and the final assembly/cancellation)
are NOT attempted -- precisely sized below.
Index-status: accepted

## Context

ADR-0970/ADR-0985 landed Gauss's lemma's counting primitive and `a := 2`
closed form. ADR-0990 landed piece 1 (least-residue injectivity) and sized
piece 2 (the pairing lemma) without building it. ADR-1015 landed the
nonzero-residue lemma and unshifted injectivity, sizing the remainder of
piece 2. The `gauss-mapsinto-bound` lane (`ff27cf71f`, same day) completed
piece 2 in full: `gaussFold` is `InjectiveOn`/`MapsInto` on the shifted
`[0,m)` range, ready to feed `Int.prodRange_permute` directly.

Piece 3 -- the product-cancellation argument connecting `gaussNegCount` to
`a^m mod pp`, plus the `Nat`/`Int` carrier bridge -- was sized by ADR-0990
into five sub-items and explicitly left for its own session, "genuinely
larger than pieces 1+2 combined". This lane (`gauss-piece-3`) took that
session.

**Before writing any proof term, this lane verified ADR-0990's five-item
list against the tree, per the standing rule that a handoff's "what
remains" is a hypothesis, not an inheritance.** Two items had already been
substantially de-risked by unrelated work landed the same day:

- `Int.modEq_prodRange`/`Int.modEq_prodRange_lt` (a `ModEq`-over-a-product
  induction) already existed in `int_prelude/prod.rs` -- ADR-0990 had
  flagged this as "likely needs a prodRange-indexed induction of its own,
  NOT confirmed present".
- `Int.mod_eq_of_nat_mod_eq` (the `Nat.ModEq -> Int.ModEq` bridge for
  nonnegative values) already existed in `int_prelude/modeq.rs` -- ADR-0990
  had flagged the whole `Nat`/`Int` carrier bridge as "real work, not
  bookkeeping ... not yet checked against this specific need".

Neither is used directly by this session's landings (see "what remains"
below for where each still applies), but both change the sizing of what
remains, and are recorded here so the next lane does not re-derive their
absence.

## Decision

**Land item A in full (two theorems) and the sign-product item in full
(two theorems, one built generically for a sibling target); do not attempt
the remaining three items, size them precisely instead.**

### Landed: item A, `∏(a·k) = a^m·m!`

Two theorems, `int_prelude/prod.rs` and the new
`int_prelude/gauss_factorial_product.rs`:

- `Int.prodRange_const_pow : ∀ a n, Eq Int (prodRange (fun _ => a) n) (pow
  a n)`. Induction on `n`; no case split anywhere -- both
  `prodRange (const a) (succ j)` (via `prodRange_succ`) and `pow a (succ
  j)` (via `pow_succ`) reduce to the identical `mul (...) a` shape by pure
  `refl`, so the successor step is a single `icongr` on the induction
  hypothesis.
- `Int.prodRange_scaledIndexEqPowMulFactorial : ∀ a m, Eq Int (prodRange
  (fun k => mul a (ofNat (succ k))) m) (mul (pow a m) (factorial m))`. No
  induction at all: `Int.prodRange_mul` at `f := const a`, `g := fun k =>
  ofNat (succ k)` (the EXACT lambda `Int.factorial`'s own `Definition`
  body uses) splits the scaled product; `prodRange_const_pow` collapses
  the `f`-half to `pow a m`; the `g`-half is defeq `factorial m` with no
  rewrite, since `g` is built identically to `factorial`'s internal term.
  Two `icongr`/`ichain` calls, no case split.

Both admitted by the kernel on the FIRST attempt -- no `TypeMismatch`
iteration needed for either.

### Landed: the sign-product item -- and a same-day collision with `euler-spine`

`euler_theorem.rs`'s own module doc names its "final assembly" gap's first
bullet as `prodRangeIf pred (fun _ => a) n = pow a (countRange pred n)`,
needed for Euler's theorem. Reading `nat_prelude/gauss_lemma.rs`'s module
doc alongside it, this is the EXACT shape Gauss's lemma needs at `a := -1`
-- so this lane built it once, generically, inline in `euler_theorem.rs`,
intending it to serve both targets rather than duplicating it. Admitted by
the kernel on the first attempt after one scratch draft was discarded.

**That construction was a genuine duplicate.** The `euler-spine` lane had
independently built and landed the SAME theorem on `main` (branched before
this session started, merged to `main` afterward, not visible until this
session's `git merge main` pulled it in): `Int.prodRangeIf_const_eq_pow_count`
in its own file `int_prelude/euler_prod_pow.rs`, with a fact already
registered (`F:int-prodrangeif-const-eq-pow-count`). Same Rust struct
field name (`prod_range_if_const_eq_pow_count`), two different kernel name
strings (`euler-spine`'s `"prodRangeIf_const_eq_pow_count"` vs. this
lane's `"prodRangeIf_constEqPowCount"`) -- a `DeclarationExists` collision
on merge, invisible to `git` because the two declarations sat far enough
apart in the struct to merge textually clean.

**Resolution, checked signature-by-signature before deciding, not assumed
from the name:** `euler_prod_pow.rs`'s statement is `∀ pred a n, Eq Int
(prodRange (selector pred (fun _ => a)) n) (pow a (countRange pred n))`
-- IDENTICAL proposition to this lane's (same `selector`/`bool_select_int`
construction, same `Int.pow`/`Nat.countRange` pairing), same arity (3:
`pred`, `a`, `n`), same Pi-binder order (`pred` outermost, `a`, `n`
innermost -- confirmed by reading the `Pi`/`lam` nesting in `declare_theorem`'s
`ty`/`value` construction, not inferred from the argument list). So this
lane's inline construction (the helpers `bool_true_or_false_int`,
`select_nat_true_local`, `select_nat_false_local`, `const_int_fn`, and the
function `declare_prod_range_if_const_eq_pow_count`, all in
`euler_theorem.rs`) was DELETED in favor of `euler_prod_pow.rs`'s already-
landed, already fact-registered version -- along with the now-unused
`select_int_true`/`select_int_false` import. `int_prelude.rs`'s field now
points at `euler-spine`'s kernel name string,
`"prodRangeIf_const_eq_pow_count"`.

Because the arity and binder order matched exactly, every downstream
consumer needed NO changes: `Int.gaussSignProdEqPowNegOneOfCount`'s
`d.lemma(p.prod_range_if_const_eq_pow_count, &[pred, neg_one, m])` call and
this lane's own test applying the theorem at concrete `pred`/`a`/`n`
continued to work unchanged against the surviving declaration.

`Int.gaussSignProdEqPowNegOneOfCount` itself (new file
`int_prelude/gauss_sign_product.rs`) is unchanged: a one-line corollary,
applying `Int.prodRangeIf_const_eq_pow_count` at `pred := fun j =>
Nat.gaussSignNeg pp a (succ j)` (the identical lambda `Nat.gaussNegCount`'s
own `Definition` uses, so `Nat.countRange pred m` is defeq `gaussNegCount
pp a m`) and `a := neg one`.

### Verification (post-merge, against `main` including `euler-spine`)

`cargo test -p axeyum-lean-kernel --lib int_prelude::` -- 56 passed, 0
failed (this lane's four tests all present and green; the count is a
coincidence of this merge -- `euler-spine`'s own commits added tests
elsewhere in the crate that are not all under the `int_prelude::` prefix,
and this lane's duplicate-construction deletion removed no test of its
own, since the surviving `euler_prod_pow.rs` carries no dedicated test and
this lane's `prod_range_if_const_eq_pow_count_computes_and_rejects_an_off_by_one_exponent`
remains the only direct coverage of the shared theorem). `derived_laws`
pinned array recounted 227 -> 229 post-merge via
`scripts/recount-pinned-inventory.py` (two entries: `euler-spine`'s own
addition plus this lane's now-single, no-longer-duplicated entry for the
shared theorem). `cargo test -p axeyum-lean-kernel --lib nat_prelude::` --
268 passed, 0 failed (up from 263 pre-merge, `main`'s `avg_pair`/`minmax`
additions; `gauss_lemma.rs` itself was touched by `main`'s workspace
clippy repair, `579db7e02`, and merged with no conflict and no test
regression). Four concrete instantiation tests remain (one per this
lane's landed theorem, each checked against a hand-built direct
computation AND the general theorem's own instantiation, per the standing
rule that a symbolic accept and a concrete check fail on disjoint defect
classes):

- `prod_range_const_pow_matches_direct_computation` (`a := 3, n := 4`, both
  sides = 81).
- `prod_range_if_const_eq_pow_count_computes_and_rejects_an_off_by_one_exponent`
  (`pred` selecting 2 of 5 indices, `a := 2`, so `pow a count = 4 != a` --
  discriminates an off-by-one exponent, the single most likely defect in a
  `pow`/`countRange` pairing induction; paired with a negative control the
  trusted gate must refuse).
- `gauss_sign_prod_eq_pow_neg_one_of_count_matches_direct_computation_at_pp_11_a_2_m_5`
  (`gaussNegCount 11 2 5 = 3`, ODD, so the product genuinely is `-1` rather
  than the `+1` a parity bug would give; the intermediate count is checked
  independently of the final sign).
- `prod_range_scaled_index_eq_pow_mul_factorial_matches_direct_computation_at_a_2_m_3`
  (`2*4*6 = 8*3! = 48`).

`derived_laws` pinned array recounted 223 -> 227 across this lane's four
pre-merge commits, then 227 -> 229 once more after the merge (above), via
`scripts/recount-pinned-inventory.py` every time (never hand-incremented).
`cargo clippy -p axeyum-lean-kernel --lib -- -D warnings` is CLEAN
post-merge -- the 8 pre-existing errors this lane's earlier commits noted
(none in this lane's own files) were fixed by `main`'s own workspace
clippy repair, `579db7e02`, pulled in by this merge.

## What remains -- three items, precisely sized

Once these land, the connecting theorem's classical proof is:

```
a^m · m! = ∏(a·k)                              [prodRange_scaledIndexEqPowMulFactorial, symm]
         ≡ ∏(ε_k · gaussFold(pp,a,k)) [pp]      [per-term congruence, NEW -- below]
         = (∏ε_k) · (∏gaussFold(pp,a,k))         [Int.prodRange_mul]
         = (-1)^gaussNegCount(pp,a,m) · m!       [gaussSignProdEqPowNegOneOfCount landed here;
                                                    ∏gaussFold = m! via prodRange_permute + piece 2]
⟹ a^m ≡ (-1)^gaussNegCount(pp,a,m) [pp]          [cancel m!, needs gcd(m!,pp) = 1]
```

### 1. The per-term congruence: `a·k ≡ ε_k · gaussFold(pp,a,k) [pp]`, for `k = 1..m`

Where `ε_k := -1` if `gaussSignNeg pp a k` else `1`. By cases on
`gaussSignNeg pp a k`:

- **Not negative**: `leastResidue pp a k ≤ m`, and `gaussFold pp a k =
  leastResidue pp a k` by definition, so `a·k ≡ leastResidue pp a k =
  gaussFold pp a k = 1 · gaussFold pp a k [pp]` -- `mod_self_congr`
  (`group.rs`, already `pub(super)`, used by piece 1) plus `mul_one`.
- **Negative**: `gaussFold pp a k = pp - leastResidue pp a k`, so
  `leastResidue pp a k = pp - gaussFold pp a k`, and `a·k ≡ leastResidue pp
  a k = pp - gaussFold pp a k ≡ -gaussFold pp a k [pp]` (since `pp ≡ 0
  [pp]`) `= (-1) · gaussFold pp a k`.

This needs the `Nat`/`Int` bridge (`Int.mod_eq_of_nat_mod_eq`, CONFIRMED
present this session, contrary to ADR-0990's "not yet checked" note) to
lift the `Nat.ModEq` reasoning above into `Int.ModEq (ofNat pp) (ofNat
(a*k)) (ε_k * ofNat (gaussFold pp a k))` -- both `a*k` (`Nat`) and its
`Int` lift `ofNat (a*k)` need to match the STATED `prodRange`'s `Int`-typed
factor `mul a (ofNat (succ j))`, so a `Nat.mul`-to-`Int.mul` distribution
lemma (`Int.of_nat_mul`-shaped; check `nat_abs.rs`/`defs.rs` for an
existing name before building one) is also needed at this step, not
flagged by ADR-0990 at all -- found while re-deriving the route for this
ADR, not yet checked against the tree.

**Estimated size**: comparable to `gauss_fold_injective_of_coprime`
(ADR-1015's landed piece, ~150 lines), since the case split and the
transport machinery are the same shape; the `Nat.mul`-to-`Int.mul` step is
new and unsized.

### 2. `gcd(factorial-as-Nat m, pp) = 1`

Needed to cancel `m!` from the final congruence. `Int.factorial` is
`Int`-typed (`prodRange` over `Int`); this coprimality is naturally a
`Nat`-typed fact about SOME `Nat`-typed accumulation agreeing with
`natAbs (factorial m)`, or built directly over `Int.factorial` via
`Int`-typed `gcd`/coprimality (check whether `int_prelude` has its own
`Coprime`/`gcd` distinct from `Nat`'s -- `wilson.rs`'s existing coprimality
reasoning, e.g. inside `factorial_pos`/`self_inverse_mod_prime`, is the
first place to check before assuming a `Nat`-side detour is needed).

Route, checked against confirmed-present lemmas: induction on `m`. Base
`gcd(1,pp)=1` trivial. Step: `gcd(k!,pp)=1` (IH) and `gcd(k+1,pp)=1` (from
`pp` prime and `k+1 < pp`, via `Nat.coprime_of_lt_prime`, confirmed present
by ADR-0990) combine via `Nat.coprime_mul_of_coprime : gcd x m = 1 → gcd x
n = 1 → gcd x (m*n) = 1` (confirmed present, `totient_multiplicative.rs`)
applied at `x := pp, m := k!, n := k+1` (after `gcd_comm`, since
`coprime_mul_of_coprime`'s first slot is the FIXED factor and `pp` is what
stays fixed here) to give `gcd(pp, (k+1)!) = 1`, i.e. `gcd((k+1)!,pp)=1`
after `gcd_comm` again.

**Not yet checked**: whether this needs to route through a `Nat`-typed
factorial mirror (built once, purely as this proof's scaffolding, since
`Int.factorial` cannot feed a `Nat.gcd` argument directly) or whether an
`Int`-typed coprimality primitive already exists that avoids the detour.
**Estimated size**: ~40-60 lines if a `Nat`-side factorial detour is
needed (one small new `Nat.factorial` mirror plus the induction above);
smaller if an existing `Int`-coprimality route is found.

### 3. The final assembly

Chains item A (symm), the per-term congruence lifted through
`Int.modEq_prodRange_lt` (CONFIRMED present this session, see Context --
ADR-0990 had marked this "not confirmed present, likely needs its own
induction"), `Int.prodRange_mul` to split the product of products, the
landed `gaussSignProdEqPowNegOneOfCount` for the sign half, piece 2's
`InjectiveOn`/`MapsInto` fed to `Int.prodRange_permute` for the
`∏gaussFold = m!` half, and a `Int.modEq_cancel`-shaped step (check the
exact name; `nat_prelude/modeq_cancel_div_gcd.rs`/`int_prelude/modeq.rs`
both have cancellation lemmas, not yet matched to this specific shape)
using item 2's coprimality to cancel `m!`.

**Estimated size**: mostly bookkeeping once items 1 and 2 land -- every
structural piece (the induction, the permutation, the sign product, the
scaled-product identity) already exists; this is the step that chains them,
comparable in size to `declare_prod_range_scaled_index_eq_pow_mul_factorial`
(this session's smallest landed piece, ~140 lines) rather than to a new
induction.

This remains real work across two or three sessions rather than one --
consistent with every prior ADR's sizing of piece 3 -- but the five-item
list is now a two-item list, and the two-item list has no "no existing
analogue found" entries remaining.

## Verification commands (re-executable)

```sh
cargo test -p axeyum-lean-kernel --lib int_prelude::
cargo test -p axeyum-lean-kernel --lib nat_prelude::
# theorem_axiom_footprint matches the KERNEL's camelCase declared name, not
# the Rust snake_case field/fn -- confirmed by running both forms; the
# snake_case form silently matches nothing and prints an empty result.
cargo run --release -p axeyum-lean-kernel --example theorem_axiom_footprint -- prodRange_constPow
cargo run --release -p axeyum-lean-kernel --example theorem_axiom_footprint -- prodRange_scaledIndexEqPowMulFactorial
cargo run --release -p axeyum-lean-kernel --example theorem_axiom_footprint -- prodRangeIf_const_eq_pow_count
cargo run --release -p axeyum-lean-kernel --example theorem_axiom_footprint -- gaussSignProdEqPowNegOneOfCount
# Each prints `integer\tInt.<Name>\t0\t` -- footprint size 0, confirmed
# 2026-08-31 for all four.
```
