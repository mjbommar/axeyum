# ADR-1025: Euler's theorem spine — item 2 closed axiom-free, item 1 re-sized cheaper by a defeq shortcut, item 3 still open

Status: accepted
Date: 2026-08-31
Index-summary: Of the three pieces `docs/plan/status/374-euler-theorem.md`
named as remaining between the landed residue-permutation lemmas and Euler's
theorem, this lane closed item 2 (`Int.euler_unit_coprime_iff`, the full
predicate-preservation iff, admitted axiom-free with no new induction),
found item 1 (the `Int`/`Nat` bridge into `Int.prodRangeIf_permute`) is
real but smaller than sized — most of its bound-hypothesis conversion is
free by defeq via `order_coercion.rs`'s existing lemmas, not a new
`ofNat`/`natAbs` derivation — and left item 3 (the final product/power
assembly) untouched.

## Context

`docs/curriculum/graded-statement-families-number-theory-and-linear-algebra.md`
§2.2 records Euler's theorem (`a^phi(n) = 1 (mod n)` for coprime `a,n`) as
the highest-yield remaining number-theory target, with a corrected sizing
from 2026-08-30: not "one theorem away", but three named pieces, all real
work, handed off in `docs/plan/status/374-euler-theorem.md` and in
`int_prelude/euler_theorem.rs`'s own module doc. This lane
(`euler-theorem-spine`) was dispatched to verify all three in-tree before
trusting the handoff — the standing "a handoff's report of what REMAINS is
a hypothesis" rule — and to land whatever verifiably lands.

## What was verified, and what changed

All three pieces from the 374 handoff were re-checked against the current
tree rather than inherited:

1. **`Int.euler_unit_injective`'s `Int`-sorted bounded hypotheses vs.
   `Int.prodRangeIf_permute`'s `Nat -> Nat` self-map.** The handoff called
   this "an `ofNat`/`natAbs` round trip and `InjectiveOn`/`MapsInto`
   re-derived in the other shape." Reading `int_prelude/order_coercion.rs`
   shows the ORDER half of that round trip needs no lemma at all:
   `Int.le`/`Int.lt` are built by `define_binary_int` and their `ofNat`/
   `ofNat` branch iota-reduces directly to the `Nat` comparison, so
   `declare_ofnat_order_coercions` proves `Int.le (ofNat m) (ofNat n) ->
   Nat.le m n` with the identity function — literally `let value =
   d.lam_fv(h_fv, hyp_ty, h);` reusing the hypothesis term unchanged. That
   defeq is symmetric: a `Nat.lt i n` proof already type-checks wherever
   `Int.lt (ofNat i) (ofNat n)` is expected, and `Int.of_nat_nat_abs_of_nonneg`
   (`x = ofNat(natAbs x)` for `0 <= x`, already declared in `gcd.rs`) covers
   the return-value half. What is NOT free: actually constructing
   `Nat.InjectiveOn`/`Nat.MapsInto` (`nat_prelude/finite.rs`'s bounded-`Nat`
   definitions) for `sigma(k) := natAbs (emod (a * ofNat k) n)` using these
   pieces. **Still open, but smaller than the handoff sized** — this lane
   did not build it, but the remaining work is assembly over two already-free
   coercions and one already-proved theorem (`euler_unit_injective` itself),
   not new lemma construction.
2. **The predicate-preservation hypothesis was an iff with only the forward
   direction proved.** `int_prelude/euler_unit_preserve.rs` (new file, this
   lane) declares `Int.euler_unit_coprime_iff : n a k, 0 < n -> 0 <= k ->
   k < n -> Coprime a n -> (Coprime k n <-> Coprime (emod (a*k) n) n)`. The
   forward direction is `Int.euler_unit_coprime` directly; the backward
   direction applies the same lemma a second time at `a`'s own modular
   inverse (`Int.modEq_inverse_exists`, commuted via `Int.mul_comm`, fed
   through `euler_totient.rs`'s private Bézout-extraction step — made
   `pub(super)` as `coprime_of_modeq_inverse` for this reuse), then a
   `ModEq`/ring chain (`emod_modeq_self`, `mod_eq_mul_left`, `mul_assoc`,
   `mod_eq_mul_right`, `one_mul`, `mod_eq_trans`) identifies the resulting
   residue with `k`, closed by `emod_eq_self_of_in_range` under the same
   bound hypotheses `Int.prodRangeIf_permute`'s `preserve` premise already
   carries. **No new induction anywhere.** Admitted by the kernel on the
   first attempt; `theorem_axiom_footprint` confirms footprint 0.
   Coverage-checked by `every_int_declaration_is_checked_and_axiom_free`
   (`derived_laws` 219 -> 220, recounted with
   `scripts/recount-pinned-inventory.py`, not incremented by hand). Fact
   `F:int-euler-unit-coprime-iff` registered via `gen-kernel-facts.py`.
3. **The final assembly** `prodRangeIf pred (fun _ => a) n = pow a
   (countRange pred n)` (a new induction pairing `Int.pow` with
   `Nat.countRange`), the pointwise-factoring step, and the termwise `ModEq`
   transport back through the product. **Not attempted this lane** — the
   handoff's sizing here was not re-verified beyond confirming the target
   still does not exist under any name (`Int.euler_totient_theorem` /
   `pow_totient`, checked via `theorem_dependency_inventory`).

## Decision

Record the corrected state so the next lane inherits an accurate map rather
than the original three-piece estimate: item 2 done, item 1 real but
cheaper (the coercion half is free, only the `InjectiveOn`/`MapsInto`
construction for this specific `sigma` remains), item 3 unchanged. Do not
re-describe item 1 as needing "an `ofNat`/`natAbs` round trip" without
qualification — that phrase now overstates its cost.

## Consequences

- Euler's theorem is reachable from here, not proximate. Two pieces (1, 3)
  remain, one of them (3) a genuine new induction with several sub-steps
  (assembly, factoring, transport, cancellation) the 374 handoff already
  detailed and this lane did not shrink.
- The kernel's `Int` order-coercion lemmas (`le_of_ofnat_le_ofnat`,
  `lt_of_ofnat_lt_ofnat`) are proved by identity functions precisely
  because the underlying `Int.le`/`Int.lt` encoding iota-reduces on
  `ofNat`/`ofNat`; any future `Nat`/`Int` bridging work in this kernel
  should check for the same shortcut before writing a new lemma.
- `docs/curriculum/graded-statement-families-number-theory-and-linear-algebra.md`
  §2.2 and `docs/plan/status/euler-theorem-spine.md` carry the same
  correction in full; this ADR is the durable decision-record copy.
