# Lane: gauss-lemma-connecting-b — Gauss's-lemma connecting theorem (piece 1)

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, gauss-lemma-connecting-b, 2026-08-31).**
Verified the three-piece sizing ADR-0970/ADR-0985 left open (least-residue
injectivity, a pairing lemma, product cancellation over `Int.prodRange`)
against the tree before starting — all citations confirmed present on
`origin/main`. Landed piece 1 in full:

- `Nat.least_residue_injective_of_coprime : ∀ pp a k k', 0 < pp -> gcd a pp
  = 1 -> k < pp -> k' < pp -> leastResidue pp a k = leastResidue pp a k' ->
  k = k'` (`nat_prelude/gauss_lemma.rs`) — no case split needed. Stated over
  bare positivity + coprimality, strictly more general than "restricted to
  `{1,…,m}`, `a` coprime to prime `p`" — a caller in the classical setting
  supplies coprimality via the already-landed `Nat.coprime_of_lt_prime`.
  Axiom footprint, read from the kernel
  (`theorem_axiom_footprint -- least_residue_injective_of_coprime`): `0`.
- Exposed two previously module-private `group.rs` helpers (`mod_self_congr`,
  `mod_eq_of_mod_eq_rel`) as `pub(super)`, reused rather than duplicated.

**Piece 2 (the pairing lemma) was NOT built this session, but its route is
simplified and precisely re-sized**, checked signature-by-signature against
the tree. Key finding: `Int.prodRange_permute`'s actual hypothesis shape is
`InjectiveOn σ n -> MapsInto σ n` on a **self-map** of `[0,n)` — no explicit
bijection witness or partner-index construction is needed, contrary to
ADR-0970's original "construct a partner `k'`" framing. So piece 2 reduces
to: the signed-fold map `gaussFold pp a k := if gaussSignNeg pp a k then sub
pp (leastResidue pp a k) else leastResidue pp a k` is `InjectiveOn`/
`MapsInto` on `[0,m)`. Same-sign collisions close via piece 1 (already
landed); opposite-sign collisions are shown VACUOUS via a modular-cancellation
argument (no partner construction) — every lemma name that route depends on
was checked present except a `leastResidue`-nonzero lemma, itself sized as
~40-60 lines structurally similar to `coprime_of_lt_prime`. Full route:
[ADR-0990](../../research/09-decisions/adr-0990-gauss-lemma-least-residue-injectivity-lands-pairing-route-simplified-and-sized.md).

**Piece 3 (product cancellation over `Int.prodRange`, the Nat/Int carrier
bridge, and connecting to `a^m mod p`) is unchanged from ADR-0970's sizing
and was not attempted** — genuinely deserving its own session.

**The `F:nat-gauss-lemma` collision was avoided**: no fact was added this
session (kernel declarations only), and the new name
`least_residue_injective_of_coprime` is unambiguously distinct from
`Nat.gauss_lemma` (`lcm.rs`, an unrelated divisibility cancellation
theorem) — checked against the full source tree and `artifacts/facts/`
before landing.

Verification this session: `cargo check -p axeyum-lean-kernel --lib`
(clean); `cargo test -p axeyum-lean-kernel --lib nat_prelude::` (252
passed, 0 failed, up from 250 before this session — nonzero count
confirmed); `cargo clippy -p axeyum-lean-kernel --lib -- -D warnings`
(clean); `cargo run --release -p axeyum-lean-kernel --example
theorem_axiom_footprint -- least_residue_injective_of_coprime` (footprint
`0`); `python3 scripts/check-autogenesis-holdout-isolation.py` (PASS,
`held_out=146`, `artifacts/autogenesis/` untouched, checked before and
after).

**Is the full connecting theorem reachable here?** Yes in principle — every
lemma name piece 2's route needs was checked present except one small
nonzero-residue lemma, and piece 2's `InjectiveOn`/`MapsInto` deliverable
plugs directly into `Int.prodRange_permute`'s exact hypothesis shape with
no adapter needed. But piece 3 alone (the product identity, a
`modEq`-over-a-product lemma, a sign-product-equals-`(-1)^count` lemma, and
the Nat/Int carrier bridge) is a materially larger, multi-lemma
construction than pieces 1+2 combined, and was not sized further than
ADR-0970 already did. Landing pieces 1+2 with a precise piece-3 handoff
across two sessions, rather than a rushed single-session attempt at all
three, is consistent with how ADR-0970/ADR-0985 each scoped their own
sessions.

<!-- plan-section: landed-changes -->

| 2026-08-31 | gauss-lemma-connecting-b | `Nat.least_residue_injective_of_coprime` (least-residue map injectivity given positivity + coprimality, no case split) lands axiom-free in `nat_prelude/gauss_lemma.rs` — piece 1 of the Gauss's-lemma connecting theorem ADR-0970/ADR-0985 sized. Piece 2 (the pairing lemma) is re-sized with a genuine simplification (self-map `InjectiveOn`/`MapsInto`, matching `Int.prodRange_permute`'s exact hypothesis shape — no bijection witness needed) and checked lemma-by-lemma against the tree (ADR-0990); piece 3 (product cancellation, Nat/Int bridge) stays open, unchanged sizing. |
