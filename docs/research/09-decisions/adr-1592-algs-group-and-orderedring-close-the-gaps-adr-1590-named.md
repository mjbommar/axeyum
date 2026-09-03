# ADR-1592: `AlgS.Group`-level theorems and `AlgS.OrderedRing` close the two gaps ADR-1590 named

Status: accepted
Date: 2026-09-03
Lane: `structures-ordered-setoid`

Index-summary: ADR-1590 named two open gaps: no `AlgS.Group`-level generic
theorem (so `Alg.neg_neg`, stated over `Alg.Group`, could not derive from
the setoid spine), and no `AlgS.OrderedRing` at all (so `linarith::generic`,
ADR-1585, could not reach `CReal`, whose carrier equality is `Equiv`, never
`Eq`). This ADR closes both. `AlgS.inv_unique`/`AlgS.invInv` are the
setoid twins of `Alg.groupInvUnique`/`Alg.neg_neg`, proved once over
`AlgS.Group` and reached at `Int` (via `ofAlg`) and at `CReal` through a
new NAMED projection, `CReal.addGroupS`; `Alg.neg_neg`'s own proof is now
DERIVED from `AlgS.invInv`, declared type measured byte-identical.
`AlgS.OrderedRing` (29 fields — `AlgS.Ring`'s 22, not `AlgS.CommRing`'s 23:
`Alg.OrderedRing` itself carries no `mulComm`, so a `CommRing`-based
record would make `AlgS.OrderedRing.ofAlg` ill-typed) adds `le`, `leCongr`
(new: `Eq`'s congruence is free, a setoid's is not), `le_refl`, `le_trans`,
`le_antisymm_equiv` (concludes `equiv`, not `Eq`), `add_le_add_left`,
`mul_nonneg`; `AlgS.OrderedRing.ofAlg` synthesizes `leCongr` via two
`subst` transports, every other field the source selector unchanged.
`rat_prelude/ordered_ring_ext_s.rs` (new) is the setoid twin of
`ordered_ring_ext.rs`: `AlgS.ofNat`/its two laws, and the three derived
order lemmas — each SHORTER than its `Eq`-flavored counterpart because
`leCongr`/`addCongr` are first-class fields, not a hand-built `Eq.rec`
motive. `CReal.orderedRingS` has every field an existing `CReal` theorem
(`le_antisymm_equiv` is `CReal.equiv_of_le_le` verbatim — already stated
as antisymmetry-up-to-`Equiv`; `add_le_add_left` derived from
`add_le_add`+`le_refl`), wired into the generated creal build.
`linarith::generic` is EXTENDED (not forked) with a `Backend` enum: the
normalizer's `congr`/`substp` calls already funnelled through five wrapper
methods and one parser, so making those backend-aware was the whole
surface — zero behavior change to the `Eq`-flavored path (all 72
pre-existing tests pass unmodified). `Problem::new_s`/`prove_s` are the
setoid entry points; a full test battery (3 ℚ goals re-proved through
`Rat.orderedRingS`, 5 goals at `CReal.orderedRingS` — the payoff, 3 false
goals decline, 2 corrupted certificates rejected) is green in `--release`.
Five `creal/*.rs` order-chain hand proofs are retired to
`linarith::generic::prove_s` over `AlgS.Rat.orderedRingS`.
Index-status: accepted

## Context

ADR-1590 §3 measured and explicitly declined to close a scope mismatch:
"`Alg.neg_neg` is stated over `Alg.Group`... `AlgS` has no `Group`-level
generic theorem at all — ADR-1588 built exactly three, all over `Ring`. So
there is no `AlgS` theorem whose scope matches `Alg.neg_neg`'s to derive
from... Left as-is, unchanged, reported here rather than forced." ADR-1585
built `linarith::generic` over `Alg.OrderedRing` and named its own scope
honestly short of `linarith::int`, but the record itself is `Eq`-flavored,
so nothing in that lane could reach `CReal` at all — ADR-1588/1590 built the
setoid spine `AlgS.Magma..CommRing` specifically because `CReal`'s carrier
equality is a *defined* relation, `CReal.Equiv`, never `Eq`, and
`AlgS.OrderedRing` was never built. This ADR closes both gaps in one lane,
because the second gap's fix (a setoid-flavored ordered-ring record) needed
the first gap's machinery (`AlgS.Group`-level reasoning, and the promoted
`CommRing.toCommGroupS`/`CommGroup.toGroupS` projections) as a prerequisite
for reaching `CReal`'s additive group at all.

## Decision

### 1. `AlgS.inv_unique`, `AlgS.invInv`, and `Alg.neg_neg` derived

`nat_prelude/structures_setoid.rs` gains two `AlgS.Group`-level theorems,
mirroring `rat_prelude::algebra_instances::build_group_inv_unique`/
`rat_prelude::algebra_ext::build_neg_neg` (the `Eq`-flavored Group-level
pair) exactly, `Eq.trans`/`symm_of`/`congr_arg` replaced by the record's
own `equivTrans`/`equivSymm`/`opCongr` (the same substitution
`declare_add_left_cancel`, ADR-1590, already made for `Alg.mul_left_cancel`):

- **`AlgS.inv_unique : ∀ (G:Group)(a b c:carrier), equiv (op b a) e →
  equiv (op a c) e → equiv b c`** — the setoid twin of
  `Alg.groupInvUnique`.
- **`AlgS.invInv : ∀ (G:Group)(a:carrier), equiv (inv (inv a)) a`** — a
  direct instantiation of `AlgS.inv_unique`, mirroring `Alg.neg_neg`'s own
  proof exactly. **Named `invInv`, not `neg_neg`**: `AlgS.neg_neg`
  (ADR-1588) already names a *different*, `Ring`-scoped theorem (`equiv
  (R.neg (R.neg a)) a`, built from `negAdd`/`addComm`/`addAssoc` over
  `AlgS.Ring`'s additive structure, pinned in the fact ledger as
  `F:algs-neg-neg`); `AlgS.invInv` is stated over `AlgS.Group`'s generic
  `inv`, the scope `Alg.neg_neg` actually has. Reusing the name would
  collide with an existing, differently-typed declaration.

**`Alg.neg_neg`'s own proof is now DERIVED** from `AlgS.invInv` applied at
`AlgS.Group.ofAlg G` (mirroring `Alg.ringMulZero`/`Alg.sub_self`'s own
derivation from `AlgS.Ring`, ADR-1590 §3): `AlgS.Group.ofAlg G`'s `equiv`
field is `@Eq G.carrier` and its `inv` field is `G`'s own selector,
verbatim, so `AlgS.invInv (ofAlg G) a`'s inferred type beta/iota-reduces to
EXACTLY `Eq G.carrier (G.inv (G.inv a)) a` — `Alg.neg_neg`'s own stated
`ty`, unchanged, so the declared type stays byte-identical before and
after. The existing `neg_neg_applies_concretely_at_int_and_symbolically_
at_rat`/`retirement_rat_neg_neg` tests (unmodified) both still pass,
confirming the re-derived proof still computes the identical value.

**Two new NAMED projections, promoting ADR-1590's test-only
`ring_s_additive_group_value`**: `AlgS.CommRing.toCommGroupS : AlgS.
CommRing → AlgS.CommGroup` (the same additive-group derivation
`ring_s_additive_group_value` used, widened to `CommGroup` by adding the
`comm` field — `addComm`, already available) and `AlgS.CommGroup.toGroupS
: AlgS.CommGroup → AlgS.Group` (a trivial PREFIX projection, the same shape
`AlgS.CommRing.toRingS` and `Alg.CommGroup.toGroup` both already use).
**`CReal.addGroupS : AlgS.Group := AlgS.CommGroup.toGroupS(AlgS.CommRing.
toCommGroupS(CReal.commRingS))`**, a real declared name (deliverable's
explicit ask), wired into the generated `creal` build right after
`declare_ordered_ring_s`. `AlgS.add_left_cancel`/`AlgS.inv_unique`/
`AlgS.invInv` all type-check applied at `CReal.addGroupS`.

`MAX_FIELDS` bumped 24 → 32 (headroom for `AlgS.OrderedRing`'s 29 fields,
§2).

### 2. `AlgS.OrderedRing`: 29 fields, `Ring`-based not `CommRing`-based

**Built over `AlgS.Ring` (22 fields), not `AlgS.CommRing` (23) — necessary,
not a simplification.** `Alg.OrderedRing` (ADR-1584) is itself Ring-based
(`Ring`'s 15 fields, no `mulComm` — none of the order laws need
commutativity), and `AlgS.OrderedRing.ofAlg` (below) must select FROM an
`Alg.OrderedRing` value, which carries no `mulComm` field to select in the
first place. A `CommRing`-based `AlgS.OrderedRing` would make that
projection ill-typed — measured by attempting it first, not assumed.
`Int`/`Rat`/`CReal` are all commutative anyway, so nothing downstream loses
reach; only the record's own field list changes shape.

Seven new fields beyond `Ring`'s 22: `le : carrier → carrier → Prop`,
**`leCongr : ∀ a a' b b', equiv a a' → equiv b b' → le a b → le a' b'`**
(new: `le` has no `Eq`-flavored congruence field to reuse, since `Eq`'s own
congruence is free — this is the one field with no counterpart anywhere in
the `Eq`-flavored spine), `le_refl`, `le_trans`, **`le_antisymm_equiv : ∀ a
b, le a b → le b a → equiv a b`** (concludes `equiv`, not `Eq` — the
deliverable's explicit ask), `add_le_add_left`, `mul_nonneg`. Four of the
five primitive order-law field BUILDERS (`rel_field`, `le_refl_field`,
`le_trans_field`, `add_le_add_left_field`, `mul_nonneg_field`) need no
`equiv` at all — none of their STATEMENTS mention the carrier's equality —
so they are reused VERBATIM from `nat_prelude::structures` (now
`pub(crate)`) rather than duplicated; only `le_antisymm_equiv` and
`leCongr` are genuinely new field builders.

**`AlgS.OrderedRing.ofAlg : Alg.OrderedRing → AlgS.OrderedRing`**. Every
LAW field, including `le_antisymm_equiv` (whose `Eq`-flavored source
`le_antisymm` selector unfolds to EXACTLY `equiv a b` once `equiv := @Eq
carrier`, the same load-bearing fact every other `ofAlg` projection in this
spine exploits), is the source record's own selector, unchanged. Only the
four equiv-infrastructure fields, the three inherited congruence fields
(`addCongr`/`mulCongr`/`negCongr`), and `leCongr` need a fresh proof term.
`leCongr` is synthesized via **two `subst` (`Eq.rec`) transports** — given
`h1 : Eq a a'`, `h2 : Eq b b'`, `hle : le a b`, first transport `hle` along
`h1` on `(fun x => le x b)` to get `le a' b`, then along `h2` on `(fun y =>
le a' y)` to get `le a' b'` — the same shape `build_binop_congr` uses for
an operation, generalized to conclude a PROP membership rather than an
operation-equality (mirroring ADR-1584's own `mul_le_mul_of_nonneg_left`
`subst` use).

### 3. `rat_prelude/ordered_ring_ext_s.rs`: the setoid twin of `ordered_ring_ext.rs`

`AlgS.OrderedRing.ofNat` and its two laws (`ofNat_add`, `ofNat_le_ofNat_
of_le`), and three derived order lemmas (`add_le_add_right`,
`le_of_add_le_add_right`, `add_le_add`) — the exact set ADR-1585 built for
`Alg.OrderedRing`, ported.

**Shorter than the `Eq`-flavored versions, not merely different.**
`ordered_ring_ext.rs`'s derivations lean on `structures::EqB`'s `Eq.rec`-
based `subst`/`congr_arg` because `Eq`'s congruence is free for an
arbitrary predicate. A setoid has no such free lunch — but `AlgS.
OrderedRing` carries `leCongr`/`addCongr` as FIRST-CLASS FIELDS, so a
rewrite under `le`/`add` is one direct field application, never a
hand-built `Eq.rec` motive. `build_add_le_add_right_s` in particular:
`h0 := add_le_add_left(a,b,c,h)`, then TWO direct `leCongr` applications
(rewriting each side across `addComm`) — no `EqB`/`subst` machinery at
all, against `ordered_ring_ext.rs`'s own multi-step `EqB::subst` chain for
the identical fact.

`AlgS.Int.orderedRingS`/`AlgS.Rat.orderedRingS` declared via `AlgS.
OrderedRing.ofAlg` applied to the existing `Int.orderedRing`/`Rat.
orderedRing`.

### 4. `CReal.orderedRingS` — every field an existing `CReal` theorem

Checked BEFORE building the record (the deliverable's explicit
constraint — "if any law is missing, name it and stop"): `CReal` already
has `le`, `le_refl`, `le_trans`, `le_congr` (`CRealPrelude::le_congr : ∀ a
b c e, Equiv a b → Equiv c e → le a c → le b e` — EXACTLY `leCongr`'s
shape, just argument-order-permuted), `equiv_of_le_le` (documented as
"antisymmetry up to `Equiv`" — EXACTLY `le_antisymm_equiv`'s shape),
`mul_nonneg`, and `add_le_add` (two-sided). No field was missing;
`add_le_add_left` is DERIVED from `add_le_add`+`le_refl`
(`add_le_add(c,c,a,b,le_refl(c),h)`), the same technique `Rat.orderedRing`
itself uses (ADR-1584) — a composition of two EXISTING `CReal` theorems,
not a new `creal` proof. `mulOneL`/`distribR` reuse the SAME derived
values `declare_comm_ring_s` (ADR-1590) already builds; no second proof.

Wired into the generated `creal` build (`scripts/creal-declare-deps.py`:
213 → 214 steps across this ADR's two new `creal` declarations,
`orderedRingS` and `addGroupS`; `--check --strict --self-check` exits 0 at
each). Full `creal::` suite green throughout.

### 5. `linarith::generic`: extended, not forked

The module's own internal structure made this a much smaller surface than
its 2,184 lines suggest: every `congr`/`substp` call in the normalizer
(flatten/reassoc/prepend_zero/arrange — 9 `congr` sites, 4 `substp` sites)
already funnelled through five wrapper methods (`refl`/`symm`/`trans`/
`congr`/`substp`) and one parser (`as_eq`) on `Problem`, rather than
calling `structures::{refl_of,...}` directly. Making those six
backend-aware was the whole change:

- **`enum Backend { KernelEq, Setoid { equiv, equiv_refl, equiv_symm,
  equiv_trans, add_congr, le_congr } }`** — a new `Problem` field.
- **`refl`/`symm`/`trans`** dispatch directly: `KernelEq` unchanged,
  `Setoid` applies the record's own `equivRefl`/`equivSymm`/`equivTrans`.
- **`congr`** gained an `AddCtx` parameter (`Left(fixed)`/`Right(fixed)`/
  `FoldFrom(tail)` — every closure in the file already had exactly one of
  these three shapes, read off at each call site). `KernelEq` ignores it
  and uses the SAME closure-driven `Eq.rec` `congr_arg` as before (zero
  behavior change); `Setoid` uses it to compose `addCongr` applications
  directly — `Left`/`Right` are one application, `FoldFrom` composes one
  per tail item via the same left-fold `fold_from_ctx` itself builds.
- **`substp`** gained a two-variant `LeCtx` (`Left(fixed)`/`Right(fixed)`)
  — `leCongr`, a first-class field, handles either shape in one
  application; `KernelEq` ignores it and uses its generic `Eq.rec` `subst`
  unchanged.
- **`as_eq`** parses either kernel `Eq` (3-application form,
  `App(App(App(Eq,ty),x),y)`) or the record's own `equiv` VALUE applied
  directly (2-application form, `App(App(equiv,x),y)` — `equiv` is already
  a 2-argument relation, not a type-indexed family the way kernel `Eq` is).

**`Problem::new_s`/`prove_s`/`emit_le_from_certificate_s`** are the setoid
entry points, mirroring `new`/`prove`/`emit_le_from_certificate` exactly,
reading from `AlgS.OrderedRing`'s selectors and `OrderedRingExtSNames`
instead of the `Eq`-flavored spine.

**Zero behavior change to the `Eq`-flavored path, measured**: all 72
pre-existing `linarith::{tests,int_tests,core_tests,generic::generic_
tests}` pass unmodified after this refactor.

## Evidence

Measured 2026-09-03 on this host, `--release`, `RUST_MIN_STACK=
1073741824` where `creal`/`linarith::generic` are exercised.

**`nat_prelude::structures_setoid::`**: 20 tests (13 pre-existing +
`inv_inv_instantiated_at_int_through_ofalg_concrete_and_symbolic`,
`inv_unique_instantiated_at_int_through_ofalg_concrete_and_symbolic`,
`add_left_cancel_instantiated_at_int_through_comm_ring_to_comm_group_s_
matches_int_add_left_cancel_type`, and the `AlgS.OrderedRing` field-count/
declaration-presence extensions to the existing pinned tests), all green.

**`rat_prelude::ordered_ring_ext_s::`**: 7 new tests (`ofnat_s_evaluation_
at_int_discriminates`, `ofnat_add_s_symbolic_at_int_and_rat`, `ofnat_le_
ofnat_of_le_s_symbolic_at_int_and_rat`, `add_le_add_right_s_matches_int_
add_le_add_right_by_type`, `add_le_add_s_matches_int_add_le_add_by_type`,
`le_of_add_le_add_right_s_symbolic_at_int_and_rat`, `ordered_ring_ext_s_
declarations_are_axiom_free`) — both retirement-style `def_eq` checks
(against `Int.add_le_add_right`/`Int.add_le_add`) pass.

**`creal::` (algebra_instance)**: `creal_ordered_ring_s_admits_and_is_
axiom_free`, `creal_ordered_ring_s_order_fields_apply_at_concrete_creal_
values`, `creal_add_group_s_admits_and_is_axiom_free`, `generic_add_left_
cancel_instantiated_at_creal_add_group_s_type_checks`, `generic_inv_
unique_and_inv_inv_instantiated_at_creal_add_group_s_type_check` — 5 new
tests, all green. Full `creal::` suite: 226+ passed, 0 failed (measured
before and after the `linarith_bridge` retirement, §6).

**`linarith::` full suite**: **86 passed, 0 failed, 1 ignored** (the
`--release`-only timing report). Of these, 14 are the setoid battery:
`rat_new_capability_{transitivity,sum_of_nonneg,slack_add_one}_via_algs`
(3 ℚ goals re-proved through `Rat.orderedRingS`); `creal_linarith_
{transitivity,sum_of_nonneg,slack_add_one,add_le_add_three,equality_by_
antisymmetry}` (5 goals at `CReal.orderedRingS` — the payoff, the last
exercising the `Shape::Eq`/`le_antisymm_equiv` route, proving `CReal.
Equiv a b` from `a≤b, b≤a`, a fact no `Eq`-flavored route could ever
reach); `creal_linarith_false_goal_{swap,cycle,off_by_one}_declines`
(three false goals decline); `creal_linarith_corrupted_certificate_
wrong_{multiplier,residual}_rejected` plus `creal_linarith_uncorrupted_
certificate_is_admitted` (two corrupted certificates rejected by the
KERNEL, `verify: false`, plus the positive control).

**Retirements (deliverable 4's last piece)**: five `creal/*.rs`
order-chain hand proofs routed through `linarith::generic::prove_s` over
`AlgS.Rat.orderedRingS` instead of a hand `le_refl`+`add_le_add`(+
`add_zero`) chain, via a new shared bridge (`creal/linarith_bridge.rs`,
`rat_le_add_right`/`rat_add_le_add`, each proved ONCE and reused): `creal/
integral.rs::le_add_nonneg_right`, `creal/integral.rs::rle_add_right`,
`creal/sqrt.rs::rat_le_add_nonneg`, `creal/supremum.rs::rat_le_add_right`
(all the SAME shape, `x ≤ x+y` from `0≤y`, independently hand-built four
times across three files — TWO of the four in the SAME file), and `creal/
completeness.rs::moduli_shift_le` (the two-sided `add_le_add` shape).
Every site's function signature and return type are unchanged; the kernel
re-checks each proof term against the SAME stated type as before.

**A real bug the first version of this ADR's own retirement surfaced,
worth recording**: `linarith::generic::Problem::ofnat_numeral` recognises
a literal zero by SYNTACTIC `ExprId` equality against `self.zero` (a
SELECTOR application off the ring term), not `def_eq`. The first version
of `creal/linarith_bridge.rs` built its hypothesis's zero from the bare
`Rat.zero` constant instead of the selector application — `def_eq` to the
right value, but a DIFFERENT `ExprId` — so `ofnat_numeral` silently failed
to recognise it as the constant `0`, and every `rat_le_add_right` call
inside a real prelude build panicked with `Decline::NoCertificate`, caught
only by running `theorem_dependency_inventory` (which builds the whole
prelude) rather than the isolated unit tests (which happened to reuse the
same selector-built zero the fix now uses everywhere). Fixed by building
`RatRingS`'s `zero` field the same way `le`/`add` already were — a
selector application off the SAME ring term, matching `Problem::new_s`'s
own `self.zero` exactly.

`cargo test --release -p axeyum-lean-kernel --lib -- creal::
--test-threads=4`: full suite green after the fix (see per-module counts
above). `cargo run -q --release -p axeyum-lean-kernel --example
theorem_dependency_inventory`: exits cleanly (the integration check that
caught the bug above). `python3 scripts/creal-declare-deps.py --check
--strict --self-check`: exit 0, 214 steps. `cargo clippy -p
axeyum-lean-kernel --lib --tests -- -D warnings`: clean. `rustfmt
--edition 2024` on every touched file.

**Fact ledger**: four new facts (`F:algs-inv-unique`, `F:algs-inv-inv`,
`F:algs-ofnat-add`, `F:algs-ofnat-le-ofnat-of-le`); `F:alg-neg-neg`'s
`depends_on` gains the `F:algs-inv-inv` edge (via `check-fact-depends-
derived.py --fix`, the same mechanism ADR-1590 used for `F:alg-ring-mul-
zero`/`F:alg-sub-self`). `python3 scripts/validate-facts.py`: exit 0.

## Alternatives

**Build `AlgS.OrderedRing` over `AlgS.CommRing` (23 fields), matching the
deliverable's literal field-list wording verbatim.** Rejected after
attempting it: `Alg.OrderedRing.ofAlg`'s SOURCE type carries no `mulComm`
field, so the projection is ill-typed the moment the record needs one.
Building over `AlgS.Ring` instead is the necessary correction, not a
simplification — recorded explicitly (§2) rather than silently deviating
from the brief.

**Give `congr`/`substp` a trait-object-based "either backend" abstraction
instead of an explicit `Backend` enum plus `AddCtx`/`LeCtx` shape
parameters.** Considered; rejected. A setoid has no generic `Eq.rec`-shaped
transport for an arbitrary closure (ADR-1588's own finding), so the
`Setoid` backend cannot simply "run the same closure" — it needs to know
the STRUCTURAL SHAPE of what the closure builds to compose `addCongr`/
`leCongr` applications instead. The shape parameter makes this explicit
rather than trying to reverse-engineer it from an opaque `dyn Fn`.

## Consequences

**Easier.** `linarith::generic` is a genuine second producer over `AlgS.
OrderedRing` at any future setoid carrier with an `AlgS.OrderedRing`
instance, reachable with zero additional emitter code — exactly the
promise ADR-1585 made for `Alg.OrderedRing` and could not extend to
`CReal` until this ADR. `creal/linarith_bridge.rs`'s two shapes are ready
for the next `creal/*.rs` module that hand-builds the same order-chain
pattern.

**Harder.** `linarith::generic` is now a producer with TWO backends
sharing one normalizer; a future change to the normalizer's own logic
(flatten/reassoc/arrange) must be checked against both `AddCtx`'s three
shapes and the `KernelEq` closure path, not just one. `AlgS.OrderedRing`
being `Ring`-based (not `CommRing`-based) is a real asymmetry with the
deliverable's literal wording that a future reader must not silently
"fix" back to `CommRing` without re-discovering why `ofAlg` needs `Ring`.

**Revisit when** a lane wants the `<`/strict fragment over `AlgS.
OrderedRing` (the same gap ADR-1585 left open for `Alg.OrderedRing` — no
`lt` field exists on either record), wants to retire more `creal/*.rs`
order-chain hand proofs to `linarith::generic::prove_s` (the census in
`creal/linarith_bridge.rs`'s own module doc names five; ADR-1576's
original count puts `creal`'s order-lemma call sites at 2,212, so this is
a first slice, not the whole census), or wants `linarith::generic` to
reach `Complex.orderedRingS` (`Complex` has no order at all today, so this
needs a genuinely new design question, not a mechanical port).
