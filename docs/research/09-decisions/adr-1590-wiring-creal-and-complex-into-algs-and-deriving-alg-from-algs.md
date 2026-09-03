# ADR-1590: wiring `CReal`/`Complex` into `AlgS`, and deriving `Alg` from `AlgS` (amends ADR-1588)

Status: accepted
Date: 2026-09-03
Lane: `structures-unify`

Index-summary: ADR-1588 built the setoid-flavored `AlgS.*` spine and
`CReal.commRingS`, but left it declared only in a test-only path, not part
of `build_creal_prelude`'s generated `STEP_DISPATCH`. This ADR (1) wires
`CReal.commRingS` into the real build (`algebra_instance::
declare_comm_ring_s` registered right after `product::declare_product`,
`steps_generated.rs` regenerated, prelude construction cost unchanged
within noise), (2) adds `Complex.commRingS : AlgS.CommRing` on the same
pattern, wired into `complex.rs`'s hand-maintained `STEPS`, (3) makes
`Alg.ringMulZero`/`Alg.sub_self` DERIVED theorems reached from `AlgS.
mul_zero`/`AlgS.sub_self` via `ofAlg`, with their declared types measured
byte-identical before and after, and (4) adds two more `AlgS` generic
theorems, `AlgS.mul_neg_one` and `AlgS.add_left_cancel`, each instantiated
at `Int` (via `ofAlg`), `CReal`, and `Complex`. `Alg.neg_neg` (ADR-1584) is
explicitly NOT derived: it is stated over `Alg.Group`, and `AlgS` has no
Group-level generic theorem to derive it from — a scope mismatch, not an
oversight, recorded here rather than forced.

Index-status: accepted

## Context

ADR-1588's own Evidence section named three gaps, explicitly: `CReal.
commRingS` not wired into the automatic build, no `Complex` instance, and
`Alg.*`/`AlgS.*` carrying two independent proofs of the same three ideas
(`Alg.ringMulZero`/`AlgS.mul_zero` chief among them — ADR-1587 §4 measured
that `AlgS.mul_zero` instantiated at `CReal.commRingS`'s `Ring` projection
is `def_eq` to `CReal.mul_zero`'s own type, closing the retirement gap
`Alg.ringMulZero` alone could never reach because `CReal`'s carrier
equality is `Equiv`, never `Eq`). This ADR closes all three.

## Decision

### 1. `CReal.commRingS` wired into `build_creal_prelude`

`creal.rs`'s build is a generated `STEPS`/`STEP_DISPATCH` pair
(`scripts/creal-declare-deps.py`, ADR-1512). A new `CRealPrelude` field
`comm_ring_s : NameId` is interned in `intern_names` alongside every other
`CReal` name, and `algebra_instance::declare_comm_ring_s` — `declare_
creal_comm_ring_s` renamed and changed to the `fn(&mut IntDev<'_>,
CRealPrelude) -> Result<(), KernelError>` shape every step follows, declaring
under `p.comm_ring_s` rather than interning a fresh name of its own — is
registered in `STEP_DISPATCH` immediately after `product::declare_product`,
the step that provides every multiplicative law field
(`mul`/`mul_comm`/`mul_assoc`/`mul_one`/`left_distrib`) this declaration
needs; every additive field it needs is provided earlier still, by
`declare_negation`/`declare_addition`/`declare_additive_laws`.
`scripts/creal-declare-deps.py` (re-run, not hand-edited) measures this from
source and writes `steps_generated.rs`: 212 steps (was 211), the new step's
`requires` are exactly the 21 fields named above, `provides` is exactly
`comm_ring_s`, `--check --strict --self-check` exits 0 (211 pointer
comparisons plus one injected self-check violation, both passing).

Two coverage checks the wiring had to satisfy, both hand-maintained (not
generated) and both caught the gap on the first run after wiring, exactly as
designed: `creal_tests::every_creal_declaration_is_checked_and_axiom_free`
(needed a new `creal/inventory/algebra_instance.rs` shard) and
`creal_tests::steps_table_matches_recorded_extraction` (needed the new
label inserted into its pinned `EXPECTED_STEP_ORDER` array at the matching
position).

**Build-time delta, measured**: `prelude_build_timing`, release,
`AXEYUM_PRELUDE_CACHE=0`, 3 iterations, on this host. Before (commit
`80b04333a`, a throwaway `lane-snapshot.sh` build): 21.64–21.66 s. After:
21.65–22.00 s. No measurable regression — the record instance is exactly
the "milliseconds" ADR-1588 itself predicted, and the ~0.3 s spread is
noise against a ~22 s build under concurrent-lane load, not a real
increase.

**Declaration-projection delta, measured**: `kernel_declaration_projection
--require-declaration CReal.commRingS --require-kind definition` finds it
in the `creal`, `complex`, and `cpoint` preludes (`complex`/`cpoint` build
on top of `creal`, so they inherit it), footprint 0 in each — exactly the
one new row the wiring adds, nothing else.

### 2. `Complex.commRingS : AlgS.CommRing`

`complex.rs` builds `Complex` as pairs of `CReal` under the *defined*
`Complex.Equiv` (ADR-0521) — never `Eq` — so it needs the same setoid
spine `CReal` did, for the same reason. `complex/algebra_instance.rs`
mirrors `creal/algebra_instance.rs` field for field: `ComplexPrelude`
already carries all nine commutative-ring laws (`declare_ring_laws` in
`complex/ring.rs`) plus `add_congr`/`mul_congr`/`neg_congr`, and reading
`declare_ring_laws`'s own proof terms (not assumed from the name) confirms
`Complex.mul_one`/`Complex.left_distrib` are stated in the identical
right/left forms `CReal.mul_one`/`CReal.left_distrib` are (`op_unit_right`/
the `complex_law(d, p, p.left_distrib, 3, ...)` closure, `complex/ring.rs`).
So `mulOneL`/`distribR` are derived by the same one-or-three `equivTrans`
composition `creal/algebra_instance.rs` uses, and every other field is a
direct selector — no new `complex` proof.

`complex.rs`'s build order is a hand-maintained `STEPS: &[BuildStep]` table
(not a `scripts/creal-declare-deps.py`-generated one — no such generator
exists for `complex`), so the new step's `requires`/`provides` are written
by hand, immediately after `declare_ring_laws`. Two hand-maintained pinned
checks needed the same treatment as `creal`'s: `EXPECTED_STEP_ORDER`
(`complex_tests.rs`, a fixed-size array, `91 -> 92`) and the `named` array
in `every_named_complex_declaration_is_checked_and_footprint_free`.

**Evaluation test** (deliverable's explicit ask): projecting `mulComm` off
`Complex.commRingS` and reading its type by reduction is `def_eq` to
`Complex.mul_comm`'s own rendered type at a free `a, b` — `AlgS.CommRing.
mulComm(Complex.commRingS, a, b) def_eq Complex.mul_comm(a, b): true`,
measured, not assumed (`projecting_mul_comm_yields_complex_mul_comm_type`).

### 3. `Alg.ringMulZero`/`Alg.sub_self` DERIVED from `AlgS`

The `Alg` spine embeds into `AlgS` via `ofAlg` with `equiv := Eq` (ADR-1588
§2): an `AlgS.<Record>.ofAlg`-projected value's `equiv`/operation fields
reduce, by iota through the projection's own selector-verbatim
construction, to exactly the `Eq`-flavored originals. So an `AlgS.Ring`
generic theorem applied at `AlgS.Ring.ofAlg R` has an inferred type that
beta/iota-reduces to precisely the corresponding `Eq`-flavored statement —
already measured concretely by ADR-1588 (`AlgS.mul_zero` at `Int.ring`) and
generalized here to a *symbolic*, Pi-bound `R : Alg.Ring`:

```
Alg.ringMulZero R a := AlgS.mul_zero (AlgS.Ring.ofAlg R) a
Alg.sub_self    R x := AlgS.sub_self (AlgS.Ring.ofAlg R) x
```

Both replace their prior *independent* proof (`Alg.ringMulZero`'s own
~140-line additive-group chain; `Alg.sub_self`'s one-line `R.negAdd x`,
already minimal but still a second proof of the same fact `AlgS.sub_self`
already carries) with a citation of the `AlgS` theorem, so each idea now has
**one** proof, reached from two directions. The stated `ty` in each case is
UNCHANGED (the exact same `eq_of`/`pi_over` construction as before — only
the `value` changed), so no transport term beyond the reduction itself is
written; the kernel's own `def_eq` at `add_declaration` confirms the
proof term's inferred type matches.

**Measured, not assumed**: `kernel_declaration_projection`'s
`canonical_type` column for both `Alg.ringMulZero` and `Alg.sub_self`,
compared between a `lane-snapshot.sh 80b04333a` build and this tree, is
**byte-identical** in both cases; `axiom_footprint` stays 0 in both cases,
before and after. `rat_prelude::algebra_ext::`/`algebra_instances::` sweep:
30/30, including `retirement_int_add_left_cancel`/`retirement_rat_sub_self`
(the retirement-match tests still pass against the now-derived proofs) and
`ring_mul_zero_matches_int_and_rat_mul_zero_by_type`.

**Which direction is derivable, the deliverable's explicit question**:
`Alg` (Eq-based) is derivable from `AlgS` (setoid-based) via `ofAlg`
wherever the record SCOPE matches (here, `Ring`) — this is now demonstrated,
not merely argued. The REVERSE — deriving an `AlgS` law from an `Alg` one —
is not possible in general: a setoid instance carries an ARBITRARY `equiv`
relation with its own congruence obligations, and there is no principle in
this kernel (no `Eq.rec`-shaped transport along a non-`Eq` relation, per
ADR-1588's own Alternatives section) that recovers those from a mere `Eq`
fact. `Alg`'s `Eq`-flavored laws are a strictly narrower special case.

**`Alg.neg_neg` is explicitly NOT derived, and this is a real scope
mismatch, not an oversight.** `Alg.neg_neg` (ADR-1584) is stated over
`Alg.Group` (`∀ (G:Group)(a:G.carrier), G.inv(G.inv a)=a`) — a pure group
theorem, proved as a direct instantiation of `Alg.groupInvUnique`, with no
additive/ring content at all. `AlgS.neg_neg` (ADR-1588 §5), by contrast, is
stated only over `AlgS.Ring` (it needs `neg`/`negAdd`, i.e. a RING's
additive negation, not a generic group's `inv`). `AlgS` has no `Group`-level
generic theorem at all — ADR-1588 built exactly three, all over `Ring`. So
there is no `AlgS` theorem whose scope matches `Alg.neg_neg`'s to derive
from; doing so would require a NEW `AlgS.Group`-level inverse-involution
theorem, which is out of this ADR's scope (the deliverable asked to derive
existing theorems, not to design new ones to make a derivation possible).
Left as-is, unchanged, reported here rather than forced through a mismatch.

### 4. Two more `AlgS` generic theorems: `mul_neg_one`, `add_left_cancel`

**`AlgS.mul_neg_one : ∀ (R:Ring)(x:carrier), equiv (mul x (neg one)) (neg
x)`**, over `AlgS.Ring`. Proof (10 `equivTrans` steps, self-contained in
the ring calculus — `AlgS` has no Group-level uniqueness theorem to borrow,
unlike `Alg.mul_neg_one`'s own proof which projects down to `Alg.Group` and
applies `Alg.groupInvUnique`): derive `h : equiv (add y x) zero` where
`y := mul x (neg one)`, from `distribL x (neg one) one` plus the
ALREADY-DECLARED `AlgS.mul_zero` (cited by name, not reproved) plus
`mulOneR x`; then the standard "both are additive inverses of x" chain
`y -> add y zero -> add y (add x (neg x)) -> add (add y x) (neg x) -> add
zero (neg x) -> neg x`, using `h` at the third step.

**`AlgS.add_left_cancel : ∀ (G:Group)(a b c:carrier), equiv (op a b) (op a
c) -> equiv b c`**, over `AlgS.Group` — the setoid twin of `nat_prelude::
structures::build_mul_left_cancel_generic` (`Alg.mul_left_cancel`,
ADR-1587), ported step for step: the same six-step `b = e·b = (a'·a)·b =
a'·(a·b) = a'·(a·c) = (a'·a)·c = e·c = c` chain, with `Eq.trans`/`symm_of`/
`congr_arg` replaced by `equivTrans`/`equivSymm`/`opCongr`.

**Instantiated at `Int` (via `ofAlg`), `CReal`, and `Complex`.** `Int`:
`AlgS.mul_neg_one(AlgS.Ring.ofAlg(Int.ring))` type-checks concretely
(`Int.zero`) and symbolically; no retirement target (`Int.neg_one_mul` is
the MIRRORED LEFT form, ADR-1584 §3 — bridging needs `mul_comm`, which this
theorem is deliberately stated without). `AlgS.add_left_cancel(AlgS.Group.
ofAlg(Int.addGroup))` closed over `(a,b,c)` IS `def_eq` to `Int.
add_left_cancel`'s own declared type — the same carrier theorem `Alg.
mul_left_cancel` already retired to (ADR-1587), now reached from the
setoid spine too, by the same measurement technique
(`retirement_int_add_left_cancel`).

`CReal`/`Complex`: neither has a named `mul_neg_one` theorem (`CReal.
alternating.rs`'s `mul_neg_one_eq_neg` is a private Rust proof-term helper,
never declared into the kernel environment — the same shape ADR-1587 §4
found for `int_prelude/gcd.rs`'s `neg_neg`) or a named `add_left_cancel`/
`Group` value of their own, so both instantiations are well-typedness-only,
via `AlgS.CommRing.toRingS(CReal.commRingS)`/`(Complex.commRingS)` for
`mul_neg_one`, and a NEW un-named term-builder, `structures_setoid::
ring_s_additive_group_value` (`#[cfg(test)]`-gated — every current consumer
is a test; not promoted to a formal `Ring.toCommGroupS` projection, which
is out of scope here), for `add_left_cancel`: it builds an `AlgS.Group`
VALUE from an `AlgS.Ring` value by selecting the additive fields and
deriving `identL`/`invL` from `addComm`+`addZero`/`negAdd` — the same
technique `Alg.Ring.toCommGroup` uses on the `Eq`-flavored spine (ADR-1584),
ported to `equivTrans`.

## Alternatives

**Build a formal `AlgS.Ring.toCommGroupS`/`AlgS.CommGroup.toGroupS`
projection pair instead of the un-named `ring_s_additive_group_value`
term-builder.** Considered; deferred. The projection pattern is real and
would generalize past this ADR's own tests, but it is a new public
declaration this ADR does not otherwise need — `ring_s_additive_group_value`
gives every current consumer (three tests) exactly what they need at a
fraction of the surface. Left as a named next step if a non-test consumer
appears.

**Derive `Alg.neg_neg` anyway, by building the missing `AlgS.Group`-level
theorem first.** Rejected as out of this ADR's scope — the deliverable's
own instruction was to derive from EXISTING `AlgS` theorems and report which
direction is derivable, not to design new ones. Recorded as the honest
answer (§3) rather than forced.

## Evidence

Measured 2026-09-03 on this host, release build, `RUST_MIN_STACK=1073741824`
where `creal`/`complex` are touched.

`python3 scripts/creal-declare-deps.py --check --strict --self-check`: exit
0, 212 steps, 0 order violations, 0 unprovided fields, self-check fires the
one injected violation as designed.

`cargo test -p axeyum-lean-kernel --lib --release -- creal:: --test-threads=4`:
**222 passed, 0 failed** (was 220/222 with 2 failures before the inventory
shard + `EXPECTED_STEP_ORDER` fix, both real gaps the coverage checks
caught on the first run after wiring).

`cargo test -p axeyum-lean-kernel --lib --release -- complex:: --test-threads=4`:
**56 passed, 0 failed**.

`cargo test -p axeyum-lean-kernel --lib --release -- rat_prelude::algebra_ext:: rat_prelude::algebra_instances:: nat_prelude::structures:: nat_prelude::structures_setoid:: --test-threads=4`:
**30 passed, 0 failed**.

`cargo test -p axeyum-lean-kernel --lib --release -- algebra_instance:: nat_prelude::structures_setoid:: --test-threads=4`:
**24 passed, 0 failed**, including the six new instantiation tests
(`mul_neg_one`/`add_left_cancel` at Int/CReal/Complex) and the
`add_left_cancel_instantiated_at_int_through_ofalg_matches_int_add_left_cancel_type`
retirement-shaped `def_eq` check.

`cargo clippy -p axeyum-lean-kernel --lib --tests -- -D warnings`: clean.
One real finding along the way: `cargo clippy --lib --tests` compiles the
plain `--lib` target SEPARATELY from the `cfg(test)` unittest target, so a
`pub(crate)` fn used only by tests is flagged dead code in the FORMER even
though `cargo test` (single cfg(test) artifact) never sees the warning —
fixed by `#[cfg(test)]`-gating `ring_s_additive_group_value` rather than
`#[allow(dead_code)]`, since it genuinely has no non-test consumer today.

`kernel_declaration_projection`: `Alg.ringMulZero`/`Alg.sub_self`
`canonical_type` byte-identical against a `lane-snapshot.sh 80b04333a`
build; `CReal.commRingS` found in `creal`/`complex`/`cpoint`, footprint 0.

`prelude_build_timing --release`, `AXEYUM_PRELUDE_CACHE=0`, 3 iterations:
`creal` 21.64–21.66 s before, 21.65–22.00 s after (no measurable
regression).

## Consequences

**Easier.** `ring_s_additive_group_value` is ready to promote to a formal
`AlgS` projection if a non-test consumer needs one. `AlgS.mul_neg_one`/
`AlgS.add_left_cancel` are the next two named, checked candidates for a
future retirement pass at `Int`/`Rat` (neither is retired here — that was
not this ADR's ask, only instantiation + the def_eq-where-a-target-exists
check).

**Harder.** Two independent proofs still exist for `neg_neg` specifically
(`Alg.neg_neg` over `Group`, `AlgS.neg_neg` over `Ring`) — a future reader
must not assume this ADR's `ringMulZero`/`sub_self` unification pattern
extends to `neg_neg` without first building the missing `AlgS.Group`-level
theorem named in §3.

**Revisit when** a lane wants `AlgS.Field`/`Apart` (ADR-1588's own named
gap, unchanged here), wants to retire `Int.add_left_cancel`'s citation
target from `Alg.mul_left_cancel` to `AlgS.add_left_cancel` (or leave both,
since both now type-match), or builds the `AlgS.Group`-level theorem that
would let `Alg.neg_neg` join `ringMulZero`/`sub_self` as a derived theorem.
