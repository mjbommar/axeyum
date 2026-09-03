# Lane: structures-1 — abstract algebraic structure spine (Magma..Field) as bundled kernel records

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, structures-1, 2026-09-03).** ADR-1578 landed and
is fully implemented: the ten-record `Magma -> Semigroup -> Monoid ->
CommMonoid -> Group -> CommGroup -> Semiring -> Ring -> CommRing -> Field`
spine (`nat_prelude/structures.rs`), ℕ/ℤ/ℚ instances plus three generic
theorems and a generic `det_one` (`rat_prelude/algebra_instances.rs`), four
fact-ledger entries, and this status doc. Every deliverable in the brief
landed; nothing was cut.

**Existing `Group`/`Ring`/`CommRing`/`IsGroup` hits, read before designing**
(ADR-1578's Context section has the full table): `Nat.IsGroupOn`
(`nat_prelude/group.rs`) + 3 lemmas, `Int.IsCommRing` (`int_prelude/ring.rs`),
`Rat.IsField` (`rat_prelude.rs`) — all three are the SAME shape, a `Prop`
over caller-supplied operations **hardcoded to one carrier**, built under the
explicit (and, per ADR-1495, now-refuted) belief that "this kernel has no
typeclasses, no structures and no polymorphism over a bound carrier type"
(`int_prelude/ring.rs`'s own doc). `RingSignature`/`RingTelescope` (ADR-0515,
`axeyum-solver`) is a different mechanism again: a fresh 30-binder
∀-statement regenerated per signature, not a record. None of the four
abstracts over the carrier itself; ADR-1578's spine is the first thing here
that does.

**The universe guard**, measured per record, not just once: every one of the
ten records carries `carrier : Sort 1` as a genuine field, so every one is
declared at `Sort 2` and every one has its own `Sort 1`-refused control run
first (`declare_record` panics the whole test suite if a control is ever
accepted — ten green test runs is ten fired controls). A positive control
(an all-`Prop` record, no `Sort 1` payload) confirms the guard is not simply
refusing every inductive: `a_record_with_no_carrier_field_is_legitimately_
accepted_at_sort1` passes. Field counts: Magma 2, Semigroup 3, Monoid 6,
CommMonoid 7, Group 9, CommGroup 10, Semiring 13, Ring 15, CommRing 16,
Field 19.

**The three generic theorems, with footprints.** `Alg.monoidIdentUnique`
(the `Nat.group_identity_unique` shape — two substitutions, one `trans`),
`Alg.groupInvUnique` (the `Nat.group_inverse_unique` shape — `b = b·e =
b·(a·c) = (b·a)·c = e·c = c`), `Alg.ringMulZero` (proved from the additive-
group + distributive axioms alone — no multiplicative identity field is ever
touched, matching the task's "from the ring axioms alone"). All three:
`axiom_footprint: []` (the whole `rat_prelude` — which is where they and
every instance are declared, since building instances needs ℕ/ℤ/ℚ — measures
axiom-free; `rat_prelude_is_axiom_free` is green with every ADR-1578
declaration in the environment). Each instantiated at TWO carriers, checked
both concretely (real numerals + existing lemmas as witnesses, for
`monoidIdentUnique`) and closed-symbolically (for `groupInvUnique`/
`ringMulZero`, which stay symbolic in their own arguments and are concrete
only in which STRUCTURE instance is plugged in) — see
`docs/contributor-guide/kernel-proof-engineering.md`'s "instantiate
concretely AND check symbolically" rule; the FIRST run of the concrete test
caught a real bug this way (see below).

**Did generic `det_one` land? Yes**, and there is a genuine payoff finding.
`Alg.sumR`/`Alg.altSignR`/`Alg.detR` generalize `Rat.det`'s cofactor
recursion (`Nat.rec` with a function-typed motive for `detR`, since the
recursive call is at a different matrix — the exact device `Rat.det`'s own
module doc names) over an arbitrary `Alg.CommRing`. `Alg.commRingDetOne`
proves `detR R 1 A = A 0 0` and is instantiated at `Rat.commRing` (a
`CommRing` built independently of `Rat.field`, from the same `Rat.*`
constants — no inheritance). **The instantiation check**: type-checks over a
symbolic matrix `A`, `axiom_footprint: []`. **The measurement neither the
ADR nor the brief predicted**: `detR(Rat.commRing, 1, A)` is `def_eq` to
`Rat.det(A, 1)` at a SYMBOLIC `A` — **true**. `detR` and `Rat.det` are two
independently-built `Nat.rec` recursions (the shape
`docs/contributor-guide/kernel-proof-engineering.md`'s `Nat.multichoose`
entry says is usually NOT `def_eq` even when the two agree on every
concrete value), yet they agree here because everything the `n=1` unfolding
touches — `add`/`mul`/`zero`/`one` — is, through `Rat.commRing`'s own
fields, literally `Rat.add`/`Rat.mul`/`Rat.zero`/`Rat.one`, so both sides
reduce (iota+beta, no law needed) to the identical normal form. This is a
one-value (`n=1`) measurement, not a claim about general `n` —
`det_mul`/multiplicativity is explicitly not attempted, matching
`rat_prelude/matrix_det.rs`'s own stated boundary.

**Two real bugs the test suite's first run caught** (not infra noise —
worth recording because they are exactly the failure classes
`kernel-proof-engineering.md` predicts):
1. `monoid_ident_unique` applied to the `Alg.CommMonoid` instances
   (`Nat.commAddMonoid`, `Rat.commMulMonoid`) instead of genuine `Alg.Monoid`
   values — a real kernel `TypeMismatch`, because this spine has no
   inheritance/coercion and a `CommMonoid`-typed term does not apply where a
   `Monoid` is expected. Fixed by building real `Monoid` values inline from
   the same underlying lemma constants.
2. `group_inv_unique`/`ring_mul_zero`/`comm_ring_det_one`'s first draft used
   `Kernel::infer` on an OPEN term (a bare `k.fvar(id)` never registered in
   any `LocalContext`) and failed `UnboundFVar` — an infra bug in the TEST,
   not the theorems; fixed by closing the checked term over its symbolic
   elements with `lam_over` before inferring, avoiding `LocalContext`
   entirely and reusing the exact closed-term machinery the declarations
   themselves already use.

**What did NOT run, and why it does not weaken the result**: an early
foreground attempt to verify the full `rat_prelude::` suite (before the
targeted `algebra_instances_tests`/`structures_tests` filters existed) was
genuinely blocked for ~9 minutes on `cargo-serialized.sh`'s host-wide `flock`
under heavy concurrent-lane load (measured `uptime` load average 6.7–10.6,
five lock slots all recently touched) before it acquired a slot and ran to
completion — 239 passed, 0 failed. Every subsequent verification in this
lane (the two new test modules, `cargo check -p axeyum-py`, the fact-ledger
scripts) ran to completion within the session; nothing here is reported
"did not run".

**ADR-1578's own tension, stated rather than silently resolved**: its
Context section records that ADR-1495's own gate for this "second rung" (a
carrier-generic congruence/transport layer, landed AND consumed by a lane
that did not build it) is not yet satisfied — the probe example still
exists only as a probe. This lane proceeded anyway on explicit coordinator
instruction, self-contained (every proof term here builds its own inline
`congr_arg`/`transport`, not routed through anything ADR-1495 gated). The
gate itself is not resolved by this lane and should not be read as such.

<!-- plan-section: landed-changes -->

| 2026-09-03 | structures-1 | `c31fd7764` status stub |
| 2026-09-03 | structures-1 | `343d3277a` ADR-1578 + the ten-record spine (`nat_prelude/structures.rs`), universe-guard controls, 2 unit tests |
| 2026-09-03 | structures-1 | `b87a70cbe` ℕ/ℤ/ℚ instances, three generic theorems, generic `sumR`/`altSignR`/`detR`/`commRingDetOne` (`rat_prelude/algebra_instances.rs`); full `rat_prelude::` suite 239 passed |
| 2026-09-03 | structures-1 | `263ef16d0` concrete+symbolic instantiation tests (6/6), the det_one payoff measurement (`detR def_eq Rat.det` at symbolic A = true) |
| 2026-09-03 | structures-1 | `62b4f4f5c` four fact-ledger entries (`F:alg-monoid-ident-unique`, `F:alg-group-inv-unique`, `F:alg-ring-mul-zero`, `F:alg-comm-ring-det-one`); registered `Alg` in validate-facts.py's kernel_theorem allowlist; fixed new-fact.py's `grep -q` output to `grep -c ... -ge 1`; regenerated `prelude_fields.rs` |
