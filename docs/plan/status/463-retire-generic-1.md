# Lane: retire-generic-1 — the retirement ADR-1584 measured and did not take

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, retire-generic-1, 2026-09-03).** ADR-1584
measured six carrier-specific hand proofs matching a generic `Alg.*` theorem
by type but deleted none, because ADR-1581's build-position check was never
run. This lane runs all three of ADR-1581's checks for real
(`scripts/generic-retirement-check.py`, artifact committed), widens the
candidate set by two, and retires the one candidate that clears every
check. Full account is ADR-1587; this block is the pulse.

**The checks, run for real (8 rows: ADR-1584's six plus two widened).**
Every candidate fails check (ii) — build position — BY DEFAULT: the abstract
record spine (`nat_prelude::structures::declare_structures_all`) is declared
first, but every instance/projection/generic theorem is declared by
`algebra_instances::declare_algebra_instances_all`/`algebra_ext::
declare_algebra_ext_all`, confirmed (not assumed) to be the literal LAST TWO
`declare_*` calls in `build_rat_prelude` — after every carrier theorem.
Three candidates ALSO fail check (i), cited directly by a producer emitter:
`Rat.neg_neg` (`ring/rat.rs`, six sites), `Int.mul_zero`
(`linarith/int.rs`, `ring/int.rs`), `Rat.mul_zero` (`ring/rat.rs`) — the last
two are this lane's widened finding (`Alg.ringMulZero`, one of ADR-1578's
OWN three generic theorems, never checked against `Int.mul_zero`/
`Rat.mul_zero` by either prior ADR). **A correction to ADR-1584 itself**:
its claim that `Int.mul_le_mul_of_nonneg_left` is blocked by `linarith::
int`'s emitter does not hold under a direct grep — `linarith/int.rs` never
mentions it; the citing file (`sign_product.rs`) is an ordinary downstream
`int_prelude` consumer, not the emitter's own search code. That candidate
fails only check (ii), same as three others.

**Widened search (deliverable 5).** `Alg.monoidIdentUnique`/`Alg.
groupInvUnique` (ADR-1578's other two generic theorems): no carrier match
in any of the four preludes, a real negative. `Alg.ringMulZero`:
`Int.mul_zero`/`Rat.mul_zero` match by type (new test `ring_mul_zero_
matches_int_and_rat_mul_zero_by_type`, `rat_prelude/algebra_instances.rs`);
`Nat.mul_zero` does NOT (`Nat` has no `Ring` instance — no additive
inverse). `CReal.mul_zero`/`CReal.mul_le_mul_of_nonneg_left`/`CReal.
pow_add` exist as named theorems but are structurally unreachable: `CReal`'s
carrier equality is `Equiv`, never literal `Eq`, and the whole `Alg.*`
spine is built on `Eq` throughout — not a scoping gap this lane could close,
a design gap (a `Setoid`-flavored spine variant) left for a future ADR.

**One retirement landed: `Int.add_left_cancel`.** `Alg.mul_left_cancel`
needs only the abstract `Group` record, so it moved to `nat_prelude::
structures::declare_mul_left_cancel_early`, called right after the
structures spine — the earliest position in the whole build.
`sel`/`mk_instance`/`derive_left_unit` moved from `rat_prelude::
algebra_instances` to `nat_prelude::structures` alongside it, so
`int_prelude` (built before `rat_prelude` exists) can build an `Alg.*`
instance too. At the retirement site (`int_prelude::add_basics::
declare_add_left_cancel`), the hand `cancel_neg_add_left`-chain (~20 lines)
is replaced by `Alg.mul_left_cancel` applied at an INLINE, anonymous
`Alg.Group` value for `Int` (not the named `Int.addGroup`, still declared
unchanged at the tail — an anonymous value of the same type is enough).
Declared name and type of `Int.add_left_cancel` unchanged; every downstream
consumer sees no difference. Lines grew (~70 replacing ~20) because the
`Group` value is built inline rather than referencing a pre-existing named
instance — the duplicate PROOF ENGINEERING removed is conceptual (one
group-cancellation proof instead of two independent hand chains), not raw
line count for this one carrier.

**What stayed, and why (deliverable 4).** Three fail check (i) — the
emitter/`ring`-tactic citation stays; unblocking them needs `ring-tactic`/
`linarith-generic` (concurrent lanes this brief scoped out) to retarget
first. Four fail only check (ii) but were NOT moved: `Rat.neg_neg`/
`Rat.sub_self` sit inside `rat_prelude/group.rs`, upstream of 40+ downstream
citations across `creal/`/`matrix*.rs`/`probability.rs`; `Int.mul_le_mul_
of_nonneg_left`/`Rat.mul_le_mul_of_nonneg_left`/`Rat.pow_add` sit similarly
inside their preludes' own foundational layers. Moving each is the SAME
technique used for `mul_left_cancel`, but the risk is different in kind — a
mistake in `Int.add_left_cancel`'s single-consumer site fails one theorem;
a mistake moving `Rat`'s core instance early risks the whole downstream
`rat_prelude`/`creal` build. Named as a sized next step in ADR-1587 §6, not
silently deferred.

**Gates run.** `cargo test -p axeyum-lean-kernel --lib -- structures::
--test-threads=4`: 2/2. `-- int_prelude:: --test-threads=4`: **81 passed, 0
failed**, including `int_prelude_admits_all_declarations` and `every_int_
declaration_is_checked_and_axiom_free`. `-- rat_prelude::algebra_ext::
rat_prelude::algebra_instances:: nat_prelude::structures::
--test-threads=4`: **22 passed, 0 failed**, including `retirement_int_add_
left_cancel` (now exercising the retired proof) and the new `ring_mul_zero_
matches_int_and_rat_mul_zero_by_type`. `-- nat_prelude::
--test-threads=4`: **424 passed, 0 failed**. `-- rat_prelude::
--test-threads=4` (full whole-prelude smoke test, ADR-1584's own baseline
was 258): **259 passed, 0 failed** (868.65s under concurrent-lane load, the
+1 being the new widened-search test). `cargo clippy -p axeyum-lean-kernel
--lib --tests -- -D warnings`: clean (two `items_after_statements` findings
fixed along the way, no logic change). `cargo check -p axeyum-lean-kernel
--lib --tests`: clean. `rustfmt --edition 2024` on every touched file.
`validate-facts.py`: 2740
facts, 0 errors, `missing_edges=0` (`check-fact-depends-derived.py --fix`
added the two edges `Int.add_left_cancel`'s retired proof now genuinely
needs: `F:alg-mul-left-cancel`, `F:ml430-int-add-left-neg-c1bf80e1`).
`check-settled-fact-statements.py`: `unpinned=0`, `drifted=0` (this lane's
own scope is clean; the pre-existing 16-fact list-carrier header FAIL is
unrelated, from the merged `list-carrier`/`structures-2` work, not this
lane's). `gen-adr-index.py`: ADR-1587 indexed; the reported
`duplicate_numbers=0166,0167` predates this lane. `scripts/
check-generated-artifact-ownership.py`'s full sandboxed run did not
complete inside this lane's budget (times out past several minutes on this
host); the new `artifacts/refactor/generic-retirement-check.json` entry
structurally matches the existing `linarith-retirement-census.json`
pattern it was modeled on — did not run to completion, reported as such,
not claimed passing.

<!-- plan-section: landed-changes -->

| 2026-09-03 | retire-generic-1 | status stub |
| 2026-09-03 | retire-generic-1 | `scripts/generic-retirement-check.py` + `artifacts/refactor/generic-retirement-check.json`: the three ADR-1581 checks, run for real, for ADR-1584's six candidates plus two widened (`Alg.ringMulZero` vs `Int.mul_zero`/`Rat.mul_zero`) |
| 2026-09-03 | retire-generic-1 | ADR-1587 (amends ADR-1584): the six-plus-two-row table, the emitter-citation correction, one retirement landed, six named stays |
| 2026-09-03 | retire-generic-1 | retire `Int.add_left_cancel` to `Alg.mul_left_cancel`: move the generic theorem + `sel`/`mk_instance`/`derive_left_unit` to `nat_prelude::structures` (declared right after the record spine); `int_prelude/add_basics.rs`'s hand proof replaced by an inline `Alg.Group` application; declared name/type unchanged |
| 2026-09-03 | retire-generic-1 | clippy fix (`items_after_statements`, no logic change); full `rat_prelude::` sweep confirmed 259/259 (ADR-1584's 258 baseline +1, the new widened test) |
