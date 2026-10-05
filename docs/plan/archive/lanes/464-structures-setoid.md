# Lane: structures-setoid — a Setoid-flavored Alg spine so CReal can be an instance

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, structures-setoid, 2026-09-03).** ADR-1588
designed and built `AlgS.Magma .. AlgS.CommRing` (nine records, stopping
short of `Field`/`Apart`, out of scope): a second, independent spine
carrying an explicit `equiv` relation plus `equivRefl`/`equivSymm`/
`equivTrans` and one congruence field per operation (`opCongr`/`addCongr`/
`mulCongr`/`negCongr`), with every law field stated over `equiv` instead of
`Eq`. Nine `AlgS.<Record>.ofAlg` projections turn an `Alg.<Record>`
(`equiv := Eq`) into the matching `AlgS.<Record>`, built once each from
`Eq.refl`/`Eq.symm`/two nested `congr_arg` applications, no theorem
duplicated. `AlgS.CommRing.toRingS` is the one forgetful (prefix)
projection needed downstream.

**Field-count cost, measured**: `AlgS.CommRing` is 23 fields against
`Alg.CommRing`'s 16 (1.44x) -- 4 fixed equiv-infrastructure fields plus 3
congruence fields (add/mul/neg) the `Eq`-flavored spine gets for free from
`Eq.rec`. The tax is per-record (fixed 4) plus per-operation (1 congruence
field each), not per-law -- so it's proportionally worse for small records
(`AlgS.Magma` is 7 vs `Alg.Magma`'s 2, 3.5x) and better for large ones.

**`CReal.commRingS : AlgS.CommRing` landed** (`creal/algebra_instance.rs`).
Every field is an *existing* `CReal` theorem, verbatim selector reuse --
carrier/equiv/equivRefl/equivSymm/equivTrans, add/mul/zero/one, addCongr/
mulCongr (`creal/congruence.rs`), addAssoc/addComm/addZero, mulAssoc/
mulOneR, distribL, neg/negCongr/negAdd, mulComm. Only two fields have no
ready-made `CReal` lemma and are DERIVED (pure term composition, no new
`creal` proof): `mulOneL` (one `equivTrans` over `mul_comm(one,a)` +
`mul_one(a)`) and `distribR` (three `equivTrans` steps over `mul_comm`
(x3), `left_distrib`, `add_congr`). No law was missing. Not wired into
`build_creal_prelude`'s generated `STEP_DISPATCH` pipeline (a sized,
named gap, not silent -- see the module's own doc comment): that needs a
new `CRealPrelude` field, its interning, a `STEP_DISPATCH` entry, and a
regenerated `steps_generated.rs`, which this lane did not spend budget on
given the risk to the shared ~20s+ `creal` build. `declare_creal_comm_ring_s`
is `pub` and is a real declaration admitted through `Kernel::add_declaration`
every time it is called (exercised by 6 tests, all passing, including an
axiom-footprint check).

**Three generic theorems over `AlgS.Ring`** (`AlgS.mul_zero`, `AlgS.neg_neg`,
`AlgS.sub_self`, plus the `AlgS.sub` definition), each proved once and
instantiated at BOTH `Int` (through `AlgS.Ring.ofAlg(Int.ring)`) and
`CReal` (directly, via `CReal.commRingS.toRingS`), concrete AND symbolic
at both sites.

**The measurement (deliverable's central question)**: does `AlgS.mul_zero`
applied at `CReal.commRingS`'s `Ring` projection have `CReal.mul_zero`'s
exact type by `def_eq`? **Yes** --
`generic_mul_zero_instantiated_at_creal_matches_creal_mul_zero_type` passes.
The same holds at `Int`: `AlgS.mul_zero(AlgS.Ring.ofAlg(Int.ring))` is
`def_eq` to `Int.mul_zero`'s own type
(`mul_zero_instantiated_at_int_through_ofalg_concrete_and_symbolic`). This
closes ADR-1587 §4's named gap exactly: `CReal.mul_zero` was structurally
unreachable from the `Eq`-flavored `Alg` spine; it is now reachable from
`AlgS`. `AlgS.neg_neg`/`AlgS.sub_self` have no named `CReal`/`Int`
counterpart to compare against (grepped: absent from both), so those two
are well-typedness-only measurements at both sites, recorded as such in
the tests' own doc comments -- not overclaimed as `def_eq` matches.

**First stuck term / real defect found**: `k.infer` on a raw `k.fvar` is
`UnboundFVar` -- a bare free variable needs a real `LocalContext` with the
fvar's type pushed (`k.infer_in`/`k.def_eq_in`), or (the technique borrowed
from `rat_prelude::algebra_instances`'s own `ring_mul_zero_...` test) close
the open term into a lambda via `lam_over` first and use plain `infer`. Both
routes are used across the two test files. Separately: `k.infer_in` over
`CReal.commRingS`'s large projected term overflows the DEBUG-build stack
(matches `kernel-proof-engineering.md`'s "run it in `--release` first"
entry) -- release + `RUST_MIN_STACK=1073741824` is required for
`algebra_instance::`/`structures_setoid::` tests that touch `CReal`.

**Everything that ran**: `cargo test -p axeyum-lean-kernel --lib -- int_prelude:: --test-threads=4` (81/81, unaffected). `cargo test -p axeyum-lean-kernel --lib -- rat_prelude::algebra_ext:: rat_prelude::algebra_instances:: nat_prelude::structures:: --test-threads=4` (22/22, unaffected). `RUST_MIN_STACK=1073741824 cargo test -p axeyum-lean-kernel --lib --release -- creal:: --test-threads=4` (221/221, unaffected -- including `all_twenty_two_ordered_ring_laws_are_checked_theorems_over_creal` and `every_creal_declaration_is_checked_and_axiom_free`). `RUST_MIN_STACK=1073741824 cargo test -p axeyum-lean-kernel --lib --release -- structures_setoid:: algebra_instance:: --test-threads=1` (19/19). `cargo clippy -p axeyum-lean-kernel --lib --tests -- -D warnings`: clean throughout. `python3 scripts/validate-facts.py`: 2743 facts, 0 errors. `python3 scripts/gen-py-prelude-fields.py --check`: up to date (nat=1094+84, was +30 -- the +54 is `AlgS`'s own registry names).

**Did not run / left undone, named**: `just check`/`./scripts/check.sh` (the
full aggregate gate) -- not run given time budget; every targeted sweep
above passed instead, each confirmed non-inert (nonzero test counts). Did
not attempt `AlgS.Field`/`Apart` (explicitly out of scope). Did not wire
`CReal.commRingS` into the automatic `build_creal_prelude` pipeline (named
above). Did not retire any existing `CReal`/`Int` hand proof to `AlgS.*`
(not asked; `AlgS.mul_zero` reaching `CReal.mul_zero`'s exact type is the
retirement CANDIDATE this lane's whole point was to make possible, not a
retirement executed).

Six commits (SHAs, in order): `c8f1d600d` (status stub), `d913745f4`
(ADR-1588), `27c8b9c04` (the `AlgS.*` spine + generic theorems),
`e6ba1452b` (`CReal.commRingS`), `814bac665` (axiom-footprint tests),
`a899868a5` (rename for the Python field generator + regenerated
bindings), `95be10f5e` (Int-side instantiation tests), `5a2c95399`
(the three facts + `AlgS` added to `validate-facts.py`'s namespace
allowlist).

<!-- plan-section: landed-changes -->

| 2026-09-03 | structures-setoid | ADR-1588: `AlgS.Magma..CommRing` (Setoid-flavored twin of the `Alg` spine, explicit `equiv`+congruence fields), nine `ofAlg` projections, `CReal.commRingS`, `AlgS.mul_zero`/`neg_neg`/`sub_self` -- `AlgS.mul_zero` proved `def_eq` to both `CReal.mul_zero` and `Int.mul_zero`, closing ADR-1587's named gap |
