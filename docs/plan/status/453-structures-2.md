# Lane: structures-2 — forgetful projections, cross-carrier generic theorems, retirement, `OrderedRing`

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, structures-2, 2026-09-03).** ADR-1584 (amends
ADR-1578) landed and every deliverable in the brief landed. Starting from
`structures-1`'s merged spine (`Alg.Magma..Field`, ℕ/ℤ/ℚ instances, three
generic theorems), this lane added seven forgetful projections, six more
generic theorems, a retirement measurement, and `Alg.OrderedRing`. Full
account is ADR-1584; this block is the pulse.

**Projections landed (all seven).** `CommMonoid.toMonoid`, `CommGroup.
toGroup`, `CommRing.toRing`, `Field.toCommRing` are literal PREFIX
projections (target's fields are a prefix of the source's, same order).
`Group.toMonoid` and `Ring.toMonoid` (multiplicative) select a
non-contiguous subset, no derivation. `Ring.toCommGroup` (additive) is the
one needing derivation: `identL`/`invL` have no `Ring` primitive, derived
from `addComm` + the RIGHT-handed field via a new `derive_inv_left` helper
(the `derive_left_unit` shape, generalized to the inverse law).
`int_comm_ring_projects_to_monoid_and_mul_one_reduces`: the deliverable's
evaluation test, `Int.commRing -> Ring -> Monoid`, `mulOneR`'s type read by
REDUCTION and `def_eq`-compared against `Int.mul_one`'s own rendered type;
negative control confirms the projected carrier is `Int` itself, not a
fresh/opaque one. `monoid_ident_unique_applies_through_the_comm_monoid_to_
monoid_projection` closes the exact `TypeMismatch` gap ADR-1578 measured.

**Six generic theorems landed, footprints all `[]`, no stuck term.**
`Alg.mul_left_cancel` (Group), `Alg.neg_neg` (Group, a direct instantiation
of `Alg.groupInvUnique` — no new proof engineering), `Alg.sub`+`Alg.sub_self`
(Ring, `sub a b := add a (neg b)`, matching `Rat.sub`/`Int.sub` exactly),
`Alg.mul_neg_one` (Ring, built via `Ring.toCommGroup`+`CommGroup.toGroup`+
`Alg.groupInvUnique` — the projections' payoff use case), `Alg.npow`+`Alg.
pow_add` (Monoid; `npow` RIGHT-multiplies to match `Nat.add`'s own recursion
direction, so `pow_add`'s induction needs no self-commutation lemma at all —
a left-multiplying first design would have needed one), `Alg.mul_le_mul_of_
nonneg_left` (`OrderedRing`). Everything instantiated at 2 carriers each
(concrete+symbolic split across the six per `kernel-proof-engineering.md`'s
rule), 21 tests total in `rat_prelude::algebra_ext::`, all green. **Nothing
stuck** — every attempted theorem landed; two direction bugs (a permuted
lambda-binder order in a derived instance field, two `symm_of` calls with
swapped `(a,b)`) were caught by the kernel's own `TypeMismatch` on the
FIRST full-prelude build attempt (`rat_prelude_builds`) and fixed by reading
`expected`/`got`, not by re-deriving the proofs by hand.

**Retirement: five type-level matches, one full `def_eq` match, zero
deletions.** `Int.add_left_cancel`, `Rat.neg_neg`, `Rat.sub_self`, `Int.
mul_le_mul_of_nonneg_left`, `Rat.mul_le_mul_of_nonneg_left` all match their
generic instantiation BY TYPE (`Kernel::infer` + `Kernel::def_eq`, never a
doc comment). `Rat.pow_add` matches `Alg.pow_add(Rat.commMulMonoid)` by full
`def_eq` — stronger, because `Alg.npow` and `Rat.pow` are themselves
`def_eq` at symbolic arguments (measured, not the ADR-1578 `detR`/`Rat.det`
one-value case). Two named absences worth recording: `Nat.mul_left_cancel`
doesn't exist under that name (only the CONDITIONAL `..._of_pos`, since
`Nat`'s multiplicative monoid has no inverse — this theorem does not
generalize it); `Int.neg_neg` is a private Rust HELPER in `gcd.rs`, never a
kernel theorem, so `Alg.neg_neg(Int.addGroup)` is a NEW fact there, not a
retirement. **Nothing deleted** — ADR-1581's rule (a hand proof's citations
are necessary, not sufficient) applies unchecked to all five/six matches;
`Int.mul_le_mul_of_nonneg_left` in particular is cited directly by
`linarith::int`'s emitter (`sign_product.rs`), so retiring it needs the
build-sequence-position check ADR-1581 §1 requires, which this lane did not
do.

**`Alg.OrderedRing`: landed at Int and Rat.** `Ring`'s 15 fields restated
plus `le`+5 order laws (21 total, same `Sort 2` universe-guard control every
record carries). `Int.orderedRing`: every field a direct `Int.*` selector.
`Rat.orderedRing`: `add_le_add_left` derived from `add_le_add`+`le_refl`
(`Rat` has no primitive). `Alg.mul_le_mul_of_nonneg_left` proved without
ever computing `mul a (neg b)` (see ADR-1584 §4 for the exact chain);
needed a new generic `subst` helper (`Eq.rec` transport for an arbitrary
predicate, generalizing `congr_arg`).

**`linarith`-over-`OrderedRing`: structurally reachable, not attempted.**
`linarith`'s SEARCH is already carrier-agnostic; only the EMISSION layer
(`linarith::int`/`nat`) hardcodes `IntPrelude`/`NatPrelude` constants
instead of projecting through a structure value's selectors. Retargeting
needs three things this lane did not build: (1) `Alg.OrderedRing` is
missing fields the emitter's fixed chain cites (`add_le_add_right`,
`le_of_add_le_add_right`, the whole `lt` fragment — some derivable, `lt`
genuinely new); (2) a generic numeral-construction routine (`R.add R.one
…` folded, not `Nat.succ`/`Int`'s own literal representation); (3)
decoupling `linarith::declare`'s emission closures from the concrete
`IntDev`/`NatDev` types so they take an abstract structure argument instead
— a real refactor. Full reasoning: ADR-1584 §5.

**Gates run.** `cargo test -p axeyum-lean-kernel --lib -- rat_prelude::
algebra_ext:: --test-threads=4`: 15/15. `-- nat_prelude::structures::
rat_prelude::algebra_instances:: --test-threads=4`: 6/6 (ADR-1578's own
suite unaffected). `-- rat_prelude:: --test-threads=4`: **258 passed, 0
failed** (ran to completion in background after ~14 minutes, queued behind
`cargo-serialized.sh`'s host-wide flock under concurrent-lane load — the
notification landed after this status block was mostly drafted, folded in
before commit, not reported as "did not run"). `-- nat_prelude::
--test-threads=4`: **424 passed, 0 failed**. `cargo clippy -p
axeyum-lean-kernel --lib --tests -- -D warnings`: clean. `cargo check -p
axeyum-py`: clean. `rustfmt --edition 2024` on every touched file.
`validate-facts.py`: 2733 facts, 0 errors. `check-fact-depends-derived.py
--fix`: one edge added. `check-settled-fact-statements.py --write`:
`unpinned=0`. `gen-py-prelude-fields.py`: `nat=1094+33` (+3, `OrderedRing`'s
`ind`/`mk`/`rec`), `rat=506+33` (+17, `AlgebraExtNames`'s 17 fields);
`--check` confirms up to date.

**What did NOT run**: `just check`/the full aggregate gate was not run in
this lane (out of scope per the brief's own scoping — targeted `--lib --`
filters plus the full `rat_prelude::`/`nat_prelude::` sweeps were what was
asked for); `int_prelude::`'s own filter was not run separately (this lane
touched no `int_prelude` file, and the full `rat_prelude::`/`nat_prelude::`
sweeps both build and exercise `int_prelude` transitively — `rat_prelude_
builds` alone is the whole-environment smoke test and it is one of the 258).

<!-- plan-section: landed-changes -->

| 2026-09-03 | structures-2 | status stub |
| 2026-09-03 | structures-2 | ADR-1584; `Alg.OrderedRing` record + `subst` helper (`nat_prelude/structures.rs`); seven projections, six generic theorems (`Alg.mul_left_cancel`/`neg_neg`/`sub`+`sub_self`/`mul_neg_one`/`npow`+`pow_add`/`mul_le_mul_of_nonneg_left`), `Int`/`Rat.orderedRing` instances (`rat_prelude/algebra_ext.rs`, new file); 21 tests, all green |
| 2026-09-03 | structures-2 | six fact-ledger entries (`F:alg-mul-left-cancel`, `F:alg-neg-neg`, `F:alg-sub-self`, `F:alg-mul-neg-one`, `F:alg-pow-add`, `F:alg-mul-le-mul-of-nonneg-left`); `prelude_fields.rs` regenerated |
