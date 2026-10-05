# Lane: linarith-generic — `linarith` over an arbitrary `Alg.OrderedRing`

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, linarith-generic, 2026-09-03).** ADR-1584 §5
named three blockers to a `linarith` emitter generic over
`(R : Alg.OrderedRing)` instead of a fixed `NatPrelude`/`IntPrelude`. All
three are built, tested green, and written up as ADR-1585 (amends
ADR-1584). Nothing was deleted; see the delete-or-keep verdict below.

**Blocker 1 — missing field citations, derived (not added as new record
fields).** `crates/axeyum-lean-kernel/src/rat_prelude/ordered_ring_ext.rs`
(new file): `Alg.add_le_add_right`, `Alg.le_of_add_le_add_right`,
`Alg.add_le_add` — each a real `∀ (R:OrderedRing) …` kernel theorem,
proved once generically from `OrderedRing`'s five primitive order laws
(`le_refl`, `le_trans`, `le_antisymm`, `add_le_add_left`, `mul_nonneg`)
plus `Ring`'s `neg`/`negAdd`/`addComm`/`addAssoc`/`addZero`. `Alg.
add_le_add_right`/`add_le_add` instantiated at `Int.orderedRing` have the
SAME TYPE as the existing hand-proved `Int.add_le_add_right`/
`Int.add_le_add` (`Kernel::infer` + `Kernel::def_eq`) — genuine,
unattempted retirement candidates. `Alg.le_of_add_le_add_right` has no
standalone hand-proved counterpart under this exact name (only the `Iff`
form `add_le_add_iff_right` exists) — a NEW fact, checked for
type-correctness at both `Int.orderedRing` and `Rat.orderedRing` rather
than compared against a hand proof. The `lt`/strict fragment
(`add_lt_add_of_le_of_lt`, `mul_pos`) is left open — ADR-1584's own
verdict ("genuinely new, not a derivation") stands; see the first stuck
term below.

**Blocker 2 — a generic numeral builder.** Same file: `Alg.ofNat : Pi
(R:OrderedRing), Nat -> R.carrier`, a `Nat.rec` over `R`'s own
`add`/`one`/`zero` (the constant-motive-in-`n` shape `Alg.npow` already
uses). Declared in `rat_prelude/ordered_ring_ext.rs`, NOT
`nat_prelude/structures.rs` — measured, not assumed: `Nat.rec` does not
exist yet at the point `nat_prelude.rs` interns the algebra spine (only
`LogicPrelude` is available there). `Alg.ofNat_add` (induction on `n`, the
argument `Nat.add` recurses on) and `Alg.ofNat_le_ofNat_of_le` (induction
on the `Nat.le` DERIVATION via `Nat.le.rec`, `m` fixed as the recursor's
parameter — the same shape `nat_prelude/order.rs`'s `le_trans` uses).
**`ofNat_le_ofNat_of_le` takes an explicit `zero <= one` witness as a
hypothesis, load-bearing and real, not incidental**: it is NOT derivable
from `OrderedRing`'s five order laws alone (nothing in the record rules
out an instance with `one < zero`). Both `Int.orderedRing`/
`Rat.orderedRing` supply it easily (`le_of_lt` on the carrier's own
`zero_lt_one`). Evaluation: `Alg.ofNat Int.orderedRing 3` reduces
(`def_eq`) to `Int.ofNat 3`, with a discriminating negative control
against `Int.ofNat 4`. `ofnat_add`/`ofnat_le_ofnat_of_le` type-check
symbolically at both carriers.

**Blocker 3 — decoupling emission from `IntDev`/`NatDev`.**
`crates/axeyum-lean-kernel/src/linarith/generic.rs` (new file):
`linarith::generic`, a `≤`/`=` Farkas emitter over one fixed
`(ring, R:OrderedRing)` term, its `Problem` struct caching every
selector/derived-lemma application as plain `ExprId`s — no `IntDev`/
`NatDev` type or method anywhere in the module. The certificate SEARCH
(`super::find_certificate`/`find_combination`) is unchanged, confirming
ADR-1584's own finding that it was already carrier-agnostic.

**Scope, stated in the module's own doc comment, not discovered later.**
Deliberately short of `linarith::int` in two ways: **no `<` at all**
(`Alg.OrderedRing` has no `lt` field; a `<` hypothesis parses as a useless
opaque atom, a `<` goal declines `GoalNotAtomic` — **this is the first
stuck term**), and **no literal multiplication** (none of the retirement/
new-capability goals need it; a literal-mul subterm parses as a sound
opaque atom). Everything else — the additive fragment, Farkas
combination, the constant-first canonical-form normalizer (flatten /
bubble-sort arrange / prepend-zero / reassociate) — is `linarith::int`'s
exact structure, ported mechanically.

**A real bug the port surfaced, fixed, not `linarith::int`'s bug.** The
shared `find_certificate` accepts `LinForm::is_nonneg_cone` (nonnegative
CONSTANT *or* nonnegative ATOM coefficients — the ℕ-style reading) and
returns the SMALLEST-WEIGHT certificate meeting that bar. Over an
arbitrary `OrderedRing`, an atom is not guaranteed nonnegative, so a
smaller-weight certificate whose residual still mentions an atom can be
found FIRST and then correctly refused by `emit_le`'s own
`is_constant()` check — with no fallback to the larger, genuinely-constant
certificate the goal needs. Measured concretely: the goal `0<=a, 0<=b |-
0<=a+b` (one of the three new-capability targets) declined on the first
attempt for exactly this reason. Fixed by exposing `find_combination`
(now `pub(crate)` in `linarith.rs`, was private) and calling it in
`generic::Problem::prove_le` with the strict acceptance
`is_constant() && const_term() >= 0` directly, so the search itself skips
the unusable smaller certificate. `linarith::int`/`nat.rs` untouched —
this only widens what `find_combination`'s existing signature is called
with elsewhere.

**Test results.** Seven of seven `int_prelude` retirement targets
(ADR-1576's five plus ADR-1581's two: `add_le_add_three`,
`add_le_of_le_neg_add`, `add_le_of_le_sub_left`, `add_le_of_le_sub_right`,
`add_left_comm`, `add_neg_cancel_left`, `add_neg_cancel_right`) re-proved
through `linarith::generic` at `Int.orderedRing`, each ACCEPTED by
`Kernel::infer` at the SAME TYPE as the existing hand-proved `Int.*`
declaration. Three new-capability goals at `Rat.orderedRing` (no
`linarith` route over ℚ existed before this lane): transitivity, sum of
nonnegatives, and a slack-1 goal (`a<=b |- a<=b+1`, genuinely exercising
`Alg.ofNat`/`ofNat_le_ofNat_of_le`; a companion assertion confirms the
same goal declines when no `zero_le_one` witness is supplied). Three
false goals decline (`a<=b |- b<=a`; `a<=b<=c |- c<=a`; `|- a+1<=a`).
Three corrupted certificates (`verify: false`, so only the KERNEL can
catch a bad witness) rejected at `Kernel::infer`: multiplier 2 where 1 is
correct, residual 0 where 1 is required, and a hypothesis slot carrying a
proof of a DIFFERENT true proposition (`le_refl c` in a slot typed
`le a b`); a fourth (positive-control) test confirms the SAME route
admits the UNCORRUPTED certificate, so the three rejections are not
evidence of a broken emitter.

**ms comparison.** `--release`, 200 repeats, `add_le_add_three`'s shape,
search only, single unpinned run on a shared host (order of magnitude,
not a baseline — see `docs/contributor-guide/measurement-hazards.md`):
`linarith::int` 8.591 ms/term vs `linarith::generic` 9.686 ms/term — about
13% slower, plausibly explained by one extra selector-application
indirection per field access (`App(Const(field_sel), R)` vs a bare
top-level constant) with everything else identical. One shape, one host —
not a claim the ratio holds generally. Reproduce:
`cargo test --release -p axeyum-lean-kernel --lib -- linarith::generic::
generic_tests::measured_ms_generic_vs_int --exact --ignored --nocapture`.

**Delete-or-keep verdict on `linarith::int`/`linarith::nat`: KEEP, for two
independent reasons, neither a build-order technicality.** (1)
`int_prelude`'s own `declare_*` call sites still cite
`linarith::int::declare` directly; retargeting even one of the seven
retirement targets needs those call sites rewritten to build an
`Int.orderedRing` term and go through `linarith::generic::prove` instead
— not attempted here, matching ADR-1581's own "blocked-pending-check, not
blocked outright" for its own candidates (a type match is necessary, not
sufficient — the retirement site's build-sequence position must also be
checked, which this lane did not do). (2) `linarith::int` covers ground
`linarith::generic` structurally cannot reach: the whole `<`/strictness
fragment, literal multiplication, and the refutation route (`¬(≤)` goals).
`linarith::nat` additionally serves ℕ, which has no `neg` field and so is
not an `OrderedRing` instance at all — `linarith::generic` cannot reach ℕ
without a separate `OrderedSemiring`-shaped record, not attempted.
**Nothing deleted.**

**Gates run.** `cargo test -p axeyum-lean-kernel --lib -- linarith::
--test-threads=4`: **72 passed, 0 failed** (17 new `linarith::generic::
generic_tests`; every pre-existing `linarith::{tests,int_tests,
core_tests}` unaffected). `-- structures:: rat_prelude::algebra_ext::
--test-threads=4`: **17 passed, 0 failed** (ADR-1578/1584's own suites
unaffected by the `EqB`/`Problem` additions). `cargo clippy -p
axeyum-lean-kernel --lib --tests -- -D warnings`: clean. `rustfmt
--edition 2024` on every touched file. `python3 scripts/validate-facts.py`:
2742 facts, 0 errors (includes the two new `F:alg-ofnat-add`/
`F:alg-ofnat-le-ofnat-of-le` facts). `gen-py-prelude-fields.py --check`:
see the landed-changes row for the counts.

**What did NOT run.** The full `rat_prelude::` sweep — out of scope per
the brief's own "no sweeps" instruction; attempted once anyway out of
caution, exceeded a 590s foreground timeout mid-run with no failures
observed in the partial output before it was cut off, so it is reported
as **did not run to completion**, not as evidence either way. `just
check`/the full aggregate gate was not run (out of scope). `int_prelude::`'s
own filter was not run separately (this lane touched no `int_prelude`
file; the `rat_prelude::algebra_ext::` sweep above builds `int_prelude`
transitively as part of `rat_prelude_builds`, which is not itself in the
targeted list run here). The `lt`-fragment extension to `Alg.OrderedRing`
(blocker 1's genuinely-new half) was not attempted — named, not silently
deferred (see ADR-1585's Alternatives section for why).

**SHAs.** `52445da65` (initial WIP commit, per the coordinator's early-commit
instruction — landed the OrderedRing extensions and a first draft of
`linarith::generic` before the test suite had been run once).
`2574afcd9` (fixes making all 17 `generic_tests` green: bare `R.zero`/
`R.one` literal recognition, the `find_combination` strict-acceptance
fix, two Eq-goal carrier-mismatch test bugs, and clippy/dead-code
cleanup). This commit (below): ADR-1585, the two `Alg.ofNat` law facts,
the ms measurement, `prelude_fields.rs` regeneration, and this status
writeup.

<!-- plan-section: landed-changes -->

| 2026-09-03 | linarith-generic | status stub |
| 2026-09-03 | linarith-generic | `ordered_ring_ext.rs` (new): `Alg.add_le_add_right`/`le_of_add_le_add_right`/`add_le_add` derived from OrderedRing's five order laws; `Alg.ofNat`+`ofNat_add`+`ofNat_le_ofNat_of_le`; `EqB` toolkit added to `structures.rs`; `linarith/generic.rs` (new, WIP, untested) |
| 2026-09-03 | linarith-generic | `linarith::generic` fixed to 17/17 green: literal-zero/one recognition, `find_combination` exposed + used with strict acceptance, two test carrier bugs, clippy clean |
| 2026-09-03 | linarith-generic | ADR-1585; `F:alg-ofnat-add`, `F:alg-ofnat-le-ofnat-of-le`; ms-measurement test (`measured_ms_generic_vs_int`, `#[ignore]`d); status writeup |
