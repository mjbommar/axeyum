# Lane: quotient-decision — W0-1, the quotient/extensionality decision (ADR-1595)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, quotient-decision, 2026-09-04).** Roadmap W0-1
(convergence C1: reviewers 04.1, 09.3, 12.1) is decided **by measurement**, and
the measurement is roadmap W2-8 — the first isomorphism theorem over
`AlgS.Group` — which **landed by the setoid route with an empty axiom
footprint**.

Twelve declarations in a new `AlgS.Hom.*` namespace
(`nat_prelude/structures_setoid.rs`, `5337d192b`): `ker`, `kerEquiv`, `image`,
`mapOne`, `mapInv`, `kerEquivOpCongr`, `kerEquivInvCongr`, `quotient`,
`quotient_equiv`, `quotient_equiv_iff_ker`, `image_mem`, `firstIso`. The
construction: a quotient group is the SAME carrier under a COARSER
equivalence — `AlgS.Hom.quotient : ... -> AlgS.Group` has `carrier :=
G.carrier` and `equiv := fun a b => H.equiv (f a) (f b)`. No `Quot`, no
`Quot.sound`, no `funext`.

Cost: 1,061 lines of term-building Rust plus 281 of tests; 12 declarations
(`shape_search` 2674 → **2686**, exactly +12); `first_iso_tests` 0.44 s;
whole `structures_setoid` suite 16.41 s, 18 passed.

**The number the experiment existed to produce: 3.** Of `AlgS.Group`'s
fifteen fields, exactly three (`equivRefl`, `equivSymm`, `equivTrans`, one
line each) were discharged by hand and would have been free under
`Quot` + `Eq`. The two real congruence proofs (`kerEquivOpCongr` 7 steps,
`kerEquivInvCongr` 6 steps) do **not** go away under `Quot.sound` — they
reappear as `Quot.lift₂`/`Quot.lift`'s well-definedness side conditions — and
the five group laws are *cheaper* on the setoid route (one `fCongr`
application each vs a `Quot.ind` induction).

Two measurements nobody asked for that decide it:

1. **`Quot.sound` is five footprint entries, not one.**
   `Kernel::axiom_footprint` filters the dependency closure to
   `Axiom | Opaque | Quotient`, so anything routed through `Quot` names
   `Quot`, `.mk`, `.lift`, `.ind` and `.sound`. Today `quot=0` in every
   constructed prelude and `add_quotient_package` is called only by the Lean
   importer and the kernel's own differential tests.
2. **`Quot.sound` does not unlock the classical statement.** The image side
   needs a subtype; `Subtype` and `Sigma` are both ABSENT (`shape_search`,
   fresh binary, positive control `any-kind=2686`). The setoid route has no
   such gap because the quotient *is* the image.

Recommendation in ADR-1595 (`Status: proposed`): **option (b), commit to
setoid quotients**, reversible on evidence — a *named, attempted* theorem
shown unreachable over setoids, with the obstruction stated as a specific
obligation the kernel could not discharge.

Downstream: **W2-8 is landed.** W3-3 (categories) has no remaining
foundational blocker — morphism equality is an explicit `equiv` field, and
`funext` is a separate question this ADR does not answer. W2-9 and W3-2
proceed over `AlgS.CommRing` (W3-2 additionally wants an `AlgS.Field`, which
needs `Apart` — ADR-1588 stopped short of `Field` for that reason; a distinct
open question). Reviewers 04 and 09 have their stated triggers met; 12's
W0-2 is still open.

ℝ, sized not attempted: migrating `CReal` to `Quot CReal.Equiv` would restate
**209** declaration types (of **610** `CReal.*` declarations), rework the
proofs beneath them, retire the 233-declaration `AlgS` spine that exists to
serve it, and put the 5-name quotient footprint on the entire real-analysis
shelf. **Do not migrate.**

Gates run (all green, nonzero counts): `--lib first_iso_tests` 5 passed;
`--lib structures_setoid` 18 passed; `--lib linarith` 99 passed / 1 ignored;
`cargo check --workspace --all-targets` clean; `clippy -p axeyum-lean-kernel
--all-targets -D warnings` clean; `rustfmt --edition 2024` on the one touched
Rust file; `gen-py-prelude-fields.py` regenerated (total=3211) after the
twelve new `StructuresSExtraNames` fields.

Next lane: the ADR is `Status: proposed` and needs the coordinator or the
user to accept it. Nothing in this lane depends on that acceptance — the
theorem is landed and axiom-free either way.

<!-- plan-section: landed-changes -->

| 2026-09-04 | quotient-decision | W2-8 landed: the first isomorphism theorem over `AlgS.Group` by the setoid route, 12 declarations, empty axiom footprint |
| 2026-09-04 | quotient-decision | ADR-1595 (proposed): quotients stay setoids; `Quot.sound` stays out — decided by the W2-8 measurement, not by argument |
