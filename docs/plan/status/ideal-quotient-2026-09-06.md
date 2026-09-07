# Lane: ideal-quotient — an ideal and the quotient ring, ADR-1676

<!-- plan-section: lane-status -->

**`DONE` (2026-09-06), 3 of 4 deliverables landed; deliverable 3 stopped with a
measured obstruction, as the brief instructed.** Brief: topic 4, carrier 3 of
the algebra shelf — `ideal` occurred **zero** times in the kernel source
(positive control in the same sweep: 981 `AlgS.` references), and so did
`subring`, `submodule`, `quotientRing`, `localiz`, `tensor`, `irreducib`,
`splitting`.

**Landed:** `crates/axeyum-lean-kernel/src/nat_prelude/ideal_setoid.rs`, 31
declarations under a fresh `AlgS.Ideal` namespace, every one admitted through
`Kernel::add_declaration` with an **empty** `Kernel::axiom_footprint` read from
the kernel.

- **Nine generic `AlgS.CommRing` lemmas** the spine did not have: `zeroAdd`,
  `negAddL` (the record carries `addZero`/`negAdd` on the RIGHT only),
  `negZero`, `zeroMul`, `mulNegR`, `mulNegL`, `negAddDist`, `addSwapMid`,
  `addRegroup`. `negAddDist` is three steps through `-1`
  (`-(a+b) ~ (a+b)*(-1) ~ a*(-1)+b*(-1) ~ (-a)+(-b)`); the obvious additive
  route is thirteen. They are namespaced under `AlgS.Ideal.*` to keep name
  allocation lane-local and **deserve promotion to `AlgS.*` once a second
  consumer appears** — recorded as debt in ADR-1676 §4.
- **`AlgS.Ideal.IsIdeal`, a five-conjunct PREDICATE** (not a record; the
  trade-off and what it costs the next lane are ADR-1676 §1), with five
  projection theorems. The five line up one-for-one with
  `AlgS.Subgroup.IsSub`'s four plus the absorbing law, so **"ideal" over
  "additive subgroup" costs exactly one field**, and the setoid tax is the same
  one field it is for subgroups.
- **Three instances**, so the predicate is not vacuous: `bot` (the equivalence
  CLASS of zero — the singleton is not closed under `R.equiv`), `top`, and the
  principal ideal `principal R g`, each with its `IsIdeal` proof.
  `principal_isIdeal` exercises nested `Exists` elimination and every helper.
- **`AlgS.Ideal.quotient : forall R I hI, AlgS.CommRing`** — `R/I` as a setoid
  coarsening on `R`'s own carrier, `x ~ y := I (x + (-y))`. All 23 fields are
  listed with labels in the body. Measured split: **6** are `R`'s own
  unchanged, **1** is the coset relation, **6** are hand-discharged congruence
  obligations, and **the ten ring LAWS are all free** through one four-step
  lemma `AlgS.Ideal.ofEquiv` — because the coset relation is COARSER than
  `R.equiv`, no ring law is re-proved. `quotient_equiv` is proved by
  `Iff.intro id id`, so it passes only if the selector on the instance reduces
  definitionally.

**Deliverable 3 (`R/ker f ≅ im f` in ring form) did NOT land.** The brief said
to stop and report the exact obstruction if it needs more than a transport. It
does, for four measured reasons: `AlgS.Hom.firstIso` and `firstIsoClassical`
quantify over `AlgS.Group` only; there is no coercion between the two records;
`HomCtx` (`structures_setoid.rs:2833`), `hom_ctx` (2867), `close_ghf` (2972)
and `close_hom` (2992) are module-private and hard-coded to the FIVE group
binders where a ring hom needs seven; and the image side needs an
`imageRing : AlgS.CommRing` with five membership proofs where `imageGroup` has
three. **The obstruction is gated as a test**, not asserted in prose:
`the_group_first_isomorphism_theorem_says_nothing_about_rings` reads both
rendered types from the kernel and goes red if the ring form ever becomes a
transport, with `AlgS.Ideal.quotient` as the positive control in the same
invocation. Four-declaration sizing for the next lane is in ADR-1676 §5.

**One real defect found and fixed on the way:** `declare_principal_is_ideal`
used `A_FV` for the principal ideal's GENERATOR, and the conjunct builders bind
`A_FV` inside `respects`, `closedAdd` and `absorb`. The statement's own
`pi_over` swallowed the generator and the kernel refused with an opaque
`TypeMismatch` naming nothing. Fixed with a dedicated `G_FV` outside the
statement builders' range, with a comment saying why.

**Mutation table — RUN, not predicted.** Each rebuilds a weakened `IsIdeal`
under a scratch namespace and asks the KERNEL; each carries a positive control
in the same test.

| mutant | predicted | RUN — what actually died | class |
|---|---|---|---|
| `absorb` dropped from `IsIdeal` | `quotMulCongr` unprovable | `quotMulCongr` REFUSED; `quotSymm` still admits | kernel rejection |
| `closedNeg` dropped from `IsIdeal` | `quotSymm` unprovable | `quotSymm` REFUSED; `quotMulCongr` still admits | kernel rejection |
| `quotSymm`'s last leg reversed (`addComm y (-x)`) | rejected | REFUSED; unreversed accepted in the SAME invocation | kernel rejection |

All three are kernel rejections, which proves the statements are load-bearing
but says nothing about the tests. The counterweight is the **evaluation test**,
a case the kernel ADMITS: `AlgS.Ideal.principal` at
`AlgS.CommRing.ofAlg(Int.commRing)` unfolds by reduction to exactly
`Exists Int (fun r => R.equiv 4 (R.mul r 2))`, `Exists.intro 2 (Eq.refl 4)`
proves `4 ∈ (2)` (type-checks only because `Int.mul 2 2` reduces to `4`), and —
same invocation — witness `1` does **not**, because `1 * 2` is `2`. Magnitudes
1, 2, 4 only; every `Nat` numeral underneath is unary.

**Gates, with counts and exit status.** `ideal_setoid_tests` **11 passed**
(release, ~15 s); `cross_prelude_collision_tests` **8 passed** (~75 s),
including `every_declaration_a_prelude_introduces_is_checked_and_axiom_free`,
whose ownership comes from the build-order diff and so covers these 31 with no
hand-maintained list; `nat_prelude_tests::every_nat_declaration_is_checked_and_axiom_free`
**1 passed**; `clippy -p axeyum-lean-kernel --all-targets --all-features
-D warnings` exit 0; `cargo check --workspace --all-targets` exit 0;
`cargo fmt --all --check` exit 0; `./scripts/check-links.sh` exit 0
("all links ok"); `gen-adr-index.py` regenerated (one row added).

**Did NOT run:** `just check` / `./scripts/check.sh`, the workspace test sweep,
`validate-facts.py`, the frontier ratchets, and any solver, CAS or Lean gate —
out of this lane's scope, and no fact-ledger entry was added. **Did not touch:**
`crates/axeyum-cas/`, the solver crates, `lean/`, `docs/math-department/`,
`metric*.rs`, `rat_prelude/probability*.rs`, `artifacts/facts/`, or
`structures_setoid.rs` (not even a `pub use` — none was needed).

<!-- plan-section: landed-changes -->

| 2026-09-06 | `7e4ec836a` | `AlgS.Ideal.*` scaffold: nine generic `AlgS.CommRing` lemmas, `IsIdeal` as a five-conjunct predicate with five accessors, `bot`/`top`/`principal` with their `IsIdeal` proofs, and `AlgS.Ideal.quotient : forall R I hI, AlgS.CommRing` — `R/I` as a coarsening on `R`'s own carrier, ten of its 23 fields free through `ofEquiv`. Wired into `nat_prelude.rs`. |
| 2026-09-06 | `33de9289a` | The suite: ten tests reading the kernel, three mutants RUN (all kernel rejections, each with a positive control in the same test), and the evaluation test at ℤ with a discriminating negative. Fixed one real defect — the principal ideal's generator shared a free variable with the conjunct builders' own binders. |
