# Lane: abstraction-mechanism — can a statement quantify over a *structure*?

<!-- plan-section: lane-status -->

**DONE, abstraction-mechanism, 2026-09-01. The answer is YES, and it was
already true.** Driver:
`docs/research/11-design-review/2026-09-01-the-abstraction-question-has-never-been-asked.md`
and [`docs/curriculum/foundational-books/axler.md`](../../curriculum/foundational-books/axler.md),
which tags roughly half of Axler's chapters `X-TA` — "no polymorphism in this
kernel's term language, so 'for every vector space' cannot even be **stated**
… **permanent** absent a change to the kernel's term language".

**That verdict is false.** Three probes, every stage first attempt, every
control firing, `axiom_footprint` empty throughout:

- `examples/bundled_structure_probe.rs` — `AbsProbe.Field`, a one-constructor
  inductive in `Sort 2` carrying a `Sort 1` **carrier as a field**, seven
  operations and ten laws (17 fields). Selectors by large elimination, then a
  **derived** cancellation theorem quantified over the structure.
- `examples/module_over_field_probe.rs` — `AbsMod.VecSp` **carrying the
  `Field` bundle as a field**, with `smul` typed through two nested
  projections, and a derived theorem chaining two of its laws. That is exactly
  "a vector space `V` over a field `F`", so Axler Ch.1–2 is stateable.
- `examples/g4_pilot_generic_assoc_probe.rs` (prior art, ADR-0865, 2026-08-30)
  had already settled the unbundled telescope half. Its finding was correct
  and was never propagated to the curriculum.

**The gap is surface, not capability.** 1,774 probe lines bought one `Field`,
one `VecSp`, 13 selectors and 2 theorems — no `structure` command, no
projection sugar, no instance resolution, and a dev-helper layer that hardcodes
a carrier.

**Decision (ADR-1495): yes to the statement class, no to a hierarchy, gated on
one named first consumer** — the carrier-generic congruence layer, whose
running metric is the 4 files carrying per-carrier `congr` helpers. `Nat.Fin`
still has **zero non-test consumers** (re-verified with a positive control), so
a mechanism ahead of a consumer is the outcome to avoid. Second rung, if the
first is adopted: a bundled algebraic structure over the **15 lemma names
proved at all five** of `Nat`/`Int`/`Rat`/`CReal`/`Complex` (49 at 3+, 23 at
4+). It must carry its own equality — `CReal.add_comm` is a setoid `Equiv`, not
`Eq`, and quotienting would cost `Quot.sound`.

**A soundness hole fell out of the probe's own control.**
`Kernel::add_inductive` never enforced Lean's constructor-field universe
constraint, so `U : Sort 1` with `mk : Sort 1 → U` plus large elimination made
`Sort u` a retract of an inhabitant of `Sort u` — `Type : Type`. Nothing in the
tree declared such an inductive and no `axiom_footprint` moves; this was a
checker weakness. Fixed, and **two pinned fixtures had been asserting that
Lean-illegal inductives ADMIT**, which is why it survived: 360 of the grammar
suite's 720 cases, and three universe shapes in the seam fuzz.

**Not run:** the full workspace `--lib` and `--tests` sweeps. Both were killed
at a 10-minute wall (exit 143, SIGTERM) inside the `creal`/`complex` suites and
neither reached a `test result:` line. What did run: `--lib inductive` 49
passed; twelve inductive-related integration suites 72 passed;
`prelude_theorem_inventory --release --include-constructed` exit 0 with 11,969
rows (every prelude still builds under the new guard); `clippy --release
-p axeyum-lean-kernel --all-targets -D warnings` clean.

**Highest-value follow-up, and it is a documentation task:** re-grade
`axler.md`'s legend and its Chapter 1/2/7/9 rows from `X-TA` ("permanent") to
unbuilt surface. The current text tells every future lane that half of linear
algebra is out of reach.

<!-- plan-section: landed-changes -->

| 2026-09-01 | `2be5cd11d` | First measurement before any probe: the kernel already admits dependent records with proof fields (`Rat` carries two, `Complex` uses large-elimination projections, `Exists.{u}`/`Acc.{u}` take a `Sort u` parameter). |
| 2026-09-01 | `de1a36083` | `bundled_structure_probe` + `inductive_universe_probe`: a 17-field `Field` bundle admits and a derived theorem quantified over it is accepted axiom-free; the universe control does NOT fire, exposing the `Type : Type` retraction. |
| 2026-09-01 | `c72fd281b` | Kernel guard: `KernelError::ConstructorFieldUniverseTooBig`, Lean's `check_constructor` universe constraint with `Prop` exempt. Repairs the two fixtures that asserted Lean-illegal inductives admit (grammar `type` families to `Sort 2`, pin and digest unchanged; seam-fuzz data fields clamped for bare-parameter universes). New test with two positive controls. |
| 2026-09-01 | `f933965ad` | `module_over_field_probe`: a bundle carrying another bundle, `smul` through two nested projections, derived theorem admitted — "a vector space over a field" is stateable and provable here. |
