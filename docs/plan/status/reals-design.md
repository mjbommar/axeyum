# Lane: agent-reals-design — constructing ℝ over ℚ with zero axioms

<!-- plan-section: lane-status -->

**ℝ has a route and it is free (`DONE`, agent-reals-design, 2026-08-17).**
[ADR-0468](../../research/09-decisions/adr-0468-real-is-constructed-as-a-setoid-over-the-rationals.md)
decides **a Bishop setoid of regular ℚ-sequences** — no quotient, no cuts.
ADR-0456's two rejections were both correct and its conclusion did not follow:
equality does not have to be `Eq`. Measured, not argued —
`cargo run -q -p axeyum-lean-kernel --example creal_shape_probe` admits the
carrier, its recursor, the representative projection (large elimination) and the
setoid relation over the *constructed* `Rat` with a **trusted surface of 0**, and
a `funext` negative control in a second kernel returns a non-empty footprint so
the zero is discriminating. The price is counted too: **9 of 30** `Real`
declarations mention `Eq`, so 13 of the 22 laws are discharged verbatim and 9
only in `Equiv` form — the order fragment Farkas actually uses is untouched.
Adding `Quot.sound` instead would read `real: axiom=0 quotient=5` and put
`[Quot.sound]` in every real footprint permanently; Dedekind costs two trusted
items, not fewer.

**One correction worth propagating beyond this lane:** the widely-repeated claim
that Coq's standard library *axiomatizes* ℝ with ~17 axioms has been false since
Coq 8.11 (Jan 2020) — `Raxioms.v` declares zero, all 17 are `Lemma`s. I wrote it
into the ADR from memory and an independent survey caught it. What is actually
there is `ConstructiveCauchyReals`: Cauchy sequences with a fixed explicit
modulus, no quotient, axiom-free, computing — i.e. this ADR's route, arrived at
independently. Corrected in place with a dated note. If you cite Coq's reals
anywhere, pin the version.

**Next:** R1 is **unblocked**. The ADR's first draft said ℚ had no order — true
of `int_prelude/rat.rs`, false of `rat_prelude.rs`, which `agent-rationals`
landed in the worktree mid-draft with `le`/`lt`/`inv`/`sub`/`div` and all 22
ordered-ring laws. The correction is recorded in the ADR rather than quietly
fixed. The only gap left is `1/(n+1)` (one definition), and writing `|a| ≤ b` as
`−b ≤ a ∧ a ≤ b` removes the `Rat.abs` dependency entirely. So: R1 carrier
(~10 decls), R2 ordered
ring + congruences (~35), R3 the one thing outside the kernel — ADR-0457's
telescope gains an equality slot (`RING_BINDER_NAMES` 30 → 39), R4 the model
witness. ℂ is scoped and **deferred with a finding**: nothing in the solver needs
it, and the only shipped complex arithmetic is exact ℚ(i) in
`axeyum-cas/src/geometry_certify.rs`, which wants a ring over ℚ and not ℝ
underneath — so ℚ(i) before ℂ, if either.

<!-- plan-section: landed-changes -->

| 2026-08-17 | `pending` | ADR-0468: ℝ is a Bishop setoid over ℚ at **zero** trusted declarations, with `creal_shape_probe` measuring the carrier's admissibility against a `funext` negative control; ℂ scoped and deferred. |
