# Lane: ivt-evt-dominance-audit — the first independent audit of the IVT/EVT Pareto claim

<!-- plan-section: lane-status -->

**IVT dominates with three named caveats; EVT does not, and the standing reason
for that is stale** (`DONE`, ivt-evt-dominance-audit, 2026-08-30). Verdict in
[ADR-0875](../../research/09-decisions/adr-0875-the-ivt-evt-dominance-claim-audited-independently.md),
with `08-ivt-and-evt-measured-against-mathlib.md` corrected in four places.

`08-…` and ADR-0692 both say EVT has no statement on which the two-axis
comparison can be run. That was true when written and is not true now.
`CReal.supOn_ub` and `CReal.supOn_approx_lub` landed since, and they compose —
`le_trans` under `Exists.rec` — into exactly the `CReal.evt_approx_max` §5
item 2 names as missing. `examples/ivt_evt_vacuity_probe` builds the term and
`Kernel::add_declaration` accepts it, axiom-free, with a negative control (the
same term with the `1/(n+1)` slack removed) refused in the same run. ADR-0692's
absence probe looked for `CReal.supOn_upper_bound`, a name that never existed.

**EVT's real blocker is bookkeeping.** No declaration names the composed
statement, and the ledger has **zero** facts for `CReal.supOn` or any of its
laws while eight `mesh*` rungs *below* the supremum do have facts. A dominance
claim a referee cannot check in the ledger is worth nothing.

**Vacuity — the risk the brief called most likely to be live — is now
machine-checked for both theorems, and was checked by nothing before.** The
probe instantiates `ivt_approx` at `CReal.ivtPlateau` and the composed
`evt_approx_max` at `CReal.evtLinear`, discharging every hypothesis with a
kernel theorem, at an **arbitrary** `v`; both instantiations are admitted
axiom-free. Those are precisely the families whose EXACT versions are proved to
imply analytic LLPO, so the approximate statements are non-trivial exactly where
the constructive difficulty lives.

**Two measurements that were previously inferred are now measured.** Mathlib's
footprints, via `lake env lean` + `#print axioms` at the pinned commit:
`[propext, Classical.choice, Quot.sound]` for `intermediate_value_Icc` and
`IsCompact.exists_isMaxOn`, with `IsMaxOn` as a control that comes back empty.
And `real_lean_creal_carrier_kernel_replay` re-run under `AXEYUM_REQUIRE_LEAN=1`
(4 passed, 136.8 s, `representable=1989 lean_kernel_constants=1989`): **18 of
the 21 IVT/EVT-family declarations are checked by official Lean's own kernel.**
The three that are not are `CReal.ivt_exact_root_at` (blocked by
`hasDerivative_add`) and the two hypothesis-class witnesses
`ivtPlateau_uniformly_continuous` / `evtLinear_uniformly_continuous`, which are
Type-valued because `CReal.UniformlyContinuousOn` is `Sort 1` and carries a
modulus.

That same `Sort 1` fact has a consequence nobody had recorded: **`CReal.supOn`
is indexed by the modulus**, so "the supremum of `F` on `[a,b]`" was not a
function of `F`. It is answerable — the probe derives
`Equiv (supOn … u1) (supOn … u2)` axiom-free from the two characterizing laws
plus `le_of_forall_le_add_small` — but nothing in the environment says so.

**Re-measurement of the earlier 0/20:** over the 17-fact IVT/EVT family selected
by content, `per_theorem_footprint`, `circularity`, `mutation_control` and
`independent_replay` are **still 0 of 17**. What changed is above the fact
level: S0 now measures them, S1 pins every statement, and the Lean replay covers
18 of 21 declarations by NAME while publishing no fact ids.

**Next, for a lane that is not this one** (an audit that lands what it audits is
a lane grading its own work): declare `CReal.evt_approx_max`; declare
`CReal.supOn_modulus_independent`; register facts for the supremum family. All
three proof terms are in `crates/axeyum-lean-kernel/examples/ivt_evt_vacuity_probe.rs`.
Also open, reported and not amended: the six `F:cas-*` IVT/EVT rows score **0 on
every** safety-matrix protection.

<!-- plan-section: landed-changes -->

| 2026-08-30 | `136998127` | `ivt_evt_vacuity_probe`: EVT row 1 composed from `supOn_ub` + `supOn_approx_lub` and admitted axiom-free; vacuity witnesses for IVT and EVT at concrete families |
| 2026-08-30 | `69d4c9b4a` | `CReal.supOn` is indexed by the modulus (`UniformlyContinuousOn : Sort 1`); modulus-independence derived and admitted |
| 2026-08-30 | `094e80a21` | Lean-replay coverage per subject, with a control of the opposite verdict |
| 2026-08-30 | `d0cc13942` | ADR-0875; four corrections to `08-ivt-and-evt-measured-against-mathlib.md`; this status file |
