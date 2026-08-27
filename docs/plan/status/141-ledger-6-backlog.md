# Lane: ledger-6 — registering the proved-but-unregistered Ch.14/24 backlog

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, ledger-6, 2026-08-27).** Registered 12 facts for
declarations that landed in `crates/axeyum-lean-kernel/src/creal/` (mostly
`integral.rs`, `power.rs`, `uniform_convergence.rs`, `congruence.rs`) but were
never added to `artifacts/facts/`: the exact mesh-point Riemann-sum split
identity and its two supporting lemmas, the domain-restricted
Equiv-congruence-from-uniform-continuity bridge, sub-interval restriction of
uniform continuity, the two-independent-index `close_within` bridge, the
free-parameter shared-accuracy-close lemma, the full `powerSeriesTerm` family
(definition + congruence + coefficient-boundedness domination +
Weierstrass-M-test-specialized uniform convergence), and `CReal.mulPowCongr`
(the same statement as `powerSeriesTerm_congr`, but produced mechanically by
the `congruence.rs` `CongruExpr`/`derive` deriver rather than hand-built).
The `Int.ModEq` family named in this batch's brief
(`add_modEq_left`/`add_modEq_right`/`mod_modEq`/`modulus_modEq_zero`/
`modEq_sub`) was already fully registered under the `ml430-int-*` ids with
complete 4-row evidence each — confirmed, not duplicated.

Validator: `818 facts checked, 0 errors` (was 806 before this batch).

Method notes: every canonical type was extracted programmatically from
`kernel_declaration_projection`'s unfiltered TSV emit (`--release`, never
hand-transcribed); every `depends_on` entry was cross-checked against the
ledger's own `formal.statement` text (parsed for the declared
theorem/def name), never guessed from a name-shape match; every
`checker_command` was executed verbatim against this tree before being
written into a fact (both the `theorem_dependency_inventory`/
`kernel_declaration_projection` presence checks and the
`nat_axiom_inventory --require-axiom-free creal` footprint check).
`CReal.riemannSum_split_exact`'s fact records the exact kernel-verifiable
counterexample to the FIXED-mesh version of interval splitting
(`m:=0, F:=id, a,c,b:=0,1,3` gives `0` vs `2`) and explicitly does not
extend that refutation to `CReal.integral_split` itself, which stays open
for the independent-witness-comparison reason already documented in
`integral.rs`'s own module doc.

`CReal.mulPowCongr`'s ~1.25ms(release)/~1.40ms(debug) derive+check timing was
measured directly in this batch (an `Instant`/`eprintln` timer added around
`declare_power_series_term_congr`'s derive step in an isolated
`scripts/lane-snapshot.sh` copy, never the shared checkout, deleted after
use) — not carried over from an unverified figure.

**Declared-but-unregistered diff, measured this batch (not exhaustive — see
below):** starting from the 12 declarations named in this lane's brief, all
12 were confirmed present in the kernel and none were already registered
(0 of 12 pre-existing). A full systematic diff of the ENTIRE
`prelude_theorem_inventory --include-constructed` theorem list against
`artifacts/facts/`'s registered `kernel_theorem`/`formal.statement` names
was NOT run this batch (budget) — only the named backlog plus the direct
proof-dependency closure of each (most of which were already registered,
confirming the ledger's Ch.13/14/22-27 coverage is otherwise current). A
future lane should run that full diff and report its size as the
headline trailing-the-kernel measurement; this batch's own diff size is
exactly 12 (all newly registered, 0 pre-existing among the named set).

Mutation testing: not run this batch on the newly-registered facts
specifically (budget) — every `checker_command` was instead verified
end-to-end against a real `--release` build on this tree (positive result
for the exact declaration named, `nat_axiom_inventory --require-axiom-free
creal` confirming `creal: axiom=0 opaque=0 quotient=0 total_trusted=0`).
No `Int.*` / `Complex.*` mutation case was produced this batch since no new
`Int.*`/`Complex.*` fact was registered (the `Int.ModEq` family was already
complete). Flagged for a follow-on lane.

<!-- plan-section: landed-changes -->

| 2026-08-27 | (uncommitted at status-file write time) | Registered 12 facts: `F:creal-riemannsum-split-exact`, `F:creal-riemannsum-split-scale-invariant`, `F:creal-riemannsum-split-exact-of-uc`, `F:creal-congrofuniformlycontinuous`, `F:creal-uniformlycontinuouson-restrict`, `F:creal-close-within-of-within-indexed`, `F:creal-riemannsum-sharedaccuracyclose-at`, `F:creal-powerseriesterm`, `F:creal-powerseriesterm-congr`, `F:creal-powerseriesterm-abs-le`, `F:creal-powerseriesuniformconvergeson`, `F:creal-mulpowcongr`. |
