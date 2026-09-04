# Lane: classical-axiom-policy — W0-2 (the classical-axiom policy) and W1-9 (the reverse-mathematics map)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, classical-axiom-policy, 2026-09-04).** Roadmap
W0-2 (convergence C4: reviewers 03.1, 12.2) and W1-9 (reviewer 10.1) are one
task, and both are decided **by measurement**: the reverse-mathematics map
*is* the evidence for the policy. **No axiom was added to the kernel.**

**Ten new theorems, all with an EMPTY `Kernel::axiom_footprint`**, read from
`Kernel::axiom_footprint` and confirmed by the
`kernel_declaration_projection` footprint-size column (0 on all ten), never
from a rendered name.

`nat_prelude/omniscience.rs` (`a56074fef`) — the map, six edges, no new
`Definition`, every principle spelled out INLINE in every type:

| declaration | edge |
|---|---|
| `Nat.em_implies_lpo` | EM → LPO |
| `Nat.lpo_implies_wlpo` | LPO → WLPO |
| `Nat.lpo_implies_markov` | LPO → MP |
| `Nat.lpo_implies_llpo` | LPO → LLPO |
| `Nat.wlpo_and_markov_imply_lpo` | **WLPO ∧ MP → LPO** — the converse half |
| `Nat.lnp_unrestricted_implies_lpo` | joins `least_number.rs`'s calibration point |

`creal/omniscience.rs` (`68b583fec`) — the deciding measurement, on
`OrderDecision := ∀ x y : CReal, Or (lt x y) (le y x)`. **All four
conclusions are statements `creal.rs`'s own field documentation records as
unavailable:** `CReal.le_total_of_order_decision` ("no `le_total` over ℝ to
recover it from"), `CReal.trichotomy_of_order_decision` (absent; only
`Rat.lt_trichotomy` exists), `CReal.apart_of_not_equiv_of_order_decision`
("the converse is Markov's principle and is neither proved nor assumed
here"), `CReal.abs_cases_of_order_decision` ("a decision on the sign of a
real and is **not** available"). Two of the four are depth-2 nodes — they
consume another theorem of the family rather than the hypothesis directly —
because W0-2 asks what CARRYING a hypothesis costs and a depth-1 family
cannot answer that.

**The number the experiment existed to produce: 11 binders, 14 argument
positions, ZERO obligations.** A classical hypothesis is not something you
discharge, it is something you carry; carrying it costs one binder in the
type and one argument at each use, and the cost does not grow with depth (the
two depth-2 theorems cost exactly what the depth-1 ones cost). Contrast
ADR-1595, where the setoid route cost three real one-line obligations — there
is **no analogue here**.

Three measurements nobody asked for that decide it (ADR-1601, `13bfb5f4a`,
`Status: proposed`):

1. **The axiom option is not one name.** Reviewer 03's blocker names EM,
   countable choice AND `funext`; `funext` was explicitly not granted by
   ADR-1595 and has never been priced. Pricing a classical addition at "one
   axiom" has now been wrong twice in this repository, measured both times.
2. **It retroactively devalues three existing row-2 certificates**
   (`lub_decides_em`, `ivt_exact_root_decides_sign`,
   `evt_attained_max_decides_sign`), whose entire content is that a classical
   conclusion COSTS a decision principle.
3. **It kills three environment-scan gates that currently pass**, each with a
   same-scan positive control. They cannot be repaired, only deleted.

**Recommendation: option (b), classical principles stay hypotheses.**
Reversible on evidence — a named, attempted theorem shown unreachable this
way. The number to watch is hypothesis-uses per theorem, **14 / 10 = 1.4**
here; re-open above roughly 3.

Downstream, and stated honestly: **(b) does not give reviewer 03 what it
asked for** — it cannot write classical analysis the way an analyst writes
it. What it gets is W3-1 unblocked with a stated shape and a measured
per-theorem cost. **W2-7 (the weak law) is gated on W1-10, not on this ADR**,
so W0-2 is removed as a blocker there and none is added. W3-6's completeness
carries its choice principle as a hypothesis, which is the standard
reverse-mathematics treatment and is what reviewer 10.3 called "a good test
of the classical-axiom policy". Reviewer 12's second trigger is met: W0-1 and
W0-2 are both written.

**Mutation table** (run in this isolated worktree, tree verified clean before
and after each; every restore checked with `git status --porcelain`):

| mutation | outcome |
|---|---|
| MU1 — drop `declare_lpo_implies_markov` from the ℕ build order | **killed 2** — exactly the two tests naming it; the other six pass |
| MU2 — drop `declare_apart_of_not_equiv` from the `CReal` build order | **killed 4** — its two tests plus `every_creal_declaration_is_checked_and_axiom_free` and `steps_table_matches_recorded_extraction`, so the inventory shard is load-bearing |
| MU3 — weaken LLPO's premise in the TYPE builder only (`And (Hits f) (Hits g)` → `And (Hits f) (Hits f)`) | **killed 8** — `Kernel::add_declaration` REJECTED the mutant, so `build_nat_prelude` errs and the whole suite dies |

**The structural finding MU3 records, and it is worth carrying forward:** for
a kernel prelude declaration, "exactly one test dies" is not an achievable
criterion for a *statement* mutation. A wrong statement is caught by the
trusted gate, and one bad declaration poisons the shared build — so the whole
suite dies, not one test. The criterion that does apply, and that every test
in these two files satisfies, is that each negative control is demonstrated
non-vacuous **by a positive twin in the same test using the same machinery**:
the theorem is applied at genuinely FREE variables of the advertised
hypothesis type and the inferred conclusion is pinned against an
independently rebuilt term, and only then is the wrong term required to be
rejected. Drop-mutations (MU1, MU2) are the ones that measure test coverage,
and both killed exactly the tests that name their subject.

**What did NOT run / was not built.** The reduction `OrderDecision → LPO over
ℕ` is **not** proved and is cited, not claimed: it needs a real built from a
`Bool` sequence (`∑ 2⁻ⁿ [f n = true]`) plus the summability estimate. It is
the natural next declaration. Every separation in the standard picture (LPO
not constructively derivable; LLPO ⇏ LPO; WLPO ⇏ LPO; MP ⇏ WLPO) is likewise
cited — each needs a model of the kernel rather than a term in it, per
ADR-1600. The `Nat.lpo_bounded` non-vacuity anchor was scoped out: the
bounded forms are already theorems (`Nat.lnp_bounded_search`,
`Nat.lnp_decidable`) and serve the same purpose.

**A tool hazard measured on the way, for the next lane.** `shape_search` run
while a build held the flock reported `declarations=1963` and a **false
UNANSWERABLE** for the `AlgS` namespace, which does exist; the same query on
an idle box reported `declarations=2686` and found all twelve `AlgS.Hom.*`
declarations. Check `declarations=` against a known-good figure before
believing any absence. Separately, `scripts/creal-declare-deps.py` requires
the registry struct to be named EXACTLY as the `CRealPrelude` field's type —
an alias on the re-export is not enough, and it exits non-zero with
"registry X has no NameId fields".

Gates (all green, nonzero counts): `--lib nat_prelude::omniscience` **8
passed** in 2.30 s; `--lib creal::omniscience` **6 passed** in 51.80 s; whole
`--lib creal::` **235 passed** in 169 s (measured during MU2's baseline);
`clippy -p axeyum-lean-kernel --all-targets --all-features -D warnings` exit
0; `cargo check --workspace --all-targets` exit 0, 0 errors; `cargo check -p
axeyum-py --all-targets` exit 0 after `gen-py-prelude-fields.py`
(total 3211 → **3221**); `rustfmt --edition 2024` on every touched Rust file;
`validate-facts.py` **2,768 facts, 0 errors** (2,497 proved; 2,397
kernel-lean of which **2,395 axiom-free**); `creal-declare-deps.py` steps
214 → **215**, fields 609 → **613**; `gen-adr-index.py` rows=807.

Next lane: ADR-1601 is `Status: proposed` and needs the coordinator or the
user to accept it. Nothing here depends on that acceptance — the ten theorems
are landed and axiom-free either way.

<!-- plan-section: landed-changes -->

| 2026-09-04 | classical-axiom-policy | W1-9 landed: LPO, WLPO, Markov's principle and LLPO over ℕ as explicit hypotheses, six implications, empty footprint |
| 2026-09-04 | classical-axiom-policy | W0-2's deciding measurement: four classical `CReal` order theorems the field docs record as unavailable, on an explicit hypothesis, empty footprint |
| 2026-09-04 | classical-axiom-policy | ADR-1601 (proposed): classical logic enters as a hypothesis, not as an axiom — 11 binders, 14 arguments, zero obligations |
