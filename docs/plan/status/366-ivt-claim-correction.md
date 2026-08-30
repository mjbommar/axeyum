# Lane 366 — `ivt-claim-correction`

<!-- plan-section: lane-status -->

## Status

**Done.** Adjudicated the adversarial audit's charge
([`2026-08-30-session-audit.md`](../../research/11-design-review/2026-08-30-session-audit.md)
§Part 1 item 3) that
[`08-ivt-and-evt-measured-against-mathlib.md`](../../formalized-math-2026-08/08-ivt-and-evt-measured-against-mathlib.md)
graded IVT and EVT on inconsistent criteria.

**The charge holds against the presentation, not against the verdict.** No
test was written down before §4's axis tables were built, so the "Net" lines
read as an unweighted vote over an ad hoc axis list — three Mathlib-wins
excused for IVT, one comparable Mathlib-win sinking EVT, with no stated rule
for the difference. But `07-the-cost-model-and-pareto-position.md` §1
already states the real test, narrower than the seven-axis table: dominance
is decided by exactly two axes — **trusted base** (axiom footprint) and
**computational content** (constructive-with-a-program vs
classical-existence) — on a statement we ship that is comparable to
Mathlib's; breadth (generality of statement, of structure, which continuity
notion is assumed) is **explicitly conceded**, per that same section, never
scored toward or against the verdict. That test was simply never carried
into the comparison document.

Applied uniformly:

- **IVT dominates cleanly** on both claimed axes for `CReal.ivt_approx`. The
  "exact conclusion" row the original table listed as a third Mathlib-win is
  not an independent axis — it is the same constructive-vs-classical trade
  as computational content, counted twice from the other side. Once
  collapsed, IVT needs no losses excused; breadth is conceded, not scored.
- **EVT is not eligible for the claim, full stop** — not "loses," not
  "mutually non-dominated." Mathlib's comparable content
  (`IsCompact.exists_isMaxOn`, a positive attained maximum) has no
  counterpart on our side: `CReal.evt_attained_max_decides_sign` is a
  refutation of what the fragment cannot reach, not a weaker positive
  statement, so there is nothing to measure trusted base or computational
  content against. `CReal.supOn` (landed today, ADR-0691) is real progress
  but is a value without the two characterizing laws that would make it a
  supremum comparable to Mathlib's maximum. Re-checked against the
  post-merge kernel with a freshly built `kernel_declaration_projection`:
  `CReal.supOn` present (`axioms=0`); `CReal.evt_approx_max` and a
  `supOn`-upper-bound-shaped declaration both absent — ADR-0691's stated gap
  is current, not stale.
- **Does not adopt the audit's "mutually non-dominated" fix for IVT.** That
  answers a different, unstated seven-axis-vote test; the test `07-…`
  actually states resolves the inconsistency without it, and per the lane's
  hard constraints, the direction of travel is the stricter, explicit test —
  not loosening EVT's verdict to match a looser reading of IVT's.

**The one-sentence claim to tell the user:** *`CReal.ivt_approx` dominates
Mathlib's intermediate value theorem on trusted base (0 axioms vs
`Classical.choice`/`propext`/`Quot.sound`) and computational content (an
executable bisection vs no extractable algorithm); it is narrower in target
and structure by design, which is reported rather than hidden, and EVT is
not yet a dominance example — `CReal.supOn` landed today but still lacks the
two laws that would make it comparable.*

## What landed

- [ADR-0692](../../research/09-decisions/adr-0692-the-dominance-test-has-two-axes-not-a-vote-and-ivt-still-passes-it.md) —
  the full adjudication, the explicit two-axis test quoted from `07-…`, and
  the kernel/Mathlib re-derivation.
- `08-ivt-and-evt-measured-against-mathlib.md` §4 rewritten: the test stated
  up front, each axis table split into "dominance axes" (scored) vs
  "conceded breadth" (reported only), exact-conclusion double-count
  collapsed, Net verdicts naming the axes explicitly instead of an
  unqualified "the Pareto claim holds/does not hold." A correction note
  added at the top of the document pointing to the audit and to ADR-0692.
- `docs/research/09-decisions/README.md` regenerated
  (`python3 scripts/gen-adr-index.py`, exit 0; the printed
  `duplicate_numbers=0166,0167` is pre-existing and unrelated to this lane).

## Re-verification performed

- Rebuilt `prelude_theorem_inventory` and `kernel_declaration_projection`
  fresh in this worktree (a stale prebuilt reports a false ABSENT/present,
  per CLAUDE.md) rather than trusting either document's prior run.
- `CReal.supOn` — found, `creal`/`complex`/`cpoint`, definition, `axioms=0`.
- `CReal.evt_approx_max` — absent (no declaration of that name).
- `CReal.supOn_upper_bound` — absent (no declaration of that name; spot
  probe for the upper-bound law ADR-0691 says is still open).
- `CReal.ivt_exact_root_decides_sign` — found, theorem, `axioms=0`.
- `CReal.le_total` — absent; positive control `CReal.lt_cotrans` — found
  (same lookup mechanism the row-2 non-vacuity check uses).
- Read three Mathlib quotes directly from the already-provisioned pinned
  checkout at `/data0/axeyum/lean-import-toolchain/mathlib4`
  (`git log -1` confirms `c5ea00351c28e24afc9f0f84379aa41082b1188f`):
  `intermediate_value_Icc` (`Mathlib/Topology/Order/IntermediateValue.lean:552`),
  `IsCompact.exists_isMaxOn` (`Mathlib/Topology/Order/Compact.lean:246`),
  `IsMaxOn` (`Mathlib/Order/Filter/Extr.lean:113`) — all verbatim against both
  the audit and the original document. Not refuted.
- `./scripts/check-links.sh` on both edited/new files — `all links ok`.

## Not touched

No fact, `epistemic_status`, or proof edited, per the lane's hard
constraints. `creal/` and `nat_prelude/` source untouched (sibling lanes are
there). No `cargo test --workspace` or `./scripts/check.sh` run — targeted
kernel-tool builds only, each run to completion in the foreground.

## Next

None outstanding for this lane. Follow-on work named but not owned here:
`08-…`'s existing §5 items (curate the nine `generated-unreviewed` IVT
facts, land the general-target/orientation IVT instantiations as facts,
relabel row 2's `evidence.kind = "exhaustive-enumeration"`) and ADR-0691's
two open laws (`supOn` upper bound, approximate least-upper-bound) remain
for whichever lane picks up EVT next.
