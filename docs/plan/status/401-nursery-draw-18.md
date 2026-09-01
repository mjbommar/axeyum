# Lane: nursery-draw-18 — author draw 18, clear the dispatchable-frontier floor

<!-- plan-section: lane-status -->

**Done (`DONE`, nursery-draw-18, 2026-09-01).** Authored nursery refill draw
18 (ADR-1465): `Mathlib.Data.Nat.Factorization.LCM` held-out (opened by a
prior lane this session, `Nat.factorizationLCMLeft`/`Right`),
`Mathlib.Data.Nat.Factors` + `Mathlib.NumberTheory.FactorisationProperties`
development, `Mathlib.Data.Nat.Log` train, `Mathlib.Data.Nat.MaxPowDiv` +
`Mathlib.NumberTheory.Bertrand` held-out. `check-dispatchable-frontier.py`
goes from **2 to 22** dispatchable against a floor of 10.

**Re-measurement at start** (`683884197`, == `origin/main`, no merge needed):
`gen-autogenesis-nursery-refill.py --check` exit 0 (`entries=460`),
`check-autogenesis-nursery.py` exit 0 (now green — was red per ADR-1450, the
cross-population component is fixed), `check-autogenesis-holdout-isolation.py`
exit 0 (`held_out=186`), `check-holdout-adjacency.py` exit 0 (18 held-out
families, 0 refused), `check-dispatchable-frontier.py` exit **1** (G7, 2
dispatchable), `validate-facts.py` exit 0 (2536 facts).

**The prior lane's proposed window filler is REFUSED at R11, measured before
being used.** Commit `36f85826f` (this session, before this lane) opened
`Factorization.LCM` and proposed the second window filler as
`Factorization.PrimePow` + `Factors` + `Factorization.Basic` (5) +
`Factorization.Induction` (1) = 10 rows, development. Screened against the
real `select()`/`screen_family()` (not `propose-nursery-refill.py`, which
lacks the fact-ledger/`HELD_OUT_CONSTRUCTIONS`/R5 screens), this is refused:
every one of the three `Factorization.*` modules shares the topic segment
`Factorization` with `natural-factorization-lcm` (held-out) — publishing it
development in the same draw is the shape-1 topical-overlap R11 exists to
catch. Repaired with `Factors` + `NumberTheory.FactorisationProperties` (17
rows, topics `Factors`/`FactorisationProperties`, no collision; the latter's
`do-not-draw-held-out` bar from ADR-1115 is held-out-scoped only and does not
reach a development use — verified against `assert_draw_lawful`).
`MaxPowDiv` alone is 7 rows, short of `PER_FAMILY=10`; bundled with
`Mathlib.NumberTheory.Bertrand` (4 rows) it reaches 11.

**The screen** (`docs/research/09-decisions/adr-1465-draw-18-screen.py`, same
construction as `adr-1240`/`adr-1245`/`adr-1255`'s screens — loads the real
generator and adjacency checker by path, runs the actual
`select()`/`assign_partitions()`/`screen_draw()`/`is_closed_evaluation`):
cycle assigns LCM held-out (index 0), Factors+FactorisationProperties
development (index 1), Log train (index 2), MaxPowDiv+Bertrand held-out
(index 3), purely from each family's primary module's lexicographic path.
R9 clean, R11 topic/vocabulary clean for both held-out families against
every published dev/train family (existing and new), R12 clean, zero churn
on any existing family's drawn ten, `failures=0`.

**`natural-max-power-dividing`'s R11 disclosure review** written into
`holdout-adjacency-review-v1.json`. Live sweep: `prime` (111, ordinary
`Coprime`/primality noise, no Bertrand-shaped statement anywhere in the tree
— grepped), `max` (44, `CReal.evt_approx_max`, different carrier and
concept), `divmaxpow` (2, the ADR-1430 definitions themselves, zero
theorems). Held-out-safe.

**Zero-diff invariant over the 460 already-drawn rows**, with a working
negative control (both run in the same script,
`/tmp/.../scratchpad/zero_diff_check.py`, not committed — reproducible from
`git show HEAD~1:artifacts/autogenesis/nursery-v2-extension.json` vs the
regenerated file): 460 of 460 rows byte-identical by `fact_id`, 0 missing, 0
changed, 0 partitions moved. Negative control: flipping one family's
partition or one entry's `partition` field in a copy IS detected by the same
diff — `detected: True` both times.

**Gates after authoring** (all re-run, exit statuses honest):
`gen-autogenesis-nursery-refill.py --check` 0 (`entries=500 development=180
held-out=190 train=130`), `check-autogenesis-nursery.py` 0,
`check-autogenesis-holdout-isolation.py` 0 (`held_out=206`),
`check-holdout-adjacency.py` 0 (20 held-out families, 0 refused),
`check-dispatchable-frontier.py` **0** (G7 clears: **22 dispatchable**),
`validate-facts.py` 0 (2576 facts, 0 errors — 40 new open facts, matching the
draw). `gen-adr-index.py --check` 0 after regenerating. `gen-plan.py --check`
run and this file conforms.

**Not run** (would need a workspace build; nothing in this lane touched
Rust): `cargo test`/`cargo clippy`/`just check`. This lane only edited Python
generator sources, JSON manifests/reviews, and Markdown/ADR docs — no `.rs`
file changed.

Full reasoning: [ADR-1465](../../research/09-decisions/adr-1465-draw-18-clears-the-dispatchable-floor.md).
