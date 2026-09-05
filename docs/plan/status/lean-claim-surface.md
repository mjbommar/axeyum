# Lane: lean-claim-surface — say what "Lean compatible" means, once

<!-- plan-section: lane-status -->

**Next Ten item 10 is `DONE` (lean-claim-surface, 2026-09-05, ADR-1668).**
Four claim surfaces had drifted independently from the measured tree: a July
"70/70 accepted" figure in `docs/plan/global/10-status.md`, a false "neither
`lean` nor `elan`" premise in action A9, an "every field `not_attempted`"
reading of the K3 matrix row that did not distinguish "no Lean-goal credit"
from "no native producers exist," and three July Lean documents still
carrying an `active` status four weeks after their own tally stopped moving.

1. **One paragraph, written once (120 words), reused verbatim** in
   `docs/plan/global/10-status.md` (replacing the stale Lean paragraph),
   `README.md` (§2, the Lean-checker section), and `docs/PROJECT-STATE.md`
   (replacing the stale close of "Evidence and Lean"). It states the K
   profile (K0 1/1, K1 6/6, K2-K6 0), the two pins (ADR-1594/1660), the
   `creal` replay census as the independent-checkability measure (1,972 of
   2,045, 48 `Type`-valued refusals, 25 blocked behind them, ADR-0760), the
   import tier (never headline, ADR-0601/1664), `by axeyum` (ADR-1666), and
   the carrier correspondence ledger (ADR-1665).
2. **A9 in `docs/plan/global/20-next-actions.md` rewritten**, not patched:
   both Lean 4.30.0 and 4.34.0-rc1 are installed under `~/.elan/toolchains/`
   on the fleet (`command -v lean` is empty only because `elan` does not
   touch `PATH`; `scripts/check-lean-gate.sh --print-toolchain` resolves
   it). The action now points at `14-lean-lang.md`'s four still-open Next
   Ten items (2, 3, 7, 9) in that file's priority order.
3. **The K3 row's assurance fields are unchanged** — every field in
   `planned-native-proof-profile` (`docs/plan/lean-compatibility-v1.json`)
   stays `not_attempted`, because `admitted`/`proof_checked` there mean
   credit toward a *Lean goal* and the native producers (`linarith`, `ring`,
   `simp`, `decide`, the tactic combinator; 18,497 lines) do not check a
   Lean goal — `by axeyum` does, on the separate route ADR-1666 already
   registered. The row gains one `residual` sentence recording exactly this
   and pointing at ADR-1666. `docs/plan/generated/lean-compatibility.md` and
   `docs/plan/generated/lean-complete-parity.json` were regenerated.
4. **The three July documents** — compatibility roadmap, implementation
   plan, parity roadmap — each got a dated status block appended
   immediately after their header metadata (their bodies are untouched):
   historical as of 2026-09-05, ordering superseded by ADR-0717's C-series,
   the complete-parity contract and registry explicitly **not** superseded.
   The parity roadmap's block additionally marks the U2 official-execution
   programme historical.
5. **ADR-1668** records the paragraph, the claim-surface list, the K3
   decision, and the rule that a future Lean claim on a claim surface is
   either a verbatim quote of the paragraph or a measured update to both it
   and the ADR together.
6. `docs/math-department/14-lean-lang.md`: items 1 and 10 ticked `[x]` with
   landing evidence (item 1 credits lane `lean-pin-gates`, ADR-1660, merge
   `c1d8db1c2`; item 10 credits this lane and ADR-1668); one progress-log
   row appended at the end. Items 2, 3, 7, 9 and every other verdict line in
   that file are untouched.

**Measured 2026-09-05, all four required checkers exit 0 on this tree:**
`./scripts/check-links.sh` ("all links ok"), `python3
scripts/gen-adr-index.py --check` (845 rows; the pre-existing `0166`/`0167`
duplicate is unrelated to this lane and was not touched — confirmed against
`git show HEAD:docs/research/09-decisions/README.md`, which already carried
it before this lane's one-line insertion), `python3
scripts/gen-lean-compatibility.py --check` (13 rows), `python3
scripts/gen-lean-complete-parity.py --check` (10 populations, terminal
claim still `false`, unchanged).

`scripts/check-merge-hygiene.sh` reports `FAILED` on this tree, but only on
`gen-plan.py --check` — expected and out of scope: this lane's brief
explicitly says not to run `gen-plan.py` or edit `PLAN.md` (the coordinator
regenerates it at merge from this file plus `docs/plan/global/`). No other
merge-hygiene finding.

Not run: `just check` / the full `./scripts/check.sh` aggregate, `cargo`
anything (documentation-only lane, no `crates/` or `artifacts/` file
touched), the real-Lean suites (require an installed pinned toolchain and
are unrelated to this lane's four required checkers).

<!-- plan-section: landed-changes -->

| 2026-09-05 | lean-claim-surface | One paragraph on what "Lean compatible" means, reused verbatim in `docs/plan/global/10-status.md`, `README.md`, `docs/PROJECT-STATE.md`; A9 rewritten off the false "neither lean nor elan" premise; K3 row residual sentence added with no assurance-field change; three July Lean docs marked historical (ADR-0717 C-series); `docs/math-department/14-lean-lang.md` items 1 and 10 ticked; ADR-1668 added and indexed. |
