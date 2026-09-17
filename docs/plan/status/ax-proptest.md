# Lane `ax-proptest` — property-test box audit (improvement-list item 5, ADR-2141)

<!-- plan-section: lane-status -->

**Audit complete, controls landed, one STOP finding open (`WIP`, ax-proptest, 2026-09-17).**
Inventory: 599 box-sampling tests in six crates; 328 cannot reach a known
counterexample class; the bulk share one mechanism — a raw MMIX LCG state read
at its low bits, so `flip()`/`below(2)` at a fixed draw offset is a constant.
The P0 fuzz's `(div p 0)` corner was asserted in one polarity for all 80 of its
seeds; 0 of 600 quantified-BV bodies mentioned a bound variable; the production
faithfulness sampler gave every symbol a low bit of 0 at every seed. 24
generators + the production sampler fixed (output finalizer), one reachability
probe each, one mutation control each; 24 oracle sweeps re-run with 0
disagreements; a ratchet (`check-lcg-raw-state.py`, 81 → 56 files) in the
pre-push L0 block. **Open:** `LiaTheory` loses a shadowed assertion on `pop`
(`tests/lia_online.rs` push/pop fuzz is RED on this branch by design — the
subject is untouched per the brief; `LraTheory` has the same shape); 273
structural box gaps recorded per row, not widened. Details:
`bench-results/proptest-box-audit-20260916/README.md`.

| exit criterion | state |
| --- | --- |
| 1. inventory, counted | **MET** — 599 rows, method per row (`read`/`derived`/`ran hits=N/M`) |
| 2. reachability measured per row | **MET** — 244 yes / 328 no / 27 n/a |
| 3. controls with mutation proof | **MET for the LCG mechanism and two seed classes** — 33 suites / 38 mutations, all `killed`; 273 structural rows left open by decision (ADR-2141 §4) |
| 4. defects reported, not fixed | **MET** — `LiaTheory::pop` (exact sequence in the README); a test-reference overflow at `(i128::MIN, i128::MIN)` fixed in the reference |
| 5. README + status + gen-plan | **MET** |
| gates | fmt clean; merge-hygiene PASS; suite-gating PASS; lcg-raw-state PASS; anchors stale=0; workspace clippy `--all-targets --all-features -D warnings` Finished, 0 warnings |

<!-- plan-section: landed-changes -->

| 2026-09-17 | `ax-proptest` | Property-test box audit: 599-row inventory, LCG output finalizer in 24 generators + the production faithfulness sampler, one reachability probe and one mutation control each, seed classes in `wide.rs` and the inprocessing corpus, `check-lcg-raw-state.py` ratchet (81 → 56 files) in pre-push L0, ADR-2141. STOP finding: `LiaTheory` loses a shadowed assertion on `pop`; `tests/lia_online.rs` left red by design. |
