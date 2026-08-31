# Lane: l4-c3-thin-lean-adapter — L4 phase C3, the thin Lean adapter

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, l4-c3-thin-lean-adapter, 2026-08-30).** C3 is
landed: `axeyum_lean_import::thin_adapter` (a ~150-line grading module, ADR-0935)
composes C2's two already-checked paths (real pinned Lean replay via
`scripts/lean/replay-lean4export.lean`, unchanged; independent reimport via
`import_ndjson`, unchanged) rather than reimplementing either. A preregistered
8-category goal pack (`artifacts/lean-adapter/goal-pack/thin-adapter-v1.json`)
runs live against real pinned Lean 4.30.0 in
`crates/axeyum-lean-import/tests/thin_lean_adapter_goal_pack.rs`: success,
unknown, timeout, unsupported, malformed_response, wrong_goal,
wrong_environment, mutated_proof -- all eight graded correctly (1 accepted, 4
declined, 3 rejected), with success/wrong_goal/mutated_proof each confirmed to
have actually invoked real Lean rather than being decided from the envelope
alone. `scripts/check-lean-adapter.py` validates the committed result with 7
guards, each mutation-verified 1:1 in
`scripts/tests/test-lean-adapter-mutations.sh`; registered in both `justfile`
(`just lean-adapter`, appended to the `check:` dependency line) and
`scripts/check.sh` (appended after the `checked-interchange` steps).

Bounded and stated as such: this covers 8 representative categories over 1
subject (`Nat.add_comm`) drawn from C2's own 9-credited-root population, not
all 9 re-verified under the adapter and not a general goal population. The
new trust assumption, named in ADR-0935: the "environment identity" is a
plain string comparison, not a cryptographic binding -- it catches a stale or
substituted identity string but does not defend against a sidecar that
fabricates a matching string while running elsewhere; the actual soundness
rests entirely on the post-Lean grading step, which never reads a
sidecar-controlled field. No in-Lean `#tactic`/command was built (a Rust-side
orchestration around the same two C2 paths, per ADR-0935's alternatives
section) -- that is a deliberate C5-adjacent scope call, not an oversight.

C4 (demand-gated elaboration features) remains blocked on a preregistered
high-value population per the roadmap; nothing in this lane's work unblocks
or blocks that separately.

<!-- plan-section: landed-changes -->

| 2026-08-30 | l4-c3-thin-lean-adapter | ADR-0935 + `axeyum_lean_import::thin_adapter` (protocol/grading, 9 unit tests) + `thin_lean_adapter_goal_pack.rs` (8-category goal pack run live against real pinned Lean) + `scripts/check-lean-adapter.py`/`test-lean-adapter.py`/`test-lean-adapter-mutations.sh` (7 guards, mutation-verified 1:1) + `just lean-adapter` / `scripts/check.sh` gate registration |
