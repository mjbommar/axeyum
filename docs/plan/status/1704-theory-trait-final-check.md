# Lane: theory-trait-final-check — the ADR-1701 slice 1 measurement the cut-off lane owed

<!-- plan-section: lane-status -->

**Measurement landed (`done`, theory-trait-final-check / theory-trait-measure,
2026-09-05).** A prior lane landed
[ADR-1701](../../research/09-decisions/adr-1701-the-theory-interface-gains-final-check-a-driver-owned-queue-lazy-explanation-and-dynamic-atoms.md)
slice 1 — `TheorySolver` gains `final_check`/`propagate_into`/`explain`/
`take_new_atoms`, all defaulted, with `DlTheory` (`dl_online.rs`) and
`LraTheory` (`lra_online.rs`) opting in — as `c64928295` (the trait) and
`2d0cf09d8` (the two opt-ins), merged to `main` at `188dddf99`, with a follow-up
clippy fix at `96a343276`. It was cut off before the before/after measurement
ADR-1701 itself deferred ("Slice 1's measured effect on the QF_IDL and QF_LRA
miss populations is reported with the implementation"). This lane changed no
production Rust; it built two release binaries (`ef119b385` pre-ADR-1701 and
current `main` post-slice-1, SHA-256-confirmed to differ) and measured both
against 83 files drawn from the 2026-08-21 linear-arithmetic diagnosis's own
miss populations.

**Result.** QF_LRA (33 files, `Timeout`-class misses excluding the
`ResourceLimit` atom-cap refusals slice 1 does not touch): 3/33 → 5/33 decided,
PAR-2 45.00 s → 42.40 s, zero regressions, one already-decided file 13x faster
(17,229 ms → 1,313 ms). QF_IDL (50 files, `Timeout`+`ResourceLimit`-class
misses): 0/50 → 0/50 decided, no measured effect. Stage attribution
(`smtcomp_cli --trace`, 5 files per population) explains both results directly
from `TheoryLayerStats` counters, not by inference: on QF_LRA,
`theory_assert`/`theory_propagate` collapse from 15–24 s to single/low-double
digit ms and `final_check` takes over the completeness work, exactly as
ADR-1701 designed; on QF_IDL, the theory's own cost is 0–112 ms against
18–20 s of Boolean propagation on every file that reports data at all, so a
wider theory interface has nothing to speed up — QF_IDL needs ADR-1701's
un-landed slice 2 (the CDCL(T) search-engine unification), not slice 1. Full
method, both before/after tables, and the stage-attribution tables are in
[the design-review note](../../research/11-design-review/2026-09-05-adr-1701-slice-1-measured.md);
raw data is under `bench-results/adr-1701-slice-1-20260905/`.

**Gates run, and by whom.** This lane ran no `cargo test`/`clippy`/`just
check` gate — it wrote no production Rust, per its brief, and the prior
landing lane's own status is what ADR-1701 itself records as green (full
solver sweep 1449, corpus sweep, both `cdclt_*_online` suites, three z3
differential fuzzes, frontier ratchets 12/12, clippy, workspace check, wasm —
see ADR-1701 and its landing commits). This lane ran `./scripts/check-links.sh`
(clean) on the docs it touched and `python3 scripts/gen-plan.py --check`
before and after adding this file.

**Not done / next.** Slice 2 (moving `CdclT`'s hand-rolled Boolean search onto
the native `proof_sat` clause arena, or making `NativeIncrementalCdcl` the
CDCL(T) driver's search) is unimplemented; `clocksynchro_4clocks.main_invar.base.smt2`
in this lane's own QF_LRA trace is direct, named evidence that at least one
file needs it even after slice 1's stage collapse (`theory_propagate` 23,792
ms → 50 ms but the file still times out on decisions alone). This measurement
covered 50+33 files, not either division's full competition list; a
corpus-wide PAR-2/decided-count claim was explicitly not attempted (see "What
this measurement does and does not establish" in the design-review note).

<!-- plan-section: landed-changes -->

| 2026-09-05 | theory-trait-final-check | Measured ADR-1701 slice 1 before/after on 50 QF_IDL + 33 QF_LRA diagnosis-miss files: QF_LRA 3/33→5/33 decided (PAR-2 45.00s→42.40s, one file 13x faster), QF_IDL 0/50→0/50 (bottleneck is D1's Boolean search, not D2's theory interface); added `docs/research/11-design-review/2026-09-05-adr-1701-slice-1-measured.md`, a "Theory interface" section to `docs/internals/solver-dispatch.md`, and raw data under `bench-results/adr-1701-slice-1-20260905/`. |
