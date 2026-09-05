# Lane: lean-conformance — the public conformance corpus and a divergence ledger

<!-- plan-section: lane-status -->

**Next Ten item 7 of [`14-lean-lang.md`](../../math-department/14-lean-lang.md)
is `DONE` (lean-conformance, 2026-09-05), recorded in
[ADR-1663](../../research/09-decisions/adr-1663-the-public-conformance-corpus-scores-both-halves-and-the-divergence-ledger-is-gated.md).**

**The corpus.** `leanprover/lean-kernel-arena` (<https://arena.lean-lang.org>),
pinned in `scripts/fetch-references.sh` at `abc55357aee17c59dfdbf39c8a2e19739e23dd10`
plus its published test tarball pinned by SHA-256
(`7e396d5de90e8871c9b1d7e2931f3efaba303056cdfd93e65f9ae1de628bf326`).

**The `189 / 121 / 62 / 6` figures in
[`lean-kernel-requirements-2026-08-13.md`](../lean-kernel-requirements-2026-08-13.md)
§4.4 / R8.5 and in `14-lean-lang.md` are stale and were not repeated.**
Measured from the corpus's own `results.json` at that revision: **204 tests,
118 accept / 73 reject / 13 either**, with `parse-only` scoring 118/118 on
accepts and **6/73** on rejects. The doc's *argument* survives the correction
intact — which is why the control, not the accept count, is what this lane
built the gate around.

**Both halves, on the 186-case published tarball** (the 13 `either` cases are
not in it, and upstream excludes the five cases over 10 MB — `mathlib`, `std`,
`cslib`, `cedar`, `init`, which are the largest accepts):

| mode | accept half | reject half |
|---|---|---|
| full | **108/113** (4 wrong, 1 no verdict) | **70/73** (1 wrong, 2 declined) |
| `parse-only` control | 110/113 (2 wrong, 1 no verdict) | **21/73** |

The control is the same reader with the trusted gate's verdict discarded
(`census_ndjson`), so the gap is an attribution and not a rhetorical flourish:
**21 of the reject half is earned by the reader and recursor regeneration, 49
by the trusted gate.** (The finding run read 69/73 with 2 wrong; the second of
those two was the defect closed below.)

**What that attribution costs us, said plainly.** Five reject-half cases —
`rec-k-lie`, `nat-rec-k-lie`, `large-elim-param`, `large-elim-prop-bool` and
`level-imax-leq` — are rejected correctly but land in the 21, on a
recursor-regeneration mismatch rather than on the property each was built to
probe. `level-imax-leq` is the `nanoda_lib` `imax`-leq soundness bug that
requirements §4.5 records as **UNKNOWN** for this kernel; we reject the stream
at line 69 on an unrelated K-flag mismatch, so **this run does not close that
UNKNOWN**, and the ledger says so rather than claiming the credit.

**Two §4.6 "known gaps" are settled.** *"No K-like reduction"* is closed —
`k_like_reduction` exists in `tc.rs` and both `rec-k-lie` soundness cases are
rejected. *"No unit-like defeq"*, predicted to block *"a block of conformance
tests"*, blocks exactly **two** (`107_unitEta1`, `108_unitEta2`), and they are
the only two accept-half cases refused from inside the trusted gate.

**The ledger.** [`docs/plan/lean-divergences.md`](../lean-divergences.md), in
lean4lean's shape, carrying the standing rule that an unlisted divergence is a
bug. Ten entries, eight open, two closed. `scripts/check-lean-divergences.py`
enforces it from three **authorities** — the conformance mismatches, the
differential's `EXPLAINED_INCOMPLETENESS`, the replay census's
`Representability::reason` classes — and holds no list of its own; L5 fails when
an authority returns zero keys, because that is exactly how L2 would otherwise
pass vacuously.

**Closed in the kernel.** D2, duplicate universe binders (arena
`bad/tutorial/019_tut06_bad01`): `Kernel::check_declaration` gained step (1a)
and `KernelError::DuplicateUniverseParam`. `Const(c, us)` substitutes
positionally, so `levelParams = [u, u]` gives `@c.{a, b}` two candidate
substitutions for one name. Both existing checks are *relative* — inference and
def-eq treat `[u, u]` exactly as `[u]` — so the repeated binder was invisible to
everything the kernel ran, the same mechanism that left the binding list
decorative before `declaration_universe_params_must_be_bound.rs`.

**Decided, not closed.** Probe 5's `imax u (imax v w) ≡ imax (max u v) w` and
ADR-1600's open `level.max-kind:1322:max-to-imax` mutant were **re-measured
first-hand** (`level_conformance_probe`, with a negative *and* a positive
control, because both findings are `true` and a degenerate `|_,_| true` prints
the same lines) and both still diverge. They are recorded as a **sanctioned**
divergence: the arena classifies exactly this shape as `outcome: either`
(`tests/corner-cases/imax-right-successor.yaml`), so the reference corpus does
not consider it a defect, and making a correct decision procedure incomplete
inside the soundness-critical core to imitate it is the wrong trade. That
closes the question ADR-1600 §4 left open.

**Red, found and not fixed by this lane.** `good/perf/app-lam` produces **no
verdict in 600 s at 3.0 GB peak RSS** (`/usr/bin/time -v`), while the official
kernel checks it and our slowest passing performance case, `grind-ring-5` at
10.2 MB, takes 8.1 s. Ledger D8. Also unfixed: the three Lean gates
`14-lean-lang.md` lists as red today are outside this lane's scope.

**Verification.** `check-kernel-conformance.py --self-test` fires all eight
artifact-layer guards on the fixture that names each; G9 was mutation-verified
separately by changing one committed `class` field with the verdict unchanged,
which fires G9 **alone**. `check-lean-divergences.py --self-test` fires L1–L5
the same way. The kernel change is covered by
`declaration_universe_params_must_be_distinct.rs` — 3 tests, confirmed nonzero,
and one of the three is the control that a kernel refusing every polymorphic
declaration would fail.

**Next for this item.** D5 (unit-like defeq), D6 (dense internalization
indices) and D8 are each bounded and named with their obstruction. When a Lean
4.29.1 toolchain exists on a fleet host, building the corpus from source adds
the 13 `either` cases and the five large accepts, and the floors should be
re-derived from that run rather than nudged.

<!-- plan-section: landed-changes -->

| 2026-09-05 | `e75b0db94` | `scripts/fetch-references.sh` pins `leanprover/lean-kernel-arena` at an exact commit plus its test tarball by SHA-256; `kernel_conformance_check` runs one case per process under the arena's own exit-code contract (0 accept / 1 reject / 2 declined / 3 error), with `--mode parse-only` as the in-tree control |
| 2026-09-05 | `a24ed468b` | `Kernel::check_declaration` refuses a repeated universe binder (`KernelError::DuplicateUniverseParam`), closing ledger D2 — the arena's `tut06_bad01`; new `declaration_universe_params_must_be_distinct.rs` (3 tests, both directions); ADR-1663; progress rows in `14-lean-lang.md` and `10-logic-and-foundations.md` |
| 2026-09-05 | `5a954d4be` | `scripts/check-kernel-conformance.py` (9 guards, `--self-test`, floors and ceilings on both halves, G6 requires the control to invert by ≥40); `scripts/check-lean-divergences.py` (5 guards, three authorities, no list of its own); `docs/plan/lean-divergences.md`; `artifacts/kernel-conformance/{results.tsv,summary.json,summary.md}`; `level_conformance_probe` example; both gates registered in `scripts/check.sh` and the `justfile` |
