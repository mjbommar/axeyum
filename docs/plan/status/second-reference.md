# Lane: second-reference — a second reference solver per division on the parity board

<!-- plan-section: lane-status -->

**Your lane's block (`DONE` for the four divisions in scope, second-reference,
2026-09-07).** Task: the parity
board (`bench-results/PARITY.md`) measures most divisions against cvc5, but
cvc5 is not the SMT-COMP 2026 division leader in six of them (see
[ADR-1732](../../research/09-decisions/adr-1732-second-reference-per-division-not-a-replacement.md)
and
[`docs/research/02-ecosystems/competition-landscape-2026-09/reference-solvers-and-proof-formats.md`](../../research/02-ecosystems/competition-landscape-2026-09/reference-solvers-and-proof-formats.md)
§1.2). Goal: obtain a second, stronger reference solver where practical and
measure it on the same committed benchmark lists, without touching any
existing ledger entry.

**Obtained and pinned, both on `/nas3/data/axeyum/harness/bin/` (fleet-shared
NAS mount, reachable from s4/s5/s6/s7):**

- **Yices 2.7.0** (`yices-smt2`), static Linux x86_64 build from the
  `SRI-CSL/yices2` GitHub release `yices-2.7.0`. Downloaded
  `yices-2.7.0-x86_64-pc-linux-gnu-static-gmp.tar.gz`; sha256
  `49566b6f817692820538df78fe406878400d79810631c9372b2495bc81d3e00a`, which
  matches the `digest` field GitHub's own Releases API reports for that asset
  (verified before extraction, not just after). Extracted binary
  `bin/yices-smt2` alone hashes to
  `eab7efbff2a6f0cce2fcd2c25cb4a94e0e048c902d8ef9e6fd7d7989aa54c501`. `--version`
  reports `Yices 2.7.0`, build date 2025-07-17, revision `4f19700f0e27`.
  `--timeout=<seconds>` — **seconds, not milliseconds**, same family as z3's
  `-T:`, unlike cvc5/bitwuzla's millisecond flags.
- **SMTInterpol**, built from `ultimate-pa/smtinterpol` commit
  `1f55c1b9bfc724468b18e0e1868e4606e0285fb9` (2026-06-12, `master` HEAD at
  clone time) via `ant smtinterpol.jar` (Java 25, Apache Ant 1.10.15, both
  installed via `apt-get install ant`). SMTInterpol ships **no GitHub
  Releases** — only two ancient tags (`2.1`, `2.5`) — so `git describe` from a
  full (non-shallow) clone is the closest thing to a version string:
  `2.5-1490-g1f55c1b9`, baked into the jar's `Version.VERSION` by the build
  (confirmed the shallow-clone build produces a broken version string —
  `git describe` fails without tag history reachable — and does NOT surface
  as a build error, only as garbage in the jar; rebuilt clean after
  `git fetch --tags --unshallow`). Jar sha256
  `5a003a53c730269a83a7ef02dfbd1b014e4921516dc6cfde2f8177a9e3e39c2c`
  (`smtinterpol-2.5-1490-g1f55c1b9.jar`). A thin wrapper script `smtinterpol`
  sits next to it (`java -jar` forwarding all args) so it can be invoked like
  every other reference binary in that directory; wrapper sha256
  `619e89c3eb3f3aea2542b2d7eeb105960e6611f4850614b4698b42e22aeddb94`. CLI:
  `-t <ms>` (timeout, milliseconds), `-no-success -w` for quiet output,
  `-version` for the version string.

Both smoke-tested standalone (a 2-var QF_LRA sat and a trivial unsat) and
under `scripts/mem-run.sh` with an 8 GiB `ulimit -v`, on `s4` and over ssh on
`s7`; both agree with the expected verdicts.

**Not obtained:** OpenSMT (needs a C++ build; not attempted — Yices2 and
SMTInterpol covered every division this task's effort budget reached) and
QiuQi (2026 QF_LIA/QF_IDL winner; no public repo or binary found). QF_LIA and
QF_UFLRA are therefore **not** covered by a second reference — see ADR-1732
for the reasoning; do not re-attempt Yices2 there believing it is the leader,
it measured 2nd/3rd at best on QF_LIA in the source table and QF_UFLRA has no
committed benchmark list yet.

**Script change:** `scripts/parity-run.sh` gained an opt-in
`PARITY_SECOND_REF=<name>` (`yices2` | `smtinterpol`) that looks up a
hardcoded per-division table (division → binary), refuses any
(division, name) pair not in that table, and stamps the ledger entry title
`SECOND REFERENCE (<name>)` with its own per-file sidecar
(`<division>--<name>.tsv`) so it can never overwrite a default sweep's detail
file. Unset (the default), behaviour is byte-for-byte what it was before this
lane. See ADR-1732 for why the table is hardcoded rather than a free-form
binary-path override.

**Measurement:** all four in-scope (division, solver) pairs measured on `s7`
(idle, `taskset -c 0-7`, load ~0.1-6 across the run — see the per-entry load
rows) at the standard 24s/8GiB protocol against the same committed lists
already on the board, from a clean detached checkout at `e5cafc533` (built via
`scripts/cargo-serialized.sh`). Zero disagreements across all four sweeps —
axeyum and every reference (cvc5 baseline entries, plus the two new solvers)
agree on every file's sat/unsat. The honest delta, latest cvc5-referenced
entry vs. the new second reference, same list:

| division | axeyum vs cvc5 | axeyum vs 2nd ref | 2nd ref | what changes |
|---|---|---|---|---|
| QF_RDL | 142/200 vs 154/200 = 92.2% | 141/200 vs 170/200 = **82.9%** | Yices2 | gap widens 7.8pp → 17.1pp |
| QF_UF | 196/200 vs 200/200 = 98.0% | 196/200 vs 200/200 = **98.0%** | Yices2 | unchanged — cvc5 also solved this 200-file sample fully |
| QF_LRA | 93/200 vs 145/200 = 64.1% | 97/200 vs 181/200 = **53.6%** | Yices2 | gap widens 35.9pp → 46.4pp |
| QF_UFLIA | 122/200 vs 180/200 = 67.8% | 123/200 vs 182/200 = **67.6%** | SMTInterpol | **essentially unchanged** — see the finding below |

`axeyum solved` moves a little run to run (load, not a code change) — this is
expected per `scripts/parity-run.sh`'s own load-sensitivity warning, and the
disagreement count (0 everywhere) is what actually matters for soundness.

**A real, disconfirming result on QF_UFLIA.** SMTInterpol is documented as the
outright SMT-COMP 2026 QF_UFLIA leader over the full competition corpus
(291/300 vs cvc5's unlisted, sub-Yices2 rank). On this repository's committed
200-file `QF_UFLIA.txt` sample, though, SMTInterpol solves only 2 more files
than cvc5 (182 vs 180) and axeyum's ratio against it is not meaningfully
different — 67.6% vs 67.8%. The full-corpus SMT-COMP ranking does not
straightforwardly predict the gap on this specific 200-file slice; reported as
measured rather than adjusted to fit the expectation from ADR-1732's table.
QF_RDL and QF_LRA, by contrast, show the expected widening: Yices2 is
genuinely stronger than cvc5 on both of *this repository's* committed lists,
not just on the SMT-COMP-wide count.

<!-- plan-section: landed-changes -->

| 2026-09-07 | `2cc15eab2` | Pinned Yices2 2.7.0 + built SMTInterpol `1f55c1b9`; taught `scripts/parity-run.sh` `PARITY_SECOND_REF=yices2\|smtinterpol` (ADR-1732); wrote this status doc. |
| 2026-09-07 | (measurement, s7) | `QF_RDL` vs Yices2: axeyum 141/200, Yices2 170/200, ratio 82.9%, 0 disagreements. cvc5 baseline on the same list: 142/200 vs 154/200 = 92.2%. |
| 2026-09-07 | (measurement, s7) | `QF_UF` vs Yices2: axeyum 196/200, Yices2 200/200, ratio 98.0%, 0 disagreements. cvc5 baseline: 196/200 vs 200/200 = 98.0% (unchanged — cvc5 also solved this list fully). |
| 2026-09-07 | (measurement, s7) | `QF_LRA` vs Yices2: axeyum 97/200, Yices2 181/200, ratio 53.6%, 0 disagreements. cvc5 baseline: 93/200 vs 145/200 = 64.1%. |
| 2026-09-07 | (measurement, s7) | `QF_UFLIA` vs SMTInterpol: axeyum 123/200, SMTInterpol 182/200, ratio 67.6%, 0 disagreements. cvc5 baseline: 122/200 vs 180/200 = 67.8% — **disconfirms** the naive expectation: SMTInterpol is the SMT-COMP 2026 QF_UFLIA leader over the full competition corpus, but on this committed 200-file sample it decides only 2 more than cvc5 and axeyum's ratio against it is marginally *lower* (67.6% vs 67.8%), not the wide gap the full-corpus 291-vs-180-ish comparison would suggest. Reported as measured, per instructions, rather than fitted to the expectation. |
| 2026-09-07 | `e5cafc533`→(pending) | All four sweeps 0 disagreements (SOUND). Fetched the four new `bench-results/PARITY.md` sections back from the s7 detached checkout (verified byte-identical prefix before appending, so this was a clean append, never a rewrite) and committed locally. |
