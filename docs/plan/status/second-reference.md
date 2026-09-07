# Lane: second-reference — a second reference solver per division on the parity board

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, second-reference, 2026-09-07).** Task: the parity
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

**Measurement:** see the `landed-changes` rows below and the
`SECOND REFERENCE` entries appended to `bench-results/PARITY.md` for the
per-division numbers, run on `s7` (idle, `taskset -c 0-7`, load ~0.1 before
starting) at the standard 24s/8GiB protocol against the same committed lists
already on the board.

<!-- plan-section: landed-changes -->
