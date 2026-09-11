# ADR-1910: The SAT referee is an external binary reading DIMACS text, and BatSat is removed

Status: accepted
Index-summary: [ADR-1703](adr-1703-the-native-core-is-the-sat-engine-batsat-is-demoted-to-a-differential-oracle.md) deferred its own "slice 2" — remove the `batsat-reference` feature, the `batsat`/`rustsat`/`rustsat-batsat` dependencies, and the gated tests. This does it, but **only after** replacing the referee, and the replacement is not like-for-like: it is strictly stronger and it actually runs. Two measurements forced that shape. (1) The retired referee had **never run automatically** — no gate, CI job, `justfile` recipe or git hook used `--features batsat-reference`, measured with positive controls — so it had provided zero automatic assurance from the day it landed; and its five *undocumented* siblings inside `proof_sat.rs` were gated on the same never-set feature, so they had never been compiled either. (2) It was also **weaker than it looked**: it handed BatSat the same `CnfFormula` object our own parser built, so a defect in `parse_dimacs` or `to_dimacs` was invisible to it — both engines consumed the same wrong formula and agreed. Decision, in four parts. (1) **The SAT referee is an external BINARY reading the DIMACS TEXT we wrote** — `crates/axeyum-cnf/tests/external_sat_referee.rs`, against CaDiCaL and/or Kissat, comparing three arms per instance (native on the in-memory formula, native on `parse_dimacs(to_dimacs(…))`, external on the text file) and replaying every external `sat` model against the original formula. It costs **no Cargo dependency**, so ADR-0002's no-C/C++-in-the-default-graph rule is untouched. MEASURED against the referee it replaces, with two mutations of `axeyum-cnf/src/lib.rs`: a `to_dimacs` sign flip and a `parse_dimacs` sign flip. On each, the BatSat differential passed **3/3** and this suite failed **3/4**. (2) **It is ungated and wired into `scripts/check.sh`, the `justfile` and `hooks/pre-push`**, through `scripts/check-external-sat-referee.sh`, which re-derives the adjudicated count from the suite's own reports instead of trusting the exit status, prints a loud SKIP when no binary is present, and fails under `AXEYUM_REQUIRE_EXTERNAL_SAT=1`. 524 comparisons on the provisioning host. (3) **BatSat, RustSAT and rustsat-batsat are gone** — feature, three dependencies, the 306-line adapter, and **ten crates out of `Cargo.lock`** (`batsat`, `rustsat`, `rustsat-batsat`, `bit-vec`, `cpu-time`, `minimal-lexical`, `nom`, and three `winapi` crates), which R-B's surface note explicitly did not measure. (4) **Nothing that could still check something was deleted.** The five gated `proof_sat.rs` differentials lost their BatSat arm and were **ungated**, keeping the decisive halves (every `sat` model must satisfy, every `unsat` proof must DRAT-check): `axeyum-cnf --lib` goes 618 → **623**, so five tests that had never run now run on every default build. `gate_b_sweep` and `xor_cdcl_curated_measure` were ported rather than retired, and `bench-results/sat-core-gate-b-20260905/` is untouched.
Date: 2026-09-10

## Context

Phase A1 and A4 of
[`docs/solver-comparison-2026-09/12-cdcl-consolidation-plan.md`](../../solver-comparison-2026-09/12-cdcl-consolidation-plan.md),
resting on
[the BatSat removal-surface inventory](../03-measurements/batsat-slice2-surface-2026-09-10.md)
(lane R-B, 2026-09-10).

[ADR-1703](adr-1703-the-native-core-is-the-sat-engine-batsat-is-demoted-to-a-differential-oracle.md)
made `axeyum-cnf`'s proof-producing core the SAT engine and kept BatSat as a
differential oracle. Its point 6 says in terms:

> **Slice 2** removes the feature, the dependencies, and the ~70 historical
> documentation references. This ADR does not do that sweep.

Slice 2 never ran. This ADR is it, plus the thing ADR-1703 did not ask for and
should have: a replacement referee that is on an automatic path.

### The two measurements that decided the shape

**The referee had never run.** R-B searched `.github/`, `scripts/`, `justfile`
and `hooks/` for `batsat-reference` and found exactly two hits, both prose.
`grep -c cargo justfile` → 145 is the positive control on the same command. So
the differential ADR-1703 point 5 sanctions had adjudicated nothing
automatically in its whole life; it ran when a human ran it, and measurably
nobody did. Worse, R-B found **five more differentials of the same shape** as
gated unit tests inside `proof_sat.rs` that no document names — the larger half
of the coverage, equally never compiled.

That cuts both ways, and the second edge is the one that matters: **a
differential nobody runs is already providing zero assurance, and its presence
is what makes the ledger read as covered.**

**The referee was weaker than it looked.** The differential hands BatSat the
same `CnfFormula` *object* the native core solved, built by our own parser. A
`parse_dimacs` or `to_dimacs` defect is therefore invisible to it: both engines
consume the same wrong formula and agree. R-B named this precisely — *"only an
external binary reading the DIMACS text is immune — which is the CaDiCaL/Kissat
arm of `gate_b_sweep`, not the in-process batsat arm."*

### What remains automatically after removal, stated honestly

R-B's table, which this ADR adopts rather than restates:

| failure mode | what catches it | automatic? | third party? |
|---|---|---|---|
| wrong `sat` (CNF layer) | `CnfFormula::evaluate` / `model.satisfies` — every accepted `sat` is replayed | yes | no, and it does not need to be: replay is **decisive**, not corroborative |
| wrong `sat` (term layer) | model lifted and replayed through the IR ground evaluator | yes | no, same |
| wrong `unsat` | our own DRAT/LRAT checkers verifying the refutation **against the original formula** — 269 call sites across 36 files, all default builds | yes | **no — same project** |
| wrong `unsat` where the defect is SHARED between core and checkers (DIMACS parsing, `CnfFormula` semantics, literal encoding) | **this is the gap** | — | — |

The last row is the entire exposure, and it is exactly the row an in-process
referee cannot cover. That is why the replacement is an external binary and not
a cheaper in-tree substitute.

## Decision

### 1. The SAT referee is an external binary reading the DIMACS text we wrote

`crates/axeyum-cnf/tests/external_sat_referee.rs`. Per instance it compares
three verdicts:

| arm | what it consumes | what a disagreement means |
|---|---|---|
| `native_direct` | the in-memory `CnfFormula` — the production path | — |
| `native_roundtrip` | `parse_dimacs(&formula.to_dimacs())` | our writer, our parser |
| external | the DIMACS **text file**, through CaDiCaL's or Kissat's own parser | a writer defect separates it from `native_direct`; a parser defect from `native_roundtrip`; a shared core/checker defect from both |

Every external `sat` is also **replayed**: the `v`-line assignment is parsed and
evaluated against the ORIGINAL in-memory formula. A permuted or off-by-one
variable map yields an external model that does not satisfy the formula it was
written from, even when both sides say `sat` — a distinct probe from verdict
agreement, and one no in-process referee performs.

Populations: the committed `corpus/micro-cnf/`, 120 seeded random 3-SAT at the
threshold ratio (`m/n ≈ 4.26`, both verdicts asserted present), seven degenerate
shapes the random family cannot produce, and a **known-verdict control** whose
expected answers are fixed in the test rather than supplied by any solver.

**No Cargo dependency is added, and none can be.** ADR-0002's rule is about the
dependency GRAPH; an external binary is outside it. This is strictly cheaper
than the three crates it replaces as well as strictly stronger.

### 2. It runs by default, and its exit status depends on the finding

`scripts/check-external-sat-referee.sh` is registered in `scripts/check.sh`, the
`justfile`'s `check` list, and `hooks/pre-push` — the three places the old
referee was absent from. It does three things a bare `cargo test` line cannot:

1. Resolves the binary itself, so an absent referee is a **visible SKIP line**
   rather than four tests that print a banner and return ok. `cargo test` has no
   way to say "skipped".
2. Re-derives the adjudicated count from the suite's own `compared=N` output and
   fails below a floor. A suite that compared nothing and one that compared 524
   instances exit identically; the count is the discriminator.
3. Asserts a nonzero TEST count, because `--test <name>` prints
   `running 0 tests ... ok` and exits 0 the moment a `#![cfg(...)]` appears at
   the top of the file — the trap that made a corpus gate here inert for fifteen
   days.

`AXEYUM_REQUIRE_EXTERNAL_SAT=1` turns an absent binary into a failure; that is
the mode for any lane publishing a soundness claim about the SAT core. Default
polarity is skip, matching `abc-crosscheck`: these are external C/C++
applications and a push must not depend on a host having built them.
`scripts/provision-external-sat-referee.sh` builds both from the gitignored
`references/` clones (into a scratch COPY, never in the shared clone), and
`scripts/provision-fleet-host.sh` runs it and verifies both binaries — a referee
wired into three gates whose binary no fleet host has is the same defect one
level down.

### 3. BatSat, RustSAT and rustsat-batsat are removed

The `batsat-reference` feature in all three manifests that declared or forwarded
it, the three `[workspace.dependencies]` lines, the three `optional = true`
lines, `crates/axeyum-cnf/src/batsat_reference.rs` (306 lines), the `pub mod`,
the six-name re-export, and both gated `use` statements.

`cargo tree -e normal --workspace --all-features` → **0** batsat/rustsat lines
(positive control: `axeyum-cnf` matches 5 times, tree is 300 lines).
`cargo tree --workspace --all-features`, i.e. **including dev and build edges**
→ **0** (706 lines). `cargo check -p axeyum-cnf --features batsat-reference` →
*"the package 'axeyum-cnf' does not contain this feature"*.

R-B recorded "which transitive dependencies become unreachable" as **did not
run**. Measured here from the `Cargo.lock` diff: **ten** crates leave —
`batsat`, `rustsat`, `rustsat-batsat`, `bit-vec`, `cpu-time`,
`minimal-lexical`, `nom`, `winapi`, `winapi-i686-pc-windows-gnu`,
`winapi-x86_64-pc-windows-gnu`. `anyhow`, `itertools`, `tempfile`, `thiserror`
and `rustix` stay, as R-B predicted: they are used elsewhere.

### 4. Nothing that could still check something was deleted

This is the part that distinguishes a retirement from a loss of coverage.

- **The five `proof_sat.rs` differentials were ungated, not deleted.** Each kept
  the two assertions that do not need a second engine — every `sat` model must
  satisfy, every `unsat` proof must DRAT-check — and lost only verdict
  agreement, which the external referee now supplies on a larger population.
  For the two *policy* tests the referee got **sharper**, not weaker: a restart
  schedule and a propagation optimisation are defined as verdict-preserving, so
  the right referee is the same core under the default policy, which varies one
  thing instead of everything. The pigeonhole arm's expected verdict is now
  asserted from the pigeonhole principle rather than from a second opinion.
  `cargo test -p axeyum-cnf --lib`: **618 → 623**. Five tests that had never
  been compiled now run on every default build.
- **`gate_b_sweep` was ported, not retired.** It produced
  `bench-results/sat-core-gate-b-20260905/`, the four-engine artifact ADR-1703
  rests on. That artifact is a recorded measurement and is **not** edited or
  regenerated — it keeps its BatSat column forever, because that is what was
  measured that day. The CaDiCaL and Kissat arms were never in-process (external
  binaries whose stdout the `verify` subcommand checks), so only the BatSat
  column is lost. `required-features` is gone, so the harness now builds on a
  default `cargo check --all-targets` instead of being skipped by it. Resuming a
  sweep now REFUSES to append to a TSV whose header is not the current one: the
  old four-engine files have a different column set, and appending to one
  produces a file where column 4 means two different things in different rows —
  a corrupted measurement that still parses.
- **`xor_cdcl_curated_measure` was re-pointed at the native core.** It asks
  whether CDCL(XOR) decides instances the *shipping* engine cannot, and since
  ADR-1703 the shipping engine is the native core. The old form was already
  asking about a solver no route used. It also stops requiring a feature nothing
  set, so it is compilable by a gate for the first time.
- **`cnf_core_bench` lost its BatSat column** and nothing else.
- **`native_cdcl_baseline` was deleted.** Its own header calls it a MEASUREMENT
  harness, not a soundness net, and it is superseded by the gate-(b) artifact.
- **The four `lib.rs` adapter unit tests were deleted.** They tested the
  adapter's raw solve/replay, its pinned determinism defaults, its resource-limit
  `unknown` and its lower-assurance UNSAT stamp. They are about BatSat, not about
  the native core, and they die with it losing nothing.

Design-lineage credit stays: `MiniSat`/`BatSat` are named in `proof_sat.rs`,
`cdclt.rs` and `lra_online.rs` as the **source of a design** — blocking-literal
watch lists, packed clause headers, `ccmin_mode = 2`, `lit_redundant`, progress
saving. That is attribution. So does the historical narration in
`config_registry.rs` and `dpll_lia.rs`: BatSat is the founding case of the
admission-limit basis doctrine and the reason
`scripts/check-admission-limit-basis.py` exists, and removing the word would
delete the reason the surrounding code and its checker exist. Removal makes that
founding case **stronger**, not stale: a `Basis::LiveSymbol` naming batsat would
now resolve to nothing, and the checker would say so.

## Consequences

**ADR-1703 is completed, not superseded.** Its slice 2 is done and its
assurance claim is now true rather than nominal.

**ADR-0007 is not superseded either**, on ADR-1703's own reasoning: choosing
`rustsat-batsat` as the first pure-Rust adapter was correct and served its
purpose. This records the end of that purpose.

**The honest statement about third-party adjudication changes.** Before this
ADR: *"after removal there is no automatically-run third-party adjudication of
any Axeyum verdict, at any layer"* — because the only third-party oracles (Z3,
cvc5, bitwuzla) sit at the QF_BV *term* level behind `--features z3` and are run
by hand. After it: there is one, at the CNF layer, on every default build,
against a binary that reads our text. It is narrow — pure CNF, small instances —
but it is the first automatically-running third-party check on any Axeyum
verdict, and the batsat differential it replaces was neither automatic nor, on
the arm that mattered, third-party.

**A gate that can fail was demonstrated to fail.** The wrapper's own
`compared=N` guard fired on its first run: the pattern was anchored with `^`, and
libtest under `--test-threads=1 --nocapture` prints a test's stdout on the line
it opened with `test <name> ... `, so the anchored pattern matched zero lines
while the suite was perfectly healthy. The guard was right about its own wiring;
the anchor was the bug. The two mutation runs are the other half of the same
discipline — a checker whose failure has never been observed is a claim, not a
check.

**What this does not claim.** Nothing here says the native core is faster than
BatSat, or than CaDiCaL or Kissat — gate (b) says it is never worse than BatSat
and modestly behind the references, and that measurement is unchanged. Nor does
it claim the CNF-layer referee covers theories: it does not, and the QF_BV and
theory oracles remain manual and `z3`-gated. Closing that is a separate
question and this ADR does not touch it.

## Alternatives considered

**(a) Re-point the differentials at `xor_dpll::solve_with_xor`,** an
independently written naive decider already in-tree. Cheapest, keeps the shape —
and does not restore what removal takes away, because the referee becomes ours
again and a shared DIMACS defect stays invisible. R-B called it "a consolation
prize" and that is right.

**(b) DRAT-check every `unsat` in those families and stop there.** Strictly
stronger than verdict agreement for `unsat`, adds nothing for `sat` beyond the
replay that already runs, and lands immediately. **This was adopted as the floor**
— it is exactly what the five ungated `proof_sat.rs` differentials now do — but
it is not sufficient on its own: our DRAT checkers are same-project, so the
shared-defect row of the table above stays open under (b) alone.

**(c) Keep the feature and wire the existing differential into a gate.** This
was the obvious minimal move and is worse than it looks. It would have put a
referee on an automatic path that *structurally cannot see* a DIMACS writer or
parser defect — the two mutations above prove it passes 3/3 on both — while
keeping three Cargo dependencies and a C-adjacent crate in the all-features
graph. Paying a dependency for a referee measured blind on the axis that matters
is the wrong trade in both directions at once.

**(d) Delete the referee and rely on model replay plus DRAT.** Defensible on the
numbers — replay is decisive for `sat` and DRAT verification is strictly stronger
than corroboration for `unsat` — and it is what the plan's phase A would have
produced if A1 had been skipped. Rejected because it leaves the shared-defect row
uncovered *and* unadmitted: the ledger would read "covered" while the one thing
an external party could see went unchecked. The external-binary referee costs a
provisioning step and ~2 s per push, which is a small price for closing the row
rather than documenting it.
