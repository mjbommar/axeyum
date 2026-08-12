# Handoff — 2026-08-12, machine move

The session's compute (five concurrent agents plus a four-host solver fleet)
exhausted this machine and crashed it. Everything below is committed and
pushed so work can resume on larger hardware. **No result was lost; five
agent tasks were interrupted mid-flight and their state is described exactly.**

Read next: [diary and roadmap](rado-session-diary-and-roadmap-2026-08-12.md)
· [findings register](findings-register-2026-08-12.md) · [result
note](claim-ledger-and-rado-frontier-2026-08-12.md).

---

## 1. State at handoff: everything green

| Gate | Result |
|---|---|
| `cargo check --workspace` | clean |
| `python3 scripts/validate-claims.py` | 37 claims, **0 errors** |
| `python3 scripts/check-claim-negative-fixtures.py` | 7 fixtures, **0 failures** |
| `python3 scripts/gen-claims-dashboard.py` | 37 claims, 80 evidence rows |
| paper `check_claims_complete.py` | **OK** — 2 asserted values, both halves checked |
| paper `make pdf` / `make check` | 29 pages, all gates green (as of last run) |

**The two headline results are intact and fully certified:**
`R_4(2(x-y)=3z) = 226` and `R_4(4(x-y)=3z) = 313`, each with a verified
witness and a complete 4096-cell cube cover whose every per-cell DRAT proof
was checked by axeyum's own `check_drat_backward` — ~250M proof steps, zero
failures.

## 2. What landed in the crates

| Change | Where | Status |
|---|---|---|
| Streaming DRAT proofs (`DratSink`, `TextProofSink`, streaming solve + check) | `axeyum-cnf` | complete, ADR-0380, tests green |
| Backward DRAT checker (`check_drat_backward`) — **66×**, restores check/solve from 470–670× to 2.0–2.6× | `axeyum-cnf/src/drat_backward.rs` | complete, ADR-0381, 343 lib tests |
| Claim ledger: schema, 3 validators, 7 negative fixtures, dashboard generator | `artifacts/`, `scripts/` | complete, ADR-0379 |
| Artifact-format contract (B8 gate) | `scripts/validate-claims.py` | **gate complete, data migrated** — see §4 |

## 3. The five interrupted agents — exact state

All five were killed by the crash. Their partial work is **committed**, and
none of it breaks the build (`cargo check --workspace` is clean).

| Agent | Target | State found after crash |
|---|---|---|
| Evidence front door (A3/A4/A5) | `axeyum-solver/src/evidence.rs`, `lib.rs` | **partial** — files modified, compiles. The A3 green-gate fix is NOT confirmed complete; re-run it and audit callers. |
| Arithmetic + quantifiers (A6/A7) | `axeyum-rewrite/src/canonical.rs`, `propagate_values.rs` | **partial** — files modified, compiles. Div/mod folding NOT confirmed; **this one is a wrong-answer risk** (§5). |
| Search crate (F1, B1, B2) | `crates/axeyum-search/` | **created but NOT wired** — absent from root `Cargo.toml` workspace members, so it is not built or tested by anything. |
| Ledger format (B8/F6/F2/F3) | `scripts/`, `artifacts/claims/` | **gate landed, migration finished by hand after the crash** (§4). Proof regeneration NOT done. |
| Backward-checker follow-ons (A8/A9/A10) | `axeyum-cnf/src/drat_backward.rs`, `lrat.rs` | **unknown extent** — files modified, compiles, 343 tests passed before the crash. Re-run the crate suite first. |

**Do not assume any of the five finished.** Re-run each one's gates before
trusting its change.

## 4. What I completed by hand after the crash

The ledger agent had implemented the B8 format gate but not migrated the
data, so 34 claims failed it. I finished that migration honestly:

- every evidence artifact now declares its **actual** format, sniffed from
  the bytes (`drat-binary-gzip`, `colouring-text`, `tsv-ledger`, …);
- **34 certificate rows were downgraded from `checked` to `replay-only`**,
  because they are binary DRAT — a dialect axeyum's own `parse_drat` cannot
  read. They were only ever checked by the external drat-trim. This is the
  honest status and it is now enforced, not merely noted;
- one negative-fixture diagnostic string was synced to the checker's actual
  message.

The two headline claims are unaffected — their covers are text-format and
axeyum-checked.

## 5. Next steps, in order

### N1 — Re-run the five interrupted agents' gates *before* anything else
Each modified crate files and each may be half-done. In particular:

> **The arithmetic agent's div/mod constant folding is a wrong-answer risk.**
> SMT-LIB leaves division and modulo by zero underspecified but **total**,
> and CLAUDE.md records a shipped wrong-`unsat` from exactly this. Before
> trusting `canonical.rs` / `propagate_values.rs`, verify the folding agrees
> with `axeyum-ir`'s ground evaluator on **every** input including zero
> divisors, and that its fuzz generator deliberately emits that case. If that
> cannot be confirmed, revert those two files.

### N2 — Wire `crates/axeyum-search` into the workspace
It exists but is not a member of the root `Cargo.toml`, so nothing builds or
tests it. Add it, run its gates, confirm B1 (model flush on SAT) and B2
(status-file clobbering) are actually fixed.

### N3 — Regenerate the 34 binary-DRAT proofs (roadmap R3)
Now the highest-value ledger work: regenerate each with axeyum's own proof
core (emits text DRAT), verify with `check_drat_backward`, and lift those 34
rows back to `checked`. This retires the external checker from the trusted
path. Minutes of compute; the largest instance solved in ~130 s.

### N4 — The remaining open findings
A3–A10 as recorded in the findings register, ordered in the roadmap. Highest
is still **A3**: `Evidence::check` returning `Ok(true)` for a bare
uncertified UNSAT.

### N5 — The paper
`../axeyum-rado-paper` is at 29 pages with all gates green and both values
stated as exact. It needs a final read, not more results. Its own handoff is
in that repo.

## 6. Resource lesson — read before resuming

The crash was caused by **five Opus agents each running cargo builds and
solver processes concurrently on a 4-core machine**, on top of a fleet
driving four remote hosts. On larger hardware, still:

- cap concurrent agents that build Rust — each `cargo build` is itself
  parallel and they multiply;
- prefer `CARGO_BUILD_JOBS=2` when several lanes may build at once;
- the solver fleet work is cheap to *schedule* and expensive to *run* —
  the search/certification split (§C1 in the findings register) means a cover
  is ~3 minutes, so long-running solver jobs are usually a sign the
  configuration is wrong, not that the problem is hard.
