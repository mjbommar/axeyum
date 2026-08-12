# Findings register — 2026-08-12 Rado/claim-ledger session

Every issue and opportunity surfaced during one session of driving axeyum at
a real mathematical frontier. Grouped by kind; each row states its status
honestly. Companion note:
[`claim-ledger-and-rado-frontier-2026-08-12.md`](claim-ledger-and-rado-frontier-2026-08-12.md).

Nothing here is committed. `FIXED` means the change exists in the working
tree with tests and gates green.

---

## A. Product defects in axeyum

| # | Finding | Impact | Status |
|---|---|---|---|
| A1 | Proof-producing CDCL retained the entire DRAT proof in RAM | OOM-killed at **27.6 GiB** after 2.5 h with no verdict | **FIXED** — `DratSink` + streaming entry, ADR-0380, 18 tests |
| A2 | `check_drat` is forward-checking and superlinear | 470–670× slower than solving; blocked all certification | **FIXED** — `check_drat_backward`, **66×**, ADR-0381, 18 tests |
| A3 | `Evidence::check` returns `Ok(true)` for `Evidence::Unsat(None)` and `Unknown(_)` | A bare uncertified UNSAT "passes the check" with zero checking — a green gate over nothing | **OPEN** — `evidence.rs:890` |
| A4 | `produce_qf_bv_evidence` ignores the caller's deadline for proof production | Calls the uncapped `export_qf_bv_unsat_proof` though `..._within` exists; timeout bounds only the decision phase | **OPEN** |
| A5 | `produce_evidence_smtlib` drops the arena | Consumer cannot run `Evidence::check` on its own result without re-parsing; correctness depends on parse determinism | **OPEN** |
| A6 | Ground `IntDiv`/`IntMod` not constant-folded before dispatch | Up to **49×** measured on semantically identical queries; converts two solved instances into timeouts (>168×) | **OPEN** — direct cause of A7's symptom |
| A7 | `expand_guarded_int_universals` does not iterate to a fixed point | `∀x. G(x) ⇒ ∀y. H(x,y) ⇒ …` refused though each layer is individually supported | **OPEN** |
| A8 | Backward checker lacks core-first propagation | Shrinks the core, not per-check cost; needs clause migration between watch structures | **OPEN** — recorded in ADR-0381 |
| A9 | LRAT does not fall out of backward checking | Ordered forward hint chains + RAT lemmas aren't expressible in today's `LratStep` | **OPEN** |
| A10 | Proof trimming not implemented | Dropping deletions enlarges the DB and can break a RAT step | **OPEN** |

## B. Harness and tooling defects

| # | Finding | Impact | Status |
|---|---|---|---|
| B1 | `agent_cube` flushes its model only at process exit and does not exit promptly on SAT | Silently lost several witnesses | **OPEN** (workaround: short `--total-hours`) |
| B2 | A restarted `agent_cube` appends to the same `--status` stem | Produced a 1093-row cover with 69 duplicates; caught by the cover checker and quarantined | **OPEN** — needs a run-id or refuse-if-exists |
| B3 | `construct.py::predicted_lower_bound` returned values for `b > a`, where the construction is invalid | Would have been **unsound** if quoted; 19/19 parameter triples defective, e.g. `(3,4,3)` at N=60 admits `(49,1,36)` | **FIXED** — guard added, falls back to `a^k` |
| B4 | `climb.py` hard-coded `k = 4` | Rejected a valid 5-colour seed as "colour out of range" | **FIXED** — k is now a parameter |
| B5 | Bisection wastes the warm start | A +219 jump discards the seed's structure; incremental +1 climbing unstuck a stalled search immediately | **FIXED** — replaced with `climb.py` |
| B6 | Monitor scripts re-grep the same log lines | Duplicate notifications for already-reported results | **FIXED** — state-tracking monitors |
| B7 | `pkill -f <pattern>` matches the ssh command carrying the pattern | Killed the session itself (exit 255), twice | **FIXED** — launcher scripts instead of inline commands |
| B8 | **34 ledger claims store BINARY DRAT proofs that axeyum's own `parse_drat` cannot read.** They were produced by kissat, which emits binary DRAT by default; axeyum reads text DRAT | Those certificates are unverifiable by the system that ships them — a stronger defect than the drat-trim attribution issue that exposed it. Found by attempting R3 | **OPEN** — fix is to regenerate with axeyum's own proof core (writes text DRAT), which also retires the external-checker attribution |

## C. Process and methodology findings

| # | Finding | Why it matters |
|---|---|---|
| C1 | **Search and certification must be separate jobs.** Checking inline throttled the search: same instance, 42% after 5.5 h vs **4096/4096 in 153 s** with checking deferred | ~460×. The single most valuable operational finding of the session |
| C2 | The "checking is fundamentally the frontier" claim was **wrong** — it was a property of one implementation, not of certified combinatorics | We had two orders of magnitude of evidence and a plausible structural story. Fixing the checker retired it |
| C3 | Depth 6 beat depth 7 in cube-and-conquer wall clock | Deeper decomposition is not monotonically better; shorter per-cell proofs didn't repay 4× the cells |
| C4 | Cube proof sizes vary by >10× at fixed depth | Undermines uniform per-cell budgeting |
| C5 | Redundant allocation: four covers ran on one instance while a new value went uncomputed | Insurance that made sense early became waste; needs periodic re-audit |
| C6 | **Selection error**: I verified a formula against 15 values I chose, missing a counterexample sitting in the source paper's own table | Verify against *all* available data, not a curated subset |
| C7 | Arithmetic slip (`ab+1` vs `a²`) propagated to a subagent before being caught | One-line checks a referee runs first must be run first |
| C8 | Two agents "disagreed" because they tested **different constructions** | Reconcile by re-deriving, not by adjudicating reports |
| C9 | Conflated the search ledger with the certification ledger | Fixed by making certification emit its own record |
| C10 | Timing quoted from run A against run B's artifact | Both real; the pairing was wrong. Exactly what the ledger exists to prevent |

## D. Literature and novelty corrections

| # | Finding |
|---|---|
| D1 | The unified closed form `S(m,k) = (m^k(m-2)+1)/(m-1)` is **published** — Znám 1966, via BB82, Myers 2015, Ahmed–Schaal 2016, Wesley 2023, OEIS 2013 — **and is false as an equality** (`S(3,4)=45≠41`) |
| D2 | Several lower bounds merely restate CDW Lemma 4.1 (`R_k ≥ a^k`, proved for all k) |
| D3 | The `a=1` bounds restate the Znám/BB82 chain (2001, 3511) unless exceeded — our climbers stopped at 1900/3425, so those rows are **not** improvements |
| D4 | The closed-form refutation was already visible from the published `R_4(3,2)=103`; our 313 confirms at a second point |
| D5 | The `R_4 > 225` lower bound is CDW's; only the **upper** bound at 226 is ours |
| D6 | The k=2/k=3 dichotomy observation juxtaposes two published theorems (Gasarch–Moriarty–Tumma; CDW) — not a discovery |
| D7 | New prior art: Li, SSRN 6814341 (2026), covers the `b=1` column and reports the same k=5 non-tightness independently |
| D8 | The valuation colouring is **CDW's Lemma 4.1 verbatim**; only the general-k nested-shell refinement is ours |

## E. Open mathematical questions

| # | Question |
|---|---|
| E1 | `R_4(5(x-y)=4z) = 741`? Constructive lower bound 740 verified; the refutation is **search**-hard, not check-hard (9 cells in 162 s) |
| E2 | `R_4(6(x-y)=5z) = 1501`? Untested |
| E3 | No k=5 **upper** bound exists for any member of this family |
| E4 | The general-k proof of the shell bound is asserted in source, **not independently verified** |
| E5 | `b > a` with k ≥ 3: the construction fails; no replacement found |
| E6 | `a = 2` is genuinely special (`R_3(2,1)=14` vs the formula's 9) |
| E7 | `a = 1` uses a different mechanism (congruence classes, not valuation strata) |
| E8 | Where exactly does tightness fail between k=4 and k=5, and why? |

## F. Opportunities not taken

| # | Opportunity |
|---|---|
| F1 | **Promote the scratch tooling into the workspace** — the cube harness, the SLS, the certification driver did the heavy lifting and live outside the repo. This is the gap between "we did this once" and "the system does this" |
| F2 | Wire `just claims` into CI once ADR-0379 is accepted |
| F3 | Flip the `C:rado-number` refs to resolved once math-education commits |
| F4 | **Connect the two graphs**: math-education has 1,565 concepts; axeyum's curriculum has 23 nodes with decidability classes. The join is 68× larger than the routing table feeding it |
| F5 | The 148-misconception corpus is an untapped evaluation set for plausible-but-wrong machine reasoning |
| F6 | Re-run the now-cheap certification across the whole 34-claim replication set, upgrading them from `checked`-by-drat-trim to `checked`-by-axeyum |
| F7 | With A2 fixed, instances previously out of reach are now worth re-attempting |
