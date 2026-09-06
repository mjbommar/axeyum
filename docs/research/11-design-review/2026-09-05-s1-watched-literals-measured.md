# S1 measured: two-watched-literal propagation in `CdclT`, 2026-09-05

What this lane changed, and what moved. Slice **S1** of the
[SMT/SAT parity plan](../../plan/smt-parity-plan-2026-09-05.md) (§2.1, §4 row
S1), which is route B of the
[ADR-1701 slice-2 design memo](../../plan/adr-1701-slice-2-design-2026-09-05.md)
(§6, §7 row 1). The defect it targets was named by the
[arithmetic timeout profiles](2026-09-05-arith-timeout-profiles.md).

## The change

`CdclT::unit_propagate` (`crates/axeyum-solver/src/cdclt.rs`) was

```rust
while changed {
    for ci in 0..self.clauses.len() {
        for &lit in &self.clauses[ci] { ... }
```

— a full clause-database rescan per fixpoint pass, no watch lists, no blocking
literals, and `self.clauses[ci].clone()` at every implication. It is now
two-watched-literal propagation with blocking literals, ported **verbatim**
from `axeyum-cnf`'s proof-producing core (`proof_sat.rs`): the same `lit_code`,
the same `Watch { clause, blocker }`, the same `ClauseHeader { offset, len }`
over one flat literal arena, the same `i`/`j` in-place watch-list compaction,
the same "highest-level literal to index 1" convention in conflict analysis.
Reasons are clause ids read out of the arena by `reason_for` on the
conflict-analysis path instead of a `Vec<Lit>` cloned at every implication.

Verbatim is the point, not stylistic preference: the memo's §6 rule is that
route B is a stepping stone to route A (plan slice **S7**, moving CDCL(T) onto
the native core) *only* if the watch code is copied rather than invented, so
S7's move is a deletion instead of a reconciliation of two watch schemes.

Unchanged, deliberately: the `TheorySolver` trait, the ten `CdclT::new` call
sites, the theory integration, `TheoryLayerStats`, every proof contract. That
is what makes `TheoryLayerStats::boolean_propagate` its own scoreboard — it
times the same stage on both sides of the change.

Two mechanisms exist because the driver is not a plain SAT core:

- **Clauses arriving mid-search.** `add_permanent_clause` is the final-check
  insertion boundary; its callers (`ufbv_online`, `qinst_egraph`) add clauses
  *after* an `Outcome::Sat`, i.e. under a total assignment that the new clause
  usually falsifies. A watch scheme cannot see such a clause, because no
  further assignment will trigger it. So the clause's watches are chosen
  against the current assignment (non-false literals first, then the deepest
  false one) and the clause is queued for exactly one full evaluation, which
  implies if it is unit and conflicts if it is falsified. Input clauses of
  fewer than two literals — which carry no watch at all — go through the same
  queue.
- **`reduce_db` rebuilds the watch lists** so none names a tombstoned clause,
  and it now computes the locked set in one walk of `reason_clause` instead of
  a full scan per candidate. That was quadratic in the search's size, and it
  only became reachable once propagation was fast enough to get there.

## Method

Host s4 (8-core i5-12600K), **shared and loaded by other lanes** — which is why
the arms are interleaved per file rather than run as two sweeps. `taskset -c
0-7`, `--timeout-ms 24000`. BEFORE is `smtcomp_cli` built from the merge base
`e7c909afc` in a `scripts/lane-snapshot.sh` tree; AFTER is the same example
built in this worktree. Binaries confirmed different:

| arm | sha256 (first 16) | bytes |
|---|---|---|
| BEFORE | `310df9397323...` | 41,637,552 |
| AFTER | `c9301a0d641d...` | 41,800,640 |

Scoring populations are the committed ones from ADR-1701 slice 1:
`bench-results/adr-1701-slice-1-20260905/qf_idl_population.tsv` (50 files) and
`qf_lra_population.tsv` (33). Raw rows:
`bench-results/s1-watched-literals-20260905/{qf_idl,qf_lra}_before_after.tsv`.

## Result 1 — the populations

| population | decided before | decided after | PAR-2 before | PAR-2 after | change |
|---|---:|---:|---:|---:|---:|
| QF_IDL (50) | **0** | **6** | 2,400,000 ms | 2,193,999 ms | −8.6% |
| QF_LRA (33) | 4 | 5 | 1,429,562 ms | 1,385,164 ms | −3.1% |

PAR-2 scores an undecided file at 2 × 24,000 ms.

Newly decided, every one agreeing with the file's `declared` status:

| file | division | verdict | after (ms) |
|---|---|---|---:|
| `gryzzles.12.lp` | QF_IDL | sat | 19,449 |
| `dimitri_yorick.59.steps.8.asp` | QF_IDL | unsat | 20,228 |
| `duthen-990602.77.steps.9.asp` | QF_IDL | unsat | 10,484 |
| `13.500.graph` | QF_IDL | unsat | 10,396 |
| `plan-30.cvc` | QF_IDL | unsat | 5,309 |
| `plan-42.cvc` | QF_IDL | unsat | 16,133 |
| `p5-driverlogNumeric_s9` | QF_LRA | unsat | 1,795 |

**Zero verdicts contradict `declared`** in either population, in either arm,
and **no file decided before and went `unknown` after**.

Two honest notes on the numbers:

- The QF_LRA BEFORE arm reads 4/33 where the slice-1 note recorded 5/33. That
  note ran on an idle s5; this pair ran on a loaded s4. The file in question is
  `unknown` in **both** arms here, so it is a timing boundary on this host, not
  a regression — but it means the QF_LRA "before" figure here is not
  interchangeable with the slice-1 note's.
- QF_LRA barely moves, and that is expected rather than disappointing: the
  profiles note measures that division at 84% `theory_final_check` and 10%
  Boolean propagation. QF_LRA is slice **S4**'s target (simplex warm start and
  implied-bound propagation), not this one's. Anything S1 gained there is the
  10% shrinking.

## Result 2 — the stage table on the profiled IDL files

`smtcomp_cli --trace`, both arms, interleaved. Raw output:
`bench-results/s1-watched-literals-20260905/idl_traces.txt`.

| file | arm | `boolean_propagate_ms` | decisions | `theory_conflicts` | restarts |
|---|---|---:|---:|---:|---:|
| `edge-matching-w=7-h=7-c=11` | before | 17,520 | 0 | 0 | 0 |
| `edge-matching-w=7-h=7-c=11` | after | **1,895** | **45,516** | 2,728 | 14 |
| `a7.3.0.tweaked.3.asp` | before | 16,881 | 0 | 0 | 0 |
| `a7.3.0.tweaked.3.asp` | after | **1,144** | **48,307** | 353 | 3 |
| `RVpredict_13` | both | *(no trace line)* | | | |
| `jobshop20-2-10-10-4-4-16` | both | *(no trace line)* | | | |
| `jobshop26-2-13-13-4-4-16` | both | *(no trace line)* | | | |

`a7.3.0` was repeated three times per arm: BEFORE 17,983 / 19,056 / 19,041 ms
with **zero** decisions every time; AFTER 1,144 / 1,129 / 1,049 ms with 48,307
/ 46,007 / 42,729 decisions. The decisions column is the finding, not the
milliseconds: before this change the search on these two files never left its
first propagation fixpoint, so no decision, no theory call, no conflict
analysis ever ran. Every other stage reads 0 in the BEFORE arm because nothing
downstream of propagation was ever reached.

**Three of the five files still print no trace line, in either arm.** That is
Finding 0 of the profiles note reproducing unchanged: the dispatcher's
per-route budgets sum past `smtcomp_cli`'s outer watchdog, so the process is
killed inside routing before `solve_smtlib` returns and there is nothing to
report. It is slice **S2**'s subject (a shared, shrinking deadline), and until
it lands the stage table simply cannot speak for those three files. One AFTER
attempt on `a7.3.0` also fell into that hole before the three clean repeats,
so the boundary is not stable.

## Result 3 — the micro-benchmark

`cargo bench -p axeyum-solver --features bench-internals --bench
cdclt_propagate -- --warm-up-time 1 --measurement-time 3`, the committed
pigeonhole CNF (7 into 6, 42 vars / 133 clauses), same host, same lock:

| arm | `cdclt_solve_php_6_7` median | 95% interval |
|---|---:|---|
| before | 48.725 ms | [46.789, 50.959] |
| after | **3.4547 ms** | [3.3990, 3.5353] |

14.1x on a formula small enough that the arena's cache locality cannot be
doing the work — this is the asymptotic change the memo predicted
(O(passes × database) → O(assignments × watch-list length)), not layout polish.

## Result 4 — the guard is load-bearing

A checker that cannot fail is worse than no checker, so the blocking-literal
fast path was mutated out (`if false && self.lit_sat(blocker) == Some(true)`)
in a throwaway `lane-snapshot.sh` tree — never in a worktree another lane
builds — and the same files re-run. Raw output:
`bench-results/s1-watched-literals-20260905/blocker_mutation.txt`.

| file | intact `boolean_propagate_ms` | mutant | intact verdict | mutant verdict |
|---|---:|---:|---|---|
| `a7.3.0.tweaked.3.asp` | 1,392 / 1,443 | 17,908 / 18,675 | unknown | unknown |
| `plan-30.cvc` (declared unsat) | 216 | 20,927 | **unsat** | unknown |

Removing the blocker costs a 13x–97x propagation-stage regression and a decided
file, and changes no verdict into a wrong one. Note how large that is: on these
instances (330k CNF variables, 800k clauses) most watch visits are of satisfied
clauses, and without the cached blocker every one of them dereferences the
arena. The memo called blockers "cheap and should be copied too"; on this
population they are most of the win, not a garnish.

## Gates

| gate | result |
|---|---|
| `test -p axeyum-solver --lib --features full -- --test-threads=8` | 1449 passed, 0 failed |
| `--test corpus_regression` (`--features full`) | 1 passed |
| `--test cdclt_lia_online` / `cdclt_lra_online` / `cdclt_online` | 9 / 9 / 8 passed |
| `--features z3 --test qf_lra_differential_fuzz` | 5 passed |
| `--features z3 --test simplex_lra_fallback_differential` | 1 passed |
| `--features z3 --test qf_uflra_differential_fuzz` | 1 passed |
| `--test progress_frontier --features full -- --test-threads=1` | 12 passed, 0 failed, no REGRESSION |
| `check --workspace --all-targets` | clean |
| `build --target wasm32-unknown-unknown -p axeyum-solver` | clean |
| `clippy -p axeyum-solver --all-targets --all-features -- -D warnings` | clean |

The frontier run is **advisory only** on every family that printed a
reference-frame line: host load 21.6–25.9 scaled the per-instance budget
1.66x–1.84x. Three families showed PROGRESS over baseline (`bv_reduction` +1,
`lia_cuts` +9, `string_bound` +32) and **no baseline was raised from that run**,
per the ratchet's own instruction. Nothing regressed.

## What this does not claim

It does not claim a division. The plan's parity rule is a count on the pinned
200-file list under `scripts/parity-run.sh` on an **idle** host; this lane
scored the 50/33-file timeout populations on a loaded one, which is the right
instrument for "did the named function stop being the bottleneck" and the wrong
one for "is QF_IDL at parity". `parity-run.sh QF_IDL` and `QF_RDL` on an idle
host are the plan's exit criterion and remain to be run.

It also does not claim the three silent QF_IDL files are unaffected — nothing
was measured on them either way, and S2 is the precondition for measuring them
at all.
