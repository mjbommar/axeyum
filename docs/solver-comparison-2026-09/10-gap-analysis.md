# Gap analysis (2026-09-09)

The synthesis of [`docs/solver-inventory-2026-09/`](../solver-inventory-2026-09/00-README.md)
(what we have) and the nine reference-solver files in this folder (what they
have). Written backwards from the question **"what would we have to build?"**

Every gap below cites both sides. Gaps are ranked by what they cost us today
divided by what closing them would take — not by how interesting they are.

## The headline

**The largest gaps are not missing capability. They are capability we built and
did not wire.** Four of the top six items are routing or configuration, and the
engines they need already exist and are already tested. That is the single most
important output of this comparison, and it was not the expected answer.

The second finding: **we are ahead on evidence, and the margin is larger than we
have been claiming.** Not one of Bitwuzla, Boolector, STP or Yices2 produces any
proof. Z3 removed its interpolation API, and its bit-vector proof checker is six
functions that all return `true`.

## Tier 0 — wire what already exists

Highest value per unit of work in the entire analysis. Nothing here needs a new
algorithm.

| # | Gap | Evidence (ours / theirs) | Size |
|---|---|---|---|
| 1 | **No warm SAT solver across refinement rounds or `check-sat`.** Our array CEGAR calls `SatBvBackend::new()` every round and re-lowers and re-blasts from scratch. | `auto.rs` has five `SatBvBackend::new()` sites (`:3993`, `:4735`, `:4853`, `:5563`, `:6672`). `IncrementalBvSolver` — a real warm engine — is used by `pdr.rs`, `dpll_t.rs`, `symexec.rs`, `ufbv_online.rs`, `bmc.rs`, and referenced **zero** times in `solver.rs` or `smtlib.rs`. Bitwuzla preserves the SAT instance, every clause, the AIG, the CNF variable allocations (tri-state, so pop demotes rather than frees), the rewrite cache and the local-search graph across `check-sat`. | **Routing.** The engine exists and has tests (`warm_vs_cold.rs`). |
| 2 | **CNF inprocessing is off by default**, so subsumption, vivification, BVE, compaction and XOR propagation never run. | `cnf_inprocessing: false`, `backend.rs:390`. CaDiCaL runs 24 named passes. | **One default**, plus measurement. |
| 3 | **The tick valve.** CaDiCaL gates every pass on a budget in search ticks (`effort/1000 × ticks since last run`, refusing below `thresh × clauses.size()`, `limit.hpp:136`), with exponential back-off (`delay.hpp:9-34`). We built the identical machine-independent meter and nothing spends it. | `axeyum-cnf/src/ticks.rs` is consumed only by one example, one test and doc comments; `span_log.rs:75` literally says "**No ticks.**" Every shipping budget is in conflicts. Z3's `reslimit` is the same idea, hierarchical and thread-aware. | **Plumbing.** The meter is written. |
| 4 | **Stable/focused mode switching.** CaDiCaL runs two decision policies (EVSIDS in stable, VMTF in focused) and two restart policies (Glucose EMA in focused, reluctant Luby in stable), switching on a tick budget. | `internal.hpp:476`, `restart.cpp:19-84`. Both of our halves exist — `proof_sat.rs` EMA restart, `phase_policy.rs` — and the only assignment enabling EMA is inside `#[cfg(test)] mod tests` (`proof_sat.rs:5425`, cfg at `:4703`). | **Wiring + a switch rule.** |
| 5 | **`minus_simplify` missing from our Carcara rule list**, costing us portability on proofs that are actually checkable. | Carcara aliases it: `"unary_minus_simplify" \| "minus_simplify" => simplification::minus_simplify` (`carcara/src/checker/shared.rs:292`). Our `CARCARA_CHECKED_RULES` (`axeyum-cnf/src/alethe.rs:868`) carries only the first. Found independently by two lanes. | **One line.** |
| 6 | **No gate runs an external proof checker.** | `carcara_crosscheck.rs` and `lean_crosscheck.rs` skip and pass when the binary is absent. cvc5 solves exactly this in `test/regress/cli/run_regression.py:312-335` — see below. | **One script.** |

### The gate to copy, verbatim in shape

cvc5 hit both problems we have and solved them together:

```python
carcara_args = ["--allow-int-real-subtyping", "--expand-let-bindings",
                "--allowed-rules", "undefined",
                "la_mult_sign", "la_mult_abs_comparison",
                "--rare-file", benchmark_info.carcara_rare]
output, error, exit_status = run_process([carcara_binary, "check"] + ...)
exit_code = self.check_exit_status(EXIT_OK, exit_status, ...)
if exit_code != EXIT_OK: return exit_code
if "valid" not in output:
    print_error("Invalid proof")
```

Two things to take from it. **It checks the exit status and then tests
`"valid" not in output`** — because Carcara's CLI prints `holey` and exits **0**
when a proof contains rules it cannot check (`cli/src/main.rs`: `Ok(false) =>
"valid"`, `Ok(true) => "holey"`, both falling through to `return`; only `Err`
exits 1). And **`--allowed-rules` names the unchecked rules explicitly**, which
is our three-rule problem written as a command line with a failing exit status
attached to it.

The same trap applies to drat-trim, which has **17** `exit (0)` sites — note the
space, which is why a search for `exit(0)` finds none — including memory-
allocation failures and `printf("s TIMEOUT\n"), exit (0)` at `drat-trim.c:905`.
Our `scripts/check-claim-certificates.py:1227` already handles this correctly by
grepping stdout for `s VERIFIED`.

## Tier 1 — real engineering gaps

| # | Gap | Evidence | Size |
|---|---|---|---|
| 7 | **19 of CaDiCaL's 24 inprocessing passes have no analogue.** Above all **SCC / equivalent-literal substitution** (`decompose.cpp`) — the cheapest pass, and every other pass feeds it binaries. | We have 5: `simplify`, `vivify`, `bve`, `compact`, `xor_propagate`. Missing: binary deduplication, SCC/ELS, hyper ternary resolution, failed-literal probing, hyper binary resolution, gate extraction + congruence, binary backbone, SAT sweeping, transitive reduction, BVA, blocked- and covered-clause elimination, instantiation, and more. | SCC alone is small and high-value. |
| 8 | **We destroy gate structure and nobody recovers it.** CaDiCaL spends 7,925 lines in `congruence.cpp` (plus `gates.cpp`, `definition.cpp`) *recovering* AND/XOR/ITE structure that someone else's Tseitin encoding destroyed. We still **have** that structure in the AIG one layer up and discard it at `tseitin_encode`; `xor_extract.rs` then re-derives XOR gates from clauses. | Our AIG is `crates/axeyum-aig`; the encoder is `axeyum-cnf::tseitin_encode`. | **An interface, not an algorithm.** Sizing this as 7,925 lines would be the most expensive mistake this document could cause. |
| 9 | **No propagation-based local search with per-operator invertibility.** **MEASURED 2026-09-10: DO NOT BUILD** — of 43 satisfiable SMT-LIB QF_BV instances our bit-blaster misses, local search decides **0**, and on 30 of them it performs zero flips. Bitwuzla also **defaults `bv_solver` to BITBLAST** (`option.cpp:238-241`); `prop` is opt-in there too, which this row did not say. | Bitwuzla's `src/lib/ls/` is 10,227 lines: `is_invertible`/`is_consistent`/`inverse_value`/`consistent_value` × 17 operator classes, plus a `preprop` portfolio. Our `pbls.rs` (1,456 lines) is WalkSAT scoring through the ground evaluator; a search for `invertib`/`inverse_value` across `crates/*/src/` finds only modular inverses in the CAS. | ~6,000 lines of operator-specific mathematics. |
| 10 | **Word-level rewriting is shallow and has no level concept.** **MEASURED 2026-09-10: DO NOT BUILD, and this row overstated the gap** — of Bitwuzla's 296 rules, 44 are FP (we eliminate at parse), 42 are `*_ELIM` for operators we lower natively, and 58 are `*_EVAL` our folds cover: **the comparable surface is 152, not 296**. Of 25 candidates measured, 14 remove zero AND gates and two make the circuit bigger. | Bitwuzla: 296 rules, `LEVEL_MAX = 2` plus an internal `LEVEL_ARITHMETIC = 3`. Boolector: 127 rule pairs, levels 0–3. We ship 59 rules, no levels. STP additionally has a 7,619-line constant-bit propagation that is both simplifier and decider. | Large, incremental. |
| 11 | **LIA gives up where nobody else does.** All three arithmetic references branch by handing a **lemma to the SAT solver** rather than running an in-theory branch-and-bound tree, which is why none of them has a node cap; Yices's `simplex_final_check` cannot return unknown at all. We cap at 50,000 B&B nodes and return `unknown`. | `04-arithmetic-theories.md`; `05-yices-opensmt-smtinterpol.md`. Two of three also use Hermite-Normal-Form cuts-from-proofs where we use Gomory fractional cuts. | Architectural, medium. |
| 12 | **The `i128` boundary.** We promote to bignum internally, then refuse at the module edge if a witness or Farkas multiplier outgrew `i128`. All three references simply keep growing the number (Yices tagged union, OpenSMT `FastRational` with `try_fit_word`, SMTInterpol `BigRational`). | `simplex.rs:420` — `narrow()` returns `None` if any value `is_big()`. | Contained: one boundary. |
| 13 | **Six quantifier instantiation strategies we lack**, several of them on by default in cvc5: conflict-based (QCF), CEGQI with per-theory instantiators, enumerative/full-saturate, pool-based, SyGuS, sub-conflict — plus 5 trigger-selection modes, 6 match-generator classes, and an instantiation evaluator. | `03-cvc5.md`. Ours: 37 quantifier files, 9 search/certificate pairs. | Large. |
| 14 | **Strings depth and test coverage.** cvc5 has 87 `STRINGS_*` inference ids to our 4, a 20-step inference strategy, loop detection with a 5-mode policy, four disequality-split procedures, and 159 RARE rewrite rules. Its strings regression is **583 files**; we vendored **20** (3.4%), with zero `QF_SLIA` and zero `seq`. | `03-cvc5.md`, `07-strings-and-regex.md`. | Large; the corpus half is cheap. |

## Tier 2 — architectural forks, not gaps

These are choices with costs on both sides. Treat a proposal to "fix" one as a
redesign, not a bug fix.

- **Eager vs lazy arrays.** Bitwuzla has *no* eager array path at all; STP is a
  staged hybrid (eager Ackermannization only when reads < 10 and estimated
  expansion < 200). Our eager-first choice (ADR-0010) buys a checkable UNSAT
  certificate (`array_elim_certificate.rs`) that **neither of them can produce**.
  **Corrected 2026-09-10 (ADR-1814):** that is true of the CAPABILITY and false
  of the shipped product. `certify_array_elim_unsat` and
  `ArrayElimUnsatCertificate` each appear ZERO times in `evidence.rs`, so **0%
  of QF_ABV `unsat` verdicts actually carry it**. Wiring it is the prerequisite
  for treating it as an advantage, and for pricing any eager/lazy trade.
  It costs us: array equalities above `MAX_ARRAY_EQ_INDEX_BITS = 8` are refused
  outright, and deep store chains expand — STP's own comment measures that at
  48× slower than refinement.
- **Derivatives vs automata for strings.** Ours degrades to a sound `unknown` at
  a named structural budget (`DEFAULT_MAX_STATES = 20_000`), which is
  reproducible across machines. Z3-Noodler's only decline path polls Z3's
  global wall-clock resource limit — sound, but quantized on time, not on a
  structural measure. Both alphabets stop at `0x2FFFF`; that is the SMT-LIB
  `UnicodeStrings` bound, not an independent choice by either project.
- **FP eliminated at parse vs SymFPU word-blasted lazily.** Ours means the
  rewriter never sees an FP term and the replay checks the same circuit the
  solver decided over (ADR-0028). Theirs keeps FP structure available to the
  lemma loop.

## Where we are ahead (verified on both sides)

Stated because an honest gap analysis reports the sign of every difference, and
because two of these are larger than we have been claiming.

| Capability | Us | Them |
|---|---|---|
| **AIG-to-CNF encoding** | Native XOR encoding and n-ary AND collection, plus ITE and NOT-AND patterns (encoder stats: `xor_gates`, `direct_xor_leaves`, `fused_xor_leaves`, `and_tree_gates`, `internal_positive_and_flattened`) | Bitwuzla has **open TODOs for exactly these two** (`aig_cnf.cpp:300-301`). Boolector wrote n-ary AND and compiled it out (`// #define BTOR_AIG_TO_CNF_NARY_AND`, `btoraig.c:60`). Only STP beats us, by delegating to ABC. |
| **Proof production for BV** | DRAT/LRAT from our own SAT core, Alethe, kernel reconstruction | Bitwuzla, Boolector, STP: **none**. Yices2: none. |
| **Proof checking that can fail** | `check_drat` (RUP+RAT), `check_lrat` with `AddRat`, an in-tree Alethe checker | Z3's bit-vector theory checker is 75 lines in which **all six functions `return true`** (`sat/smt/bv_theory_checker.cpp:34-73`). Its legacy proof checker is gated on a parameter that is never registered. |
| **Interpolation** | 8 interpolant modules, always-on checking that declines to `None` | Z3 **removed** the interpolation API (`RELEASE_NOTES.md:989-990`). OpenSMT has six systems but its check `assert`s and returns the interpolant anyway. SMTInterpol is genuinely ahead of us here. |
| **Model replay** | Unconditional on the default path | cvc5's `--check-models` defaults off with three escape hatches; Bitwuzla and Boolector self-check in debug builds only; STP's is opt-in and defaults false. |
| **Optimization** | OMT and MaxSAT | cvc5 has **none** (`OptimizationSolver`: 0 hits; control `SygusSolver`: 6 files). |
| **Determinism, no C/C++ dependency, WASM** | Public API promises | cvc5 has one line of stated intent and never forwards `--seed` to CaDiCaL. |

## Corrections to claims we have been making

- **Exact arithmetic is a tie, not a differentiator.** Z3's `lp::mpq` is its
  bignum `rational` and its simplex values are rational+δ pairs, the same as
  ours. **Done** — the row was removed from `02-z3.md`'s "We have, they do not"
  table under
  [ADR-1905](../research/09-decisions/adr-1905-exact-arithmetic-is-parity-not-a-differentiator.md),
  which also records the sweep establishing that this was the only place in the
  tree the claim survived.
- **Our own strings doc understates our surface.**
  `docs/solver-inventory-2026-09/07-strings-and-regex.md` omits `str.update` and
  the whole `seq.*` family, which we do lower (`parse.rs:2643` and following).
- **"Reference solvers are the frontier" needs care.** Yices's Gomory multi-cut
  round is `if (false && ...)` under a comment reading "NOT READY FOR PRIME
  TIME" (`simplex.c:8498`, `:9117`). SMTInterpol's `DEEP_CHECK_INTERPOLANTS`
  flag is `false` but its guard reads `(true || Config.DEEP_CHECK_INTERPOLANTS)`.
  CryptoMiniSat's XOR finder contains `assert(false && "TODO FRAT")`.

**These projects carry the same pathologies we documented in ourselves** — dead
branches, short-circuited flags, checkers that cannot fail. Do not read this
analysis as "they are disciplined and we are not." The gaps are specific and
real; the difference is not one of rigor.

## Method and confidence

Nine agents read the reference sources; the coordinator independently re-checked
each lane's load-bearing claims against the cited lines, with a positive control
on every negative result. Nothing was built or run. Reference clone SHAs are
pinned in [00-README.md](00-README.md).

Two claims here were corrected during verification and are recorded in
[`docs/solver-inventory-2026-09/10-verification-log.md`](../solver-inventory-2026-09/10-verification-log.md):
a lane's report (not its file) overstated the Carcara gate situation, and a
separate lane's "no production caller" for `bitblast_miter` was wrong.

Confidence is highest on Tier 0, where both sides are short and were checked
line by line, and lowest on the size estimates in Tier 1, which are line counts
of the reference implementation and not estimates of what an equivalent would
cost us.
