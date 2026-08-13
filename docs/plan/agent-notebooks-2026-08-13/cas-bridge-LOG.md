# CAS <-> SMT bridge lab notebook (append-only)

## 2026-08-12T21:11:01-04:00 — session start
Task: wire axeyum-cas into axeyum-solver; two routes:
  (1) cas-identity-refuter (polynomial disequality refutation via MvPoly)
  (2) cas divisibility/units route (a*p=1 etc.) avoiding int-blast-ladder width-32 ceiling
Branch: session/rado-claim-ledger-2026-08-12, worktree clean at start.

## 2026-08-12T21:12:37-04:00 — BASELINE probe (before any change)
Temp file crates/axeyum-solver/tests/zz_cas_probe_tmp.rs (deleted after).
CMD: cargo test -p axeyum-solver --features full --test zz_cas_probe_tmp -- --nocapture --test-threads=1

VERBATIM RESULTS:
  (a+b)^2 != a^2+2ab+b^2   -> Unsat 1.43ms   via int-real-relax          (ALREADY decided)
  (a+b)^3 != ... over Real -> Unsat 841.90us via nra-real-root           (ALREADY decided)
  a>=2 & a*p=1             -> Unknown(Timeout "preprocessed dispatch timeout after reduced solve") 20.00s
      trace: probe/dl-online declined/lia-simplex unsupported/lia-dpll unsupported/
             nia-square not-applicable/nia-linearize verifier-rejected/nia-bounded-blast not-applicable/
             int-blast-ladder declined (budget: integer bit-blast width ladder: wall-clock timeout reached)
  a>=2 & a*a*a*s=1         -> Unknown(Timeout) 20.01s, same trace shape.

FINDING: simple degree-2/3 identity disequalities are ALREADY decided by int-real-relax /
nra-real-root. The identity refuter must be measured on shapes those miss (more vars /
higher degree). Next: probe harder identities to find the real gap.

## 2026-08-12T21:15:28-04:00 — GAP HUNT (verbatim, 15s budgets)
ALREADY DECIDED (no gap, route must not regress these):
  4var (a+b+c+d)^2         Unsat 1.80ms  int-real-relax
  3var (a+b+c)^3           Unsat 2.62ms  int-real-relax
  cyclic a(b-c)+...        Unsat 1.07ms  int-real-relax
  (a+b)^5                  Unsat 2.02ms  int-real-relax
  Sophie Germain           Unsat 1.23ms  int-real-relax
  deg-9 3var               Unsat 5.05ms  int-real-relax
  identity + array assn    Unsat 7.91ms  int-real-relax
  UF-atom identity         Unsat 3.53ms  uf-arithmetic
  opaque M                 Unsat 1.13ms  int-real-relax
  NEAR MISS (a^2+3ab+b^2)  Sat 22.54ms   nia-linearize   [negative control OK]
  SAT CONTROL a>=1,a*p=1   Sat 2.48ms    nia-linearize   [negative control OK]

REAL GAPS (Unknown before):
  G1 identity diseq + `div` term elsewhere   Unknown(Timeout) 15.00s  int-blast-ladder decline
  G2 rational-coeff identity over Real (/2.0) Unknown(Timeout) 15.44s  nra budget decline
  G3 a>=2 & a*p=1                            Unknown(Timeout) 15.00s
  G4 a<=-2 & a*p=1                           Unknown(Timeout) 15.00s
  G5 a>=2 & b>=2 & a*b*q=1                   Unknown(Timeout) 15.00s

Design decision: route (1) is NOT vacuous but its measurable win is G1/G2 (mixed with
unspecified arith / rational division) plus a cheap re-checkable certificate where
int-real-relax gives none. Route (2) owns G3-G5.

## 2026-08-12T21:29:32-04:00 — AFTER wiring both routes (same probe file, same 15s budgets)
CMD: cargo test -p axeyum-solver --features full --test zz_cas_probe_tmp -- --nocapture --test-threads=1
  G1 identity + div elsewhere   BEFORE Unknown 15.00s -> AFTER Unsat  154.73us  cas-identity-refuter
  G2 rational-coeff Real /2.0   BEFORE Unknown 15.44s -> AFTER Unsat  139.16us  cas-identity-refuter
  G3 a>=2 & a*p=1               BEFORE Unknown 15.00s -> AFTER Unsat   78.81us  cas-int-units      (probe_units_neg is a<=-2)
  G4 a<=-2 & a*p=1              BEFORE Unknown 15.00s -> AFTER Unsat   78.81us  cas-int-units
  G5 a>=2 & b>=2 & a*b*q=1      BEFORE Unknown 15.00s -> AFTER Unsat   96.65us  cas-int-units
NO REGRESSION on the already-decided set; they now decide FASTER via the new route:
  deg-9 3var  5.05ms -> 7.34ms (cas) ; mixed array 7.91ms -> 192us ; opaque M 1.13ms -> 145us ;
  UF-atom 3.53ms -> 136us
NEGATIVE CONTROL still SAT: a>=1 & a*p=1 -> Sat 2.82ms, and the trace RECORDS the decline:
  "cas-int-units: declined (incomplete: no integer equation normalized to a refutable k.m = c)"
Suite wall clock 60.48s -> 0.02s.

## 2026-08-12T21:34:56-04:00 — GATES
cargo test -p axeyum-solver --lib --features full        -> 1104 passed; 0 failed (84.24s)  NONZERO ok
cargo test -p axeyum-solver --features full --test corpus_regression -> 1 passed (18.60s)   NONZERO ok
cargo test -p axeyum-solver --test progress_frontier --features full -- --test-threads=1
   -> 8 passed; 1 FAILED (frontier_bv_reduction: frontier 26 < baseline 30), 9 total NONZERO ok

## 2026-08-12T21:40:16-04:00 — A/B on the frontier failure (is it mine?)
Patched auto.rs dispatch hook to `if false && ...` (CAS routes unreachable), rebuilt, reran:
   frontier_bv_reduction STILL FAILS: frontier 26 < baseline 30, load 2.02
=> PRE-EXISTING / ENVIRONMENTAL, not caused by this change. bv_reduction is a pure QF_BV
   instance (`not (= (x*a1*..*aD) (x*A))` over BitVec) so features.has_int/has_real are both
   false and dispatch_cas_refuters is never entered. Box is NOT idle: `uptime` shows load
   2.02-2.47 at rest (another agent shares this checkout, per CLAUDE.md multi-agent note).
   Undecided points sit at 4009-4020 ms of a 4000 ms budget = at the measurement's resolution.
Hook restored to `features.has_int || features.has_real`.

## 2026-08-12T21:43-21:46 — implementation landed, clippy + targeted gates
Files:
  crates/axeyum-cas/src/mvpoly.rs        + MvPoly::term_count/terms(), Monomial::powers()
  crates/axeyum-solver/Cargo.toml        + axeyum-cas optional dep, in `full`
  crates/axeyum-solver/src/cas_poly.rs        NEW  (untrusted search: MvPoly normalization + 2 refuters)
  crates/axeyum-solver/src/cas_certificate.rs NEW  (trusted checker, NO axeyum-cas import)
  crates/axeyum-solver/src/auto.rs       + dispatch_cas_refuters after term-identity-refuter
  crates/axeyum-solver/src/lib.rs        + modules + doc(hidden) re-exports
  crates/axeyum-solver/tests/cas_bridge_routes.rs NEW (25 tests)

clippy findings fixed: explicit_iter_loop x4, too_many_lines on check_auto_with_recorder
  (moved the feature gate INTO dispatch_cas_refuters so the call site is 3 lines),
  redundant_closure_call in the new test file.
cargo clippy -p axeyum-solver -p axeyum-cas --all-features --all-targets -- -D warnings  -> clean

cargo test -p axeyum-solver --lib --features full cas_   -> 17 passed (1104 filtered out) => lib total 1121
cargo test -p axeyum-solver --features full --test cas_bridge_routes -> 25 passed
Trace-sensitive suites (grep for check_auto_explained|RouteTrace|RouteOutcome):
  route_trace 12 passed / finite_domain_split 5 passed /
  uf_arith_dispatch_differential 2 passed / ufnra_route 5 passed
Deleted crates/axeyum-solver/tests/zz_cas_probe_tmp.rs (temp probe, never committed).

## 2026-08-12T21:52 — ADR + overflow hardening
Wrote docs/research/09-decisions/adr-0386-cas-refutation-routes.md (next free number:
0386; 0385 is local-only, origin/main tops out at 0384; `ls adr-0386*` -> no such file).
Added the README index row.

Hardening pass while the full sweep compiled (i128::MIN paths — `abs`, `/ -1`, `% -1` all
PANIC in Rust; a pathological coefficient must make the route DECLINE, not abort):
  cas_poly.rs   coefficient.abs()      -> coefficient.checked_abs()?
  cas_certificate.rs  target % coefficient  -> target.checked_rem(coefficient)
  cas_certificate.rs  (target / coefficient).checked_abs() -> checked_div(..).and_then(checked_abs)

Worktree note: bench-results/frontier/*.json are DIRTY as a side effect of my
progress_frontier runs (the harness writes them). NOT committing them and NOT reverting
them (another agent may also be running the ratchet; CLAUDE.md forbids checkout on files
you don't own). docs/plan/cas-smt-capability-2026-08-12/ is another agent's untracked WIP
(created 21:21 while I was working) — untouched.

## 2026-08-12T21:50:55-04:00 — COMMIT 175372bdc
git add <10 paths> && git commit -m ... -- <same 10 paths>   (pathspec-only, verified)
 Cargo.lock 1+ / axeyum-cas/src/mvpoly.rs 28+ / axeyum-solver/Cargo.toml 5+ /
 auto.rs 117+- / cas_certificate.rs 689+ / cas_poly.rs 750+ / lib.rs 12+ /
 tests/cas_bridge_routes.rs 605+ / 09-decisions/README.md 1+ / adr-0386 177+
NOT included (correctly): bench-results/frontier/*.json (my harness side effects),
docs/plan/cas-smt-capability-2026-08-12/ (another agent's untracked WIP).
cargo fmt --all --check -> no diffs anywhere in the workspace.

## 2026-08-12T21:56 — post-commit hardening (arity)
Audited the `-` handling: SMT-LIB `-` is unary negation at arity 1. The arena only ever
builds IntSub/RealSub BINARY (`int_bin`), unary `-` becomes IntNeg/RealNeg — but my Sub
handler read args[0] and looped over the rest, so a hypothetical 1-arg Sub node would have
silently dropped the negation (a wrong-unsat shape). Added an explicit `args.len() < 2 =>
decline` in BOTH expanders rather than relying on the invariant. Will land as a follow-up
commit after re-running the tests.

## 2026-08-12T22:07:24-04:00 — RESUME after parent process exit
git status: only the two in-flight arity-guard edits were uncommitted. Completed + formatted.
Coordinator restored bench-results/frontier/*.json and bisected frontier_bv_reduction to
9f0f4ed00 and 61ee26217 (both BEFORE this work) => my routes exonerated, matching my own
`if false &&` A/B at 21:40. I did NOT touch bench-results/ again.

## 2026-08-12T22:07-22:13 — FINAL GATES (all NONZERO)
cargo test -p axeyum-solver --features full --test cas_bridge_routes
  -> test result: ok. 25 passed; 0 failed; ... finished in 0.06s
cargo test -p axeyum-solver --lib --features full cas_
  -> test result: ok. 17 passed; 0 failed; 1104 filtered out
cargo test -p axeyum-solver --lib --features full
  -> test result: ok. 1121 passed; 0 failed; 0 ignored; finished in 79.53s   (was 1104 pre-change)
cargo test -p axeyum-solver --features full --test corpus_regression
  -> test result: ok. 1 passed; 0 failed; finished in 20.36s
cargo clippy -p axeyum-solver -p axeyum-cas --all-features --all-targets -- -D warnings
  -> Finished, no diagnostics
cargo fmt --all --check   -> 0 "Diff in" lines (whole workspace clean)
cargo test -p axeyum-cas  -> 147 doctests + unit tests, 0 failed  (blast-radius check on mvpoly)
RUSTDOCFLAGS="-D warnings" cargo doc -p axeyum-solver -p axeyum-cas --features full --no-deps
  -> Finished, clean
progress_frontier: NOT re-run (it rewrites bench-results/frontier/*.json and the coordinator
  restored them). Last run 21:34: 9 tests, 8 passed, frontier_bv_reduction failed; proven
  pre-existing by both my `if false` A/B and the coordinator's bisect.

## 2026-08-12T22:10:34-04:00 — COMMIT 8cda98eca
fix(cas): require arity >= 2 before reading a `-` node as subtraction
  crates/axeyum-solver/src/cas_certificate.rs 8+ / crates/axeyum-solver/src/cas_poly.rs 8+
Tree clean afterwards.

## ADR numbering re-verified 2026-08-12T22:10 (after `git fetch origin`)
origin/main now carries adr-0384 and adr-0385 (nat prelude). NOTHING at 0386 on any ref:
  git log --all --oneline --diff-filter=A -- 'docs/research/09-decisions/adr-0386*'
  -> 175372bdc only (mine). Index row present at README.md:444.

## axeyum-cas change, stated explicitly (blast radius)
crates/axeyum-cas/src/mvpoly.rs: +28 lines, ZERO deletions, ZERO modified lines.
Three read-only accessors over already-private fields; no algorithm touched:
  Monomial::powers()    -> Iterator<(&str, u32)>   (BTreeMap iteration, ascending var order)
  MvPoly::term_count()  -> usize                    (self.terms.len(); named term_count, not
                                                     len, to avoid clippy len_without_is_empty
                                                     and to keep is_zero as the predicate)
  MvPoly::terms()       -> Iterator<(&Monomial, &Rational)>  (self.terms.iter())
Needed because the certificate emitter must serialize the polynomial normal form and the
translator must cap intermediate term counts; both were impossible with the fields private.
cargo test -p axeyum-cas passes unchanged.

## 2026-08-12T22:14:00-04:00 — post-merge re-confirmation
Another lane merged origin into the branch (HEAD = 9bf54e822, a merge commit created after
my two commits). Verified both my commits are ancestors of HEAD, all four new/changed files
are present at HEAD, the arity guard survived (grep count 1), and the tree is clean.
Re-ran at merged HEAD: cas_bridge_routes 25 passed; lib cas_ subset 17 passed.
