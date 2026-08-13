# Rado publishable result — replication and evidence pinning, 2026-08-13

Detail moved out of PLAN.md under the 50 KB authority ceiling. PLAN.md keeps
the pointer; this file keeps the record.

**Lane extension — publishable result, replication, and evidence pinning
(2026-08-13).** Three sibling repositories (`axeyum`,
`../axeyum-rado-paper`, `../axeyum-rado-artifacts`) were brought to a
submittable state. What changed here:

- **The 313 upper bound had no identified subject.** `F_313.cnf` was
  untracked and `claim.json` recorded no instance hash, so five cover ledgers
  held verdicts about a formula nothing named. Added an `instance-pin`
  evidence kind, checked by **regeneration** (an independently written
  encoder re-derives the CNF from `(a,b,k,n)` and requires byte-identity),
  and pinned both headline instances. Two negative controls fire, including
  a *self-consistent forgery* — corrupt CNF plus matching hash — which any
  hash-only gate would pass.
- The 226 `upper-drat` row was **not evidence of its stated bound** (kind
  `unsat-certificate`, artifact the formula, checker external kissat, note
  claiming a run "in progress" that was not). Restated as an instance pin.
- The 313 claim's **default artifact was the wrong cover**: `cube-cover.tsv`
  was the 1024-cell, 224-deferred one while the prose described the complete
  4096-cell cover, which sat under a name the prose never used. Swapped.
- **Both re-check commands the shipped arXiv bundle documents had never
  worked** (missing schema; `FileNotFoundError` on the first witness). Fixed;
  the checkers now also report rows they could *not* re-check rather than
  passing them silently.
- New claim `rado-r4-a6-b5-frontier`: `R_4(6(x-y)=5z) > 1500`, the second
  open cell of the `k = 4` row, **free from the main theorem** — written down
  from the construction, not searched for, and checked three independent
  ways.
- **Replication on five hosts from clean clones**, roles `gate`, `cover226`,
  `cover313`, `ladder`, `ledger`, across three `cargo` toolchains
  (1.96/1.97/1.99-nightly). `ledger` and `ladder` each passed **7/0 on two
  different hosts and two different toolchains**. Measured and recorded:
  `recertify_rado` needs **~28 GiB** and was OOM-killed at exit 137 on a
  27 GiB box — a resource failure that reads exactly like a refuted claim, so
  `replicate.sh` now warns before and annotates after.
- Three review passes (codex CLI plus independent agents) found **no error in
  any of the three theorems**, including the `a = 2` rigidity corner, and
  confirmed them by exhaustive enumeration. They did find one false step in a
  written proof (`a \nmid m'n'`, false for composite `a`), two malformed
  statements, and four overclaims — all corrected. Details in the paper
  repository's history.

## Results that arrived after the section above was written

**F_313 refuted MONOLITHICALLY.** On replication host s4, from a clean clone,
`recertify_rado` regenerated F_313 to its pinned sha256 and refuted it as one
formula: 60,543,837 steps, 5,001,394,569 bytes of text DRAT, verified by
`check_drat_backward`. Solve 1677.348 s, parse 24.117 s, check 2669.084 s;
proof sha256 `097a6cd386a14d1957cd3d5b4ff4e7ef68ad7c7ebb6ee88032f98047873c3f03`.
Recorded as evidence row `upper-monolithic`. For that value the cover
composition meta-argument is not merely dischargeable, it is unused. It does
NOT remove the backward checker, and it says nothing about 226.

**The F_103 forward check finally completed, on the third attempt.** Two runs
were killed at ~50 minutes with no output; a third, left detached, finished in
3643.051 s with both checkers confirming UNSAT over 1,202,198 steps (backward:
6.421 s, a 567x ratio). Both earlier kills had landed within ten minutes of a
run that was going to succeed. This is the largest demonstrated
forward/backward agreement; agreement at *cover* scale (~100x larger) remains
undemonstrated.

**Memory requirement, measured twice.** `recertify_rado` was OOM-killed at
27,742,576 kB on a 27 GiB host (n=313) and at 26,345,012 kB on a 26 GiB host
(n=226); it completed on 123 GiB. Exit 137 reads exactly like a refuted claim
and is not one. `scripts/replicate.sh` now warns below 48 GiB and annotates
exit 137.

## Mistakes made in this session, recorded because they cost real work

1. **Two multi-hour replication runs were destroyed by redeploying
   `scripts/replicate.sh` while the hosts were executing it.** Bash reads a
   script incrementally by byte offset, so overwriting it mid-run corrupts
   execution: s0 died with `line 154: A: unbound variable`, s4 with
   `line 178: syntax error near unexpected token ';;'`. s4's cover226 had
   produced an 18.9 GB proof over roughly five hours and never reached a
   verdict. **Never overwrite a script a long-running job is executing** --
   deploy to a versioned filename, or wait.

2. **A fixture lock refresh traded one test failure for another.** Refreshing
   `mir-contract-target/Cargo.lock` fixed the `--locked` build but broke
   `committed_capture_is_authenticated_and_root_independent`, because the
   capture is authenticated by `artifacts/SHA256SUMS` and Cargo.lock is one of
   the six files it covers. Both places recording the hash must move together.

3. **The aggregate gate had been red since 175372bdc** (the CAS bridge gave
   `axeyum-solver` a dependency on `axeyum-cas` while the fixture's lock
   predated it). Only a full-gate run catches this class, and only the fleet
   replication ran one.
