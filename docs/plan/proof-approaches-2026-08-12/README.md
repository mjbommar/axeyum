# Proof approaches — session of 2026-08-12

**What changed today:** the general-`k` shell-construction lower bound went
from *"verified at 11 computational points and asserted in a Python script"*
to **a theorem with a written, reviewed proof**.

That distinction is the point of the session. Every Rado number this project
had produced was established by *verification* — a DRAT certificate answering
"is this one formula unsatisfiable?" in ~10^8 opaque steps, silent about
`n+1` and silent about why. A proof of the construction is a single finite
argument covering infinitely many `(a, b, k)`. No amount of instance-checking
produces one.

## The result

> **Theorem 1.** Let `a >= 2`, `b >= 1`, `gcd(a,b) = 1`, **`b < a`**, `k >= 2`.
> The shell colouring of `[1, N]`, `N = b(a^(k-1) + 2(a + ... + a^(k-2)))`,
> contains no monochromatic solution of `a(x-y) = bz`. Hence
> `R_k(a(x-y)=bz) >= N + 1`.

with an exact characterisation of when the construction works at all —
**solution-free iff `b < a` or `k = 2`** — and a closed-form monochromatic
witness for every `b > a`, `k >= 3` proving the hypothesis is not an artifact.

## Three routes, run as concurrent Opus subagents

| Route | Question | Outcome |
|---|---|---|
| **A** — traditional proof | Can the construction be proved by hand? | **Yes.** Theorem 1 + sharpness + the `k=2` characterisation. `route-a/proof.tex` |
| **B** — axeyum `forall`-refutation | Can axeyum discharge a *universally quantified* statement, as it once did for the solution-form lemma? | see `route-b/` |
| **C** — axeyum Lean kernel | Can the in-tree Lean kernel check a real mathematical theorem? | **Yes, with zero axioms.** 9 `forall`-theorems over `N`, real induction. `route-c/` |

## Layout

- `ORCHESTRATOR-LOG.md` — my own append-only notebook (18 entries), including
  **three of my own errors, their detection, and their retraction**. Read this
  for the honest path; the reports are the tidy conclusions.
- `PROOF-BRIEF.md` — the measured ground truth all three agents started from.
- `route-a/` — the proof (`proof.tex`), its report, its log, and seven Python
  stress-test scripts (`run_all.sh`).
- `route-b/` — the `forall`-refutation attempt.
- `route-c/` — the Lean-kernel development, its log, and the exported
  self-contained Lean module.
- `cas-verification/verify_proof_algebra.rs` — verifies the proof's algebra
  with **axeyum's own CAS** (`axeyum-cas` `MvPoly`, exact rational polynomial
  arithmetic): 118 symbolic checks, 0 failures, including 11 negative
  controls that correctly refuse to vanish.
- `preliminaries.tex` — the structural lemmas (solution form; `a | z`;
  self-similarity; the lifting principle). **Note:** the corollary
  `R_k >= a^k` reproved there is *Chang-De Loera-Wesley Lemma 4.1*, already
  published — it is included as the baseline the shell construction beats,
  not as a contribution.

The Lean development itself lives in the crate, not here:
`crates/axeyum-lean-kernel/tests/rado_shell_arithmetic.rs`.

## What is NOT claimed

Stated plainly so it cannot drift in later editing:

- **No upper bounds.** Nothing in this session shows `R_k = N + 1` anywhere.
  The exact values 31 / 73 / 103 / 313 rest on the refutation evidence in
  `artifacts/claims/`, which is a separate body of work.
- **Tightness fails at `k = 5`.** The construction gives 318 at
  `(a,b,k) = (3,2,5)` while a verified solution-free 5-colouring of `[350]`
  exists. Exhaustive enumeration over 644,956 cut vectors shows 318 is the
  *hard ceiling of the whole shell shape*, so the gap needs a different
  colouring, not better parameters.
- **The Lean export has not been checked by real Lean.** `lean`, `lake` and
  `elan` are all absent on this machine (verified). The module is emitted and
  structurally checked (0 `sorry`, 0 `axiom`); validating it against the real
  toolchain is one command for anyone who has it, and is the highest-value
  next measurement.
- **Route A used no axeyum.** Its Python stress-tests the proof; it is not
  the proof. The axeyum contributions this session are route C (kernel) and
  the CAS verification.

## Reproducing

```sh
# the Lean-kernel theorems (expect: 9 passed)
cargo test -p axeyum-lean-kernel --test rado_shell_arithmetic

# the proof's computational stress tests
cd docs/plan/proof-approaches-2026-08-12/route-a && ./run_all.sh

# the CAS symbolic verification (expect: 118 run, 0 failed)
# copy verify_proof_algebra.rs into a crate depending on axeyum-cas + axeyum-ir;
# Cargo.toml.reference records the exact dependency stanza used.
```
