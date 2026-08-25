# Notes: 123-theorem-correspondences

Detail moved out of [`../status/123-theorem-correspondences.md`](../status/123-theorem-correspondences.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Next**, and the ordering is deliberate. (1) **The 20 cross-carrier ℕ/ℤ pairs
already in the ledger** — `modeq-*` (13 of them), `fib-*`, `gcd-greatest`,
`add-modeq-*`. The carrier-erasure check makes each cheap to adjudicate and
impossible to fake, and some will be **refused** as `depends_on` dependencies,
which is the useful half of the answer. (2) **A fact for `Int.fib_cassini` and a
fact for `Rat.det2_mul`** — see the blocker below; the correspondence between
them is one JSON file once they exist. (3) `null` `via` refs are a named
backlog: `Int.ofNat` injectivity, `↑a ∣ ↑b ↔ a ∣ b`, and the two CPoint/SMT-real
carrier steps are each a missing fact that three correspondences point at.

**Blocked, and worth someone's attention beyond this lane.**
`artifacts/autogenesis/kernel-dependency-projection-v1.json` is STALE against
theorems that landed the same day it was refreshed:
`git merge-base --is-ancestor aa3e8ea24 e256492c2` is **false**, so the refresh
at `e256492c2` predates the linear-algebra commit. It holds 195 `Rat.*`
declarations and zero `det2`, zero `cramer`, zero `fib`. Every
`kernel-declaration` endpoint anywhere in the knowledge overlay inherits that
blind spot, and refreshing it needs a workspace `cargo run` this lane could not
justify in a tree five lanes are editing.

Two pre-existing gates are red for reasons this lane did not cause and did not
fix: `check-control-registration.sh` reports `py_orphans` 199 → 203 (all
`test_analyze_*`, committed by other lanes), and `check-aggregate-scope.sh`
reports a long standing `just-only` list of autogenesis steps. The new gate is
on **both** sides and adds no divergence.
