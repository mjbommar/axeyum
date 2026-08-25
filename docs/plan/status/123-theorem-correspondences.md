# Lane: agent-correspondence-model — saying that two theorems are the same idea

<!-- plan-section: lane-status -->

**Theorem correspondences (`WIP`, agent-correspondence-model, 2026-08-24).** The
data model can now state that two settled facts are the same mathematical
content, and cannot state it where `depends_on` belongs
([ADR-0546](../../research/09-decisions/adr-0546-theorem-correspondences-are-not-proof-dependencies.md)).
`artifacts/correspondences/*.json`, one file per adjudication on the
`artifacts/facts/` pattern, gated by `scripts/validate-correspondences.py`
(`just correspondences`; 39 mutations, 39 killed, one test each). Three
instances landed, all `route-recorded`.

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

<!-- plan-section: landed-changes -->

| 2026-08-24 | `c0c2b6fea` | **ADR-0546 + the gate wired into both aggregates.** Records three findings against the brief: `technique`/`concept` are NOT uninstantiated overlay kinds (24 endpoints, resolved `external-pinned` next door); the existing vocabulary still does not suffice, because `unlocks` is reachability and every `formalizes` edge is *required* to be `completeness: partial` so two cannot compose into "same"; and the motivating `Int.fib_cassini ↔ Rat.det2_mul` edge **is not landable** — neither theorem has a fact and neither is in the kernel projection, so `specialization` ships as a declared kind with zero instances and the gate prints that zero. |
| 2026-08-24 | `06b41a5e6` | **`artifacts/correspondences/` — two theorems can be said to be the same idea, and the claim is checked.** Refuses any pair the ledger's *transitive* `depends_on` closure connects (`F:ml430-nat-fib-add-two` / `F:ml430-int-fib-add-two` is a real such pair and the control pins the refusal against the committed ledger). `carrier-transport` is checked *structurally* — erasing the carrier from both formal statements must leave the same string, and an unknown carrier FAILS rather than skipping. Two status axes mirroring the ledger's, each backed: `asserted` ⟺ empty `via`; `route-recorded` requires every non-null ref to resolve; `mechanized-here` forbids a null ref and requires a checker command; evidence at all requires `mechanized-here`. Empty population exits 1. Prose floors set from measuring `../math-education` (1,263 reasons, median 190 chars — and a bridge to `C:pi` whose reason was about *density* validated cleanly there, which is why nothing here rests on prose). |
