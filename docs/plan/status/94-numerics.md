# Lane: numerics — exact certificates for polynomial dynamics

<!-- plan-section: lane-status -->

**Landed a sums-of-squares capability for polynomial dynamical systems — Lyapunov
stability, barrier reachability, and a PSD-not-SOS witness — as exact rational
certificates, and stopped before putting any of it in the fact ledger** (`WIP`,
numerics, 2026-08-15). This lane was cut off mid-step by the account's monthly
spend limit; the code, artifacts and controls are committed, the ledger entries
are not. Decision record: [ADR-0467](../../research/09-decisions/adr-0467-numerical-dynamics-enter-as-exact-certificates-with-the-analytic-bridge-named.md).

**Why this lane existed.** The project's owner named four useful domains —
planning, logistics, database design, and numerical / ODE / PDE. The first two
had schedule infeasibility with Farkas certificates reconstructed into Lean, the
third was built the same day by [`db-design`](57-db-design.md), and this was the
last one with nothing in it.

**What is in.** `61b4bc73c`, 4,027 lines: `crates/axeyum-cas/src/sos/` (`check`,
`corpus`, `json`, `psd`), the `sos_certify` and `emit_sos_certificates` examples,
committed Lyapunov / energy-barrier / Motzkin artifacts, a
`sos_certificate_artifacts` test suite, and — the part worth naming —
`scripts/gen-sos-negative-controls.py` with `scripts/check-sos-negative-controls.sh`.

**Verified by the coordinator when landing the rest of the session, not inherited
from a report this lane never wrote:**

```
scripts/check-sos-negative-controls.sh
  21 negative control fixture(s), 36 assertion(s) run, 0 failure(s)   exit 0
```

**What is NOT done, and must not be read as done.** There is **no fact** for any
of this. `artifacts/facts/` was untouched by `61b4bc73c`, so the capability exists
and the self-extension loop is not closed over it: nothing in the ledger claims a
Lyapunov result, and `fact-frontier.py` therefore cannot see this capability
either. The obvious next step is three facts with checkers that fail when the
claim is false, following the shape `db-design` used.

**The ADR is the durable part.** ADR-0467 records that the passage from a
pointwise polynomial inequality to a statement about *solutions* of an ODE is an
**axiom in `axiom_footprint`, never a silent step** — the same honesty the
`simson` lane applied to the ℝ-versus-ℚ̄ question in geometry. It was written as
ADR-0466 and renumbered when `import-projrec` turned out to have claimed that
number concurrently and already referenced it from code.
