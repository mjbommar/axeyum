# Lane: absence-expiry — make an absence claim in prose expire against the kernel

<!-- plan-section: lane-status -->

**Done (`WIP`, absence-expiry, 2026-08-27).** ADR-0608 made *retrieval* answer
honestly. This lane makes the *documents* do so: a doc that records an
obstacle carries a machine-checkable marker, and a gate fails the moment the
declaration it claims absent appears in `kernel.environment()`.

**The mechanism, and why this shape.** `scripts/check-absence-claims.py`
reads two markers, both of which are HTML comments (invisible in Markdown and
in rustdoc, since a `//!` doc comment is Markdown, so one grammar covers both
surfaces):

- **`absent:`** — a LIVE claim. FAILS when the named declaration is PRESENT.
  That is the expiry.
- **`was-absent:`** — a RESOLVED record. FAILS when the declaration is
  ABSENT, so a "this was fixed, see X" note cannot start pointing at nothing
  after a rename. The `check-shape-duplicates.py` both-directions discipline.

Correcting a stale claim is a **one-word edit** that keeps the record under
the gate rather than removing it from it.

Colocated rather than a central registry, because the in-tree model is
`#[expect(dead_code, reason = "…")]` (which `creal/integral.rs` uses for
exactly this): silent while its condition holds, an error the moment it
clears, attached to the line you have to edit. A registry would also become a
shared append point across lanes, the failure CLAUDE.md documents for
`PLAN.md` and the ADR index. Rejected alternatives and their reasons are in
[ADR-0611](../../research/09-decisions/adr-0611-an-absence-claim-in-prose-must-expire.md)
(expiry date: goes red on a schedule, not on a fact; doc-test: Markdown here
is not compiled and the Rust half is in `//!` comments in a crate five lanes
are editing).

Detail moved to [`../notes/151-absence-expiry.md`](../notes/151-absence-expiry.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | (pending commit) | ADR-0611 + `scripts/check-absence-claims.py`: an absence claim in prose carries `<!-- absent: Root.name -->` and the gate fails the moment that declaration exists in `kernel.environment()` — `#[expect(dead_code)]` for documentation. `<!-- was-absent: … -->` is checked in the opposite direction so a historical record cannot point at nothing. Seeded on four of the five known-stale records of 2026-08-27 (the fifth, `trig_fn.rs`, verified still literally true); demonstrated red-then-green by `scripts/tests/demo-absence-expiry-seeds.sh`; 25/25 guards mutation-killed, 0 survived, 0 unmeasured. Adoption printed on every run: 4 of 145 checkable claim sites annotated (one of them a LIVE `absent:` claim on `CReal.within_of_close_within`, which reds the day that bridge lands), 141 not, 560 sites structurally uncheckable. |
