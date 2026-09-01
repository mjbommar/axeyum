# ADR-1300: A coverage table must state a verdict for every producer, and a blank cell is a defect

Date: 2026-08-31
Status: Accepted
Lane: `cas-coverage-audit`

Index-summary: The Spivak spine table's route legend named three routes and omitted the CAS, which produced a wrong answer to the user about what is complete. Chapter 20 read "open" while `taylor.rs` shipped Taylor's theorem with the Lagrange remainder, and chapter 19 had no row at all. Every row now carries an audited `C` (ADR-0603 row 3) cell -- a named module and function, or an explicit `audited -- none` with its reason -- and `scripts/check-spivak-cas-column.py` fails on a blank one, eight guards each mutation-verified to be killed by exactly one control.
Index-status: Accepted

Extends
  [ADR-0601](adr-0601-three-producers-one-trust-anchor.md) and
  [ADR-0603](adr-0603-classical-theorems-land-as-graded-statement-families.md)
  into the documents that *report* coverage.

## Context — the failure this closes

Asked how much of Spivak's *Calculus* is complete, I answered from
`docs/curriculum/foundational-books/spivak.md`'s route column. Its legend read

> Three routes, not two:
> **S** — solver-decidable · **K** — constructive kernel · **X** — unavailable
> in this logic.

and the string `axeyum-cas` appeared **once** in the whole file, against 28
mentions of `CReal`. So I reported the `X` rows as terminal.

`X` is ADR-0603 **row 1**'s verdict — the general constructive form. The CAS is
**row 3**: the exact classical statement, decided on the fragment where it is
decidable, with a re-checkable certificate. The two are different propositions,
and ADR-0603's whole argument is that row 1 is optimal *because* row 2 refutes
the general form while row 3 still settles the decidable one.

What was actually in the tree, found by reading module docs in one command:

| Spivak | what the table said | what the module doc says |
|---|---|---|
| 7 EVT | "not constructive" | `extremum.rs`: "Exact polynomial EXTREMUM (ADR-0603 row 3): the Extreme Value Theorem on the decidable fragment" |
| 11 MVT | "unavailable, rests on EVT" | `mvt.rs`: "Exact polynomial MEAN VALUE THEOREM (ADR-0603 row 3)" |
| **19** | **no row at all**, in a table running 1 → 30 | `partial_fractions.rs`: "Certified PARTIAL-FRACTION DECOMPOSITION (**Spivak ch. 19**)"; `ratint.rs`: Horowitz–Ostrogradsky |
| **20** | `\| 20 \| Taylor polynomials \| — \| open \|` | `taylor.rs`: "Exact polynomial TAYLOR'S THEOREM with Lagrange remainder (ADR-0603 row 3, **Spivak ch. 20**)" |

The chapter-20 cell is the instructive one. It is not stale — nothing about it
ever became false. Nobody looked.

## The failure mode, stated generally

**A coverage table with one verdict column per row cannot distinguish "this is
out of reach" from "nobody checked this route."** Both render as a dash. And the
cost is asymmetric in the way `spivak.md`'s own Postscript II already records: a
stale *"this is impossible"* suppresses attempts silently and forever, while a
stale *"this is easy"* is corrected by the first lane that tries.

That asymmetry is why this is worth a decision rather than a fix. The document
was not wrong about `K`; every `K` cell held up under audit. It was **silent
about a producer**, and silence read as a verdict.

## Decision

1. **A document that reports coverage, capability or reachability must carry a
   column or an explicit section per PRODUCER** (ADR-0601: autogenesis /
   kernel, the CAS, the importer), not one merged verdict.

2. **A cell that reports nothing must say so explicitly, with a reason.** The
   marker in `spivak.md` is the literal string `audited — none`, followed by why.
   An unexplained "none" is exactly as unfalsifiable as a blank, and this
   repository's standing rule is that a checker which cannot fail is worse than
   no checker.

3. **A cell that asserts a route must name what was consulted** — a
   `module::function`, a `module.rs`, or a `F:…` ledger fact id. "The CAS
   handles this" is not an audit finding.

4. **A CAS cell must state its ADR-0601 §2 classification.** `cas-internal`
   (the certificate terminates in the CAS's own normal form) and
   `kernel-reconstructed` (an executed checker segment names
   `axeyum-lean-kernel`) are different claims, read from
   `scripts/validate-facts.py`'s `classify_cas_certificate_fact`, never from a
   label a fact carries. Measured 2026-08-31 over the 46 `cas-certificate`
   facts: **32 `cas-internal`, 14 `kernel-reconstructed`**.

5. **The rule is enforced, not written down.**
   `scripts/check-spivak-cas-column.py` is an L0-shaped gate in `check.sh` and
   the `justfile`. Eight guards, each failing on something the others cannot
   see; controls in `scripts/tests/test_check_spivak_cas_column.py`, registered
   as `spivak-cas-column` in `scripts/tests/mutation_controls.py`.

## Consequences — what the audit actually found

All 23 spine rows now carry a `C` cell. Six contradicted the `Route`/`State`
columns; the refuted text is quoted in a dated block under the table rather than
deleted, per the file's own convention. Chapter 19 was added.

Two corrections went the **other** way and matter as much: FTA over ℂ (Ch 25–27)
and uniform convergence (Ch 24) are `audited — none` on the CAS side too —
`sturm.rs` and `algebraic.rs` isolate REAL roots only, and nothing in the crate
states uniform convergence. So the `K` rows' pessimism about those two is
*confirmed by an independent route* rather than contradicted. An audit that only
ever adds capability is not an audit.

Three further findings, each of which is a task rather than a conclusion:

- **Unregistered capability.** Chapters 5, 12, 13 and 14 have a real,
  certificate-carrying `C` route and **zero** ledger facts. `lib.rs::integrate`
  returns a proof of its own correctness on every call and nothing in
  `artifacts/facts/` records it.
- **The legend's own numbers were low.** It says "72,008 lines, 363 public
  functions across 53 modules". Those are `src/*.rs` with `pub fn` at column 0 —
  excluding the `mvpoly/`, `ntheory_certify/`, `sos/` and `bin/` subdirectories
  and every `impl` method. All 68 `.rs` files under `src/`: **77,590 lines**,
  **685 `pub fn`**. 53 modules is right. The error ran in the under-reporting
  direction, which is the direction this ADR is about.
- **`docs/research/08-planning/capability-matrix.md` is a structural instance
  and cannot be fixed here.** It is generated from
  `axeyum_solver::capabilities::CAPABILITIES`, so it is a matrix of *solver*
  capabilities and the CAS is not one. Nothing in it is wrong; its NAME promises
  more than its source can deliver, and a reader treating it as the capability
  index will not find the CAS. Fixing that means widening the generator's
  source, which is a separate decision.

## Alternatives considered

- **Fix the prose and stop.** Rejected: `spivak.md` already carries two dated
  corrections and a Postscript II *specifically about documents going stale*,
  and the omission still produced a wrong answer to the user. Prose demonstrably
  did not hold this.
- **Gate every coverage document, not just `spivak.md`.** Rejected for now: the
  three others swept in this lane
  (`docs/learn/math/calculus-theorem-boundary.md`,
  `docs/mathematics-2026-08/04-reachability.md`,
  `docs/curriculum/03-destinations/calculus.md`) have no table shape a checker
  could read, so a gate over them would be a keyword scan — which is the
  "crude classifier that flags a whole shape" this repository has already been
  burned by. They got dated pointers instead, and the pointer says the existing
  scoping statements are correct about what they scope.
- **Merge the CAS into the `Route` column as a fourth letter.** Rejected: a
  single letter cannot say `cas-internal` versus `kernel-reconstructed`, which
  ADR-0601 requires be visible. A route letter is a claim; the `C` column is
  evidence.
