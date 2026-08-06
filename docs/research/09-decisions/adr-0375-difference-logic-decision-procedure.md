# ADR-0375: Difference logic as a first-class fragment, with conjunctive Farkas evidence

Status: accepted

Date: 2026-08-03

## Context

Until 2026-08-03 the stack had **no difference-logic decision procedure**. A
`QF_IDL` or `QF_RDL` query fell through to the generic linear-arithmetic cores,
whose Fourier–Motzkin / simplex conflict explanations are large: measured on the
`QF_IDL` residuals, thousands of blocking rounds with cores in the hundreds of
literals. `crates/axeyum-solver/src/dl_online.rs` closed that gap, and the
measured effect on the committed 200-file parity lists was `QF_RDL` 6.6% → 68.6%
and `QF_IDL` 41.5% → 53.7% of the cvc5 reference, 0 disagreements.

Two things were then out of sync with the code, and this project's rule is that
neither is allowed to stay that way:

1. **The ledger did not know.** `capabilities.rs` (the golden-tested capability
   ledger) and `support_matrix.rs` had no difference-logic row at all, so the
   authoritative statement of what the stack decides *understated* it. The safe
   direction, but still wrong.
2. **The evidence was thrown away.** Every theory conflict was already rebuilt as
   a `FarkasCertificate` and passed through `FarkasCertificate::verify` before it
   could become a lemma — and then dropped. A difference-logic `unsat` therefore
   reached the evidence front door as a **bare** `unsat`. `bench-results/PARITY.md`
   carries a measured `certified / unsat` column; roughly 95 new `QF_RDL` unsats
   would have moved that number in the wrong direction, for a fragment whose
   certificates already existed and already verified.

CLAUDE.md is explicit that a logic fragment becomes public surface only after the
decision is recorded. This ADR records it.

## Decision

**Admit difference logic (`QF_IDL` / `QF_RDL`) as a decided fragment through
incremental negative-cycle detection, dispatched behind an exact structural gate
and a reserved probe budget; and export a CONJUNCTIVE difference-logic refutation
as the EXISTING `FarkasCertificate`, citing the query's verbatim relations, or
decline.**

### The procedure

A constraint `x_u - x_v ≤ w` is the graph edge `v → u` with weight `w`. A
conjunction of such constraints is satisfiable **iff** the graph has no
negative-weight cycle, and any feasible potential `π` *is* a model. `DlGraph`
maintains a feasible `π` at all times (Cotton–Maler): adding an edge whose
reduced cost `w + π[v] - π[u]` is already nonnegative is free, and otherwise a
Dijkstra-style propagation over reduced costs either reaches `v` with a negative
accumulated value — a negative cycle through the new edge — or terminates with a
correction that restores feasibility. The edge trail is append-only; `pop`
truncates it and deliberately does *not* restore potentials, because dropping
edges can only preserve feasibility. The theory implements
`cdclt.rs`'s `TheorySolver`, so the Boolean skeleton is the generic CDCL(T) spine.

### The fragment and the exact dispatch condition

`scan_dl` is the front gate and returns `None` — after which every route below
runs **byte-identically** — unless *all* of the following hold:

- every relational atom normalizes to `x - y ⋈ c` with coefficients **exactly
  ±1** (a single-variable bound `x ⋈ c` uses a distinguished zero vertex, pinned
  to `0`, so this is an exact encoding and not a relaxation);
- the query is **single-sorted** numeric — all `Int` or all `Real`, never mixed,
  never with a non-arithmetic sort present;
- there is no uninterpreted application, no product, no `div`/`mod`, and no
  numeric operator outside `+ - neg` and plain leaves; and
- every connective above the atoms is one the **skeleton encoder covers**
  (`not`, `and`, `or`, `implies`, `xor`, `ite`, plus the two equality gates
  below); and
- no arithmetic overflows while normalizing (the rational-denominator LCM is
  capped at `2^40` so scaled weights keep their `i128` headroom).

### Delta handling

Over the **reals** a strict `x - y < c` is the edge weight `(c·scale, -1)`: the
infinitesimal `δ` component makes the strict/non-strict boundary exact with no
epsilon guessing, and lexicographic `(c, d)` comparison is exactly the
`δ`-rational order. Over the **integers** the strict bound is instead *tightened*
to `x - y ≤ ⌈c⌉ - 1` (and `≤ c` to `≤ ⌊c⌋`). That tightening is where integer
difference logic gets its extra strength: `x - y < 1 ∧ y - x < 0` is
real-feasible and integer-infeasible.

### Equalities live in the SKELETON, not in the theory

A numeric `a = b` is expanded into the two difference atoms `a ≤ b` and `a ≥ b`
joined by a Tseitin `and` gate. Its *negation* is then the ordinary clause
`¬(a ≤ b) ∨ ¬(a ≥ b)`, which the CDCL search case-splits on — so the theory never
has to reason about a **disequality**, which is not a difference constraint at
all. A **Boolean** `p = q` gets an `XNOR` gate for the same reason: the skeleton
encoder has no equality case, and without the Boolean gate every query carrying
Boolean frame axioms fell out of the fragment — that is not hypothetical, it is
the entire `fischer` family.

### The probe budget is RESERVED

`dl_probe_budget` hands the probe at most the caller's timeout minus
`min(timeout / 4, 6 s)`. Without that reservation the probe **is not a probe — it
is a commitment**: it runs ahead of the whole linear-arithmetic chain, and a
query that is difference-shaped but hard for negative-cycle search would burn the
entire budget and hand the established routes zero milliseconds. Measured, not
hypothetical: `QF_IDL/sal/lpsat/lpsat-goal-18` is decided `unsat` by `lia-dpll`,
and an unreserved probe turned it into `unknown`. A fresh 2026-08-06 isolated
fallback needed 7.41 seconds, so the original six-second reserve was no longer
sufficient for that shape. Global 8- and 12-second reserves were rejected: the
12/12 candidate lost five of 171 current decisions. The accepted policy shortens
the maximum 18-second probe to 12 seconds only when scanning finds at least 128
numeric-equality gates and at most 1,024 difference atoms. The causal row is
906/350; compact gate-free controls are 489–1,011/0, and the large equality
control is 7,095/2,028. Every other query retains 18/6. The dispatcher stays
**strictly additive**, and the complete retained QF_IDL/QF_RDL decision set is
the acceptance gate.

**2026-08-06 deadline correction.** The initial implementation created the
probe deadline only *after* `scan_dl` and skeleton encoding. A 268,862-byte
QF_IDL query could therefore spend the reserved fallback slice in the unbounded
front end, then receive a fresh 18 seconds in CDCL(T). The retained run lost
`lpsat-goal-18`; three current-main and three exact-credited-revision reruns each
returned `unknown`, while an audit-only DL bypass restored `unsat` in 7.41
seconds. The deadline now starts at `try_check_qf_dl` entry and is polled through
the sort/DAG scan, linearization, equality collection, skeleton encoding, clause
materialization, and CDCL(T). The adaptive split and its end-to-end scope are
covered by focused regressions and the retained-decision A/B control.

### The evidence export, scoped honestly

`conjunctive_farkas_certificate` returns `Some` only when the query is a
**conjunction of difference literals** (`and`/`not`/`or`-under-negation over
atoms, plus a positively-asserted numeric equality contributing both of its
bounds), a negative cycle closes, and the rebuilt certificate passes the
independent `FarkasCertificate::verify`. It is emitted as
`Evidence::UnsatFarkas` — the same object `QF_LRA` already emits — from
`produce_evidence`, ahead of the route split.

A second, weaker tier exists because the measurement exposed a *decision* gap
under the certification gap: `evidence_route` sends a pure-real query to the
`PureReal` branch, whose lazy-SMT / Farkas engine is the only thing it tries — it
never reaches the auto dispatcher, so the difference-logic procedure was never
run there at all. On the committed 200-file `QF_RDL` parity list the evidence
front door decided **2** files where the solver front door decided **105**.
`dl_decided_report` therefore runs the procedure under the same reserved probe
budget and records its verdict — a replay-checked `sat`, or a correct
**bare** `unsat` for the Boolean-structured case. It is **size-gated** above
`PRE_SOLVE_ALETHE_MAX_NODES` so it can never displace a certificate the routes
below would have emitted on a small query; the conjunctive certificate path is
not gated, because it *is* a certificate. A correct-but-uncertified verdict
strictly dominates an `unknown`.

Two boundaries are deliberate:

- **Conjunctive only.** With Boolean structure the refutation is a *resolution*
  over many theory lemmas, which a single Farkas combination cannot express.
  Inventing a format for that is a separate decision; this one does not overreach
  into it.
- **Verbatim relations only.** The emitted `FarkasAtom`s are built from the
  **untightened** normalization, not from the graph's tightened edges, and the
  zero vertex is dropped from the coefficient list so a one-variable bound stays
  a one-variable atom. A refutation that genuinely *needs* the integer tightening
  therefore fails `verify` and is declined rather than shipped as a certificate
  describing a system the query never asserted.

## Evidence

### Soundness, `unsat` direction

A negative cycle is precisely a Farkas refutation with **unit multipliers**: a
simple cycle enters and leaves each vertex exactly once, so every variable
coefficient cancels and the constant sum is the cycle weight; the derived
relation is false exactly when that weight is negative, which is the detection
condition re-derived independently. `cycle_certificate` builds it and
`FarkasCertificate::verify` — exact-rational, overflow-checked, a pure function
of the atoms and multipliers — must accept it before the conflict can become a
lemma. A cycle that does not verify is **discarded**, which costs completeness
and never soundness. Dropping the zero-vertex column preserves cancellation
because a simple cycle passes through that vertex at most once.

For the query-level export the additional obligation is that the cited atoms are
really asserted. They are, by construction: each is a top-level conjunct at the
polarity it was asserted at, tagged with its `origins` index into the assertions
slice, and `verify` then proves that conjunction infeasible over the rationals.
Since the rational refutation holds a fortiori over the integers, the export is
sound in both modes.

### Soundness, `sat` direction

`sat` is never trusted from the search. The candidate model is read off the
vertex potentials, lifted to `Value::Int` / `Value::Real`, and **replayed through
the ground evaluator against the original assertions**; any non-replay is
`CheckResult::Unknown`. Anything not provably difference-shaped is refused up
front by `scan_dl`, and a budget-exhausted probe returns `unknown` and falls
through, so the dispatcher only ever *adds* decisions.

### Measured

- Parity, 200-file committed lists, 24 s wall, per-file, vs cvc5 1.3.4:
  `QF_RDL` 105/200 (68.6% of reference, up from 6.6%), `QF_IDL` 66/200 (53.7%,
  up from 41.5%), **0 disagreements** in both.
- Unit tests in `crates/axeyum-solver/src/dl_online/tests.rs` cover the negative
  cases that matter: a non-negative cycle is rejected as a certificate, a
  zero-weight cycle refutes only when a cited relation is strict, integer
  tightening is exact at negative bounds, a satisfiable system exports nothing, a
  disjunctive query declines the export, and — the honesty test — the
  tightening-dependent refutation `x - y < 1 ∧ y - x < 0` over `Int` is decided
  `unsat` while the export declines.

## Alternatives

### Leave `QF_IDL`/`QF_RDL` to the simplex / Fourier–Motzkin cores

Rejected by measurement: the generic cores' explanations are non-minimal on this
fragment, and a negative cycle is a minimal explanation by construction — it
names exactly the constraints that close the cycle and nothing else.

### Give the theory disequalities and drop the skeleton equality gates

Rejected. A disequality is not a difference constraint, so the theory would have
to case-split internally, duplicating the CDCL search it already sits under. The
Tseitin `and` / `XNOR` gates put the split where the search already handles it.

### A new evidence format for the CDCL(T) refutation

Deferred. The Boolean-structured refutation is a resolution over theory lemmas;
recording it needs a format decision (Alethe-style lemma + resolution, or an
in-tree object) plus a checker. Shipping the conjunctive case now moves the
measured `certified / unsat` column with zero new format surface.

### Run the probe on the caller's full budget

Rejected by measurement — see the reserved-budget section above.

## Consequences

Difference logic is now a public fragment with a ledger row, and a conjunctive
`QF_IDL`/`QF_RDL` `unsat` carries a certificate that `Evidence::check` re-runs
with the same independent exact-rational verifier `QF_LRA` uses. The route runs
ahead of the linear-arithmetic chain, so a regression in `scan_dl`'s conservatism
would be felt widely — its decline conditions are therefore the tested surface,
not an implementation detail.

What is *not* closed and gets revisited: the Boolean-structured (CDCL(T))
refutation is still a bare `unsat`; integer-tightening-dependent refutations
carry no certificate, and closing that needs an integer certificate shape (the
`Evidence::UnsatDiophantine` / `IntPrelude` ladder is the natural home); and
`recheck` for a Farkas certificate stays `na` at the text front door, exactly as
it does for `QF_LRA`, because verifying the algebra alone does not re-derive the
binding between the cited atoms and the query text.

## Backlinks

- Code: `crates/axeyum-solver/src/dl_online.rs`
  (`scan_dl`, `DlGraph`, `cycle_certificate`, `conjunctive_farkas_certificate`),
  `crates/axeyum-solver/src/auto.rs` (`dispatch_difference_logic`,
  `dl_probe_budget`), `crates/axeyum-solver/src/evidence.rs`
  (`dl_conjunctive_farkas_report`).
- Ledger: `crates/axeyum-solver/src/capabilities.rs`,
  `crates/axeyum-solver/src/support_matrix.rs`, rendered into
  [capability-matrix.md](../08-planning/capability-matrix.md) and
  [support-matrix.md](../08-planning/support-matrix.md).
- Result: `bench-results/PARITY.md` (`QF_RDL` 2026-08-03T20:24:24Z, `QF_IDL`
  2026-08-03T22:03:54Z).
- Related: [ADR-0015](adr-0015-linear-real-arithmetic.md) (the
  `FarkasCertificate` and its verifier), [ADR-0014](adr-0014-first-arithmetic-fragment.md)
  (integer arithmetic), [ADR-0002](adr-0002-ground-up-identity-oracle-bootstrap.md)
  (pure-Rust identity).
