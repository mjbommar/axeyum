# ADR-0465: The axiom ledger is derived from a measurement, not transcribed

Status: accepted
Index-summary: Supersedes ADR-0388's fixed 34-assumption disclosure: the integer prelude now costs **1**, the trusted total is **32**, and every published count is generated from a coverage-declaring measurement rather than authored
Index-status: accepted

Date: 2026-08-15

Supersedes:
[ADR-0388](adr-0388-retain-axiomatized-int-and-use-nat-deficits-for-rado.md).

Related: [ADR-0387](adr-0387-fallible-composable-lean-preludes.md),
[ADR-0456](adr-0456-real-is-an-ordered-ring-modelled-by-int.md),
[ADR-0042](adr-0042-integer-prelude.md).

## Context

ADR-0388 was accepted on 2026-08-13, when `build_int_prelude` admitted 34
axioms. It made that number a **publication rule**, and it binds:

> 1. Every result whose checked dependency closure touches `build_int_prelude`
>    states that it relies on 34 assumptions. "No axiom" and "zero axiom" are
>    prohibited for that closure even if all theorem-specific hypotheses and
>    proof terms are explicit.
> 2. The 34-row integer population remains in the generated axiom ledger and is
>    linked to this decision. R2 does not discharge or reclassify a row.

Both clauses are now false statements about this repository, in the direction
that understates it. Two lanes constructed ℤ over the proved ℕ development
rather than assuming it — `Int` became an inductive over `Nat`, its operations
became checked definitions, and its laws became theorems with empty axiom
footprints. `integer` went **34 → 6** (`229cceb1e`, 2026-08-14) and then
**6 → 1** (`0fc7cc357`, 2026-08-15). ADR-0388 did not forbid this; its clause 2
scoped the R2/Rado lane, and its rejected alternative was *quotient*-constructed
ℤ with `Quot.sound`, which is not the route taken. But its numeric disclosure
rule was written as a constant, and constants do not follow the code.

So for two days the published ledger required every dependent claim to disclose
34 assumptions where the kernel admits one, and the generated ledger advertised
a 65-row trusted base against an actual 32. `prelude_axiom_inventory` — the
ledger's own source command — had been exiting **101** on committed `HEAD` for
the same reason, asserting 34 in Rust; nothing noticed, because nothing checked
its exit status.

The count went stale precisely because it had been **transcribed**: into a
Python constant, two row-count assertions, a trust-policy literal, the rendered
prose, a unit test, a Rust `assert_eq!`, and ten documents. Updating those
by hand fixes today's number and reproduces the mechanism that broke it.

## Decision

**Supersede ADR-0388. Every count this project publishes about the trusted
prelude surface is derived from a runtime measurement that declares its own
coverage, and is gated by `--check`; no count is authored anywhere.**

1. **The disclosure rule is generated, not written.** The ledger's
   `trust_policy.publication_rule` is composed by
   `scripts/gen-lean-axiom-ledger.py` from the measured integer population and
   names the assumptions individually while there are few enough to name.
   Today it reads: *any checked dependency closure using the integer prelude
   must disclose 1 assumption (`Int.euclidean_decomposition`); credited Rado
   rigidity uses the zero-axiom Nat prefix-deficit encoding instead.* The
   substance of ADR-0388 clause 1 survives — a closure over `int_prelude` may
   not be called "zero axiom" — but the number in it moves with the kernel.
2. **ADR-0388's Nat-only boundary for credited Rado rigidity is retained
   unchanged.** One remaining assumption is still not zero, and the prefix-
   deficit encoding of §4–§5 of ADR-0388 remains the encoding for `thm:rigid`.
   That part of ADR-0388 is re-accepted here verbatim rather than reopened.
3. **Coverage is declared by the measurement.** The ledger consumes two
   enumerations. `prelude_axiom_inventory` gives the rows (name + canonical
   type, SHA-256 bound). `nat_axiom_inventory` gives the whole *trusted
   surface* (`axiom` + `opaque` + `quotient`, because `Opaque` has no proof
   body and `Quotient` admits `Quot.sound`) for **five** preludes and prints a
   per-prelude count line for each — including the axiom-free ones. An
   axiom-free prelude emits no rows, so absence and zero are otherwise
   indistinguishable; the coverage lines are the tool stating what it looked
   at. The manifest records the prelude set, so a prelude dropping out of the
   measurement fails the gate instead of shrinking the total.
4. **The two enumerations are cross-checked against each other.** Per-prelude
   axiom counts, name sets, and canonical types must agree byte-for-byte, so a
   filter bug in either — `Declaration::Axiom` alone versus the full trusted
   surface — surfaces as a disagreement, not as a smaller number.
5. **A population change is an explicit act with a paper trail.** `--check`
   fails when rows are added or removed. Clearing it requires
   `--accept-population-change --retired-on … --retirement-note …
   --retirement-evidence …`, which files departed rows in `retired_entries`
   with a date, a reason, and existing repository evidence. Retired rows are
   **never deleted**: a reduction in the trusted base is the result, and a
   ledger that shrinks silently publishes a smaller table instead of a
   discharge.
6. **Documents that cite the counts are scanned.** The manifest lists
   `live_documents`; each is checked against a closed family of anchored count
   phrasings, and each must yield at least one match. A stale count fails the
   gate — and so does a document that quietly stops citing the ledger, which
   would otherwise be the cheapest way to pass.
7. **`assert_eq!` on a count is removed from the Rust inventory examples'
   emit path.** An example that panics on drift is not a gate (nothing runs it
   for its status) and is an outage when the number improves. Expectations are
   opt-in flags — `--expect-axioms PRELUDE=N`, `--require-axiom-free PRELUDE`,
   `--expect-count N` — which fail when the named prelude was never enumerated.

## Evidence

All figures below were re-measured on 2026-08-15 before this ADR was written;
none is copied from another document.

### The trusted surface

`cargo run -p axeyum-lean-kernel --example nat_axiom_inventory` (stderr):

| prelude | axiom | opaque | quotient | trusted total |
|---|---|---|---|---|
| `logic` | 0 | 0 | 0 | **0** |
| `nat` | 0 | 0 | 0 | **0** |
| `real` | 30 | 0 | 0 | **30** |
| `integer` | 1 | 0 | 0 | **1** |
| `string` | 1 | 0 | 0 | **1** |

`prelude_axiom_inventory` independently emits 32 rows — real 30, integer 1
(`Int.euclidean_decomposition`), string 1 (`axeyum.string.2.append`) — with
matching names and canonical types. **The trusted total is 32, not 65.**

`real: 30` is asserted **by design**: ADR-0456 established that the `Real`
package is an ordered commutative ring with 1, modelled by the constructed ℤ
with empty footprints, and that constructing ℝ is deferred with a price tag. A
blanket "axiom-free" claim would be wrong; expectations are therefore
per-prelude.

### The reduction being published

- `int_theorem_inventory`: **51 derived, 51 with an EMPTY `axiom_footprint`,
  1 still asserted**.
- 33 integer rows retired: **8 constructed** (`Int`, `Int.add`, `Int.le`,
  `Int.lt`, `Int.mul`, `Int.neg`, `Int.one`, `Int.zero` — the carrier and the
  operations, now an inductive and checked definitions) and **25 proved**
  (every ring/order law ADR-0042 assumed, including `Int.no_int_between`
  discreteness and ADR-0106's `Int.eq_em`). Classified by membership in the
  current theorem inventory, not by hand.
- Control: `nat_theorem_inventory` still reports **119** theorems;
  `--expect-count 119` exits 0 and `--expect-count 120` exits 1.

### The gate fires (negative controls, each exercised)

| Control | Expected | Observed |
|---|---|---|
| `nat_axiom_inventory --expect-axioms integer=34` | fail | exit 1 |
| `nat_axiom_inventory --require-axiom-free integer` | fail | exit 1 |
| `nat_axiom_inventory --expect-axioms bogus=1` (never enumerated) | fail | exit 1 |
| ledger `--check` with a hand-edited count in the derived block | fail | exit 1 |
| ledger `--check` with a row the kernel no longer admits | fail | exit 1 |
| ledger `--check` with a stale count in a `live_documents` file | fail | exit 1 |
| ledger `--check` with a `live_documents` file that cites no count | fail | exit 1 |
| ledger `--check` with a prelude dropped from the coverage lines | fail | exit 1 |
| the two enumerations disagreeing on a canonical type | fail | exit 1 |

The last five are unit tests in `scripts/tests/test_lean_axiom_ledger.py`,
which mutates a captured measurement rather than the kernel, so the controls
run without a Cargo build.

## Alternatives

### Update the ten documents and the constant, and move on

Rejected. It is the easy half and buys nothing durable — the number went stale
because it lived in a dozen places, and this restores exactly that arrangement
with fresher digits. The next reduction (ℤ's last assumption, or a `Real` row)
would break it again, silently, in the same direction.

### Keep ADR-0388 and merely correct its number

Rejected. A decision record is a dated artifact; editing 34 to 1 inside it
would falsify the record of what was decided when 34 was true, and would leave
the next reader unable to see that the reduction happened. ADR-0388 keeps its
numbers and gains a supersession pointer.

### Assert the counts in the Rust examples

Rejected as the *primary* mechanism, and removed from the emit path. That is
what `prelude_axiom_inventory` did; it converts an improvement into an
`exit 101` in a tool nobody checks the status of, and it puts the expectation
in a file the ledger does not read. Expectations belong on opt-in flags that
fail on absence, consumed by a gate.

### Ban counts from prose and require every document to link the ledger

Rejected. It is enforceable, but a roadmap that cannot state its own headline
number is worse documentation, and the failure mode it prevents is already
covered by scanning declared citations with a liveness requirement.

## Consequences

The published trusted base falls from 65 to 32 and is now correct rather than
conservative. Anything that disclosed "34 assumptions" for an `int_prelude`
closure was over-disclosing and may be restated as 1; anything that disclosed
"zero axiom" for such a closure is still wrong.

`scripts/gen-lean-axiom-ledger.py --check` becomes the single place a count
can go stale, and it is already wired into `./scripts/check.sh` and
`just check`. The cost is that a genuine prelude change now needs a deliberate
`--accept-population-change` run with a note and evidence — which is the point.

The scan's limit is stated in the generated ledger and repeated here: it gates
the *anchored* phrasings in `COUNT_CLAIM_PATTERNS` inside declared documents.
Unanchored prose numbers elsewhere are not gated. Historical records — dated
plan results, diaries, superseded ADRs — are deliberately excluded and keep
the numbers that were true when they were written.

This does not classify or discharge the remaining 32 rows, does not construct
ℝ, and does not discharge `Int.euclidean_decomposition`. Those remain open.
