# ADR-0805: The module-baseline receipt is a hash and a parser, not a vendored checkout

Status: accepted
Date: 2026-08-30
Index-summary: G0's receipt (`artifacts/module-baseline/receipt.json`) pins
Mathlib module-import identity by content hash and a self-hashed parser
rather than by vendoring a checkout. Verified against the pinned mathlib4
tree: 8,094 modules, 25,495 internal edges, 1,476 no-importer sinks --
matching the roadmap's evidence baseline exactly. Two independent runs
produce byte-identical JSON; source drift and parser drift each fail
independently, mutation-verified nine ways.

Phase: G0 of the graph-directed library roadmap (ADR-0717)
Lane: `l1-g0-module-baseline`

## Context

[docs/plan/graph-directed-library-roadmap-2026-08-30.md](../../plan/graph-directed-library-roadmap-2026-08-30.md)
phase G0 asks for a compact, reproducible receipt of the Mathlib module-import
graph, without vendoring a Mathlib checkout into this repository. Every later
phase (G1's declaration graph, G2's join to Axeyum state, G3's frontier
queues) computes downstream of this baseline, so if the baseline cannot be
independently reproduced, nothing built on top of it is falsifiable either.

The roadmap's own evidence baseline (8,094 modules, 25,495 internal
direct-import edges, 1,476 no-importer sinks, specific hub degrees) was
measured once, by hand, on server5. This phase turns that one-off measurement
into a receipt any host can reproduce and any drift a gate can catch.

## Decision

1. **Read a checkout, never commit one.** The receipt generator
   (`scripts/gen-module-baseline.py` / `scripts/lib/module_baseline.py`) reads
   whatever mathlib4 directory it is pointed at (default: the pinned checkout
   `scripts/provision-lean-import-toolchain.sh` provisions at
   `/data0/axeyum/lean-import-toolchain/mathlib4`) and writes nothing there.
   Nothing under `Mathlib/` is ever added to this repository's tree.

2. **Two independent identity signals, checked separately.** The receipt
   records a git commit hash (a label) AND a content tree hash -- sha256 of
   every `Mathlib/**/*.lean` file's own sha256, sorted by path -- so a
   checkout that was locally modified without updating its claimed commit is
   still caught. The parser is hashed too (sha256 of
   `scripts/lib/module_baseline.py`). `scripts/check-module-baseline.py`
   diagnoses SOURCE_DRIFT and PARSER_DRIFT as independently-firing failure
   reasons: changing the source without changing the parser fires only the
   former; a behaviour-preserving parser edit (same logic, different bytes)
   fires only the latter. Verified in
   `scripts/tests/test-module-baseline.py`'s `source_drift_detected_
   independently` / `parser_drift_detected_independently` tests, run against
   real subprocess invocations of the checker, not simulated.

3. **The checker re-derives reproducibility on every run, not just once by
   hand.** `check-module-baseline.py` parses the source TWICE per invocation
   and requires byte-identical JSON before comparing either run against the
   committed receipt; a NONDETERMINISM failure is distinct from a drift
   failure. This is "two runs reproduce the receipt" as a standing gate
   property rather than a one-time claim in a commit message.

4. **Absence fails loudly.** Three fail-closed cases, each independently
   mutation-verified: the source directory does not exist, it exists but has
   no `Mathlib/` subdirectory, and the `Mathlib/` subdirectory exists but
   contains zero `.lean` files. All three raise before any receipt is
   written, matching CLAUDE.md's standing rule that a run which finds nothing
   must never look like a clean baseline.

5. **Comment- and string-literal-aware parsing.** A naive line-anchored
   `grep '^import '` over Mathlib's `.lean` files counts doc-comment
   illustrations of import syntax as real edges --
   `Mathlib/Tactic/MinImports.lean` literally contains lines reading
   `import A` / `import B` inside a `/-! -/` block, purely as documentation.
   The parser strips nested block comments, line comments, and string
   literals before matching, which is what makes the measured totals agree
   with the roadmap's hand-measured baseline (see Evidence below) rather than
   over-counting by a small but real amount.

6. **The receipt is compact by construction.** It carries: source kind,
   commit, content tree hash, file count; parser path and sha256; module
   count, internal/external edge totals, no-importer sink count; the top 15
   modules by indegree and top 10 by outdegree. It does not carry the graph
   itself -- that is G1's job, over `artifacts/library-artifact/` (a sibling
   lane's contract, not this one's).

## Evidence

Run against the pinned mathlib4 checkout (commit `c5ea00351c28e24afc9f0f84
379aa41082b1188f`) at `/data0/axeyum/lean-import-toolchain/mathlib4`,
provisioned via `scripts/provision-lean-import-toolchain.sh --verify`
(network-free, already verified present on this host):

```
modules=8094  internal_edges=25495  external_edges=607  no_importer_sinks=1476
top indegree: Mathlib.Init 193, Mathlib.Tactic.Common 69,
  Mathlib.Algebra.Ring.Defs 43, Mathlib.Algebra.BigOperators.Group.Finset.Basic 41,
  Mathlib.Util.CompileInductive 41, Mathlib.Algebra.Field.Defs 38,
  Mathlib.Algebra.Group.Basic 38, Mathlib.Algebra.Order.Group.Nat 38,
  Mathlib.Algebra.Polynomial.AlgebraMap 32
top outdegree: Mathlib.Tactic 336 (aggregator), Mathlib.Tactic.Common 85
```

This matches every specific figure the roadmap's Evidence baseline section
names: 8,094 modules; 25,495 internal edges; 1,476 no-importer sinks;
`Mathlib.Init` 193 importers; `Mathlib.Tactic.Common` 69; `Mathlib.Algebra.
Ring.Defs` 43; finite big-operator basics 41; field/group/order definitions
38 each; polynomial algebra maps 32; `Mathlib.Tactic` the largest
direct-import aggregator at 336. This is the whole parse over all 8,094
files, not a bounded subset -- it runs in roughly 7-9 seconds per invocation,
well inside the check's step budget, so there was no need to reduce scope.

Two consecutive runs of `scripts/gen-module-baseline.py` produced
byte-identical JSON (`diff` empty). All nine mutation-tested guards (comment/
string-literal decoy stripping, internal/external edge classification, sink
counting, the lexicographic tie-break on equal-degree modules, the three
absence cases, and the two drift-detection conditions) each kill exactly one
test in `scripts/tests/test-module-baseline.py` when deleted in a scratch
copy (`scripts/tests/test-module-baseline-mutations.sh`), never zero, never
more than one.

## What the receipt does not pin

The receipt is silent on WHICH declarations live inside each module, their
types, their proof terms, or any cross-module dependency finer than "this
file imports that file". Two Mathlib checkouts with identical import
structure but arbitrarily different theorem content would produce the same
receipt. That finer join is G1's declaration graph and G2's join to Axeyum
state, explicitly out of scope here.

## Alternatives

**Vendor a frozen Mathlib snapshot into this repository.** Rejected per the
roadmap's explicit instruction and ADR-0717's decision to keep Mathlib a
pinned external reference, not a dependency this repository ships; a
committed copy is exactly the drift the receipt exists to detect, and it
would also commit ~110 MB of someone else's source tree.

**Trust the git commit hash alone as source identity.** Rejected: a commit
hash says what SHOULD be checked out, not what IS on disk. The content tree
hash is the check that does not require trusting `git` at all, which also
lets test fixtures (plain directories, not real git repos) exercise the same
code path via `--commit` override.

## Consequences

G1 (build the declaration graph) can treat this receipt's module set and
edge counts as a checked precondition rather than re-deriving them. Any
future change to the pinned Mathlib commit, or to the parser's definition of
"an import", must be accompanied by a receipt regeneration or
`check-module-baseline.py` fails the gate by design.
