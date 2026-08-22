# Exact `Int.gcd_fib` construction plan

`Int.fib_neg` closed the last explicit dependency of `Int.gcd_fib`, and the
authoritative frontier now selects the latter. This plan freezes the first
bounded construction before any new source is compiled or proof-bearing stream
is read. It does not consult or transport Mathlib's proof of the target.

The useful intermediate statement is

```lean
∀ (m : ℤ), (Int.fib m).natAbs = Nat.fib m.natAbs
```

Call its final target-owned form
`Axeyum.Autogenesis.intFibNatAbsV1`. Mathematically it says that the sign
extension used by integer Fibonacci disappears when `natAbs` is taken. The
positive constructor is definitional. The negative constructor must be reduced
through the already admitted exact `Int.fib_neg` theorem and independently
checked `natAbs` transport; an assumption-bearing simplifier is a decline
rather than a usable result.

The V1 plan named that final bridge directly. Before execution, closure analysis
showed why that is one boundary too coarse: Lean source that directly names the
official `Int.fib_neg` would inherit its rejected source proof closure before
Axeyum could substitute the admitted clean theorem. V2 therefore exports
`intFibNatAbsResidualV1` with `fib_neg` and `natAbs_neg` as explicit theorem
parameters, requires that residual to be dependency-free, and only then
specializes it against the exact admitted capsule and a separately checked
clean `Int.natAbs_neg` root.

Once that bridge is clean, the final composition is short:

```text
gcd (fib m) (fib n)
  = gcd (natAbs (fib m)) (natAbs (fib n))       by the exact Int.gcd equation
  = gcd (Nat.fib (natAbs m)) (Nat.fib (natAbs n))
  = Nat.fib (gcd (natAbs m) (natAbs n))         by admitted Nat.fib_gcd
  = Nat.fib (Int.gcd m n)                       by the exact Int.gcd equation
```

The machine-readable authority is
[`mathlib-int-gcd-fib-construction-plan-v1.json`](../../artifacts/autogenesis/mathlib-int-gcd-fib-construction-plan-v1.json).
Its checker verifies that both prerequisite facts are currently proved, their
sealed capsules still have their exact bytes, the target remains open, and the
first execution has no target-submission or ledger-write authority.

```sh
python3 scripts/check-autogenesis-int-gcd-fib-construction-plan.py
python3 scripts/check-autogenesis-int-gcd-fib-construction-plan-v2.py
```

On a clean bridge result, the next increment will preregister the exact
four-part target composition before constructing `Int.gcd_fib`. On a nonempty
footprint, the measured dependency carrier becomes the next bottom-up leaf.

## V2 result

The residual source compiled once and exported twice as the same 9,846,065-byte
stream (`5ae684d7...67152`). The independent checker accepted the stream, but
the root retained eight assumptions, so specialization was not attempted and
the target received no credit. All five direct theorem dependencies were
individually empty-footprint. The contamination therefore lies in a
non-theorem declaration retained by source-level reduction or case analysis;
the next bounded step is a non-rendering path audit to identify that carrier.
V3 freezes that single read over the eight exact blockers and forbids rendering
proof terms, theorem types or definition bodies.

V3 produced no durable output through the execution channel and therefore gets
zero diagnostic credit. V4 retains the same non-rendering audit but limits its
output to five nearest carriers per blocker, making the evidence small enough
to preserve before another proof-bearing read.

V4 completed after more than a minute with healthy memory but again left no
durable report. Before another read, the shared blocker-path auditor will cache
candidate closures across blockers and gain a fail-if-present explicit output
path. Four controls retain the legacy interface, prove durable creation and
overwrite refusal, and count closure computations under shared carriers.

That repair is now implemented. Candidate closures are computed once and
reused across all blockers; `--output` creates and syncs one new JSON file and
refuses an existing path before reading the proof stream. Three focused tests
cover legacy arguments, parseable fail-if-present output, and shared-carrier
cache reuse; focused Clippy passes with warnings denied.

The repaired V5 audit is durable and decisive. Every one of the eight blockers
shares the same top-level source path: official `Int.fib`, through
`Int.instDecidablePredEven` and its proof. The residual was not contaminated by
its five direct equality helpers; it accidentally retained the broad official
function definition. V6 therefore abstracts both Fibonacci functions and uses
only explicit positive, negative-even, negative-odd, modulo-case, and `natAbs`
contracts. It contains no proposition-level `Even` conditional at all.

The single V6 compile stopped before export on three residual goals: each
universal `natAbs` rewrite consumed its first occurrence and left the second
under `natFib`. V7 changes only those rewrite lists. It does not reintroduce
`Int.fib`, Even decisions, automation, specialization, or ledger authority.
