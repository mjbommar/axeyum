# The first general producer: one operation, three theorems, no per-target code

Date: 2026-08-22

Plan: [`226`](226-production-measurement-and-general-producer-plan.md) P3/P4
Predecessor: [`229`](229-nat-descfactorial-one-reflexivity-decline.md) — the
decline that named this capability.

## The result

`bounded_induction_support` is a target-agnostic producer: `Eq.refl`, and where
that is stuck, a bounded structural induction over a discovered zero/succ binder
plus one congruence rewrite driven by the induction hypothesis. Measured over the
nine frozen goals that reach the kernel:

| Outcome | Goal |
|---|---|
| **proved** | `∀ (n : ℕ), n.descFactorial 1 = n` — **new; bare reflexivity could not** |
| **proved** | `∀ (n : ℕ), n.ascFactorial 0 = 1` |
| **proved** | `∀ (n : ℕ), n.descFactorial 0 = 1` |
| **declined** | `∀ (n : ℕ), n.factorial = 0` — **FALSE. The negative control.** |
| declined | `n < k → n.descFactorial k = 0` (strong induction relating two binders) |
| declined | `n.descFactorial n = n.factorial` (diagonal recursion) |
| declined | `Nat.ascFactorial 1 k = k.factorial` |
| declined | `Nat.ascFactorial 0 k.succ = 0` |
| declined | `Nat.fib (n+2) = fib n + fib (n+1)` |

**Three theorems from one producer.** That is the first generality this project
has measured; every operation in the registry before today named exactly one
fact.

## Why it is general, checked rather than asserted

The claim "target-agnostic" is exactly the claim a capsule would also make, so it
was verified against the source, not the description:

- **zero hardcoded type names.** The zero/succ shape is discovered from
  `Kernel::environment()` — a constructor with `num_fields: 0`, and one with
  `num_fields: 1` whose field type and result type are both the family. It works
  identically whether the kernel calls the type `Nat`, `AxNat`, or anything else
  with that shape, and the imported kernel does call it `AxNat`.
- **zero fact ids or theorem names in code.** The seven occurrences of
  `descFactorial`/`ascFactorial` in the file are all inside `//!` doc comments
  recording measured reach.
- **no pre-existing `congrArg`.** An isolated statement-import kernel keeps only
  Definitions and Inductives, so the producer builds the congruence directly from
  the kernel's generated `Eq.rec`.
- every budget is a named constant (`MAX_BINDERS = 8`, `MAX_INDUCTIONS = 2`) and
  exhausting one is a typed decline, never a hang.

Reproduced here independently of the agent that wrote it. The proved goal's
`goal_sha256` is `29d67ba6…`, byte-identical to the value the frozen 2026-08-19
census recorded for that row — the same goal, now closed:

```text
BOUNDED_INDUCTION_OK|target=…r068|goal_sha256=29d67ba6…|proof_sha256=17701004…
GOAL|((n : AxNat) -> Eq.{1} AxNat (AxNat.descFactorial n (OfNat.ofNat …1…)) n)
PROOF|fun (n : AxNat) => AxNat.rec.{0} … (Eq.refl.{1} …) (fun x1 x2 => Eq.rec.{0,1} …) n
```

The false mutation declines with a typed reason, and the tool errors on a
nonexistent input path rather than answering — both checked, because a producer
that cannot fail is worth nothing and a tool that ignores its argument
[has already cost a day here](231-weak-model-flywheel-experiment.md).

## What is NOT claimed

**No fact was flipped to `proved` and no operation was registered here.** Formal
admission needs an authoritative statement-adapter manifest re-exported through a
pinned Lean 4.30 / Mathlib toolchain, and the streams used above are marked
`diagnostic-no-ledger-credit` in their own manifest. Registering without that
would be fabricating provenance.

**Correction, same day.** This section originally said no `lean` or `lake` binary
existed on this host. That was wrong, and wrong in the way this repository warns
about: `command -v lean` is empty because `elan` keeps toolchains off `PATH`.
Lean 4.30.0 at the pinned commit `d024af09` is installed here, and s5 carries the
Mathlib and `lean4export` checkouts at exactly the commits the adapter manifests
pin. The admission chain is reachable; it simply had not been walked. See the
`command -v lean` entry in `CLAUDE.md`.

So the ledger still reads `via_multi_target=0`. **The producer is real and the
credit is not yet earned**, and those are different sentences.

## A hole this closed in the metric itself

Holding a genuine three-fact producer with no authoritative path to register it
is exactly the situation in which one edits the JSON. `gen-production-provenance-ledger.py`
counted every operation regardless of `scope`, so the headline generality number
could have been moved by registering a `counterfactual-fixture-only` operation
naming three facts — no producer, no receipt, no kernel.

A metric its own author can move by hand is the checker-that-cannot-fail defect
wearing the other hat. The headline now counts **authoritative** operations only,
fixture-scope coverage is reported beside it rather than folded in, and a control
pins both directions.

## Next

The four remaining declines are honest and name their own successors: strong
induction relating two binders, diagonal recursion, and a step-case bridge that
is not a single congruence. None needs per-target code.

The larger lever is still elsewhere: `adapter-rejection` is 114 of 138
([`230`](230-producer-decline-shape-census.md)), so 83% of the population never
reaches a producer at all.
