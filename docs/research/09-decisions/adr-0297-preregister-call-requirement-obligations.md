# ADR-0297: Preregister explicit scalar call-requirement obligations

Status: accepted
Date: 2026-07-20

## Context

[ADR-0296](adr-0296-preregister-verified-scalar-contract-composition.md)
accepts the first body-verified scalar contract and then discards the callee
body before caller reflection. Its requirement is deliberately restricted to
`true`. Conjoining an arbitrary `requires` predicate to the transition would
otherwise erase precisely the executions on which the caller violates the
callee contract, allowing an unsafe caller to appear safe.

[P5.2](../../plan/track-5-verified-systems/P5.2-contracts-modular.md) requires
violated contracts to produce replayed witnesses. The existing LLVM loop bridge
already has the right semantic destination: a `TransitionSystem` exposes a
replay-checked `bad` predicate, and the natural-loop reflector already computes
the exact selected-edge prefix for every admitted header-to-latch path. The
next step is therefore a composition rule, not annotation syntax or a new
executor.

The exact Glaurung PAC `leaf(i32) -> i32` cell remains the smallest measured
case with a body-verified contract, an inlined baseline, nontrivial poison
conditions, and two real callers. This work supports the reviewer-facing
correctness spine: strict sorts, precise failures, explicit `Unknown`, and no
dropped executions. It is not a replacement performance claim or a new
Glaurung finding-parity result.

## Decision

Preregister one opt-in call-requirement obligation experiment over the existing
verified scalar-contract resolver before admitting nontrivial requirements in
production reflection.

For a verified-contract call site `j` in pre-state `s`, define:

```text
violation_j(s) = prefix_j(s) and args_defined_j(s) and not requires_j(s)
bad(s)         = existing_property_bad(s) or OR_j violation_j(s)
```

The experiment may implement that rule only under all of these boundaries:

1. Contract verification continues to check every expression and sort without
   coercion. It may admit a nontrivial Boolean `requires`, but each body/contract
   immediate-definedness, result-definedness, and result-value equality is then
   proved under that requirement. A counterexample, `Unknown`, timeout, sort
   mismatch, or solver error remains a distinct fail-closed result.
2. `prefix_j` contains exactly the checked immediate-definedness and selected
   branch-edge predicates that must hold *strictly before* the call is reached.
   A call on an untaken natural-loop path cannot fail. A later branch condition,
   later undefined operation, or later call cannot erase an already reached
   requirement violation.
3. The transition relation assumes `args_defined_j and requires_j` before using
   the verified summary and retains the existing callee immediate/result
   definedness. This restriction is sound only because the rejected complement
   is simultaneously visible through `bad`; there is no silent pruning route.
4. Argument undefinedness remains the existing LLVM `noundef`/poison boundary,
   not a contract-requirement witness. The evidence bundle must classify it
   separately rather than count it as agreement, safety, or a precondition
   failure.
5. Every verified call site retains deterministic callee and source-span
   metadata. A replayed bad state can therefore be attributed to a specific
   requirement rather than appearing as an anonymous combined property.
6. The unchanged default reflector and ADR-0295 direct-body route acquire no
   implicit contract or obligation. `puts`, indirect/nested calls, recursion,
   memory, pointers, variadics, external effects, and unsupported attributes
   continue to fail exactly where they do now.
7. Version one still uses the exact functional scalar result; it does not add
   havoc, existential results, relational `ensures`, Rust attributes, MIR call
   terminators, panic contracts, or a revised Glaurung semantic census. Those
   require later separately frozen composition rules.

This is the second bounded T5.2.2/T5.2.4 slice. The selected requirement is an
experiment in sound call-site accounting, not a recommended user annotation.

## Frozen evidence gates

Implementation is admitted only if one committed evidence bundle passes all of
the following without weakening after result observation:

1. Revalidate ADR-0295/0296's exact Glaurung source, compiler command,
   source/module/function hashes, and live-source provenance before the selected
   tests. The resolver must still discard the verified callee body.
2. Use the existing bounded contract AST to state the nontrivial `leaf`
   requirement `not bv_uaddo(x, 0xffff_ffff)`, which is true exactly at `x = 0`.
   Under it the contract states immediate/result definedness as `true` and the
   exact result as `x*x+1`. Independently check at least one satisfying input and
   one violating input; do not add LLVM or annotation syntax for this row.
3. Verify the contract against the body under `requires`. A mutation inside the
   admitted domain must be disproved. A mutation only outside the domain may be
   accepted only when an independent implication check proves it irrelevant;
   vacuous or malformed evidence is not counted as agreement.
4. With the ordinary unsigned-PHI property made identically false, replay-checked
   BMC must find the `compute` and `main` call-requirement violation at the
   shallowest expected step. Attribute the witness to `@leaf` and its exact
   source span, and replay a defined `n >= 2` source execution that reaches the
   violating `leaf(1)` call.
5. Independently build the expected obligation and transition formulas. Prove
   modular/inlined transition agreement under `requires`; compare at least
   100,000 deterministic tuples with every row classified as valid agreement,
   explicit requirement violation, or source undefined. Require zero semantic
   disagreements and zero dropped/unclassified rows.
6. A synthetic checked single-latch natural loop must place the contracted call
   on only one internal path. Concrete and term-level checks must show no
   violation on the untaken path, a violation on the taken path, and no false
   suppression by conditions that occur after the call.
7. Mutation/negative tests cover omission of the requirement from `bad`, omission
   of the requirement from `trans`, inverted path polarity, a non-Boolean
   requirement, missing/duplicate contracts, signature drift, and an explicit
   zero-resource verification `Unknown`. Every source-backed failure keeps its
   stable class and location.
8. Report gate counts and construction cost only as mechanism observations.
   The standing reflection-semantics gate, complete `axeyum-verify` tests and
   doctests, strict all-target/all-feature Clippy, warning-denied rustdoc,
   formatting, documentation links, and live Glaurung provenance must pass
   under a bounded-memory runner.

## Rejected alternatives

- **Conjoin `requires` only to `trans`:** unsound because it deletes caller bugs.
- **Treat `not requires` as LLVM poison:** loses the contract boundary and can
  again disappear through transition feasibility.
- **Check every requirement on every path:** produces false alarms for untaken
  natural-loop calls.
- **Add `#[requires]` syntax now:** expands the surface before the composition
  rule has a replayed witness.
- **Introduce relational havoc together with requirements:** combines two
  independent trust boundaries and removes the exact ADR-0295 differential.

## Consequences

If the frozen gates pass, verified scalar calls can carry nontrivial
preconditions without hiding their violations. The result will close the
call-site-obligation prerequisite only; P5.2 will still require relational
results, the checksum module, MIR parity, panic propagation, and annotations.

If any formula, path-prefix, replay, mutation, resource, or zero-dropped-row gate
fails, reject the implementation and retain ADR-0296's universally true
requirement boundary.

## Observed result and acceptance

The frozen experiment passes without widening LLVM syntax or weakening an
error boundary:

- `VerifiedContractResolver` now rejects unsatisfiable requirements, proves
  each contract/body component under a satisfiable nontrivial requirement, and
  keeps counterexample/`Unknown`/solver failures distinct. The selected
  `leaf(0)` contract verifies with immediate/result definedness stated as
  `true`; an `x*x+2` in-domain mutation is disproved, while the independently
  checked `x*x+1+x` outside-domain-only mutation is accepted.
- Contract call lowering returns separate satisfied and violated requirement
  terms. The transition assumes the former; `CanonicalLoopSystem::bad` ORs the
  latter under only the already executed instruction/selected-edge prefix.
  Literal-`true` ADR-0296 contracts bypass this machinery and retain their
  prior exact formulas.
- Both PAC callers retain one exact `@leaf` source span. Replay-checked BMC
  reaches the violation at depth 1 with loop index 1, and the independent
  defined source execution at `n = 2` reaches the same `leaf(1)` call.
- Independent formulas prove `bad == bv_uaddo(i, UINT_MAX)` and
  `restricted_trans == inlined_trans and requires`. The stratified 100,000-row
  gate reports 33,334 valid-domain rows, 33,334 defined requirement violations,
  33,332 source-undefined rows, 16,666 omission controls where the inlined
  transition would continue, zero disagreements, and zero dropped rows.
- A two-path checked natural loop proves that the untaken call does not fail,
  the taken invalid call does fail, and a later division-by-zero condition does
  not suppress the earlier requirement violation.
- The focused binary passes 17/17 tests at a 487.7 MiB peak. The standing gate
  passes 63 variants / 15 groups / nine binaries / 98 tests plus ten checker
  mutations at a 1.9 GiB peak. The complete all-feature `axeyum-verify` suite
  and doctests pass under a 4 GiB hard cap (28.1 MiB swap, no OOM).

This accepts explicit nontrivial scalar call requirements as replayable
obligations. It does not accept relational result havoc, annotation syntax,
MIR calls, external effects, recursion, memory contracts, or a performance
claim. The next P5.2 experiment must freeze a relational scalar result rule on
the checksum module before broadening syntax.
