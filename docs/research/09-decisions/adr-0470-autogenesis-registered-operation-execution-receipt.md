# ADR-0470: Autogenesis registered-operation execution receipts

Status: accepted
Date: 2026-08-18
Index-summary: Typed authoritative execution binds clean commit, frontier, registry, fact, source bytes, budget, and normalized checked result

## Context

The authoritative fact frontier can now select exactly one open fact because a
matching producer/checker operation exists. Selection alone does not execute
anything, and the v1 registry previously named Rust producer and checker source
files without specifying a runnable driver, input artifact, budget, or expected
observable result. An orchestrator would therefore have had to rediscover those
values from prose or accept caller-authored shell, recreating the manual trust
boundary Autogenesis is intended to remove.

ADR-0468 fixes the later prepared-proposal and durable-admission boundary.
ADR-0469 fixes the mathematical certificate accepted for the first real route.
This decision fixes the missing boundary between machine selection and typed
transaction preparation.

## Decision

**Every authoritative Autogenesis operation must carry a validated typed
executor contract, and execution emits a content-addressed receipt binding the
clean Git commit, exact frontier, registry, fact, operation, input bytes, fixed
budget, and normalized independently checked result. Callers may choose only
the frontier artifact and output location; they may not supply a command,
artifact, fact, route, checker, timeout, or expected result.**

For the first driver, `axeyum-bench/smtcomp-evidence-v1`, the registry supplies:

- the repository implementation and exact SMT-LIB input artifact;
- the sole fact ID to which those bytes apply;
- a timeout in the bounded range 1 through 900 seconds; and
- the expected public evidence label.

The validator requires that the fact ID be the operation's sole applicability
target, that the input follow the fact-ledger negation-artifact convention, and
that this driver be paired with `smtlib2`, `smt-term-level`, and
`unsat-certificate`. It rejects path traversal, missing files, unknown drivers,
fact/artifact mismatch, and inconsistent route/evidence/footprint tuples. An
operation remains a durable capability after its target settles; frontier state,
not registry validity, determines whether it can be scheduled again.

The executor re-verifies the frontier against the live ledger and registry and
requires exactly one admissible selected fact and one exact authoritative
operation. It executes only the registered driver and accepts only one evidence
line whose verdict is `unsat`, label is the registered label, certification is
true, serialized recheck is not applicable, and fresh-arena check is `ok`.
Elapsed milliseconds are deliberately omitted from the receipt because they
are observational noise, not identity.

Receipt verification re-runs the registered operation from the same clean
commit and requires byte-for-byte equality of the normalized derived object.

## Evidence

- Registry mutation tests reject missing executors, unknown drivers, path
  escape, fact/artifact mismatch, unsupported admission tuples, and footprints
  that contradict their declared policy.
- Frontier tests show that the exact authoritative operation selects only its
  registered fact and that fixture scope restores selection refusal.
- Executor mutation tests reject every weakened observation field, missing or
  duplicated evidence lines, a rehashed receipt mutation, and a changed
  frontier selection.
- The real driver reports the registered
  `unsat-int-quadratic-negative-discriminant` result with `certified=1` and
  `arena=ok` on the exact fact artifact.

## Alternatives

### Let the orchestrator construct a shell command

Rejected. It would make the caller—not the reviewed registry—the authority for
the input, timeout, checker, and expected result. Content-addressing the output
would preserve an untrusted decision rather than remove it.

### Treat producer and checker implementation paths as executable contracts

Rejected. A Rust function's source path does not specify how to construct its
input, which binary exposes it, what budget applies, or which normalized result
licenses admission.

### Store complete stdout in the receipt

Rejected. Timings and diagnostics make a semantically identical replay obtain a
different identity. The executor parses one strict versioned line and retains
only its load-bearing fields.

### Allow one operation to target multiple facts initially

Rejected for v1. The input artifact must bind unambiguously to one fact before
the first authoritative transaction. Parameterized multi-fact operations can
be introduced only with a typed statement-to-input derivation.

## Consequences

- The first selected fact can be executed without caller-authored route
  metadata or shell text.
- Registry changes now alter both frontier and execution identities, so stale
  frontiers and receipts fail closed.
- Execution remains read-only. A receipt cannot change fact status or claim a
  durable admission event.
- The next required adapter consumes this receipt to derive the evidence row,
  footprint, provenance, and prepared transaction fixed by ADR-0468.
- Additional drivers require an explicit validation contract; merely adding an
  arbitrary executable path cannot grant authoritative scope.
