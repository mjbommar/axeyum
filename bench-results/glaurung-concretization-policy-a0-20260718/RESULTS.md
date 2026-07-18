# Accepted Glaurung concretization-policy A0 compatibility result

Glaurung branch `axeyum-concretization-policy-a0` extracts concretization into
a public `ConcretizationPolicy` seam without changing the default `AnyModel`
behavior. The implementation commit is `34c26c2`; documentation and acceptance
evidence are committed at branch tip `07ea0c1`. The branch is isolated from the
active dirty Glaurung checkout and is not yet merged there.

The seam covers both existing concretization sites, `concretize_addr` and
`eval_concrete`. `AnyModel` retains the existing per-site trace identities
`glaurung-any-address-v1` and `glaurung-representative-value-v1`. The preferred
selector is `GLAURUNG_CONCRETIZATION_POLICY`; the existing
`GLAURUNG_CANONICAL_MODEL_CHOICE` selector remains a compatibility alias, and
conflicting selectors fail closed.

## Byte-identical default gate

The A0 binary was run twice, in order-balanced sole-authority cells, against the
same fixed tcpip prefix used by ADR-0239: input SHA-256
`ff965206a37f2c258b7199bc87b49ee12c834e5fc50f58dae2f3de66a57022ea`,
15 of 338 reachable functions, 250 ms per check, 300,000 solves, and an
1,800-second process bound. Both Axeyum-authoritative repetitions exactly match
all three pre-A0 accepted controls:

| Gate | Pre-A0 (N=3) | A0 (N=2) |
|---|---:|---:|
| Findings per repetition | 126 | 126 |
| Solves per repetition | 2,991 | 2,991 |
| Ordered-list SHA-256 | `a67d7bca28602ab20bbc46d9a5d42705463bd340067dc8e6ec660b35d58ba265` | same |
| Policy identity | `glaurung-any-model-v1` | same |
| Canonical attempts/completions/probes | 0 / 0 / 0 | 0 / 0 / 0 |
| Fixed-work boundary | 15 / 338 | same |

The two known Z3-only rows remain: Z3 emits 128 findings and 3,079 solves in
both repetitions, while Axeyum emits 126 and 2,991. Consequently the report's
overall parity flag is intentionally false. That is the accepted pre-existing
any-model divergence, not an A0 regression.

A separate one-function exercise selected least-unsigned through the preferred
and legacy environment variables. Both routes emitted identical findings and
identical policy/work telemetry: policy `glaurung-min-unsigned-v1`, 13 attempts,
13 completions, 858 probes, zero failures, and 869 solves. Only elapsed timing
differed.

## Test and validation evidence

- TDD red/green sequence covered policy parsing, stable identities, site-hash
  determinism, selector conflict rejection, and policy injection at both seams.
  The final focused suites pass 6 policy tests and 17 explorer tests.
- `cargo check --features solver-z3,solver-axeyum --all-targets` and the release
  `ioctlance` build pass.
- `cargo test --features solver-axeyum --no-fail-fast` passes 977 of 979 library
  tests plus all integration tests and doctests. The two failing WinAPI tests
  reproduce unchanged on base commit `e98c090` and are unrelated to A0.
- The new module passes direct rustfmt and changed-file clippy filtering. The
  repository-wide format and strict-clippy gates remain red on inherited,
  unrelated debt.

## Claim limits and next gate

A0 establishes that value selection is now one configurable mechanism, not
several algorithms. It does not yet execute `BoundarySet` candidates or add
`DiverseEnum`; unsupported multi-value/deferred choices fail closed. The next
scientific step is a preregistered fixed-work policy sweep. Symbolic memory is a
different memory-model architecture and remains conditional on residual
coverage headroom after that sweep.

## Artifact hash

```text
ccb3c971bc1a4a89fce144d0999044228a19a63a5147b429f0a65dd406b2ef03  any-model-report.json
```
