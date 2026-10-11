# CAS trace reconstruction route inventory

Source review through Rust cc65885a3 and generated stubs6c11a0008.
This records concrete routes and limits, not
general kernel admission coverage. Release validation44600 passed one test,
0 failed/ignored,95.98s; compilation4m55s. The test independently required
admission, empty measured footprint and rejection at a changed endpoint.

| Route | Producer | Replay/checker | Context | Kernel boundary |
|---|---|---|---|---|
| Polynomial v1 trace | `normalize_with_trace` | `replay_json` / `check_trace` | Empty | New step test translates original syntax and composes Complex ring proofs; one generated multistep integer-ring identity admitted with empty measured footprint |
| Wide polynomial v2 trace | `normalize_with_trace_wide` | Same checker, version-selected bounded promoted arithmetic | Empty; closed divisor nonzero conditions | New translator currently declines fractional/large coefficients and division |
| Guarded quotient v1/v2 | `cancel_factor_with_trace` / `_wide` | `replay_guarded_json` / `check_guarded_trace` | Exact external ordered nonzero assumptions | Requires implication/domain reconstruction; not implemented by new unconditional bridge |
| Nested conditional composition v1 | `cancel_nested_with_trace` | `replay_conditional_json` / `check_conditional_trace` | Caller-bound ordered nonzero premises; local guarded quotient v2 witnesses | Preserves partial rational value/definedness through checked congruence; no kernel reconstruction/admission claim |
| Existing Complex CAS bridge | `build_true_identity` in `complex/cas_bridge_tests.rs` | Kernel declaration type checking | Free Complex variable; integer univariate polynomial | Whole product identity proof through polynomial evaluation/ring laws; does not consume trace bytes |
| Solver CAS certificates | `cas_poly.rs` refutation producers | Independent expander in `cas_certificate.rs` | Original solver assertions | Separate solver reconstruction route; no claimed automatic trace admission |

The new bridge translates each carried expression directly to `CExpr`; it does
not translate both endpoints by first normalizing them. Each step becomes a
ring-law proof, composed with `Complex.Equiv.trans`, then universally bound over
the free variable. Kernel rejection of the composed proof at a changed endpoint
is a required negative control. The accepted declaration's reached axiom
footprint must be read with `Kernel::axiom_footprint`.

Current bridge bounds: one named variable x, integer coefficients[-8,8], powers
at most4; prior trace replay bounds expression depth/nodes/work. These are
explicit admission declines, not claims of general CAS reconstruction.
Remaining requirements include rational constants, promoted literals, conditional
premises, public reconstruction API, persistent admitted receipts, and discovery
integration. Existing rational literal construction in `creal/pi.rs` and
`creal/creal_tests.rs` is the next reuse point; it must retain exact denominators
and does not justify silently treating a fractional coefficient as an integer.

## Nested composition evidence and arithmetic boundary

The nested route was added at `1a8eab81d`; helper-order lint correction
`0b829e980` preserves its behavior. Each step selects an exact quotient at a
child-index path, checks both polynomial identities and its denominator premise,
and reconstructs the surrounding expression unchanged. Step IDs, predecessors,
ordered context, source and final endpoint are checked. Whole-result polynomial
normalization is not substituted for these obligations.

Replay shares bounded exact arithmetic with existing polynomial/guarded checkers;
it does not call cancellation search and is not an independently implemented
arithmetic engine. Six Rust controls include independently evaluated nonzero
assignments and undefined outer divisions. A private snapshot's removed
congruence guard gives exactly one intended death and restores bytewise.
Fresh native `99af1a4c` passes 34 trace tests including 13 nested controls,
wide surrounding coefficients, producer-disabled child replay and refusal of
partial evidence after an unsupported later step.

Each local cancellation is conditional, not an unconditional equality. Ordered
nonzero premises are caller inputs; the checker does not prove them from nothing.
Remaining outer division domains remain partial. Unsupported quotient operands,
pi/nonrational expressions and unsupported kernel bridges explicitly decline.
Work policy bounds aggregate declared polynomial witness-work allowances;
syntax/serialization have separate caps, not a claimed wall-clock deadline.
A produced or checked outcome carries no kernel admission receipt.

## Completed release controls and design adoption

Release13258 is terminal:3 passed,0 failed/ignored,2655 filtered,72.62s,
compilation3m54s (`/var/tmp/axeyum-cas-trace-kernel-controls.log`). All three
controls ran: generated multistep admission with empty measured footprint and
wrong-endpoint rejection; hostile added assumptions rejected at source-bound
intake; fractional/wide/domain/foreign-variable translation declines.
Current `complex/cas_bridge_tests.rs` matches revision97e700533 byte-for-byte.
ADR6700 adopts that bounded design. Final whole-workspace verification remains
pending, and the unsupported reconstruction families above remain explicit.

## Final public-surface review

Reviewed Rust polynomial, guarded quotient and nested conditional envelopes,
producer/checker entry points, Python registration/re-export and generated
`axeyum._native.cas` stubs. Conditional replay requires saved JSON plus external
original input, claimed result and ordered nonzero context. Version, source,
step IDs/predecessors, local path/witness, unchanged surroundings and final
continuity all enter checking. Caller limits bound the policy; envelopes cannot
enlarge it. Transport rejects unknown fields and oversized input.

Python exports `cancel_nested_trace` and `replay_conditional_trace` through the
native registration and `axeyum.cas` re-export. The frozen outcome retains
produced/checked/rejected/unsupported/resource_limited, optional failing step
and reason. Refusals have no JSON/result and zero steps. Generated stubs retain
keyword-only nonzero context and integer limits. No production result claims
proof or admission. Ordinary/guarded trace outcomes use their distinct versioned
contracts; shared bounded arithmetic and independent negative controls remain
explicit rather than claiming a separate arithmetic implementation.

The final workspace binary passes all three bounded kernel bridge controls:
generated multistep admission/empty measured footprint, added-assumption
rejection, and unsupported translation decline. The complete kernel/workspace
gates are still running. Public generalized reconstruction, persisted admission
receipts and discovery integration are further extensions; the plan requires
the demonstrated admission boundary before connecting discovery.
