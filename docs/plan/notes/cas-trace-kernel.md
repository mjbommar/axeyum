# CAS trace reconstruction route inventory

Source inspection at5d7f0d85f. This records concrete routes and limits, not
kernel admission results. Release validation44600 is compiling.

| Route | Producer | Replay/checker | Context | Kernel boundary |
|---|---|---|---|---|
| Polynomial v1 trace | `normalize_with_trace` | `replay_json` / `check_trace` | Empty | New step test translates original syntax and composes Complex ring proofs; admission unverified |
| Wide polynomial v2 trace | `normalize_with_trace_wide` | Same checker, version-selected bounded promoted arithmetic | Empty; closed divisor nonzero conditions | New translator currently declines fractional/large coefficients and division |
| Guarded quotient v1/v2 | `cancel_factor_with_trace` / `_wide` | `replay_guarded_json` / `check_guarded_trace` | Exact external ordered nonzero assumptions | Requires implication/domain reconstruction; not implemented by new unconditional bridge |
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
