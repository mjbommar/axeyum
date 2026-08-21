# Lane: theorem-opacity — the `def` spelling, built and declined

<!-- plan-section: lane-status -->

**Do not flip the default: every `.lean` artefact this repository SHIPS already
elaborates clean under `theorem`** (`DONE`, theorem-opacity, 2026-08-18).
ADR-0517 measured that re-spelling proofs as `def` makes Lean's elaborator take
the whole constructed-real carrier, and left the change untaken. Built as
`Kernel::set_render_proofs_as_def` — a `Kernel` field, off by default — and
measured on the pin (Lean 4.30.0 `d024af09`): the single-file front door
(1,304,276 B) and the shared half (1,300,891 B) **both exit 0 today**, at 9.3 s
and 9.7 s; under `def` they still exit 0, at 14.9 s and 13.2 s. Only the
whole-carrier module gains — 4 refusals to none — and ADR-0511 does not ship it,
while Lean's *kernel* already accepts it in 1.4 s. So the switch costs 1.36–1.69x
elaboration and 212 lines of "this is a proof" to fix a refusal no shipped
artefact suffers. `#print axioms` reads the same either way, so soundness is not
in play; ADR-0458's honesty argument is what decides it. Decision:
[ADR-0518](../../research/09-decisions/adr-0518-proofs-stay-spelled-theorem-and-the-def-option-is-a-measuring-instrument.md);
numbers: [notes](../notes/68-theorem-opacity.md).

**ADR-0517's blast-radius argument was narrower than stated.** "18 real-Lean
suites read the single-file front door" — they assert on the module's ROOT
theorem, which this option deliberately leaves alone, so they are indifferent to
it. The option's boundaries are pinned by 7 tests, mutation-checked 1/1/1/1/2.

**Nothing that ships moved.** The default path is byte-identical (the carrier
renders at 2,541,928 B, ADR-0517's figure to the byte),
`front_door_carrier --require-axiom-free` still reports
`the module's axiom lines equal the kernel footprint: true`, and
`scripts/check-lean-gate.sh` is **OK at 472 real-Lean checks** (floor 218),
`lean_crosscheck` 77 of 77.

**Next**: a structurally recursive `Nat.gcd`. It closes the same elaborator gap
from the other end, with no keyword change and no elaboration cost, and it is
now the preferred route to the residue ADR-0517 named.

<!-- plan-section: landed-changes -->

| 2026-08-18 | `035a92d9a` | ADR-0518: proofs stay spelled `theorem`. `Kernel::set_render_proofs_as_def` built as a `Kernel` field, OFF by default, so nothing shipped moves; 7 guards in `tests/proof_keyword_render_option.rs` (no `lean` binary, 0.69 s, so `hooks/pre-push` is unaffected), mutation-checked 1/1/1/1/2; `examples/proof_keyword_cost.rs` renders the front door, the shared half and the whole carrier both ways and `--require-keyword-only` fails if the switch moves anything but the keyword. Measured: the shipped artefacts already elaborate clean under `theorem`; flipping the default costs 1.36-1.69x elaboration, +9.7% on the Lean gate, and makes `real_lean_wellfounded_elaborator_divergence` report that Lean CLOSED the divergence. |
