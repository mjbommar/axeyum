# ADR-0489: Proofs stay spelled `theorem`; the `def` option is a measuring instrument

Status: accepted
Index-summary: ADR-0488 measured that re-spelling every `theorem` as `def` makes Lean's elaborator accept the whole constructed-real carrier, and left the change untaken; this builds it as `Kernel::set_render_proofs_as_def` (a `Kernel` field, off by default) and measures it, and the answer is **do not flip the default** — every `.lean` artefact this repository SHIPS already elaborates clean under `theorem` (front door 1,304,276 B, exit 0 in 9.3 s), so the switch costs 1.36–1.69x elaboration, +9.7% on the whole Lean gate, and 212–359 lines of "this is a proof" to buy nothing on the shipped surface; the only module it rescues is the whole 470-declaration carrier, which is not shipped and which Lean's kernel already accepts in 1.4 s — and flipping it makes `real_lean_wellfounded_elaborator_divergence` report that Lean CLOSED the divergence, a checker whose failure mode is a false all-clear. The limitation to publish instead, stated as narrowly as it is true: four carrier declarations are kernel-checkable but not elaborator-checkable, and no shipped artefact contains them
Index-status: accepted

Date: 2026-08-18

Related: [ADR-0488](adr-0488-lean-has-two-checkers-and-the-kernel-is-the-one-we-target.md),
[ADR-0482](adr-0482-the-shared-development-is-emitted-once-as-its-own-lean-module.md),
[ADR-0485](adr-0485-the-pinned-lean-toolchain-is-the-one-that-runs.md),
[ADR-0458](adr-0458-lean-modules-declare-whether-they-contain-reasoning.md).

## Context

ADR-0488 established that Lean has two checkers and that they disagree about a
proof's opacity: the kernel unfolds anything carrying a value, the elaborator
will not unfold a `theorem` while reducing. Four `CReal` declarations whose
type-checking must compute through `Nat.gcd` — whose Euclidean descent rests on
the *theorem* `Nat.mod_lt` — are therefore refused from `.lean` source and
accepted by the kernel. It also measured the fix (re-spell every `theorem` as
`def`) and deliberately did not take it, citing blast radius, doubled
elaboration, and a hot file.

That left a decision nobody could take without re-deriving the measurement. This
ADR takes it.

## What was built

`Kernel::set_render_proofs_as_def` — a **`Kernel` field, not a global, not an
environment variable**, off by default. It changes the keyword that opens an
environment `Declaration::Theorem` and nothing else. Two boundaries are part of
the design rather than accidents of the patch:

* an `Opaque` does **not** follow the switch. It shares the `Theorem` arm of the
  module writer's `match`, so the obvious implementation re-spells it; an
  `opaque` has no value to unfold and re-spelling it changes what Lean checks.
* the module's **root** `theorem <name> : <goal> := <proof>` does not follow it
  either. Nothing reduces through a module's root, so re-spelling it would cost
  the artefact's central claim and buy nothing. This is why the root-theorem
  assertions in `lean_crosscheck`, `lean_module_fixtures`, `axeyum-property` and
  the `evidence_quant_*` suites are indifferent to the option.

`crates/axeyum-lean-kernel/tests/proof_keyword_render_option.rs` (7 tests) pins
both boundaries plus the central property — that over a real development the two
renderings differ by **exactly** the leading keyword, checked as a byte equality
against a line-prefix rewrite and as a size identity (`4 B x <theorem lines>`).

`crates/axeyum-solver/examples/proof_keyword_cost.rs` renders the three artefacts
that matter both ways and, under `--require-keyword-only`, makes its exit status
depend on that same property holding at carrier scale.

## What was measured

Lean 4.30.0, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`, the pin
(ADR-0485), resolved by `scripts/check-lean-gate.sh --print-toolchain`. Three
runs per module on a 16-core host under a load average of 8–11 (other lanes were
building); medians reported, and the spread is wide enough that only the
*direction* and the rough factor should be believed — see the reference-frame
rule in `frontier-ratchet-reference-frame.md`.

| artefact | shipped? | `theorem` | `def` | factor |
| --- | --- | --- | --- | --- |
| front door, self-contained (1,304,276 B) | **yes** | **accepted**, 9.3 s | accepted, 14.9 s | 1.60x |
| shared half of the split layout (1,300,891 B) | **yes** | **accepted**, 9.7 s | accepted, 13.2 s | 1.36x |
| the WHOLE carrier, 470 declarations (2,541,928 B) | no | **4 refused**, 17.3 s | accepted, 29.2 s | 1.69x |

Byte size moves the *other* way, and by exactly the keyword: −848 B on each
shipped artefact (4 B x 212 theorem lines) and −1,436 B on the carrier
(4 B x 359). Size is not a consideration either way.

The four refusals on the carrier are exactly ADR-0488's four, re-measured:
`CReal.Equiv.not_zero_one`, `CReal.not_le_one_zero`, and
`CReal.not_equiv_mul_one_one_zero` / `CReal.no_total_inverse` as
`unknown constant` cascades.

`#print axioms` is **unaffected**. `CReal.add_comm` and `CReal.Equiv.trans` each
report `does not depend on any axioms` under both spellings, so the audit
command this repository's headline claim rests on reads the same either way.

### The finding that decides it

**Every `.lean` artefact this repository ships already elaborates clean under
`theorem`.** The single-file front door and the shared half of the split layout
both exit 0 today. ADR-0488's residue is real and it is *entirely outside the
shipped surface*: the only module the switch rescues is the whole carrier, which
ADR-0482 deliberately does not ship (the shared module is rooted at the reached
union) and which Lean's kernel already accepts in 1.4 s
(`real_lean_creal_carrier_kernel_replay`).

So for a third party who checks our `.lean` by elaborating it — the thing a
reader will naturally do — **nothing changes**. They can run
`lean FrontDoor.lean` today and it succeeds. What the switch would change is
that the same run takes ~1.6x longer and that 212 declarations that are proofs
stop saying so.

### The whole surface, not one probe

`scripts/check-lean-gate.sh`, the authority, on the pinned toolchain:

| run | result |
| --- | --- |
| default (`theorem`) — this commit | **OK**, 20 suites, 64 tests, **472 real-Lean checks** (floor 218), `lean_crosscheck` 77 of 77, 9m04s |
| default flipped to `def` (measurement mutant, snapshot worktree, warm) | **FAILED**, 468 real-Lean checks, 2 suites red, 9m57s (**+9.7%**) |

The two red suites, and one of them is why this is not a close call:

* `diophantine_lean_reconstruct` — the golden body pin, −272 B = 4 B x 68
  environment theorem lines. Expected; a re-bless.
* `real_lean_wellfounded_elaborator_divergence` — **not** a re-bless. Its control
  renders the `gcd` module and requires Lean to REFUSE it. Under a flipped
  default the module is already spelled `def`, Lean accepts it, and the suite
  dies reporting *"Lean's ELABORATOR now accepts a reduction through a `theorem`
  … this suite is stale: re-measure the residue and update the ADR."* Flipping
  the default does not merely break the check that pins ADR-0488's divergence —
  **it makes that check report that Lean fixed the divergence.** A checker whose
  failure mode is a false all-clear is the specific hazard this repository has
  written down; taking the change would require rebuilding that suite to hold
  the spelling itself rather than inherit it.

Outside the gate, five more tests die under a flipped default —
`quant_counterexample_cover`, `quant_affine_growth_lean`, `quant_residue_lean`,
`quant_eq_partition_lean` (golden body pins) and
`real_lean_string_monoid_crosscheck`, which asserts an *environment* theorem's
spelling by name. Seven tests in seven suites in total, five of them invisible to
the gate: `check-lean-gate.sh` is not a sufficient blast-radius measurement for a
renderer change, which is worth knowing independently of this decision.

## Decision

**The default does not move. Proofs are emitted as `theorem`.**

The option ships anyway, off, because it is the instrument that makes ADR-0488's
account falsifiable at any time and at any scale: if a future Lean closes the
gap, or if a future carrier declaration lands whose elaboration *does* need the
`def` spelling, the measurement is one flag rather than a day of bisection.

### The cost of this recommendation, stated plainly

Keeping `theorem` means **4 of the carrier's 470 declarations are checkable by
Lean's kernel and not by Lean's elaborator**: `CReal.Equiv.not_zero_one`,
`CReal.not_le_one_zero`, and `CReal.not_equiv_mul_one_one_zero` /
`CReal.no_total_inverse` which cite the first. They are not incidental — they are
exactly the declarations that make `CReal.Equiv` and `CReal.le` non-total, i.e.
the ones that stop the setoid witness being vacuous.

What that does and does not cost a third party, precisely:

* **Every `.lean` file this repository ships is elaborable end to end, today.**
  `lean FrontDoor.lean` exits 0 in 9.3 s; the split layout's shared half and its
  query module exit 0 too. A reader who does the natural thing — run `lean` on
  our artefact — gets a clean answer with no caveat and no replay harness.
* **A module rooted at the whole carrier is not.** We do not ship one (ADR-0482
  roots the shared module at the reached union), and its coverage is discharged
  by `real_lean_creal_carrier_kernel_replay`, which hands all 470 declarations to
  `Environment.addDeclCore` — Lean's kernel — and requires Lean's constant count
  to equal ours. But a third party who *builds* such a module, or who reaches one
  of those four declarations from a future query, meets four errors and needs the
  NDJSON replay to resolve them.

So the limitation to publish is not "our artefact is kernel-checkable but not
elaborable" — it is narrower and should be stated as narrowly as it is true:
**four declarations of the constructed-real carrier are kernel-checkable but not
elaborator-checkable, and no shipped artefact contains them.** That is a real
limitation and it belongs in the open, not in a footnote. It is also strictly
preferable to the alternative on offer, which does not remove the limitation —
it hides it, by spelling 212 proofs `def` so the elaborator stops distinguishing
them, and by breaking the one suite that could tell us the limitation still
exists.

The honest fix removes the limitation instead of the evidence for it: a
structurally recursive `Nat.gcd` needs no `mod_lt` in its descent, so the four
declarations elaborate as `theorem`s. That is the route this ADR prefers and it
remains open.

## Consequences

- Nothing that ships moves. The emitted bytes on the default path are
  byte-identical (the carrier renders at 2,541,928 B, ADR-0488's figure to the
  byte), `front_door_carrier --require-axiom-free` still reports
  `the module's axiom lines equal the kernel footprint: true`, and the golden
  module pins and `module_banner_pin` are untouched.
- ADR-0488's blast-radius argument is **narrower than it stated**, and that is
  worth recording because it was the stated reason for deferring. The change
  does not disturb "18 real-Lean suites that read the single-file front door":
  those suites assert on the module's ROOT theorem, which this option leaves
  alone. The suites it would actually break are the ones that assert an
  *environment* theorem's spelling — `real_lean_string_monoid_crosscheck`
  (`"theorem axeyum.string._2.append_nil"`) and the golden body pins.
- The honesty cost is the one that outranks the timing. A `def` and a `theorem`
  are the same term to Lean's kernel and to `#print axioms`, so nothing about
  soundness changes; but ADR-0458 has a module declare whether it contains
  reasoning, and an artefact in which the word `theorem` appears once — on the
  root — while 212 proofs are spelled `def` says something weaker about itself
  than it is entitled to. We would be paying that, and 1.6x elaboration, for a
  refusal no shipped artefact suffers.
- `tests/proof_keyword_render_option.rs` invokes no `lean` binary (7 tests,
  0.69 s, pure rendering), so it does not add to what `hooks/pre-push` runs
  wholesale for `axeyum-lean-kernel`. The Lean-invoking half of the measurement
  is `examples/proof_keyword_cost.rs`, which no gate runs — deliberately: it is
  an instrument, not a check.
- `scripts/check-lean-gate.sh` is not a sufficient blast-radius measurement for a
  renderer change. Five of the seven tests a flipped default kills are outside
  it.
- The residue's real fix is upstream of the renderer: a structurally recursive
  `Nat.gcd` closes the same gap from the other end with no keyword change and no
  elaboration cost, and it makes the carrier module elaborable rather than
  merely accepted-if-spelled-loosely. That remains open and is now the preferred
  route.

## Alternatives considered

- **Flip the default.** Rejected on the numbers above: 1.36–1.69x elaboration
  and a weaker artefact, to fix a refusal that only occurs in a module we do not
  ship.
- **Flip it only for the carrier module.** Rejected: it would make the one
  artefact rooted at everything the odd one out, and the carrier's coverage
  claim is already discharged, better, by the kernel replay — Lean's *kernel* is
  the checker ADR-0488 decided to target, and it needs no re-spelling.
- **An environment variable rather than a `Kernel` field.** Rejected: this
  repository's standing rule is that per-lane state lives in per-lane paths or
  per-process environment and never in one global every lane reads; a render
  option that a stray variable can change is exactly the mechanism by which two
  lanes measure different artefacts and compare the numbers.
- **Re-spell the root theorem too, for uniformity.** Rejected: it buys nothing
  (nothing reduces through a root) and costs the module its statement.
