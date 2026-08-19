# Lane notes: agent-theorem-opacity — `theorem` vs `def`, measured

The decision is [ADR-0518](../../research/09-decisions/adr-0518-proofs-stay-spelled-theorem-and-the-def-option-is-a-measuring-instrument.md);
the finding it acts on is [ADR-0517](../../research/09-decisions/adr-0517-lean-has-two-checkers-and-the-kernel-is-the-one-we-target.md).
This file is the working record: every number, the frame it was taken in, and
the claims that turned out wrong.

## The instrument

`Kernel::set_render_proofs_as_def(bool)` — a `Kernel` field, off by default.
Renders every environment `Declaration::Theorem` with the `def` keyword.
Deliberately does **not** touch `Opaque` (no value to unfold; it shares the
`Theorem` arm of the module writer's `match`, so the obvious patch re-spells it)
and does **not** touch the module's root `theorem <name>` (nothing reduces
through a root).

`prelude_cache::try_restore` assigns a whole-kernel template over the caller's
kernel, which cleared the flag. It now carries it across. Without that, a
measurement run renders the DEFAULT bytes while believing it rendered the other
— a silent wrong measurement, not a crash.

Reproduce every byte figure below with:

```sh
cargo run -p axeyum-solver --features full --example proof_keyword_cost -- \
  --emit /data0/pk --require-keyword-only
```

## Elaboration cost — the reference frame first

Lean 4.30.0 `d024af099ca4bf2c86f649261ebf59565dc8c622` (the pin, ADR-0514),
resolved via `scripts/check-lean-gate.sh --print-toolchain`. 16-core host, load
average 8–11 throughout because other lanes were building. Three runs per
module. The spread is large — `thm/FrontDoor` ran 13.5 / 8.8 / 9.3 s — so this
frame supports the DIRECTION and the rough factor and nothing finer.

| module | run 1 | run 2 | run 3 | median | verdict |
| --- | --- | --- | --- | --- | --- |
| `thm/FrontDoor` | 13.51 | 8.77 | 9.31 | **9.31** | accepted |
| `def/FrontDoor` | 14.86 | 15.70 | 13.14 | **14.86** | accepted |
| `thm/AxeyumShared` | 9.81 | 8.22 | 9.66 | **9.66** | accepted |
| `def/AxeyumShared` | 16.78 | 13.12 | 13.18 | **13.18** | accepted |
| `thm/AxeyumCarrier` | 17.26 | 22.14 | 15.68 | **17.26** | **4 refused** |
| `def/AxeyumCarrier` | 29.20 | 27.54 | 34.77 | **29.20** | accepted |

Factors: front door 1.60x, shared half 1.36x, whole carrier 1.69x. ADR-0517 said
"roughly doubles"; at carrier scale this frame says 1.7x, and its 14.1 -> 27.9 s
pair is within the noise of 17.3 -> 29.2.

Bytes move the other way and by exactly the keyword — `def` is four bytes
shorter than `theorem`:

| module | `theorem` | `def` | delta | env. theorem lines |
| --- | --- | --- | --- | --- |
| front door, self-contained | 1,304,276 B | 1,303,428 B | −848 | 212 |
| shared half (reached union) | 1,300,891 B | 1,300,043 B | −848 | 212 |
| whole carrier, 470 decls | 2,541,928 B | 2,540,492 B | −1,436 | 359 |

2,541,928 B is ADR-0517's carrier figure to the byte, which is the check that
the default path did not move.

The four carrier refusals re-measured, unchanged from ADR-0517:
`CReal.Equiv.not_zero_one` (line 795), `CReal.not_le_one_zero` (831), and
`CReal.not_equiv_mul_one_one_zero` (885) / `CReal.no_total_inverse` (899) as
`unknown constant` cascades.

`#print axioms` is unaffected: appending
`#print axioms CReal.add_comm` / `#print axioms CReal.Equiv.trans` to both
spellings of the shared module gives `does not depend on any axioms` from both.

## The whole surface

`scripts/check-lean-gate.sh` on the pin, default rendering, at commit
`035a92d9a`: **OK — 20 suites, 64 tests, 472 real-Lean checks** (floor 218),
`lean_crosscheck` 77 of 77, 37 theory families / 40 attestations, **9m04s** wall.

Flipped-default run: a measurement mutant (`proof_keyword` returns `"def"`
unconditionally) applied in a `scripts/lane-snapshot.sh` worktree of the same
commit, so the shared checkout never rendered a non-default byte.

**Flipped-default result: `FAILED`.** 20 suites, 64 tests, **468** real-Lean
checks (four fewer — the divergence suite reports zero when it dies), and two
suites red:

| suite | why |
| --- | --- |
| `real_lean_wellfounded_elaborator_divergence` | its control renders the `gcd` module and requires Lean to REFUSE it. Under a flipped default the module is already `def`, Lean accepts, and the suite dies saying *"Lean's ELABORATOR now accepts a reduction through a `theorem` … this suite is stale: re-measure the residue and update the ADR."* **That is the worst outcome in this whole measurement**: flipping the default does not just break a test, it makes the suite that pins ADR-0517's divergence report that Lean fixed it. |
| `diophantine_lean_reconstruct` | the golden body pin: −272 B = 4 B x 68 environment theorem lines. |

Warm-to-warm the gate goes **9m04s -> 9m57s (+9.7%)**. (The first flipped run
was 9m50s on a cold target directory and is not comparable; the warm re-run is
the number above.)

Beyond the gate, under a flipped default, seven tests in seven suites die:

| suite | in the gate? |
| --- | --- |
| `real_lean_wellfounded_elaborator_divergence` | yes |
| `diophantine_lean_reconstruct` | yes |
| `quant_counterexample_cover` | no |
| `quant_affine_growth_lean` | no |
| `quant_residue_lean` | no |
| `quant_eq_partition_lean` | no |
| `real_lean_string_monoid_crosscheck` | no — it asserts `"theorem axeyum.string._2.append_nil"`, an ENVIRONMENT theorem's spelling |

Five of the seven are outside the gate, which is its own finding: the gate is
not a sufficient blast-radius measurement for a renderer change.

## Mutation checks

Seven tests in `tests/proof_keyword_render_option.rs`. Each mutant compiled and
ran all 7 (the count is the check that a mutant died rather than failed to
build):

| mutant | tests killed |
| --- | --- |
| M1 `Opaque` follows the switch | 1 — `an_opaque_declaration_is_not_re_spelled` |
| M2 the module root follows the switch | 1 — `the_root_theorem_keeps_its_keyword` |
| M3 `try_restore` clears the flag | 1 — `the_option_survives_a_prelude_build` |
| M4 `render_lean_decl` ignores the switch | 1 — `a_theorem_declaration_renders_as_def_only_under_the_option` |
| M5 the module writer ignores the switch | **2** — `a_prelude_module_differs_only_by_the_keyword` and `the_option_survives_a_prelude_build` |

M5 kills two because the restore guard asserts on rendered module text, which is
what makes it non-vacuous: a flag that survives a restore and changes nothing is
not worth pinning. Reported rather than tuned away.

A caveat for whoever repeats this: `grep -c '^error'` returned 1 for **every**
mutant, including the healthy ones — it matches cargo's `error: test failed, to
rerun pass ...` line, not a compile error. The signal that a mutant compiled is
the nonzero `running 7 tests` count, not the absence of `^error`.

## Claims that turned out wrong

* **ADR-0517, "it changes every artefact the repository ships, including the
  single-file front door that 18 real-Lean suites read."** True of the bytes,
  misleading about the blast radius. Those suites assert on the module's ROOT
  theorem, and the option leaves the root alone; they are indifferent to it. The
  suites that would actually break are the ones asserting an ENVIRONMENT
  theorem's spelling.
* **ADR-0517's implied benefit.** The residue is real but it is entirely outside
  the shipped surface: `thm/FrontDoor` and `thm/AxeyumShared` both elaborate
  clean today. The switch rescues only the whole-carrier module, which ADR-0511
  does not ship and which Lean's kernel already accepts.
* **"elaboration roughly doubles."** 1.36–1.69x in this frame, not 2x.
* The brief's "466+ real-Lean checks" and "`lean_crosscheck` 77 of 77" were both
  right (472 and 77 of 77 measured); the floor is 218, not 466.

## Left undone

* A structurally recursive `Nat.gcd` closes the same gap from the other end with
  no keyword change and no elaboration cost. That is the better fix and it is
  still open.
* Per-suite elaboration deltas are not separable from cargo build time in a
  gate run; the per-module table above is the clean elaboration measurement and
  the gate's +9.7% warm-to-warm is the aggregate.
* `tests/proof_keyword_render_option.rs` invokes **no** `lean` binary (7 tests,
  0.69 s, pure rendering), so it does not add to `hooks/pre-push`'s wholesale
  `cargo test -p axeyum-lean-kernel`. The Lean-invoking measurement lives in
  `examples/proof_keyword_cost.rs`, which no gate runs.
