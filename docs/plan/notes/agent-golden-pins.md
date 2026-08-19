# Lane: golden-pins — the module banner is no longer under every pin

Detail for [`../status/agent-golden-pins.md`](../status/agent-golden-pins.md).

## The defect, stated as a mechanism

Every Lean module `axeyum-lean-kernel` renders opens with a fixed banner
(`lean_pp::write_module_banner`): a header comment, `prelude`, `set_option`
lines, and Lean's compiler-internal constants. It is identical in every module,
it says nothing about any proof, and it sat **inside every golden byte pin in the
workspace**. So a commit that changes the banner for a good reason moves every
golden pin at once, and re-pins only the ones it happens to run.

Three recurrences, all the same shape:

| commit | date | banner delta | re-pinned | shipped red |
| --- | --- | --- | --- | --- |
| `0fc7cc357` | 08-15 | (body, not banner: axioms became theorems) | `diophantine_lean_reconstruct` | 3 quant suites |
| `b760fd6ae` | 08-17 | +863 (`unsafe axiom lcErased/lcAny/lcVoid`) | `diophantine`, `farkas_over_the_integers` | 4 quant suites |
| `46724faec` | 08-18 | +777 (`set_option maxRecDepth 65536`) | the 17 `lean-modules` fixtures | 4 quant suites, `diophantine` |

Every producer was right. `6389e0194` diagnosed it on 08-15 and re-pinned; it
recurred twice more. The structural half — *nothing ran those suites* — was named
in `31442bd5d`'s message and left open.

Note the third row: `46724faec` re-blessed **all seventeen** committed
`.lean` fixtures in one command, and none of them shipped red. The fixture
mechanism (`AXEYUM_BLESS_LEAN_FIXTURES=1`, `reconstruct::tests`) already solved
this problem for the goldens it covers. The five that broke are the ones too
large to commit as fixtures — 17 KB, 114 KB, 126 KB, 208 KB and **1.14 MB**.

## What landed

**1. The banner is not in the pins.** `axeyum_lean_kernel::split_module_banner`
splits a rendered module into `(banner, body)`; the shared helper
`crates/axeyum-lean-kernel/tests/support/lean_golden.rs` pins the **body** and
*refuses* a source that does not begin with the banner this kernel emits, byte
for byte. So the banner is still checked on every golden — it is just no longer
the thing whose length they assert.

**2. The banner has one pin, as committed text.**
`axeyum-lean-kernel --test module_banner_pin` holds the three banner shapes
(`self-contained`, `shared-prelude`, `importing`) as fixtures under
`tests/fixtures/module-banner/`, blessed by the **same** `AXEYUM_BLESS_LEAN_FIXTURES=1`
that blesses the seventeen module fixtures. A header change now fails exactly one
test, and its failure is a text diff of the header — the thing that should be read
and waved through deliberately, rather than re-derived from a moved integer.

That is deliberately *not* "one command re-pins the numbers". A pin that is easy
to re-bless carelessly is worse than one that is hard to re-bless; the numbers
stay hard, and only the reviewable text got easy.

**3. Membership is discovered, never listed.**
`scripts/check-lean-golden-pins.sh` finds every suite that calls
`assert_golden_module` — the same act as *being* a golden pin — and runs it, with
a nonzero-test-count assertion per suite. It also **refuses** a test file that
renders a Lean module and hashes bytes with FNV-1a without the helper, which is
the only way to write a new whole-module pin. A new golden therefore cannot be
added outside the gate, and the old style cannot come back. Wired into `just
check` and `scripts/check.sh` (both, so `check-aggregate-scope` stays clean) and
diff-scoped into `hooks/pre-push`.

## The suite membership — the brief's regex was wrong

The brief supplied a first-pass regex and four candidate files, flagged as a
guess. All four are **false positives**; none can be moved by a banner change:

| file | line | what it actually pins |
| --- | --- | --- |
| `axeyum-lean-kernel/tests/mutual_inductive_group_grammar.rs` | 1048 | `specs.len() == 720` — generated case count |
| `axeyum-lean-kernel/tests/nested_inductive_grammar.rs` | 2552 | `specs.len() == 640` — generated case count |
| `axeyum-lean-import/tests/wire_mutation_corpus.rs` | 449 | `first.len() == 226` — corpus population |
| `axeyum-solver/tests/quant_bv_alternation_counterexample.rs` | 203 | `outer_bindings.len() == 318` — certificate bindings |

Three more files carry the FNV-1a offset and are *also* not in the class
(`strict_positivity.rs`, `recursive_induction_hypotheses.rs`,
`lean_pp`'s sibling `quotient.rs`): they hash generated **descriptor transcripts**,
not module text. And `axeyum-verify`'s `MIR.len()` pins (2 691 / 8 218 / 10 120)
are rendered MIR, a different renderer entirely.

The real class is "asserts an exact byte length or content hash of a string
produced by `render_lean_module*`", and it is exactly five suites — the four that
failed plus `diophantine_lean_reconstruct`, which was re-pinned by hand three
separate times (`b760fd6ae`, `7e9a3088f`, and `0fc7cc357` before them) precisely
*because* it is the one that sits in a gate.

## Measurements

All at `760befd16` in a `scripts/lane-snapshot.sh` tree, so none of the seven
other lanes' uncommitted `src/` edits are in them.

**The pins.** Every one moved by exactly **2,122 bytes** — the self-contained
banner's length — and by nothing else:

| suite | old whole-module pin | new body pin |
| --- | --- | --- |
| `diophantine_lean_reconstruct` | 1 144 134 | **1 142 012** `0xc3d7_4e54_f071_0274` |
| `quant_affine_growth_lean` | 208 220 | **206 098** `0x059f_ad6b_63f4_1238` |
| `quant_residue_lean` | 125 761 | **123 639** `0xb342_d148_fdc5_a621` |
| `quant_eq_partition_lean` | 113 943 | **111 821** `0xadca_ca06_49f6_11e5` |
| `quant_counterexample_cover` | 17 034 | **14 912** `0x873f_0c80_83b0_a826` |

Banner fixture sizes: self-contained 2 122 B, shared-prelude 2 296 B,
importing 1 495 B.

**The gate.** 6 suites, 33 tests, nonzero count asserted per suite. (7 and 40
until the printed TABLE was read rather than the exit status: `module_banner_pin`
carries the helper's own controls, so discovery found it *and* the script
appended it, and it ran twice under a cheerful green.)
Warm execution 33.5 s (`quant_counterexample_cover` 23.1, `diophantine` 8.7,
the other four under 1 s each); **35 s wall** end to end on an idle box. The
first run measured 2 333 s wall, ~97% of it queued on the fleet-wide
`scripts/cargo-serialized.sh` flock behind other lanes — which is why the gate
now makes ONE cargo invocation per (package, features) group instead of one per
suite. `rustup run stable cargo clippy --workspace --all-targets --all-features
-- -D warnings`: exit 0.

**Where it runs, and what that costs.** `just check` and `scripts/check.sh`
(both, so `check-aggregate-scope` stays clean) — always. `hooks/pre-push`,
diff-scoped to `crates/axeyum-lean-kernel/src/**`: **0 s** on a push that does
not touch it, ~35 s on one that does. That scope is not a guess — all three
recurrences originated there (`lean_pp.rs` twice, `int_prelude.rs` once). The
hook is already 722–1176 s and every second is paid by every push, so an
unconditional 35 s was not worth it for a producer set this narrow.

**The demonstration.** One line added to `write_module_banner` (+60 bytes):

```
axeyum-lean-kernel  module_banner_pin  5  ran (group FAILED)
  the self-contained module banner moved by +60 bytes (2122 -> 2182).
  first difference at line 22: ...
axeyum-solver       diophantine_lean_reconstruct  5  ok
axeyum-solver       quant_affine_growth_lean      4  ok
axeyum-solver       quant_counterexample_cover    8  ok
axeyum-solver       quant_eq_partition_lean       6  ok
axeyum-solver       quant_residue_lean            3  ok
```

Gate exit 1. **One** test of the seven in `module_banner_pin` failed, naming the
changed line and both texts; all five proof pins stayed green, because no proof
byte moved. `AXEYUM_BLESS_LEAN_FIXTURES=1 cargo test -p axeyum-lean-kernel
--test module_banner_pin` then re-blessed it in one command and the gate went to
6/6 green — with a reviewable +1-line text diff as the record. Repeated with a
same-length mutation (`maxRecDepth 65536` -> `65537`): identical outcome, `+0
bytes`, first difference named.

**Mutation checks.** Every guard deleted, one at a time; the count is the number
of controls that died.

| guard | control that died | count |
| --- | --- | --- |
| gate: discovery floor | `a tree with no golden pins is refused` | **1** |
| gate: hand-rolled-pin refusal | `a hand-rolled whole-module pin is refused` | **1** |
| gate: zero-tests (INERT) | `a suite that runs zero tests is refused` | **1** |
| gate: reads the group exit status | `a failing suite is refused` | **1** |
| `split_module_banner`'s no-banner refusal | `a_foreign_or_mangled_header_is_refused` | **1** |
| `module_banner_pin`'s fixture-count check | `the_banner_fixtures_are_committed_files` | **1** |
| `assert_golden_module`'s body comparison | `a_wrong_body_pin_is_rejected` | **1** |

The last row is the one worth reading. Deleting the comparison inside
`assert_golden_module` first made **all twenty-five** tests in the five golden
suites pass — measured, not feared: an assertion's removal is invisible to the
assertion, so the central mechanism of this change was the one thing nothing
could catch. `a_wrong_body_pin_is_rejected` / `the_right_body_pin_is_accepted`
were added for exactly that, and with them the same deletion kills one control.

Two honest notes on isolation. `the_banner_fixtures_are_committed_files`
overlaps the comparison test on a *deleted* fixture directory (both fail); it
isolates only on a **stray extra** fixture, which is the case it uniquely owns —
measured: 1 of 5 dies with the guard present, 0 of 5 with it deleted. And a
mutation that makes `split_module_banner` accept anything removes a *mechanism*
rather than a guard: on the banner suite alone it kills one control, but it
would also silently widen every golden pin, which is why the helper's refusal
and the pin live in the same function.

## Left undone

* The five golden suites are not in `scripts/check-gate-liveness.sh`'s floor
  manifest. The new gate asserts a nonzero count per suite, which is the floor
  of one; a per-suite ratchet (a suite quietly losing most of its tests) would
  be strictly stronger and is a separate, cheap follow-up.
* `scripts/local-ci.sh` has not been re-run; the record on disk
  (`a6ee37c6a-s4.json`) is still the FAIL that started this. A fresh run costs
  ~107 minutes and one fleet-wide lock.
* The gate runs the suites but does not hand their modules to real Lean; that
  remains `scripts/check-lean-gate.sh`'s job via `lean_crosscheck`, which covers
  three of the four quant families and `diophantine`.
