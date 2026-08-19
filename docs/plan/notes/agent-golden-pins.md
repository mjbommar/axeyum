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

See the status file for the numbers this lane measured, including the
mutation-check (one byte changed in the banner) and the per-suite gate cost.
