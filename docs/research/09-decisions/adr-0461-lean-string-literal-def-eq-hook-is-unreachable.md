# ADR-0461: Lean 4.30's `String`-literal def-eq hook is unreachable, and we carry it anyway

Index-summary: `try_string_lit_expansion` cannot fire while `String.ofList` is a definition; structure eta through the projection rule is the live route
Status: accepted
Date: 2026-08-15

## Context

[ADR-0366](adr-0366-preregister-lean-string-literal-semantics.md) preregistered
checked `String`-literal semantics against pinned Lean 4.30 and named three
places the pinned kernel converts a literal to
`String.ofList (List.cons Char (Char.ofNat c₀) … (List.nil Char))`:

1. definitional equality, symmetric, against an **immediate** `String.ofList`
   application (`type_checker.cpp:1030`, `try_string_lit_expansion`);
2. projection reduction (`type_checker.cpp:360`, inside `reduce_proj_core`); and
3. recursor reduction (`inductive.h:95`).

Implementing all three revealed that (1) **cannot fire in Lean 4.30**, and the
reason is the same fact ADR-0366 flagged as the place a port goes wrong.

`try_string_lit_expansion_core` requires `app_fn(s) == g_string_mk`, where
`g_string_mk` is the bare constant `String.ofList`
(`type_checker.cpp:1213`). But `is_def_eq_core` runs `lazy_delta_reduction`
**before** it, and `String.ofList` is an ordinary definition in 4.30
(`String` is `structure String where ofByteArray :: (toByteArray : ByteArray)
(isValidUTF8 : …)`). With a literal on one side — never δ-reducible — lazy delta
always unfolds the other, so by the time the hook is consulted the head is
`String.ofByteArray`, and the shape test never matches.

The rule dates from when `String` was `structure String where mk :: (data :
List Char)` and the constant it keys on **was a constructor**, which δ cannot
unfold. Renaming the global to `String.ofList` turned it into a definition and
silently retired the rule.

Measured in this kernel, 2026-08-15: deleting the def-eq hook fails **no test**
in `crates/axeyum-lean-kernel/tests/string_literal_semantics.rs`, while deleting
the projection hook fails three and deleting the recursor hook fails one.

## Decision

**Port `try_string_lit_expansion` at Lean's exact position in `is_def_eq_core`
and keep it, while recording that the live route by which a literal is
identified with a constructor application is structure eta calling the
projection rule — and pin that mechanism with a test rather than a comment.**

Concretely:

- `Kernel::try_string_lit_expansion` sits in the `Exhausted` branch of
  `def_eq_core_uncached`, after `try_eta_expansion` and `try_eta_structure`,
  which is where `is_def_eq_core` calls it. Placing it earlier would identify
  terms the pinned kernel leaves distinct, which is a widening of definitional
  equality that no source justifies.
- `"ab" ≡ String.ofByteArray <bytes>` is decided by `try_eta_structure`, which
  compares `Proj(String, 0, "ab")` against the constructor's field; the
  projection reduces because `reduce_projection` converts a literal major.
  That is the path every real import takes.
- `string_literal_semantics::delta_reaches_the_constructor_before_the_def_eq_hook_can_see_of_list`
  asserts the *mechanism* — that `whnf (String.ofList xs)` is headed by
  `String.ofByteArray` — so a future Lean in which `String.ofList` stops being
  δ-reducible makes that test fail rather than silently changing which rule
  carries the weight.

## Evidence

- `references/lean4` at `d024af0` (v4.30.0): `type_checker.cpp:1030-1042`
  (`try_string_lit_expansion*`), `:1124` (its call site, after
  `lazy_delta_reduction` at `:1091` and both eta attempts), `:884-941`
  (`lazy_delta_reduction_step`, which unfolds the delta-reducible side when the
  other is not), `:1213` (`g_string_mk = String.ofList`), and
  `src/Init/Prelude.lean:3505,3525` (`String` the structure, `String.ofList` the
  definition).
- Hook-removal controls in this kernel, one at a time
  (`docs/formalized-math-2026-08/diary-import-strings.md`): projection → 3
  failures, recursor → 1, def-eq → **0**.
- Whole-route confirmation on Lean's own bytes: the ADR-0366 root
  `importStringLiteral`, re-exported from Lean 4.30.0 and byte-identical to the
  frozen SHA-256 `2404a6ca…0ab4`, admits all 290 declaration records, and
  `crates/axeyum-lean-import/examples/string_literal_reduction_probe.rs` shows
  the imported literal definitionally equal to `String.ofList` over its scalars
  — through Lean's real `ByteArray`/`List.utf8Encode` definitions — while
  refusing the reordered list.

## Alternatives

### Drop the hook, since it cannot fire

Rejected. "Cannot fire" is a property of Lean 4.30's `String`, not of the
algorithm; a toolchain re-pin could restore a constructor-headed `String.ofList`
and the rule would matter again. A hook whose only possible effect is to accept
*more* is never a soundness risk, and deleting a rule the pinned source has is a
divergence we would have to re-derive later.

### Move it before `lazy_delta_step` so it does fire

Rejected, and this is the important rejection. It would make this kernel
identify a literal with an `String.ofList` application by a route Lean does not
use. The terms happen to be equal here, so nothing observable would break today
— which is exactly why it is the kind of change that ships and is discovered
later, on a shape where the two orders disagree. Definitional equality in the
trusted kernel tracks the pinned source's control flow, not its intent.

### Say so in a comment instead of an ADR

Rejected. The repository's own standing lesson is that comments describing
mechanisms drift out of true faster than tests do; the mechanism is asserted, and
the reasoning that makes an unexercised rule acceptable belongs where decisions
live.

## Consequences

- One rule in the trusted kernel is carried and unexercised by the suite. That
  is stated here and in its doc comment, so a later reader does not mistake
  "untested" for "untestable" or delete it as dead code.
- The soundness argument for string literals rests on structure eta and the
  projection rule, both of which have their own controls and both of which are
  exercised by every real import.
- A toolchain re-pin must re-check this: if a future `String.ofList` is a
  constructor again, `delta_reaches_the_constructor_before_the_def_eq_hook_can_see_of_list`
  fails and the def-eq hook becomes load-bearing.
