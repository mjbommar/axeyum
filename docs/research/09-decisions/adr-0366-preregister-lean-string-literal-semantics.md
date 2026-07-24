# ADR-0366: Preregister checked Lean String-literal semantics

Status: proposed

Date: 2026-07-23

Execution plan:
[TL2.9 String-literal plan](../../plan/lean-string-literal-semantics-tl2.9-plan-2026-07-23.md)

## Context

Axeyum already stores `.strVal` payloads losslessly as Rust `String` values,
hashes them in declaration identity, and renders them as Lean string syntax.
The trusted kernel still rejects every `Lit::Str` during inference, and the
format-3.1 reader returns `Unsupported(literal-string-typing)` before it even
constructs the expression. TL2.9 must close the semantic boundary, not merely
remove that decline.

Pinned Lean 4.30 gives a string literal the type `String`. Its kernel converts
the UTF-8 payload to a list of Unicode scalar values, wraps each scalar as
`Char.ofNat (Lit n)`, preserves scalar order with `List.cons`/`List.nil`, and
applies `String.ofList`. That conversion is used in three distinct places:

1. symmetric definitional equality against an immediate `String.ofList`
   application;
2. projection reduction when the projected value is a literal; and
3. recursor reduction when the major premise is a literal.

The conversion is not byte-oriented. For example, `"é"` contributes one
scalar `0xE9`, `"🙂"` contributes one scalar `0x1F642`, and the decomposed
sequence `"e\u{301}"` remains two ordered characters. Rust `String::chars`
has exactly this Unicode-scalar contract after `serde_json` has decoded JSON
escapes and rejected invalid Unicode strings.

Official Lean starts with reserved core declarations already installed.
Axeyum's importer starts from an empty independent kernel. As with Nat
literals, assigning primitive meaning to reserved names without checking the
environment would let name coincidence authorize semantics. String conversion
also depends on a larger interface than Nat: canonical `Nat`, `List`, `Char`,
`Char.ofNat`, `String`, and `String.ofList`.

The exact historical String dependency closure was measured but intentionally
not retained: 570,807 bytes, 10,339 records, 1,781 names, 24 nonzero levels,
8,243 expressions, and 290 declaration records, with SHA-256
`2404a6ca64999088ee9e4aa76f3426e77fda8eed5c63f5d8ad593c6b08ae0ab4`.
Its old projection blocker is closed, but the next current-product blocker has
not been measured. Regenerating or executing that closure remains a separately
authorized milestone.

## Decision

**Type and convert Lean String literals only after validating the checked
reserved String-literal bootstrap; reproduce the pinned kernel's exact
Unicode-scalar `String.ofList` expansion in definitional equality, projection,
and recursor reduction; and make the format-3.1 reader construct `Lit::Str`
without granting official-root credit until the exact large closure and
pinned-Lean differential are separately authorized and retained.**

### Checked bootstrap

One private `StringLiteralBootstrap` gate validates all declarations used by
the primitive rule. It requires:

- the already accepted canonical `Nat`/`Nat.zero`/`Nat.succ` bootstrap;
- `List` to be the one-parameter, zero-index, recursive family at one universe
  parameter with constructors exactly `List.nil`, then `List.cons`;
- `List.nil` and `List.cons` to have the canonical owner, constructor indices,
  field counts, universe arity, parameter spine, binder information, and types;
- `Char : Type` to be the non-polymorphic, non-recursive, one-constructor
  structure whose constructor is `Char.mk`, and `Char.ofNat` to be a checked
  definition of exact type `Nat -> Char`;
- `String : Type` to be the non-polymorphic, non-recursive, one-constructor
  structure whose constructor is `String.ofByteArray`; and
- `String.ofList` to be a checked definition with no universe parameters and
  exact type `List Char -> String`.

All compared types are independently synthesized. Universe-parameter display
names are alpha-renamable only positionally; binder information, declaration
kind, owner, constructor order/index, and field count are semantic. The two
definition bodies remain subject to the ordinary trusted declaration checker,
as in Lean's bootstrapped environment; the authorized official closure later
binds their exact imported content identities. Any missing or mismatched
surface returns `KernelError::StringLiteralBootstrapMismatch` naming the first
failed reserved declaration. No partial bootstrap flag is stored.

This is intentionally stricter than returning `Const String` after finding an
arbitrary declaration with that spelling. It is also deliberately separate
from Axeyum's finite-character reconstruction prelude, whose `Str`/`Char`
types are solver-proof encodings and must never impersonate Lean's core types.

### Literal typing and conversion

After the gate succeeds, `Lit::Str(value)` infers as the exact checked
`String` constant. The literal remains compact and is not expanded by ordinary
WHNF.

`string_literal_to_constructor` performs the pinned conversion:

```text
String.ofList
  (List.cons.{0} Char (Char.ofNat (Lit scalar_0))
    ...
      (List.cons.{0} Char (Char.ofNat (Lit scalar_n))
        (List.nil.{0} Char)))
```

The payload is traversed as Unicode scalar values, the list is built from the
end to preserve order, every code point remains an arbitrary-precision Nat
literal, and no UTF-8 byte is exposed as a character. Empty strings map to
`String.ofList (List.nil Char)`. Rust strings cannot contain surrogate code
points; malformed JSON Unicode remains a reader error rather than being
repaired or replaced.

### Definitional equality, projection, and recursors

The three hooks match pinned Lean 4.30:

- two string literals use the existing payload equality fast path;
- if exactly one side is a string literal and the other side is an immediate
  application of the checked `String.ofList`, compare the other side with the
  WHNF of the canonical expansion, symmetrically;
- projection reduction first WHNFs the projected value, converts and WHNFs a
  string literal, then follows the ordinary checked constructor projection;
- recursor reduction first WHNFs the major, converts and WHNFs a string
  literal, then selects the ordinary checked recursor rule; and
- unrelated applications, same-named declarations that fail the bootstrap,
  underapplied terms, or non-String recursor/projection contexts remain inert
  or reject through existing typing rules.

No special reduction is added for `String.append`, equality, length, indexing,
UTF-8 operations, `Char.ofNat`, or `String.ofList` beyond their already checked
ordinary definitions. Those computations follow normal delta/iota/projection
reduction or remain future work.

### Wire and publication boundary

The format-3.1 reader accepts `{"strVal": <JSON string>}` by constructing the
same `Lit::Str`. Parsing a literal alone is not admission credit: any
declaration that uses it must pass the kernel bootstrap and ordinary checking.
Malformed JSON, invalid Unicode escapes, a missing bootstrap, or any later
record failure returns no `CompletedImport`.

The existing `axeyum-lean-declaration-identity-v1` tag and raw UTF-8 payload
hashing for `Lit::Str` remain unchanged. Existing declaration identities must
stay byte-identical. The reader retires `literal-string-typing` only after the
authorized official closure proves that the selected root reaches or passes
the literal; until then documentation distinguishes implemented wire support
from complete K1/root evidence.

## Evidence required for acceptance

1. Empty, partial, renamed, reordered, wrong-kind, wrong-owner, wrong-universe,
   wrong-binder, wrong-type, and wrong-field-count bootstrap mutations reject
   with the typed String mismatch.
2. Empty, ASCII, NUL/control, escaped, BMP, supplementary-plane, combining,
   and mixed strings infer as the exact checked `String` type.
3. Canonical expansion produces exact scalar values and order, including the
   composed/decomposed distinction and proof that multi-byte UTF-8 does not
   become multiple characters.
4. Literal/`String.ofList` definitional equality is symmetric; adjacent,
   reordered, duplicated, byte-split, wrong-head, and non-immediate controls
   reject.
5. Projection and String recursor reductions compute through literals using
   the existing checked structure/recursor metadata; stuck and ill-typed
   controls do not fabricate reductions.
6. A deterministic public-path seam grammar crosses bootstrap state, payload
   class, comparison form, projection/recursor form, and expected outcome with
   at least 512 unique rows and a byte-identical repeated digest.
7. The reader preserves decoded scalar payloads, rejects malformed Unicode
   JSON, and never publishes on bootstrap or late-stream failure.
8. Every existing v1 declaration identity remains unchanged; new String-backed
   identities repeat and distinguish scalar order and normalization form.
9. Focused kernel/importer tests, clippy, rustdoc, parity documentation,
   foundational-resource checks, and link checks pass in the isolated lane.
10. Under separate authorization, the exact String source is exported twice,
    both streams are byte-identical, the historical hash is reconciled, the
    artifact is retained content-addressably, and Python/Rust inventories
    agree.
11. That official root either admits and computes `importStringLiteral` or
    records the exact first new typed blocker without converting partial
    progress into complete K1 credit.
12. A separately authorized pinned-Lean 4.30 differential covers the registered
    positive computations and false controls before ADR acceptance and TL2.9
    completion.
13. Every milestone is path-scoped, committed with the required co-author
    trailer, pushed, and verified against its tracking ref before integration.

## Primary sources

- [Lean 4.30 literal type](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/Lean/Expr.lean)
- [Lean 4.30 String defeq/projection hooks](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/kernel/type_checker.cpp)
- [Lean 4.30 Unicode-scalar conversion and recursor hook](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/kernel/inductive.cpp)
- [Lean 4.30 recursor conversion](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/kernel/inductive.h)
- [Lean 4.30 `Char`, `List`, and `String.ofList`](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/Init/Prelude.lean)
- [lean4export 3.1 `strVal` and dependency forcing](https://github.com/leanprover/lean4export/blob/a3e35a584f59b390667db7269cd37fca8575e4bf/Export.lean)

## Alternatives

### Type a literal after finding any constant named `String`

Rejected. In a fresh imported environment, spelling alone is not a trusted
bootstrap and can assign primitive syntax an attacker-chosen type.

### Convert UTF-8 bytes instead of Unicode scalar values

Rejected. It disagrees with `utf8_decode` in the pinned kernel for every
multi-byte code point and would make projection/recursor computation unsound.

### Reuse the finite solver-proof string prelude

Rejected. That prelude is an explicit proof encoding over a corpus-specific
finite character enumeration; it is not Lean's core `String` representation.

### Expand every literal eagerly during parsing

Rejected. The wire format contains a primitive literal, Lean keeps it compact,
and eager expansion would multiply memory before any semantic operation asks
for constructor form.

### Claim TL2.9 from native tests while the large root is unavailable

Rejected. Native tests can establish the kernel rule, but TL2.9's exit requires
the exact official root and its next blocker. The authorization-gated artifact
and differential remain explicit acceptance gates.

## Consequences

- String typing becomes environment-dependent on a checked reserved bootstrap,
  consistent with TL2.7's Nat boundary.
- Unicode semantics are explicit and testable at the scalar/list seam.
- Projection and recursor code gain one shared conversion helper rather than
  separate ad hoc encodings.
- The importer can represent valid `strVal` records without weakening
  completion-only publication.
- Offline implementation can make real semantic progress, but the historical
  unretained closure and pinned-Lean differential remain honest external gates;
  zero complete K1, parity axis, or terminal-gate credit follows from P0.
