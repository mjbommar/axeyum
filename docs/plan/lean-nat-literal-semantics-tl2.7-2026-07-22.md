# TL2.7 result — checked Lean natural-literal semantics

Date: 2026-07-22

Status: complete

Decision: [ADR-0347](../research/09-decisions/adr-0347-checked-lean-nat-literal-semantics.md)

## Result

TL2.7 types arbitrary-precision natural literals and implements the exact
constructor/literal conversion needed by Lean's kernel semantics. A natural
literal infers as `Nat` only when the checked environment contains the
canonical `Nat`, `Nat.zero`, and `Nat.succ` bootstrap. Literal zero is
definitionally equal to `Nat.zero`; a positive literal peels against
`Nat.succ`; `Nat.succ` applied to a literal reduces to its successor; and the
`Nat` recursor exposes one literal constructor layer before iota reduction.

The pinned official Nat-literal export now translates all 90 expressions and
independently admits ten declarations from five declaration records with zero
axioms. Its imported definition reduces to the literal `37`. This closes the
exact TL2.7 K1 root; it is not broad `Init`, `Std`, mathlib, native-source, or
ecosystem compatibility credit.

## Semantic contract

Axeyum's importer starts from an empty kernel environment, unlike Lean's
normally bootstrapped process. Literal typing therefore activates only after
the environment has independently admitted this exact shape:

- `Nat` has no universe parameters, parameters, or indices, is recursive, and
  has type `Sort 1`;
- its constructors are exactly `Nat.zero` followed by `Nat.succ`;
- `Nat.zero` has no fields and type `Nat`;
- `Nat.succ` has one field and type `Nat -> Nat`.

Missing, renamed, reordered, malformed, or Prop-valued substitutes return
`KernelError::NatLiteralBootstrapMismatch`. This guard prevents a user-defined
constant named `Nat` from silently assigning meaning to raw literal syntax.

Once the bootstrap is established:

- `Lit::Nat(n)` infers as the checked `Nat` constant;
- equal literal nodes compare directly, including values above `u128`;
- literal zero and `Nat.zero` are definitionally equal;
- `Lit(n + 1)` and `Nat.succ(t)` are definitionally equal exactly when
  `Lit(n)` and `t` are;
- transparent delta wrappers do not obstruct that offset comparison;
- `Nat.succ (Lit n)` reduces to `Lit(n + 1)`;
- `Nat.rec` over a literal converts one constructor layer and then follows the
  ordinary checked iota route.

String literals remain fail-closed. General accelerated reductions such as
`Nat.add` and `Nat.mul` remain TL2.8; the implementation does not assign
special meaning to an arbitrary constant with one of those names.

## Import and mutation evidence

The format-3.1 reader now constructs a kernel `Lit::Nat` expression after
arbitrary-precision decimal validation. The exact official fixture
[`lean4export-v4.30-nat-literal.ndjson`](fixtures/lean4export-v4.30-nat-literal.ndjson)
has this observed inventory and result:

- 30 names, four nonzero levels, 90 expressions, five declaration records;
- ten independently admitted kernel declarations, zero retained axioms;
- `importNatLiteral` reduces to `37`;
- replacements at `2^128 - 1`, `2^128`, `2^128 + 1`, and a much larger
  decimal all retain their exact value and admit;
- renaming the exported `Nat.zero` bootstrap rejects the dependent definition
  at its declaration boundary.

The machine-readable compatibility contract now records five passing profile
rows, one explicit import decline, and eight source-bound decline codes.
`literal-nat-typing` is retired; quotient and String remain registered
fail-closed boundaries.

## Differential and native evidence

The mandatory pinned-Lean differential uses Lean 4.30.0 commit
`d024af099ca4bf2c86f649261ebf59565dc8c622` under the repository's 4 GiB
limit. Both kernels accept:

- literal zero equal to `Nat.zero`;
- literal three equal to its unary constructor form;
- `2^128` equal to `Nat.succ` of the preceding literal;
- the identity `Nat.rec` computation over literal three.

Official Lean rejects the false adjacent-value equality. Axeyum's native
matrix adds canonical-bootstrap mutations, delta wrappers, values above the old
width boundary, recursor computation, and an explicitly inert `Nat.add`
control. The deterministic seam fuzz still contains 768 cases, now records
typed Nat-literal and rejected String-literal populations separately, and
rejects every attempted `False` admission.

## Validation

Passed locally with build concurrency capped at two:

- `cargo test -p axeyum-lean-kernel --tests --no-fail-fast`: 179 unit tests and
  35 integration cases across twelve integration binaries;
- `cargo test -p axeyum-lean-import --tests`: 18 integration cases;
- required pinned Lean 4.30 Nat-literal differential under the 4 GiB limit;
- 14 compatibility/prototype Python tests;
- deterministic compatibility generation: 12 rows, five profile passes, one
  declined row, eight decline codes, and eight assurance fields.

The required pinned-Lean test is also wired into CI beside the existing
inductive differential. Focused formatting, warning-denied Clippy/rustdoc,
doctest, parity-document, foundational-resource, and link gates pass. The first
doctest link attempt hit the host's existing `/tmp` disk quota; the exact test
passed with compiler temporary files redirected to `/dev/shm`, without changing
the semantic or memory limits. The `just` wrapper was unavailable on this host,
so its `parity-docs` constituents were run directly and all passed.

## What this does not claim

- no accelerated general Nat operation is implemented;
- String literal typing/reduction is not implemented;
- recursive-indexed, mutual, nested, reflexive, quotient, and broader library
  closures remain outside this exact result;
- one official dependency closure does not establish complete Lean kernel,
  language, workflow, runtime, or ecosystem parity.

## Next action

At this checkpoint TL1.3 was next. It has since published completed imported
environments transactionally; TL1.4 mutation coverage and TL1.7 dependency
identity have also landed. TL2.8 separately owns accelerated Nat operations,
and TL2.9 owns String literal semantics.
