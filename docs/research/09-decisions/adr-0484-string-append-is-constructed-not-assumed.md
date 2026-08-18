# ADR-0484: `str.++` is a checked recursion over `Str.rec`, not a primitive interface

Status: accepted
Index-summary: The last non-`real` prelude assumption is gone: `append` becomes a `Declaration::Definition` over the `Str` recursor with four proved monoid laws, so `string` joins `logic`/`nat`/`integer` at a **zero** trusted surface and the ledger's `primitive-interface`/`retained` classification of that row is overturned
Index-status: accepted

Date: 2026-08-17

Related: [ADR-0465](adr-0465-the-axiom-ledger-is-derived-not-transcribed.md),
[ADR-0387](adr-0387-fallible-composable-lean-preludes.md),
[ADR-0051](adr-0051-first-class-seq-string-sort.md).

## Context

`build_string_prelude` admitted `axeyum.string.<n>.append : Str → Str → Str` as
a `Declaration::Axiom`. The generated axiom ledger classified that row
`primitive-interface` with discharge status `retained` — "a carrier or operation
[that] intentionally remains an abstract interface constant" — and it was the
**last** assumption anywhere outside the `real` prelude, measured
2026-08-17 as `logic 0 / nat 0 / integer 0 / real 30 / string 1`.

Three things made the classification wrong rather than merely conservative:

1. **`Str` is not an interface.** It is the recursive inductive
   `Str.nil | Str.cons (Char) (Str)` declared through
   `Kernel::add_recursive_datatype_family`, and its generated `Str.rec` carries
   an induction hypothesis per recursive field. `append` over it is the same
   shape as `Nat.add` over `Nat.rec`, which this repository has defined and
   proved out since the ℕ development. A `primitive-interface` row is one whose
   carrier is abstract; this carrier is constructed, so nothing about the row
   was primitive.
2. **The reason it survived was scope, not necessity.** The word-clash
   reconstruction joins clashing members by `Eq`-congruence over whole terms and
   never reduces `append`, so a binary function symbol sufficed. The cheapest
   thing that worked was to assume one. That is a legitimate first slice; it is
   not a boundary.
3. **An assumed operation is invisible to an external checker.** Lean accepts an
   `axiom` vacuously, so a `string` reconstruction could pass both kernels while
   the operation it is about was never constructed in either — the exact
   failure mode ADR-0465 exists to keep measurable.

The remaining `real` rows are a genuinely different case: their carrier is an
opaque constant (ADR-0483 is the live work to construct it), so they are
primitive in a way `append` never was.

## Decision

**`append` is a checked structural recursion, and the free-monoid laws its
consumers will need are theorems the kernel re-checks, not assumptions.**

```text
append a b ≔ Str.rec.{1} (motive := λ _ => Str) b (λ h t ih => Str.cons h ih) a
```

so `append nil b ≡ b` and `append (cons h t) b ≡ cons h (append t b)` hold by
ι-computation. Four laws are admitted as `Declaration::Theorem`s:

| law | statement | route |
|---|---|---|
| `nil_append` | `∀ b, append nil b = b` | ι, `Eq.refl` |
| `cons_append` | `∀ h t b, append (cons h t) b = cons h (append t b)` | ι, `Eq.refl` |
| `append_nil` | `∀ a, append a nil = a` | `Str.rec` induction |
| `append_assoc` | `∀ a b c, (a ++ b) ++ c = a ++ (b ++ c)` | `Str.rec` induction |

Consequences that follow, and are gated:

1. The `string` prelude's trusted surface is **empty**, and
   `nat_axiom_inventory` reports `string: axiom=0 opaque=0 quotient=0`. The
   ledger row is filed in `retired_entries` with this ADR's reasoning rather
   than deleted, per ADR-0465's population-change rule.
2. The ledger's `primitive-interface` / `retained` classification of that row is
   **overturned**; it was a `derivable-theorem` all along.
3. `append` still gets *stuck* on an opaque word, so the word-clash and
   lex-clash reconstructions behave exactly as before — defining an operation
   adds definitional equalities, it never removes one, and a test pins that the
   stuck behaviour survives.
4. The claim is checked **outside** this kernel too: a real `lean` binary
   accepts the exported module and its `#print axioms` report names only the
   problem's own hypotheses, with no `axeyum.string.*` row. That is the
   assertion that could not have been made while `append` was an axiom.

## Alternatives considered

- **Keep the axiom and add the laws as axioms too.** Cheaper, and strictly
  worse: it grows the trusted surface to state facts the recursor already
  proves, and an external checker still learns nothing.
- **Keep `append` opaque and define a separate computable `appendC`.** Two
  operations that must then be related by — an axiom. This is the same problem
  one level down.
- **Define `append` but leave the laws to consumers.** Rejected on the grounds
  that a definition nobody can reason about propositionally only moves the
  assumption to the call site; `append_nil` in particular is *not* definitional
  on an open word, so without the induction a consumer would reach for an axiom.

## Consequences

- Length, cancellation, and prefix/suffix reasoning over the free monoid now
  have a proved base to build on rather than a deferred follow-up.
- The trusted surface of this project is now exactly the `real` prelude. Any
  future assumption outside it is a regression with a named owner, and
  `string_prelude_trusted_surface_is_empty` fails in-tree before the ledger
  gate is ever reached.
