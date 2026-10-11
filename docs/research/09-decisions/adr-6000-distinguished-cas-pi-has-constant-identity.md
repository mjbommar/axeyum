# ADR-6000: distinguished CAS pi has constant identity

Status: accepted; bounded surface adopted, final integration gates remain open
Date: 2026-10-11

## Problem

The requested symbolic pi constructor cannot safely reuse `CasExpr::Var("pi")`.
The public floating evaluator accepts an explicit pi binding, differentiation
returns one with respect to that name, but exact trig recognition treats it as
the mathematical constant. A fresh probe with pi bound to two changes
sin(pi) from 0.9092974268256817 to zero after `evaluate_trig`. Enclosure walkers
also recognize an unbound variable named pi as `StepHead::Pi`. These routes
have incompatible denotations. Source evidence lives in the
[lane audit](../../plan/notes/cas-pi.md).

## Decision

Introduce `CasExpr::Pi` and `CasExpr::pi()`, exposed as Python `Expr.pi()`.
This leaf denotes the mathematical real constant independently of all variable
bindings. It is structurally distinct from every Var, including Var("pi") and
Unicode names. Differentiation with respect to any variable returns zero;
substitution cannot replace it. Exact rational evaluation returns None when
pi is genuinely needed, rather than inventing a rational value. Approximate
evalf uses the platform pi value; exact bounds use the existing Machin producer
and `StepHead::Pi` checker. No floating value is a proof certificate.

Migrate internal formulas, special-function derivative rules, exact-trig
recognition and numerical constant reconstruction to this distinguished leaf.
Var("pi") follows ordinary variable semantics: it requires a binding, accepts
substitution, and cannot trigger a pi-only rewrite or enclosure fallback. Other
reserved constants are separately scoped; do not silently change Euler gamma.
Legacy source tests that intentionally used a mathematical pi variable must
construct the new constant. Add paired ordinary-variable controls, rather than
preserving a wrong rewrite for compatibility.

Human rendering uses pi. The bounded text parser reserves pi and its Unicode
alias for the constant; constructor-built Var("pi") remains possible. Canonical
serialization uses distinct tagged constant and variable nodes and must round
trip both. Human printing alone does not establish this distinction. Trace
encoding and any generic expression transport must preserve the tag; bridges
without a checking contract explicitly decline, never manufacture a rational
or a bindable pi variable.

Algebraic treatment of pi must preserve constant identity. If represented as
an opaque polynomial generator internally, its key is separate from every
source variable and is decoded back to Pi; user-controlled strings cannot
forge that generator. An unchecked spelling convention is insufficient.
The checker may certify zero-polynomial algebraic identities over the constant.
A nonzero formal polynomial is insufficient for a fixed-value inequality: those
claims explicitly decline until a checked interval or transcendence certificate
provides the missing basis. Replay applies this policy independently, including
when a caller forges a matching witness. Canonicalization removing Pi does not
by itself supply a value certificate for the original source. Pi subjects with
raw internal-named source variables also decline, so a user string cannot forge
an opaque constant atom. This does not claim complete transcendental equality
or irrationality from normalization.

Enclosure production and replay map Pi to StepHead::Pi even when bindings
contain a variable named pi. A Var(pi) enclosure uses its actual binding and
StepHead::Var, and an unbound Var(pi) declines. Cross-source replay between
those nodes must reject. Preserve existing enclosure evidence algorithms and
endpoint-tamper controls. Kernel admission remains behind
Kernel::add_declaration; a computed bound is not an admitted theorem.

## Required validation

Constructor/variable structural distinction, constant and variable derivatives,
substitution and explicit bindings, exact rational declines, negative-power
semantics and mixed pi/variable expressions. Exact-trig cases must recognize
only the constant; use the pi=2 regression and its commuted/nested variants.
Parser pi/Unicode, precedence, malformed/resource controls, and canonical tagged
round trips must pass. Produced enclosure bytes must replay, while changed
endpoints and changed constant/variable subject fail. Check producer/verifier
head agreement with a private guard-removal test that kills exactly one target.
Audit all expression consumers and reconstruction routes for explicit support
or decline; run fresh affected CAS/Python and full workspace gates with nonzero
counts. This ADR is not a completion claim for any of those gates.

## Adoption and validation boundary

This bounded surface is adopted on the feedback implementation branch. Current
CAS library tests and the fresh native consumer suites cover exact values,
transport, parser/domain controls and explicit unsupported/resource outcomes;
see the [validation receipts](../../plan/notes/28-wide-real-smtlib-writer.md).
Signed-power fuzzing includes guaranteed zero-base negative-exponent and
undefined-base seed classes. Private Pi/source-binding controls remain recorded
with exact intended failures. Production Python parsing uses ADR-6900; ADR-3100
is historical and superseded. Promoted transport does not widen every arithmetic
operation, and Pi bounds or parsed expressions do not grant kernel admission.
The final workspace/all-target gates and main integration remain open.
