# ADR-6100: CAS expression wire preserves source identity

Status: proposed; implementation and validation in progress
Date: 2026-10-11

## Decision

Provide a version-1 JSON expression envelope with explicit node tags for exact
rational constants, Pi, variables, ordered Add/Mul, Neg, Div, Pow and every
UnaryFunc including its exact order. Rational components are canonical decimal
strings, reduced with positive denominator; no float intermediate. Preserve
syntax and operand order without simplification. Pi and Var("pi") have different
bytes. Human display and the convenience parser are separate contracts.

Expose Rust expression_wire::{to_json,from_json} and Python Expr.to_json and
Expr.from_json. Deserialization accepts whitespace and object-key order but
rejects duplicate fields, unknown fields/tags/versions, noncanonical rational
components and trailing data. Canonical output uses fixed serde field order.

Hard caps: 1 MiB bytes (including a conservative pre-encoding syntax budget), 4096 nodes, 32 expression levels, 16384 bits per rational
component, 1024 UTF-8 bytes per variable name. Serialization screens depth before
recursive conversion. JSON parsing retains serde's recursion limit; decoding
checks the stricter expression caps before recursive tree construction. No
expression normalization, search or proof is invoked. Resource and malformed
input errors remain distinct. Raw variable names round-trip as names and never
become constants; this transport grants no algebraic evidence.

This encoding transports expressions, not certificates. Existing trace version1
remains a separate bounded polynomial format; changing that format or claiming
kernel admission requires its own evidence. Enclosure certificate transport and
checked value inequalities remain required follow-up work.

## Validation

Round-trip every node/head and promoted rationals, zero-arity operations,
maximum exponents, negative-power quotient structure and Pi/Var(pi). Paired
malformed/oversized controls exercise each limit, duplicate/unknown fields,
zero/negative/nonreduced denominators and source-tag substitution. Fresh Python
must produce the same bytes as Rust and reconstruct exact expressions. Run CAS
and workspace gates separately from focused transport tests.
