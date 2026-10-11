# ADR-6400: Conditional CAS traces bind external nonzero assumptions

Status: proposed
Date: 2026-10-11

The unconditional polynomial trace contract (ADR-2500) deliberately excludes
division. Extending its version-1 meaning silently would make old replay clients
misinterpret conditional equality as an identity over all rational assignments.

A separate guarded quotient certificate carries the original numerator and
denominator, the proposed polynomial result, and an ordered external context
whose entries mean that the corresponding rational polynomial is nonzero.
Its cancellation step has an explicit denominator-nonzero premise. Two existing
polynomial traces establish the cross-multiplication identity. Replay binds the
whole subject and context supplied by the caller, checks the denominator premise,
and checks both polynomial traces against their exact inputs before comparing
normal forms. Replay does not call cancellation search.

A context is an assumption, never a proof that the polynomial is nonzero on all
assignments. The certificate claims equality only on assignments satisfying that
context. Dropping or changing an assumption cannot promote it to an unconditional
identity. Literal/provably zero denominators are declined. Version 1 continues
to reject nonempty contexts and division.

The first producer finds a syntactic numerator factor matching the denominator;
the checker uses a polynomial identity, so producer heuristics are outside trust.
Existing version-1 bounds apply to each polynomial witness, and the envelope has
an aggregate byte and assumption-count cap. Wide arithmetic and a unified nested
conditional rewrite log remain follow-up extensions, as does reconstruction into
kernel lemmas. Checked conditional evidence grants no kernel admission receipt.

Validation requires original-subject/context controls, the zero corner, an
incorrect quotient result, independent byte replay, and a private one-guard
mutation control. Rust/Python public exposure follows the checked contract.
