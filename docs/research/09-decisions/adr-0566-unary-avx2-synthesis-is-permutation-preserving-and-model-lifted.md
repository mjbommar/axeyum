# ADR-0566: Unary AVX2 synthesis is permutation-preserving and model-lifted

Status: accepted
Date: 2026-08-26
Index-summary: Synthesize bounded unary AVX2 byte permutations with complete lossless controls, lifted models, replay, and checked DRAT lower bounds

## Context

ADR-0559 proved one calibration over only `vpshufb` and same-source `vperm2i128`.
It had no multi-step search, exposed no control variables, and therefore could not establish
minimality after adding another instruction family. The open-problem lane needs a reusable
bounded synthesizer whose positive and negative results refer to exactly the same semantics.

The full AVX2 ISA includes multi-source, arithmetic, memory, duplicating, and zeroing
operations. Calling a small model “AVX2 minimality” would overstate its coverage.

## Decision

Add deterministic bounded SAT synthesis for this explicitly named single-register unary
language:

- lane-local permutation controls of `vpshufb`;
- permutation controls of `vpermd` and `vpermq`;
- same-source `vpalignr` rotations with immediates 0 through 15; and
- identity or swap forms of same-source `vperm2i128`.

Each byte at each layer has a one-hot provenance tag. Exactly one instruction family and one
valid control are selected at every step. Variables, clauses, and steps have stable public
ceilings. SAT models are lifted to typed instructions and replayed from the identity input;
a model that fails either CNF evaluation or replay is rejected. UNSAT is authoritative only
when DRAT is checked against the generated formula.

For permutation targets, restricting each control to a permutation is complete within this
single-register unary language: after a deterministic instruction duplicates a tag or emits
zero, some distinct input tag is absent, and no later unary instruction can recreate it.
Non-permutation targets are rejected rather than silently searched in this reduced language.

## Evidence

- Unit tests exercise model lifting, checked DRAT, non-permutation refusal, and the independent
  semantics of dword, qword, and same-source align operations.
- A GCC intrinsic oracle agrees with all five modeled families on AVX2 hardware, including
  the zero-filling immediate-17 align edge. Changing its expected align rotation from five to
  four is rejected at byte zero.
- Global 32-byte reversal produces a 2,663-variable / 87,940-clause one-step formula.
  CaDiCaL 3.0.1 emitted a 957,982-byte DRAT proof, and Axeyum's file-backed checker accepts it.
- The two-step formula has 4,302 variables / 159,912 clauses. A model lifts and replays as
  dword reversal by `vpermd`, followed by within-dword byte reversal by `vpshufb`.

## Consequences

Global byte reversal has certified minimum length two in this five-family language. This is
strictly stronger than ADR-0559's two-family calibration but is not a result about all AVX2
programs, latency/throughput cost, multi-register sequences, or memory operations.

HieraSynth already proves optimal vector programs, and LLVM already documents a two-operation
AVX2 byte-reversal lowering. Current Scholar, arXiv, and web searches did not locate this exact
five-family certificate, but a negative search does not justify a priority claim. The next
research boundary is multi-source shuffle/blend/unpack semantics with an explicit live-value
and cost model.
