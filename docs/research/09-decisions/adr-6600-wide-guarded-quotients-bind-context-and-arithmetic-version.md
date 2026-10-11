# ADR-6600: Wide guarded quotients bind context and arithmetic version

Status: proposed
Date: 2026-10-11

ADR6400 conditional cancellation binds the caller's exact ordered nonzero
context and certifies numerator = denominator * result. ADR6500 adds bounded
promoted polynomial traces. Compose these through an explicit guarded-quotient
v2 envelope; v1 remains narrow. Version selection applies to every subject,
result, assumption and identity witness, never merely to output serialization.
Require both identity traces to use the matching polynomial version so an
unconditional closed-division witness cannot silently replace a conditional
context obligation.

V2 uses existing canonical wide rational transport and16384-bit arithmetic,
shape/work/degree/byte limits. The external exact denominator-nonzero premise
remains mandatory. Independently normalize the denominator and reject the zero
polynomial; a contradictory external assumption cannot license undefined input.
Replay checks the original subject/result/context and both source-bound identity
traces without invoking factor search. Trace checking does not grant kernel
admission. Python explicitly opts in with wide=True; default behavior is v1.

Validation: wide coefficient cancellation, v1 decline, exact Fraction endpoints,
changed contexts/results/versions, zero denominator and budget controls;
separate-process byte replay; private checker mutations; existing v1 tests;
fresh Python extension/stubs and required broad gates. Nested conditional steps
and kernel reconstruction remain separate required work.
