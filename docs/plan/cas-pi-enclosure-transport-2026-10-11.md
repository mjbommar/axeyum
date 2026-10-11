# Portable exact pi enclosure evidence — 2026-10-11

Implements the pi-specific enclosure-byte requirement in the
[CAS plan](cas-certified-trace-plan-2026-10-10.md). Contract:
[ADR-6200](../research/09-decisions/adr-6200-portable-pi-enclosure-replays-source-bound-machin-evidence.md).
Scheduling remains in [PLAN.md](../../PLAN.md).

```python
from fractions import Fraction
from axeyum import cas

certificate = cas.enclose_pi(64)
encoded = certificate.to_json()
replayed = cas.PiEnclosure.from_json(encoded)
report = replayed.check(cas.Expr.pi())
assert report.accepted and report.discharged == 1
assert 3 < replayed.lower <= replayed.upper < Fraction(22, 7)
assert replayed.upper - replayed.lower <= Fraction(1, 1 << 64)
assert not replayed.check(cas.Expr.var("pi")).accepted
```

`lower` and `upper` are exact Fraction claims, never approximate floats. Parsing
is not checking. Replay checks both original distinguished source and carried
source identity, then reconstructs the single Pi step and calls the existing
Machin enclosure verifier with empty bindings. It does not invoke the producer.
The arithmetic kernels are shared by producer/checker; this is separate-process
replay, not a claim of independent mathematical implementation or kernel admission.

Version1 preserves precision, order, exact remainder and exact endpoints. Its
single Pi head has no inputs or root signs by definition. Changed source,
insufficient order, understated remainder, overstated precision and invalid
endpoints reject. A conservative larger remainder can remain sound and accepted;
replay establishes mathematics rather than original byte identity.

Hard caps are precision256 bits, order128, component width16384 bits and wire
length64 KiB. Malformed/noncanonical components, unknown/duplicate fields and
unsupported versions raise ValueError; resource exhaustion raises BudgetExceeded.
The report retains examined/discharged counts, acceptance and a failure reason.
Limits are applied before exact replay, including when importing untrusted bytes.

Rust API: `pi_certificate::enclose_pi`, `PiEnclosureCertificate::{to_json,
from_json,check,lower,upper}`. General expression/binding/root transport, checked
fixed-Pi inequalities and kernel reconstruction remain required follow-up work.
This document does not claim those requirements or any broad gate completed.

Validation is in `tests/pi_certificate.rs` and `test_cas_pi_certificate.py`.
Four Rust tests and283 fresh-build Python tests pass, including separate-process
replay. Source-binding mutation (four baseline, three pass/one mutant failure),
stubs/runtime signature/type ratchets, formatting and focused CAS Clippy pass.
Broad child gates remain pending.
[Lane evidence](notes/cas-pi-certificate.md) retains identities and terminal logs.
