# LIB-6 exact-input evidence

Branch `fix/cas-exact-inputs-20261010`, worktree
`/home/mjbommar/projects/personal/axeyum-cas-exact`, base `0b6c39dde`.

`axeyum-ir::Rational` has small/promoted storage and exact big getters already.
Its narrow numerator/denominator getters intentionally panic for promoted inputs.
`CasExpr::Const` can therefore store a promoted value today, but
`normalize_rational_big_within` converts constants using the narrow getters.
The patch changes only those two conversions to exact big getters. Existing
checked CAS arithmetic stays bounded; Python construction is still bounded.
The audit was corrected to distinguish the carrier from route support.

Fresh integration build/test handle 75555:
`scripts/cargo-serialized.sh test -p axeyum-cas --test wide_input_zero_test`,
target `/home/mjbommar/projects/personal/axeyum/target/cas-exact`. Two controls
use a 193-bit numerator: scaled polynomial equality with independent certificate
replay and changed endpoint rejection; nonzero constant requires CertifiedBig.
No pass is credited before terminal output.

Still required: other promoted-input narrow boundaries, wide expression
arithmetic/evaluation, Python input/output, certificate serialization, explicit
resource limits and independent Fraction amortization. LIB-5 traces and LIB-6
negative powers/pi/parser remain fully in scope.

## Fresh exact normalization results

Handle 75555 ended exit 0, 2/2 tests passed against `bc3e865d5`. Added an
independent Python `fractions.Fraction` fixture for P=300000, r=1/240, n=360;
its exact numerator is 2859 bits, denominator 2849 bits. Fresh handle 89890
ended exit 0, 3/3 tests passed in 0.06 s, including equality and certificate
replay against that fixture. This demonstrates exact normalization/certification
for the concrete amortization expression with reciprocal lowering; it does not
claim a general payment API, signed power API or Python big-rational transport.

Checker sensitivity run 31707 uses private snapshot
`/data0/axeyum/scratch/snap-cas-exact-bc3e865d5`; baseline 2/2 passed. It removes
the zero/nonzero correspondence guard in positive_rational_multiple by replacing
the guarded return with True. Expected: the changed-endpoint rejection alone
fails. Mutation run is live and not yet credited. No active-tree mutation.
