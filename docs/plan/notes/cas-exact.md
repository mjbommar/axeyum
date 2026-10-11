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
