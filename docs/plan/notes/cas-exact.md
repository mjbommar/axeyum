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

## Mutation terminal result

Handle 31707 is terminal with expected rejection: snapshot baseline 2/2 passed;
guard-deleted mutant 1 passed / 1 failed, exit 101. The sole failure was
`promoted_coefficients_reach_exact_normalization_and_replay`, on its changed
endpoint rejection assertion. The genuine nonzero certificate still passed.
This satisfies the exactly-one negative-control requirement. Do not reapply
the mutation to an active worktree.

Full CAS library validation has now started on source `074dde371` with one
test thread via handle 74901; retained log
`/var/tmp/axeyum-cas-exact-gates-upyai0w9/cas_lib.log`. It is not
credited until terminal output and nonzero counts are verified.

## Full CAS library terminal result

Handle 74901 completed exit 0: 2140 passed, 0 failed, 11 ignored, in 619.83 s
with one test thread. Log `/var/tmp/axeyum-cas-exact-gates-upyai0w9/cas_lib.log`.
This validates the exact-input patch's library population; three new integration
tests passed separately. It is not a workspace gate and does not validate the
new trace module, which is on a child branch in a separate worktree.

## Wide Python transport and evaluation in progress

ADR-2900 proposes reusing the existing promoted Rational carrier for Python.
Constructor/getter/Fraction/operand transport uses bounded signed integer bytes
(16,384 bits per component), including builtin integer descriptors so subclass
overrides cannot change the transported value. Numeric hashes use exact Python
Fraction hashing. A private rational evaluator supports bounded big intermediates
(4,096 visits, depth 128, 16,384 component bits) and repeated-squaring powers.
Missing variables and undefined division remain None; resource limits are explicit.
No float intermediates or Python decimal conversion are involved.

Initial fresh Python run: 208 pass/one fail (209 collected). The failure exposed
PyO3 masking arithmetic extraction errors as NotImplemented. Operand now carries
recognized input errors into the operator body. Fresh post-fix package
`/var/tmp/axeyum-wide-python-final-0jafsvsm`, native SHA-256
`15ef062fd1312c6c8250f41f0fcae6d652db89d630e25fc14de6c559602b8584`,
passed 210 tests (210 collected), including independent 360-period Fraction
calculation, signed wide round trips, hash equality, decimal settings, subclass
controls, resource limits and missing/undefined distinctions. Focused clippy passed
before the later constant-fold changes. Four Rust wide-input controls passed.

Generated stubs contain 645 items in 27 modules; constructor/rat defaults now
show optional integer denominator None (means one), and getters return Python int.
Subsequent audit found remaining narrow constant abs/sign/floor/ceiling and
negative-product rendering; repaired and rebuilding with new controls, including
i128::MIN ceiling. Rust narrow eval and unsupported operation boundaries remain
separate; no all-operations wide guarantee, LIB-6 completion or integration claim.
Full CAS/workspace gates must be rerun for the new core changes.

Final constant-fold validation: fresh build 97916 exited 0; isolated package
`/var/tmp/axeyum-wide-fold-python-wiklqz87` loaded native SHA-256
`662f862b46c2c1020203a0ed76fe6cba996efde03239c3e6f2ebdde79549569c`.
213 Python tests passed (213 collected), including wide constant unary folds and
i128::MIN ceiling. Focused clippy and four Rust wide-input tests passed in 49080.
The arithmetic-boundary gate caught the earlier test's direct num_* imports;
changed them to axeyum_arith::big, and the gate now passes (zero unallowed/stale).
Rustfmt check on the modified CAS core and diff whitespace checks pass.

Remaining wide coverage includes auditing older CAS operation/numeral extraction
boundaries, full expression/certificate serialization and kernel bridges. The
new exact evaluation route is computed evidence, not a newly admitted theorem.
Negative powers, distinguished pi and text parsing remain required work.

Full-gate runner 59537 is live against e7b58fc86, with logs at
`/var/tmp/axeyum-wide-cas-full-gates-uixaunea/`. It runs CAS library then
workspace library with one test thread, retaining terminal exit status and
nonzero counts. Do not restart merely because observation yields no output.
No terminal result is credited yet.

## Latest full CAS gate is red

Runner 59537 completed its CAS library phase against e7b58fc86: exit 101,
2139 passed, one failed, eleven ignored, 1314.04 seconds. Sole failure:
matgroup::tests::psl2_f7_isomorphic_to_gl3_f2 reports 6.095126417 seconds
against its five-second single-thread debug budget. Functional assertions reached
the timing check. The matgroup source is untouched; no threshold was changed.
This is a red gate, not proof of an ambient-load cause. Parent/quiet comparison
is still required. Workspace phase has started and remains live; do not restart.
