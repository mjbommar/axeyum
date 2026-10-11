# Expression transport evidence — 2026-10-11

Source b191b97be, child of ff9e9301e. Branch feat/cas-expression-wire-20261011;
worktree axeyum-cas-expression-wire, separate target cas-expression-wire.
Four Rust integration transport tests pass/zero ignored, 0.02s. Log
/var/tmp/axeyum-expression-wire-rust.log. All UnaryFunc variants/order parameters,
all node forms and wide rational components have structural round-trip controls.
Focused Gaussian regression now requires Unknown before radical simplification,
retaining is_certified and simplified identity: one pass, zero fail, 0.02s;
log /var/tmp/axeyum-expression-wire-gaussian.log.

Parent Pi repair full CAS gate is terminal red: 2139 pass, one failed, 11 ignored,
380.19s. The failed Gaussian assertion expected a Certified(false) opaque-atom
inequality between mathematically equal functions, inconsistent with the repair.
Changing that expectation does not waive the unchanged successful integration
or radical-simplification equality checks. Parent workspace phase remains live;
source286c6d445 results cannot prove changed child behavior.

Native build completes successfully in 2m51s. Log
/var/tmp/axeyum-expression-wire-native.log. Sealed package
/var/tmp/axeyum-expression-wire-python-mtfxh9re/package loads native SHA-256
663c385262cc3ab70b4e0278b9cb1713bbe5b6d287922c3d971f96d6c96f5380.
Eight Python suites collect and pass279, zero skips, 0.81s: expression_wire,
pi, cas, wide_rationals, signed_powers, text_parser, wide_evalf, trace.
Import path/hash asserted before pytest; tests.log retains terminal output.

Stub runner87525 completes successfully, 27 modules/649 items, 4m00s.
Name/arity gate: 27 modules, 1849 symbols, five aliases, 319 synthesized dunders.
Type ratchet: 1794 parameters, 1709 typed, 131 Any/131 allowlisted,
46 Any returns; 95.3% typed. Generated CAS stub includes both methods. Private canonical-component guard mutation67551
completed successfully: baseline four pass; remove only canonical-component
validation and exactly malformed_wire_and_noncanonical_rationals_reject fails,
three pass/one fail, exit101. The mutant accepts unreduced 2/4; positive
round trips still pass. Snapshot /data0/axeyum/scratch/snap-cas-expression-wire-b191b97be and logs
/var/tmp/axeyum-expression-wire-mutation-j7li1042/. Shared sources untouched.
Initial read-only format check found only lib.rs module ordering/serde attribute
layout; single-file rustfmt with skip_children=true corrects those after stub
compilation finishes. Direct full read-only format check passes. Link and
plan-authority pass. Focused CAS-library Clippy with -D warnings passes (6.88s),
log /var/tmp/axeyum-expression-wire-clippy-final.log. Initial Clippy found one
missing semicolon in the transport walker and four identical-arm warnings in
Pi consumer code; combine those identical patterns without semantic changes.
A first cleanup accidentally removed the separate series coeffs_of Pi decline;
compiler rejection caught it and the arm was restored before successful Clippy.
Test crate-level documentation removes its missing-doc warning. Fresh Python
results above remain tied to b191b97be; subsequent source changes are formatting
and identical-pattern grouping, and broad gates must verify the final commit.
Full CAS/workspace gates and certificate transport/kernel reconstruction remain
pending, not inferred from focused transport or native Python passes.

Broad runner64759 launched against c34b7bc89a1902359939202bc7a4dc19cd2b8412.
Logs /var/tmp/axeyum-expression-wire-full-gates-gidvutll/: format.log,
cas_lib.log, workspace.log. Runs direct read-only format check, full CAS library
then workspace library suites with one test thread; validates every summary has
a nonzero passed count and retains failures. Running is not a pass. Preserve
Rust source while the job executes; follow-up code goes in a new child.

Runner64759 full CAS completes successfully against c34b7bc89: 2140 passed,
zero failed, 11 ignored, 372.78s. Direct format check passes. Workspace phase
remains confirmed live; no workspace pass or child Pi-certificate credit inferred.
