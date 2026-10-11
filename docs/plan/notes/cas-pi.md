# CAS pi identity migration — 2026-10-11

Worktree axeyum-cas-pi, branch feat/cas-pi-20261011, base baf50f913. Read PLAN
and foundational DAG before the public expression contract. ADR-6000 allocated
above the previous feedback decisions; no existing ADR-6000 path was present.

Sealed package /var/tmp/axeyum-feedback-combined-gates-invfxf_7/package, native
SHA 831f35b5f744de86057caa8cdbeb3a23abe0b805f64227ad0641597a4b14238c;
source 2a111e062bd6242c13e96dac8b098ba68d7a188a.
Authoritative probe (actual terminal exit 0):

```python
from axeyum import cas
p = cas.Expr.var("pi")
e = p.sin()
print(p.differentiate("pi"))                     # 1
print(cas.evalf(e, {"pi": 2.0}))                # 0.9092974268256817
print(cas.evaluate_trig(e))                       # 0
print(cas.evalf(cas.evaluate_trig(e), {"pi": 2.0}))  # 0.0
```

This disproves denotation-preserving trig evaluation for the exposed bound
variable. No timing or approximate closeness assumption is needed: the rewrite
is structurally zero while the ordinary variable can be assigned freely.
Original source: lib.rs pi_coefficient (monomial key pi), evaluate_trig and
floating evalf fallback; enclosure.rs reserved_constant, build, expected_head,
enclose_fixed_order. Special-function derivatives also manufacture Var(pi).
A dedicated expression variant must migrate these paths together, including
literal recognition/nsimplify and checker assumptions, not just add a constructor.

Next implementation keeps integration Rust source immutable while runner88821
finishes. New variant requires auditing every exhaustive expression match,
polynomial/opaque atom handling, trace encoding, bounded exact Python evaluation,
expression collection and kernel bridge declines. Unsupported bridges must
return explicit declines, never reinterpret Pi as a bindable source variable.

Implementation started after ADR commit 4d235730a. Draft lib.rs adds CasExpr::Pi,
pi(), zero derivative, substitution invariance, exact-evaluation None, pi
rendering, and constant evalf independent of bindings. Var(pi) evalf no longer
falls back to the constant. No compiled or tested feature claim: initial
serialized cargo check (runner50435) is terminal101 with 19 exhaustive matches
to migrate. Log /var/tmp/axeyum-cas-pi-initial-check.log; separate target
/home/mjbommar/projects/personal/axeyum/target/cas-pi. Rust source remains an
uncommitted draft owned by this lane; integration source is untouched.
Compiler locations: rewrite_trace341; assumptions165; enclosure833/1643/1705/
1928/2016; groebner216; mvpoly637; series265/428; lib1908/2157/4658/5698/7178/
8767/14696/16097 (line numbers at initial draft). Resolve semantics per ADR,
not wildcard assumptions: rational-only bridges decline explicitly, constant
walkers preserve the leaf, enclosure producer/checker use the Pi head and
ordinary Var bindings, sign-of Pi is positive. Core polynomial pi recognition
and all internal Var(pi) manufactures still require migration. Then compile
consumers, add Python constructor/parser/encoding and required regressions.

Implementation increment: all 19 original exhaustive matches are addressed,
with a distinct Pi leaf and source-variable semantics. Core check passes
(third-check.log, terminal0, 7.10s). Rational-only Groebner/series and version1
polynomial traces explicitly decline Pi; normalization uses a dedicated internal
constant generator, rejects its source-variable spelling and decodes to Pi.
Opaque unary keys use structural Debug for non-rational arguments to keep Pi
distinct from Var(pi) even though human rendering is the same. Internal special
function formulas, constant reconstruction and CAS examples now construct Pi.
Enclosure producer/checker map Pi to StepHead::Pi regardless of bindings;
ordinary Var(pi) has no constant fallback and uses its supplied interval.

Five Rust identity/binding/trig/algebra/enclosure/forged-key tests pass, zero
failures/ignored, in pi-identity-tests.log. The first evaluate_trig filter ran
zero tests and is not credited. The real trig population first had 20 pass/one
Fourier failure: Pi was unsupported in MvPoly, preventing needed cancellation.
Adding the separate constant generator to MvPoly repairs it: 21 pass/zero fail,
5.34s, trig-population.log. MvPoly reconstruction now restores Pi, too.

Fresh native build runner70370 is terminal0, 2m41s; binary SHA-256
100ec3d9e13fe23b0649b5c5220f17ef31f94254a55cfc468a2ec0058dd694c8.
Sealed package /var/tmp/axeyum-cas-pi-python-mjoefrni/package. Seven Python
suites (new Pi, CAS, wide rational, signed powers, text parser, wide evalf,
traces) collect/pass 269, zero skips/failures, 0.49s. Parser now consumes both
pi/Unicode constant tokens with the existing node/resource accounting; old
unsupported-pi cases migrate to positive controls. Python exact rational
evaluation declines irrational Pi; approximate evaluation is not a certificate.
All check/build/test logs above use /var/tmp/axeyum-cas-pi- prefixes.

Stub generator52472 is confirmed live; no generated-stub pass yet. Required
full CAS/workspace tests, private checker guard mutation, portable tagged Pi
encoding, canonical serialization and kernel reconstruction remain work.
The combined integration workspace runner88821 remains distinct and live after
its full solver red; no integration source is modified by this lane.

Stub generator52472 is terminal0: 27 modules/649 items. Generated CAS stub
adds Expr.pi(); SMT stub also catches up the imported internal-only Boolean/LIA
proof docstring. Fresh-native name/arity check passes: 27 modules/1848 symbols,
five aliases, 319 synthesized dunders. Type ratchet passes: 1793 parameters,
1708 typed, 131 Any sites/131 allowlisted, 46 return Any. These are measured
current counts, not the old pre-integration inventory. Five Rust controls were
rerun on current source after strengthening enclosure replay with a variable
bound to exactly the Pi interval: terminal0, five pass/zero ignore. Matching
numeric bounds must not erase the source head distinction. Native implementation
commit dff045a24 is retained; full library and private mutation checks are next.

Private checker mutation runner14551 is terminal0. Snapshot from 1b17f7e4a:
/data0/axeyum/scratch/snap-cas-pi-1b17f7e4a. Logs:
/var/tmp/axeyum-pi-head-mutation-nf53tye5. Baseline five pass/zero failures;
removing only the head mismatch guard yields four pass/one failure, exactly
enclosure_is_bound_to_constant_or_variable_subject. Original working tree
remains untouched. Full CAS/workspace runner21448 is live at source
1b17f7e4a4441930c9eeb0259f49d4b233e75225; logs
/var/tmp/axeyum-pi-full-gates-5ngckzns. CAS phase has progressed through
bignum tests; workspace has not started. No broad pass is credited.

Additional sealed-native evidence probe: equal(Pi^2, 0), equal(Pi^2, 2), and
equal(Pi^2, Pi) all return Certified(equal=false) from formal polynomial
nonzeroness alone. Those mathematical inequalities are true, but the current
witness does not check a Pi bound or a transcendence basis. ADR-6000 explicitly
does not license deriving such a claim from normalization. Required follow-up:
retain zero polynomial identity certificates, but decline nonzero fixed-constant
refutations until independently checked interval evidence decides them. Add a
mandatory negative certification control and a positive algebraic identity.
Do not edit current Rust source under runner21448: use an isolated child for
this evidence repair, then revalidate the changed source. No full Pi completion
or new trusted-base claim is made by the present constructor/parser increment.

Evidence repair isolated in axeyum-cas-pi-evidence, branch
fix/cas-pi-evidence-20261011, base f67504b37. Parent runner21448 keeps immutable
Rust source: full CAS completed 2140 pass/zero fail/11 ignored, 412.13s, then
workspace starts; parent result does not prove the changed child implementation.

Child repairs producer and replay policy. Nonzero Pi-source formal polynomials
decline with FixedPiValue; public equal also declines after canonicalization
eliminates Pi rather than surfacing an uncertified source-value claim. Replay
rejects matching forged inequalities independently of the producer. Zero
polynomial identities over Pi and ordinary Var(pi) cases remain checkable.
Another actual parent-native probe showed equal(exp(Pi), Var("\0exp:Pi"))
returning Certified(true): source variables could forge an opaque constant atom.
Both producer and replay now reject Pi subjects containing raw internal-named
source variables; ordinary variables remain distinct. Seven Rust controls pass,
zero failures/ignored, 14.09s compilation plus immediate test run. Log
/var/tmp/axeyum-pi-evidence-tests.log. Compilation initially exposed moved-value
errors in the new test; clones fix that, no failing run is counted as a pass.

Fresh child native build20145 is live, logs /var/tmp/axeyum-pi-evidence-native.log,
separate target /home/mjbommar/projects/personal/axeyum/target/cas-pi-evidence.
Two new Python regressions require unknown/None for gated inequalities and raw
atom aliases, with a positive Pi identity. They are not credited until that
new binary is built/sealed/tested. Guard mutations and broader child gates still
apply. Canonical serialization/enclosure-value certificates remain next work,
not replaced by the present explicit unsupported result.

## Child repair validation — 2026-10-11

Source 286c6d445ee935fb30975ec8fe2bff68c82b8def. Native build20145
completed successfully in 2m02s. Sealed package
/var/tmp/axeyum-pi-evidence-python-25g80_ib/package loads native SHA-256
e88b462e0b41028b982bed87a5badd2cc6be52546d1d03f75bb5e01ffbb6ce78.
Seven CAS Python suites collect and pass 271 tests, zero skips, in 0.57s;
tests.log beside the package retains terminal evidence.

Private snapshot /data0/axeyum/scratch/snap-cas-pi-evidence-286c6d445
checks each replay guard separately. Baseline seven pass; removing only the
fixed-value inequality guard produces six pass/one failure; restoring it then
removing only the raw-atom subject guard also produces six pass/one failure.
Both mutants exit101. Logs /var/tmp/axeyum-pi-evidence-mutations-1_eqgmez/
(baseline.log, inequality.log, atom-alias.log). Shared sources were not mutated.

Broad runner15629 remains confirmed live (wrapper4077990, Cargo4078071 and
CAS test4090146 observed). Logs
/var/tmp/axeyum-pi-evidence-full-gates-oc8atvuk/cas_lib.log and workspace.log;
CAS followed by workspace library suites. No broad pass credited yet.
Next implementation remains tagged expression serialization and checked Pi
value evidence, followed by remaining trace/proof/OMT/consumer requirements.

Child runner15629 CAS terminal red: 2139 pass, one failure, 11 ignored, 380.19s.
The Gaussian test expected Certified(false) between two equivalent functions
represented by distinct opaque atoms. Repair policy correctly declines this
Pi-source claim. Expression-wire child b191b97be requires Unknown there while
retaining certified integration/simplified equality; focused Gaussian passes.
Runner15629 workspace phase remains live; no workspace result credited.
See [expression transport evidence](cas-expression-wire.md) for child work.
