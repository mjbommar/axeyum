# Portable pi certificate evidence — 2026-10-11

Branch feat/cas-pi-certificate-20261011, worktree axeyum-cas-pi-certificate,
base087fc31b5. Source9a4bb90cb introduces Rust and Python source-bound single-Pi
Machin evidence transport with precision256/order128/resource caps. Original
parent full CAS now passes2140/zero fail/11 ignored; parent workspace remains
live and does not prove changed child source.

Initial four-test Rust run had three pass/one fail: the tamper test expected
remainder4 to reject, but Enclosure::verify accepts conservative overestimates.
Use understatement0, preserving that mathematical checker contract. Raise
transport precision from initially drafted32 to256 before committing; Rust
round-trip cases include0,8,16,32,64,256. Final four tests pass/zero ignored,
0.01s; log /var/tmp/axeyum-pi-certificate-rust-final.log. Source, endpoint,
remainder, order, precision, canonical-component, duplicate-field and cap
controls have mandatory outcomes.

First native build finished while draft precision changed; no Python evidence
credited to it. Rebuild17701 against committed9a4bb90cb completes in51.55s;
log /var/tmp/axeyum-pi-certificate-native-final.log. Sealed package
/var/tmp/axeyum-pi-certificate-python-srpw7ugs/package loads SHA-256
a8faa53cca20ae927b5a5ff46a3a48ea62c7b42866c45bb1def41b86a72d218d.
Nine Python suites collect/pass283, zero skips,1.20s: pi_certificate,
expression_wire, pi, cas, wide_rationals, signed_powers, text_parser, wide_evalf,
trace. Import path/hash asserted before pytest. Certificate suite also exports
JSON to a separate Python process, replays without producer invocation and
requires a nonzero discharged count plus Var(pi) rejection. tests.log retains
terminal output. Producer/checker arithmetic is shared; no independence or
kernel admission claim.

Stub runner6460 completes in5m37s: 27 modules/652 items. Runtime name/arity
check passes27 modules/1855 symbols/five aliases/319 synthesized dunders. Type
ratchet passes1797 parameters/1712 typed/131 Any and131 allowlisted/46 Any
returns,95.3% typed. Fresh runtime and generated CAS stubs agree.
Read-only format24339, focused CAS Clippy93508 (-D warnings), link80688 and
plan-authority gates pass.

Private source-binding mutation69248 completes successfully in snapshot
/data0/axeyum/scratch/snap-cas-pi-certificate-9a4bb90cb. Logs
/var/tmp/axeyum-pi-certificate-mutation-dc1hllye/: baseline four pass/zero fail;
remove only the source-binding guard and exactly
certificate_source_binding_cannot_be_substituted fails (three pass/one failure,
exit101). Ordinary Var(pi) rejection still follows from the underlying checker;
the new guard independently rejects a forged carried source with otherwise
valid Pi numerical evidence. Shared checkout sources were not mutated.
Broader child gates, general enclosure transport and checked Pi inequalities
remain pending; source-only serialization is not library theorem admission.

Broad runner43938 launched on56fe5378dd0c54d20264f5d9741d6353f2b9a1af,
logs /var/tmp/axeyum-pi-certificate-full-gates-_dy3bzlq/ (cas_lib.log,
workspace.log). Sequential full CAS library and workspace library suites use
one test thread and require every terminal summary to have nonzero passed
count. No broad pass credited. Keep Rust sources immutable while it runs;
subsequent implementation belongs in a child if this runner remains live.

## Broad CAS terminal result

Source 56fe5378dd0c54d20264f5d9741d6353f2b9a1af: full CAS library suite
completed with 2,140 passed, 0 failed, 11 ignored in 373.02 seconds. Log:
`/var/tmp/axeyum-pi-certificate-full-gates-_dy3bzlq/cas_lib.log`. Workspace
phase of runner 43938 remains live (complex kernel tests observed); no
workspace success claimed.
