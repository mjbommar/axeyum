# A5/A3/A2 repair journal (2026-08)

Moved verbatim out of [`docs/plan/global/10-status.md`](global/10-status.md) on
2026-08-17. `scripts/check-plan-authority.py` budgets the files `PLAN.md` is
generated from at 52 KB and says what to do when they exceed it: *"move
journal/detail to a result note."* This is that note.

Nothing is edited apart from link paths: the `global/` sources are written with
root-relative links because they are assembled into `PLAN.md` at the repository
root, and this file sits in `docs/plan/`.

Exact pushed `e996afd83` passed `just check`; its RDL capture then failed closed
at 196/200 because allocator arenas accumulated across files. ADR-0379 rejects
allocator tuning and uses one inherited-limit child at a time. The isolated
200-row trigger passed with zero stderr; the old partial stream remains
non-credited. See the
[result](qf-linear-a5-rdl-process-isolation-repair-2026-08-09.md).

Exact pushed repair `5a53012e1` passed the complete external-frontier
`just check` gate with exit 0. The preregistered V2 sequence then produced three
structurally valid atomic 200-row captures with zero stderr and the exact
pushed source/binary identity. QF_LRA decided 89, QF_IDL 68, and QF_RDL 105;
the RDL stream crossed the former row-196 process boundary and completed in
2,127,949 ms. The lossless derivation nevertheless stopped correctly:
historical QF_LRA UNSAT control
`sal/windowreal/windowreal-no_t_deadlock-17.smt2` returned deterministic pre-SAT
resource `unknown` at 1,217 arithmetic atoms and 6,526 CNF variables. Gains
elsewhere hid that loss in the aggregate count. The entire V2 sequence is
non-credited. A bounded
[pre-SAT boundary discriminator](qf-linear-a5-pre-sat-boundary-monotonicity-v1-preregistration-2026-08-10.md)
now owns the P0 path; no residual grouping or census-based breadth change is
authorized.

The bounded repair is exact-pushed at `8a6de50ac`. Its rebuilt 11,859,344-byte
binary (`eec4813b557165ec95afc43912ad9fc2b5400ec94db5b7134ecacd50b100867d`)
replayed the lost control as byte-identical UNSAT in 3/3 observations at 0.10
seconds and below 17 MiB peak RSS; both allocation-abort controls and the
low-atom/31,944-variable IDL control retained typed pre-SAT declines. Formatting,
strict all-feature solver Clippy, all 1,091 solver-library tests, deep-input
16/16, online arithmetic/CDCL(T) 41/41, and both differential suites are green
with zero disagreement. Exact pushed checkpoint `3267432a7` then passed one
uninterrupted external-frontier `just check` in 6,410 seconds with exit 0; see the
[result](qf-linear-a5-pre-sat-boundary-monotonicity-v1-result-2026-08-10.md).

The `sc-39` classifier repair (`d646382e7`, gated at `b9938576b`) and the V2
DL repair (`d1b570f91c2`, full external-frontier `just check` exit 0) are
release-qualified. Exact-pushed `6d4718e13` completed fresh atomic QF_LRA and
QF_IDL captures — 90/200 and 70/200, six agreeing gains, zero losses or wrong
verdicts, all controls retained. QF_RDL is authorized but not started. Full
detail, including the rejected non-credited streams, is in the
[result](qf-linear-a5-idl-extended-dl-slice-v2-result-2026-08-11.md).

A3 is **WIP**. Pushed result checkpoint `3696e7dd5` is integrated on current
main by `47d8cd956`; its retired source tip is in the 2026-08-12 branch-cleanup
bundle. The repaired complete
67-row census
classifies 52 NIA-linearization budget declines, 13 former generic model-replay
declines, one verifier rejection, and one bounded giant-`distinct` ingest
decline. The ingest repair replaces a 4.36 GiB expansion abort with a typed
resource limit. The 13-row diagnostic proved that absent reconstruction models
were fabricated after typed oracle declines; `4ff9a82c6` preserves empty,
model, declined, and inconsistent outcomes separately. A preregistered exact
probe-model reuse experiment recovered zero of seven SAT targets, kept six
UNSAT controls non-SAT, and was rejected without retaining its code or
authorizing a 200-row run. The residuals are now split between five large
DPLL/core-search targets and two integer-model reconstruction-deadline targets.
The two-case reconstruction cluster is now rejected: both valid diagnostic
observations entered reconstruction after the shared deadline, dense Gomory was
size-inadmissible, and B&B ran zero nodes; a follow-up root-repair discriminator
shifted among earlier load-sensitive stops and never produced stable mechanism
evidence. No cap, deadline, route-order, or solver-code change was retained.
The repeated-large-core diagnostic then confirmed size-only admission in 3/3
direct `SAT14/1051` observations and 2/3 `SAT14/1280` observations. A separately
preregistered, sound four-group deletion pass shrank the broad clauses but
reduced `1051` from 192--202 to 35 lazy rounds and `1280` from 391--397 to 338,
without deciding either target. It was rejected at the two-target gate; all
temporary solver code was removed and no 200-row run was authorized.
The remaining small-core pair then received the cheaper preregistered
relevance-activated bound ladder. It emitted 470--472 checked implications on
`p4943` and 484 on `p32598` without extra theory-oracle calls, but all six target
observations remained `unknown`; the target gate failed and all temporary code
was removed. This closes the five-row DPLL/core-search partition against both
measured explanation-quality mechanisms. The 52 budget rows are now exactly
repartitioned into 37 width-ladder timeouts, 11 all-reference-SAT pre-lowering
clause-estimate refusals, three reference-UNSAT combined-theory timeouts, and
one reference-UNSAT replay-detected model overflow. Fresh discrimination shows
the four-row UNSAT tail is not a valid target for the SAT-only width ladder.
The bounded estimate-attribution route also closed without production code.
V1 exceeded its analysis-work cap; deduplicated v2 stayed bounded but its
fresh-parse estimates differed from the exactly reproduced live route by 24/39
clauses. The complete-record gate failed, so no mechanism or 200-row run is
authorized and the 64,000,000 ceiling is unchanged. A3 yields to A4.
The first aggregate A3 gate exposed one load-sensitive string/integer fixture:
a hidden two-second default deadline could return `unknown` before the known
`i = 500` witness under aggregate CPU contention. Commit `db7b426e8` removes
that implicit clock, retains the caller's explicit timeout, and uses
deterministic 128-candidate / 2,000-node ceilings. The repaired rerun passed
format, stable all-target Clippy, every workspace unit/integration/differential
test and doctest, the 1,078-test solver library, the repaired 14/14 coupling
fixture in 15.58 s, 9/9 isolated frontier tests, both order-255 CAS moment
proofs in 1,014.84 s, warning-denied rustdoc, QF_BV/reflection/Glaurung gates,
foundational resources, rules-as-code, the 165-test resume aggregate, and all
Lean contract suites. It then exited 1 in the final parity-docs stage because
the generated complete-parity manifest still hashed `.github/workflows/ci.yml`
before the pinned-`just` workflow repair. Commit `704318a5f` refreshes that one
source-identity SHA-256 without changing any outcome or parity claim; complete
parity-docs, plan authority, and links are green. Because the aggregate command
itself did not exit 0, a final exact-head rerun was required. That rerun at
`3586c41d9` exited 0 with the tracked tree clean: stable format and all-target
Clippy; every workspace test and doctest; the 1,078-test solver library; the
repaired coupling fixture; 9/9 externally stored frontier tests in 212.94 s;
both order-255 CAS moment proofs in 940.10 s; warning-denied rustdoc; QF_BV,
reflection, and both 162-file Glaurung policies with zero disagreement;
foundational resources; rules-as-code; the 165-test resume aggregate in 47.125 s
with one expected live-host skip; every Lean/process-free contract; parity docs;
plan authority; and links. The five 20 KiB external frontier artifacts and their
pointer were removed after recording the result. Topic `ee5042dee` was then
pushed, merged as `0c31baf97`, and independently passed the combined-main gate
described above. Exact-SHA hosted docs run `31192792512` and CI run
`31192792245` at later merge `bd413357c` are separately terminal green.

A2 is **DONE** on current main. The old
`agent/smtcomp/full-preparation-live` head `3e53ca631` is 401 commits behind
current main and was rejected as a whole. Four still-valid process-free code
increments and their R1--R4 contracts were ported; stale root tracker changes
were excluded. R5 exact-source build provenance is now implemented at topic
commit `e4bb854bf`: the live CLI has no caller-selected Axeyum binary, the
operator builds once from exact clean integrated source in a unique private
locked/offline two-job target, and preparation schema v3 retains and replays
the source/tool/output/binary/run/completion chain. The port passes 52 focused
tests with 82 subtests, the 165-test resume aggregate with one expected
live-host skip, the generated-contract check, and the scoped gate. A real
fixture-boundary build smoke produced a 14,208,408-byte binary with the
registered environment and removed its private target. The exact pushed topic
`2925efea556cab59251e690c9e4e449468865d2c` passed a clean, uninterrupted
`AXEYUM_PROGRESS_FRONTIER_ARTIFACT_DIR=<external> CARGO_BUILD_JOBS=2 just check`
with exit 0. All five frontier artifacts were written only to the external
directory, the worktree and tracked curves remained clean, and the local and
remote topic refs matched exactly. A prior direct
`CARGO_BUILD_JOBS=2 just check` passed every
code, solver, doctest, ignored moment-proof, rustdoc, profile, reflection,
benchmark, foundational-resource, rules-as-code, and SMT-COMP resume stage,
then exited 1 because its frontier stage used the historical tracked artifact
location and the later scoreboard check correctly rejected those volatile
curves. The exact committed curves were restored with no retained diff;
`just parity-docs plan-authority links` then passed cleanly. That earlier run
reproduces why the port's R3 external artifact isolation is required; the later
exact-topic gate closes the topic-only gap. Integration-owner review found the
20-commit topic strictly ahead of main with no divergence, and the synthetic
merge preview was conflict-free. Merge `8ed5ad089` integrated the reviewed
stack. Focused post-merge gates passed 52 readiness tests, the 165-test resume
aggregate, resume-contract generation, plan authority, links, and
`git diff --check`. That exact merge then passed one uninterrupted
external-frontier `CARGO_BUILD_JOBS=2 just check` with exit 0: workspace tests
and doctests, 9/9 frontier tests, both order-255 CAS moment proofs (939.24 s),
warning-denied rustdoc, both 162-file Glaurung policies, generated resources,
rules-as-code, SMT-COMP resume, Lean/process-free contract checks, parity docs,
plan authority, and links all passed. The five frontier artifacts were
external and the tracked tree remained clean. No host, NAS, sentinel,
allocation, live Lean, or solver action was performed. See the
[`A2 stale-branch audit`](smtcomp-a2-stale-branch-audit-2026-08-06.md)
and
[`R5 implementation result`](smtcomp-credited-full-preparation-f2-live-capture-r5-implementation-2026-08-06.md).
