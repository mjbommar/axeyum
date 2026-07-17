# ADR-0210: Exact ordered timeout-continuation replay

Status: accepted
Date: 2026-07-16

## Context

ADR-0209 keeps Glaurung's one-check same-session timeout continuation
off-by-default because neither a wall-time run nor a fixed function prefix held
the authoritative query and finding streams constant. One bounded Z3
nondecision changed the explorer worklist even when both processes completed
the same 156 functions. The existing Glaurung ordered-trace v1 artifact already
captures the exact occurrence order, assertion scopes, query bytes, lineage,
model choices, and per-backend outcomes needed for a fixed-stream experiment.

The replay gate must also incorporate the client measurement rule that a faster
error or `Unknown` is not a solver win. A validation replay and a production
timeout experiment therefore cannot silently share one convenient timeout.

## Decision

Extend the independent `glaurung-ordered-trace` consumer with an explicit
bounded-policy replay control, while leaving Glaurung's production default
unchanged.

- `--timeout-ms` remains the mandatory strict parse/verdict/model-choice
  validation budget.
- `--policy-timeout-ms` is a separate explicit budget for `--snapshot` or
  `--lineage`. It reports every recorded-decided/Axeyum-nondecided split while
  keeping any SAT-versus-UNSAT disagreement fatal.
- `--continue-on-unknown` grants exactly one additional check on the same
  retained `IncrementalBvSolver`, under a fresh instance of the same policy
  budget. A second `Unknown` or operational error preserves the original
  `Unknown` and is counted separately.
- Control and candidate run as separate processes over the same manifest and
  event hash. Their check count and recorded stream are therefore identical;
  policy outcomes, continuations, time, retained structure, and process RSS
  remain explicit.

Do not infer a native Glaurung default merely from an independent snapshot or
naive-lineage replay. Admission still requires the production topology and
existing time, ratio, RSS, reset, replay, finding, and variance gates to agree
with the mechanism result.

## Evidence

The fail-closed boundary has 11 focused tests. It requires an explicit retained
replay policy and policy budget, preserves an original `Unknown` after a
repeated timeout or continuation error, accepts a recovered SAT/UNSAT result,
rejects opposite decided verdicts and recorded operational errors, and never
hides a bounded nondecision in the default strict replay. The compact identities
are order/count/field sensitive; fork, missing-assertion, model, and snapshot
scope tests exercise the reconstructed event state machine.

The final 8-function smoke validates 2,038 unique queries and replays all 2,519
exact checks (1,719 SAT / 800 UNSAT) with zero disagreements under both
policies. No 250 ms nondecision occurs on this bounded prefix, so it is a
resource/functionality gate rather than continuation evidence. Executable
SHA-256 is
`77f63aa5b4dcfa7c74718c9537f29120a8647026f8485e45b867b1ae9474a8dd`.

The first fixed-prefix trace exposed a resource defect in the producer rather
than useful continuation evidence: recursive SMT-LIB rendering expanded shared
expression DAGs into a 35 GiB query store. Glaurung `3c3c77e` replaces that
tree renderer at every trace/text boundary with deterministic nested `let`
bindings. Postorder ordinal names preserve byte identity across pools whose
internal `ExprId`s differ, and the focused linear-size, cross-pool identity,
pipe, text-bridge, and producer/validator tests pass.

The clean `3c3c77e` producer then completes 156/338 tcpip functions under 4
GiB in 14m22s at 465,708 KiB maximum RSS. It records 70,823/70,823 shadow
agreements, zero decided disagreements, 782 high-confidence findings, and a
3.8 GiB ordered trace containing 301,852 events, 15,501 paths, 70,823 checks,
50,429 unique queries, 9,860 assertions, and 27,731 model reads. The producer
validator independently accepts the complete artifact under the same memory
ceiling. Manifest/event/query-index SHA-256 identities are respectively
`1b4a05706778851d3389b41e9894a2c7350e6bdbcf2d73eeae60b51fdb87d3f2`,
`d64570096beb6bb0f43064d8698ccdbd3349f14a6dc1811b4a03be264eb7ca3b`, and
`ccb36684aee26c40165caba7d90f6f10c4db93b7543062f409bc053f9953ff7c`.

The no-continuation control validates all 50,429 unique queries and 25,403
unique model choices, then replays the exact 70,823 occurrences under the 250
ms lineage policy. It observes 46,152 SAT / 24,658 UNSAT / 13 `Unknown`, with
70,768 exact recorded outcomes, eight recorded-decided/observed-nondecided
splits, 47 recorded-nondecided/observed-decided splits, and zero decided
disagreements. All 27,731 model reads evaluate (27,214 recorded-value matches,
517 valid divergences); no assertion or fork root is unmaterialized. The warm
pass takes 188.646 s including 53.128 s in checks, or 0.570451x recorded Z3
including the shared-arena build. It reaches 1,417,699 live AIG nodes,
1,424,451 CNF variables, 1,753,678 clauses, 44 live paths, and 1,262,596 KiB
external maximum RSS. The complete process takes 24m28s; its 394 deterministic
query-validation workers peak at 236,052,480 bytes.

The continuation candidate binds the same manifest, event stream, validation
budget, policy budget, and replay executable. Its event/query/model counts,
recorded and strict-validation outcomes, scope operations, retained roots,
peak paths/AIG/CNF structure, and complete model-read evaluation match the
control exactly. Fourteen initial policy checks return `Unknown`; one fresh
same-instance check recovers one SAT and six UNSAT results, repeats seven
`Unknown`s, and encounters zero continuation errors. The final candidate is
46,152 SAT / 24,664 UNSAT / 7 `Unknown`, with zero decided disagreements,
70,770 exact recorded outcomes, four recorded-decided/observed-nondecided
splits, and 49 recorded-nondecided/observed-decided splits.

Candidate warm replay takes 192.356 s, +1.97% over control, including 53.315 s
of initial checks and 2.421 s of continuations. Its measured ratio is 0.581590x
recorded Z3, +1.95%, and external maximum RSS is 1,263,024 KiB, +0.034%. The
complete 24m31s process is +0.16%. All are inside the existing 3% warm-time /
5% RSS alarms. The control observes 13 initial `Unknown`s while the candidate
observes 14, which is ordinary bounded-runtime variance; the causal mechanism
claim is the candidate's seven decisions after an already-observed initial
`Unknown` on the same solver and exact occurrence, not identical timeout
scheduling across separate processes.

## Alternatives

- Repeat another live explorer pair: rejected because authoritative timeout
  steering has already defeated both wall-time and fixed-function identity.
- Use one 250 ms timeout for both validation and measurement: rejected because
  a policy timeout could prevent independent validation of a sound recorded
  query or model choice.
- Treat `Unknown` as a mismatch or silently skip it: rejected because
  `Unknown` is a first-class bounded result and decided-rate is part of the
  evidence.
- Continue more than once or without a deadline: rejected because it changes
  the deterministic resource contract under test.

## Consequences

ADR-0209 gains a passing causal same-stream mechanism gate without weakening
strict query validation or claiming that replay topology equals the live
explorer. The additional CLI and JSON fields remain opt-in and do not affect
ordinary solver constructors, cold corpus gates, or Glaurung defaults. Native
admission now routes to a production-topology repeat with exact traffic and
finding identity plus the existing time, ratio, RSS, reset, replay, and
variance gates. The seven residual candidate timeouts remain explicit
`Unknown`s and are the bounded SAT-attribution set; they are not converted to
errors or UNSAT.
