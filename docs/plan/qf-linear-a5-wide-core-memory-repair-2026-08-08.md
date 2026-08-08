# QF linear A5 wide-core memory repair — 2026-08-08

## Verdict

The first preregistered QF_LRA A5 capture failed closed and exposed a P0
process-abort defect. The exact pushed and fully gated revision
`1de73748877253d6d134d71af3b5d22183c646d4` emitted 172 of 200 rows, then
`sal/tgc/tgc_io-safe-20.smt2` reached the external 8 GiB address-space ceiling
and aborted with `SIGABRT`. QF_IDL and QF_RDL were not started.

The candidate repair at `9d7a70a65` adds a deterministic 8,192-literal budget
for dynamically retained unminimized arithmetic-theory cores. Exhaustion now
returns `Unknown(ResourceLimit)` before the next warm SAT round. This is a
process-survival repair, not a newly credited A5 gain: the row was historically
`unknown`, and the complete three-division census must restart from row 1 only
after the repaired exact commit is clean, pushed, and comprehensively gated.

## Failure evidence

- Frozen list: `QF_LRA.txt`, 200 rows, SHA-256
  `b636239947db1e65f2665a62fca8f852acdcd459c799a9bb326c718a1d1d8da5`.
- Capture binary: 11,698,408 bytes, SHA-256
  `0cc1a0ff3d62ce8bc59e4eaaecaa79de1f6c51e1e4f89c7711c0f2d62d2d6943`.
- Non-credited failure record:
  [`QF_LRA-attempt-001.failure.json`](evidence/qf-linear-a5/failures/QF_LRA-attempt-001.failure.json),
  SHA-256
  `83f9cbf7acb43fc0cc86f710b6a6fa8e31bcfde748b9ee05d894e144aa8cd753`.
- Terminal facts: 697,127 ms, 172 rows, exit `-6`, 118 stderr bytes; the
  partial stdout was not published as a result.
- Trigger file: 75,229 bytes, SHA-256
  `8700a40350b6d721a0537ff1b0328bf0d98a272a8923c32f57a31128a2e375d8`.
- Isolated reproduction under the same 8 GiB cap printed
  `memory allocation of 13824 bytes failed` and exited 134. Per-second process
  observation showed resident memory rise through roughly 1.7, 2.3, 5.0, 7.7,
  and 8.38 GiB before aborting; this was allocation growth, not a malformed
  stream or outer timeout.

## Root cause and repair boundary

The exact row has 1,411 linear-arithmetic atoms and a large Boolean skeleton.
The `lira-dpll` route repeatedly found valid but unminimized theory conflicts of
roughly 428--443 literals. At a 10-second diagnostic budget it retained 24 such
clauses and returned typed `unknown`, with about 1.78 GiB peak RSS. Under the
standard 24-second budget, a later incremental `BatSat` round accumulated
learned state faster than its cooperative deadline callback was polled and hit
the process ceiling.

The repair counts only literals in `ArithCoreSource::Large` conflicts. Small,
bound, difference, affine, LP, and deterministically minimized cores do not
consume the new ceiling. Once the total reaches 8,192, the lazy arithmetic
driver returns `Unknown(ResourceLimit)` before another SAT solve. The counter is
derived solely from stable core lengths, so admission is deterministic across
machines and cannot fabricate SAT or UNSAT.

## Focused evidence

After the repair and the merge of current `origin/main` at `8ccae9c43`:

- the exact 24-second/8-GiB trigger returns exit 0 in 6.08 seconds with a
  schema-1 trace, `unknown`, route `lira-dpll`, reason `budget`, 19 large cores,
  8,224 retained large-core literals, and peak RSS 1,777,884 KiB;
- merged release `explain_corpus` SHA-256 is
  `27934e11c76a6af5f9261884d0d053f5055c630f940780332a0c18111c590a38`;
- the load-bearing wide-core guard and counter unit tests pass with
  `--features full` (the first default-feature invocation ran zero tests and is
  explicitly non-evidence);
- strict all-target/all-feature solver Clippy passes;
- all 1,079 all-feature solver library tests pass;
- deep-input no-abort passes 16/16;
- QF_LRA differential fuzz passes 5/5 with zero disagreement; and
- simplex LRA fallback differential passes 1/1 in 114.81 seconds with zero
  disagreement.

These focused results establish the root-cause repair but do not establish
population monotonicity or replace a fresh full `just check`.

## First full-gate attempt

Exact pushed commit `57e85608a9cfab0bb82b219b826da8f17efb937e`
passed the complete workspace test and doctest population, all 1,079 solver
library tests, retained differential suites with zero disagreement, 9/9
capability-frontier tests, both order-255 CAS proofs, warning-denied rustdoc,
the 162-file Glaurung gate, foundational resources, and the 165-test SMT-COMP
resume aggregate. It then failed closed in the final parity-doc stage because
the gap-ownership manifest omitted `--features full` while the generated guide
retained the required non-vacuous command. The gate exit was 1 and is not
credited as comprehensive green. The full log SHA-256 is
`a4683f742fd0594cc968cb10712879aeaf3190e5216416a1f4838d6711a326ed`.

The repair adds `--features full` to `docs/plan/gap-ownership-v1.json`; the
already-correct generated guide remains byte-identical. The manifest repair
was committed as `b07be65aa`. A fresh uninterrupted frozen `just check` at that
exact pushed commit completed with exit 0. Its log SHA-256 is
`dd82f231c01c0c6febf391650843e754bd10582f47803365adade33af5504cd9`;
the previously failing `gen-gap-ownership.py --check`, independent
`check-parity-docs.py`, plan-authority check, and link check all passed.

## Second capture attempt: valid mixed-sort `ite`

The row-1 QF_LRA restart at `b07be65aa` completed the process successfully in
891,888 ms and emitted all 200 rows without stderr or an abort. Atomic
validation still failed closed because
`sal/gasburner/gasburner-prop3-12.smt2` returned `parse-error` instead of its
historical decided state. The stream is not credited. The exact record is
[`QF_LRA-attempt-002.failure.json`](evidence/qf-linear-a5/failures/QF_LRA-attempt-002.failure.json),
SHA-256 `e1af0be595aef8bf035f7e35391158b713db3791d31f6aa19791899d8ccb28b8`.

The parser already applies SMT-LIB Int-to-Real coercion to mixed arithmetic,
comparisons, equality, and declared Real constant bodies, but the shared `ite`
operator required exactly equal branch sorts. The benchmark contains the valid
Real-valued shape `(ite ?v_88 ?v_93 0)`, where `?v_93` is Real and the bare
numeral was parsed as Int. The candidate parser repair gives the two `ite`
value branches one common numeric context: integer constants become exact Real
constants and symbolic Int terms use the existing exact `to_real` embedding.
An isolated replay now parses and returns typed `unknown` through the existing
wide-core budget (42 rounds, 8,371 retained large-core literals), rather than a
parse error. Focused parser coverage is 230/230 with strict all-feature Clippy
green; the complete capture must restart from row 1 after the repair is pushed.

## Third capture attempt: first-solve propositional growth

The parser repair was committed and pushed as `11deff4ee`. Its pre-push gate
passed the workspace library, full-feature frontier, and parser/front-door
integration suites. The next row-1 QF_LRA restart still failed closed after 168
rows: `sal/pursuit/pursuit-safety-16.smt2` aborted at the 8 GiB process ceiling
before emitting row 169. The non-credited exact record is
[`QF_LRA-attempt-003.failure.json`](evidence/qf-linear-a5/failures/QF_LRA-attempt-003.failure.json),
SHA-256 `e8633274661c65d344d28af7888a76a9615d131f41099ef04fbd76cd84ee5643`.

This is distinct from the repeated-wide-core defect. Isolated reproduction
aborted in 6.39 seconds at 8,377,860 KiB peak RSS. Temporary environment-gated
instrumentation showed 1,447 arithmetic atoms, 4,733 propositional CNF
variables, zero initial theory clauses, and only two dynamic blocking clauses:
rounds 0 and 1 returned, while the third warm `BatSat` solve allocated past the
ceiling before its deadline callback ran. The instrumentation was removed.

The candidate repair adds a joint deterministic pre-SAT boundary: decline only
when both arithmetic atoms exceed 1,024 and CNF variables exceed 4,096. Neither
large flat arithmetic nor a large mostly-Boolean skeleton alone is refused. The
boundary returns typed `Unknown(ResourceLimit)` before the first SAT round. In
one 8-GiB process, isolated `pursuit-safety-16`, repaired
`gasburner-prop3-12`, and the original `tgc_io-safe-20` all returned typed
budget unknown in 6.11 seconds total at 625,076 KiB peak RSS; their stable
pre-SAT counts were respectively 1,447/4,733, 396/below-boundary, and
1,411/6,774. The joint-boundary and wide-core load-bearing tests each execute
1/1; strict all-feature solver Clippy, all 1,080 solver-library tests,
deep-input no-abort 16/16, QF_LRA differential fuzz 5/5 with zero
disagreements, and simplex LRA fallback differential 1/1 in 108.55 seconds are
green.

## Required continuation

1. Commit and push the focused-green joint pre-SAT repair with the third failure
   record, then verify `HEAD == upstream`.
2. Restart QF_LRA from row 1 under the original A5 protocol. Any historical
   decision loss, wrong verdict, stderr, malformed trace, or process failure
   stops the sequence.
3. Only after QF_LRA publishes valid success metadata may QF_IDL and QF_RDL run
   sequentially, followed by the preregistered derivation.

The failed partial stream is permanently non-credited. No timeout, external
memory ceiling, route order, normalization ceiling, DL allocation, or reference
result changed.
