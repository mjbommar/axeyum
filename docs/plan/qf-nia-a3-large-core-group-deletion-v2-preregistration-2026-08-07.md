# QF_NIA A3 large-core group-deletion v2 preregistration — 2026-08-07

## Evidence boundary

The
[`v1 result`](qf-nia-a3-large-core-cluster-v1-result-2026-08-07.md)
meets its mechanism-selection gate. `SAT14/1051.smt2` reproduced hundreds of
size-admission cores in 3/3 direct observations; `SAT14/1280.smt2` did so in
2/3. Their broad cores occupy different fixed buckets but share the same
downstream behavior: hundreds of large blocking clauses accumulate in one warm
Boolean skeleton before the query budget is exhausted.

This document authorizes one bounded A/B implementation experiment. It does
not authorize a general cap increase, a new deadline, a route-order change, or
a whole-list run.

## Mechanism

When all of the following hold:

1. the integer or real theory oracle has already proved the current index set
   `unsat`;
2. no cheap bound, difference, affine-bound, or LP-relaxation core was found;
3. the index set exceeds the existing 128-atom deletion-minimization guard; and
4. the shared query deadline has not passed;

perform one deterministic balanced group-deletion pass before returning a
`Large` core:

- partition the original stable index order into exactly four contiguous,
  near-equal groups using integer range boundaries;
- visit groups from lowest to highest index;
- for each group still represented in the current core, construct the current
  core without that group;
- remove the group only when the existing deadline-bounded theory oracle
  returns `Unsat` for the nonempty trial;
- retain the current core on `Sat`, `Unknown`, or deadline expiry, and stop
  probing once the shared deadline passes.

The exact additional work bound is at most four theory-oracle calls per
otherwise-`Large` conflict. There is no retry, second pass, adaptive group
count, elapsed-time threshold, randomization, or fixture-specific behavior.
The starting core is already inconsistent, and a group is removed only after
an independent `Unsat` result, so every emitted clause remains sound even if
the pass stops early.

If the result remains above 128 atoms, return it as a `Large` core. If it is at
or below 128 atoms, return it as a distinct `Grouped` source; do not invoke the
existing atom-by-atom minimizer in the same round. This keeps the new work
bound at four oracle calls and makes attribution explicit.

## Measurements

Add verdict-neutral aggregate counters for:

- group-deletion attempts and oracle calls;
- groups and atoms removed;
- grouped-core count and final fixed size buckets;
- passes stopped by the shared deadline.

These counters may appear only under
`AXEYUM_NIA_LARGE_CORE_DIAGNOSTIC`. Do not record literal identities, terms,
models, per-call timings, or any data that changes policy.

## A/B targets and controls

The A/B targets remain the exact ordered v1 target list, SHA-256
`09d46491340903af0181bde3cf8f08af073268b1b62bc937349d4eab5aecde17`.
Baseline is the six observations in the v1 result.

Mandatory controls are unchanged:

- routing-control list SHA-256
  `df0e044140a72a4e8fa0eb733745e9d7b91e2f6b014b586fb0302ee34403a05b`;
- six reference-UNSAT controls SHA-256
  `cf8d03e83b237aeea2413bf23b317b590429c40f08e0d955e8b50824212014e3`;
- all 34 retained QF_NIA decisions from the bound sidecar;
- the ADR-0378 giant-`distinct` process-survival row;
- existing small-core, model-replay, typed-decline, opaque-UF, and core-
  minimization unit tests.

## Acceptance and stop conditions

The first gate is one direct run of each target under the unchanged 8 GiB and
24,000 ms protocol, followed by a second confirming run for any apparent SAT
gain. Retain the implementation only if:

1. at least one target becomes SAT in both confirming runs;
2. every gained SAT model replays all selected literals and original
   assertions;
3. no target or control produces a wrong SAT, replay failure, crash, or memory
   breach;
4. all 34 prior retained decisions remain identical; and
5. focused solver tests and the mandatory control lists are green.

Reject and remove the implementation if neither target gains, if extra theory
work merely moves both stops earlier, or if a prior decision is lost. A fresh
200-row QF_NIA run is authorized only after the two-target gate, confirming
runs, and every mandatory control pass. The full `just check` remains a
pre-merge gate, not an experiment-loop command.
