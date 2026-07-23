# Lean complete-parity current-main integration R2 plan

Date: 2026-07-23

Status: **preregistered integration correction; no process or parity credit**

Owner: complete Lean parity lane, retained-evidence portability boundary

Base: `ec1e469680ee3aaed6efc66484969fdc08dc3053` (`origin/main` at extraction)

## 1. Purpose and boundary

The accepted worktree-portability repair is buried in the divergent complete-
parity topic stack while shared `main` still fails its docs job at:

```text
LEAN_PROCESS_ATTEMPT_ERROR|exit-zero-4g: run/spec attribution drift
```

This plan prepares one minimal integration branch from current `main`. It must
carry only the prerequisite historical/current acceptance-input split and the
four accepted ROOT-relative repair commits. It does not merge the broader Lean
parity stack, run Lean or Axeyum, change retained authority/evidence bytes, or
create an outcome, pair, performance row, completed axis/gate, or parity credit.

The extraction order is:

1. merge-drift preregistration and implementation (`959374cf`, `d51650e4`);
2. retained process attribution (`c3f068ea`);
3. retained store process attribution (`09e1dcd2`);
4. clean tracked Git permission representation (`2267f41b`); and
5. historical replay/current result generation separation (`98d85098`).

The prerequisite is mandatory: current `main` does not contain
`CURRENT_REPOSITORY_INPUTS`, so applying the process fix alone would merely
move the first failure from process attribution to the changed pinned-Lean
installer identity.

## 2. Newly exposed current-main drift

After the ordered extraction, the exact process result and 60 process/store/
acceptance tests pass. The first complete-parity check reaches the U2 official
result builder and rejects one different current input:

```text
frozen repository input drift: scripts/smtcomp_repro/resume_contract.py
```

The retained U2 authority records historical SHA-256
`4713707b26d81e0e5444acc7c653b461fa79c2a94c392873c8565b443ba33930`.
Current `main` contains SHA-256
`c128444f940b04a99a5be5def253d56df9f17d488dcb2d739891b0085dd0efd7`
from SMT-COMP commit `60f98ae9`, which adds
`solver_environment_sha256` to the run-identity/configuration projection.

The U2 runner imports only `canonical_bytes` from this module. That function
and the retained evidence are unchanged. The two-line SMT-COMP successor is a
strictly stronger current validation contract, not an input used to reconstruct
historical U2 bytes.

## 3. Exact correction

R2 must:

1. keep the old resume-contract digest in `REPOSITORY_INPUTS`, so historical
   result `source_inputs` remain byte-for-byte reproducible;
2. add only the exact current digest to
   `CURRENT_REPOSITORY_INPUT_OVERRIDES`, so live validation admits this reviewed
   successor and no arbitrary future file;
3. add a focused regression proving current repository validation succeeds
   while a rebuilt retained authority still emits the historical digest; and
4. reject a different current digest, missing input, or changed historical
   result source row through the existing fail-closed validators.

No accepted JSON authority or evidence root may be regenerated. Generated
complete-parity reporting may update only its content identities for current
validator/test sources.

## 4. Required gates

Before handoff, the current-main branch must pass:

1. focused process, store, acceptance, U2 official, and M2 replay tests;
2. exact retained process/store/acceptance/U2 result checks;
3. `python3 scripts/gen-lean-complete-parity.py --check` in the integration
   worktree and a differently rooted detached worktree;
4. `just parity-docs` and `just links`;
5. the repository green-before-merge command `just check`; and
6. clean local/tracking/remote equality after path-scoped commits and push.

Any historical authority diff, unexplained current-input override, external
process launch, test failure, generated drift, link failure, or dirty replay
stops the handoff.

## 5. Nonclaims

This work repairs validation portability and integration ordering only. It
does not make TL0.6.3 or TL0.6.4 complete, authorize TL0.6.5 execution, validate
SMT-COMP solver results, or advance any Lean complete-parity counter.
