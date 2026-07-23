# Lean complete-parity current-source identity R7 plan

Date: 2026-07-23

Status: **preregistered offline merge-drift repair; no process, outcome, or
parity credit authorized**

Owner: complete Lean parity lane, historical/current source-identity boundary

Extraction base: `308f7676eca707e06c54cf182eb85d06049d889c`

Contract:
[complete Lean 4.30 parity](lean4-complete-parity-contract-2026-07-22.md)

## 1. Trigger

The ROOT-relative worktree-portability repair and the complete-parity stack
landed together on `main` at `27828c40`. At that exact tree, the focused,
relocated-checkout, parity-document, link, workspace, and Glaurung validation
gates passed.

A later legitimate SMT-COMP repair, commit `9e578a58`, changed the shared
filesystem primitive
`scripts/smtcomp_repro/resume_fs.py` from SHA-256
`1968e7b6424c2dd9273bff5041e96fc21b83ec01b2205dcc840d5dc942be1aec`
to
`b05c32185d75d5790f26ba25b6891c373712a565942400f4b08fa49bdc3c0ea6`.
It added a keyword-only `eligible_targets` filter to
`recover_orphan_temporaries`. The default remains `None`, so the Lean store's
existing call retains the prior all-temporary recovery behavior. The atomic
install functions imported by the Lean acceptance and U2 validators did not
change semantically in this commit.

Current `just parity-docs` consequently stops at the one exact failure:

```text
test_preregistered_source_identities_are_frozen
expected 1968e7b6...; observed b05c3218...
```

The SMT F1 result independently reports the same boundary. This is a semantic
merge drift between immutable historical source rows and a reviewed current
compatible successor. It is not the earlier worktree-path defect, evidence
corruption, or a changed Lean observation.

## 2. Identity model and authorized repair

R7 must preserve two distinct identities:

1. **Historical evidence-producing identity.** Keep `1968e7b6...` in every
   frozen authority/source-input collection. Retained TL0.7.3, TL0.7.4, and
   TL0.6.3 result authorities must reproduce byte-for-byte.
2. **Current repository identity.** Admit only exact current SHA-256
   `b05c3218...` in the live store test, TL0.7.4 current repository inputs, and
   TL0.6.3 current repository-input overrides. Arbitrary future bytes, a
   missing file, and mutation to either historical or current identity must
   still reject.

Because the current TL0.6.3 base validator changes, the downstream M2 validator
must update only its current override for that base validator. Its historical
input remains unchanged. The complete-parity generator may refresh only the
content identities of changed current validator/test sources and generated
summaries.

Authorized implementation files are:

- `scripts/lean_execution_acceptance.py`;
- `scripts/lean_u2_official_execution.py`;
- `scripts/lean_u2_official_execution_m2.py`;
- their three directly affected test modules; and
- generated complete-parity summaries whose current-source identities change.

`scripts/lean_execution_store.py`, `scripts/smtcomp_repro/resume_fs.py`, all
accepted JSON authorities, and every retained evidence root are read-only for
R7. The store test may distinguish the historical row from the current live
primitive without changing either.

## 3. Required controls

The implementation must prove all of the following:

1. Git bytes at `27828c40` hash to the historical primitive identity and Git
   bytes at `9e578a58` plus current `origin/main` hash to the exact successor;
2. current repository-input validation passes for store, acceptance, U2, and
   M2;
3. focused mutation controls reject a different current primitive identity;
4. reconstructed historical acceptance and U2 source-input rows still contain
   `1968e7b6...`, never `b05c3218...`;
5. every accepted authority and retained-evidence aggregate digest is unchanged;
6. focused store, acceptance, U2, M2, complete-parity, and SMT filesystem tests
   pass;
7. `python3 scripts/gen-lean-complete-parity.py --check`, `just parity-docs`,
   and `just links` pass in the owning worktree;
8. the same complete-parity check passes from a clean detached worktree rooted
   at a different absolute path; and
9. `git diff --check`, pathspec commits, push, and local/tracking/remote equality
   complete before handoff.

The evidence-directory aggregate digests and accepted authority file hashes
will be captured before implementation and compared afterward. Any authority
or retained-evidence byte change, unenumerated source successor, relocated-root
failure, external process launch, or nonzero parity-credit change stops R7.

## 4. Resource and execution boundary

R7 is offline validator/documentation work. It does not authorize Lean,
Axeyum, M2.1--M2.7, solver, network, retained-evidence, installer, exporter, or
toolchain execution. Unit tests may use temporary synthetic fixtures only.

No SMT-COMP implementation file is edited. The SMT lane owns the successor
primitive and its live-run policy; R7 consumes only the exact reviewed current
identity already integrated on `main`.

## 5. Nonclaims and next step

R7 restores a green cross-lane identity gate. It adds no official Lean or
Axeyum outcome, dependency edge, native-support fact, matched pair,
performance row, completed U0--U9 population, completed A0--A11 axis,
satisfied G1--G10 gate, or parity credit.

After R7 is integrated and current `main` is green, the complete-parity lane
still requires explicit authorization before the preregistered TL0.6.4 M2.1
execution. M2.2 and every downstream native comparison remain separate later
steps.
