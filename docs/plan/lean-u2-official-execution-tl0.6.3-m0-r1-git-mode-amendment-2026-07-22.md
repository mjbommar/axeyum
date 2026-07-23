# TL0.6.3 M0 R1 amendment — live evidence mode versus Git checkout mode

Status: **preregistered; no R1 harness or test process has run**

Date: 2026-07-22

Parent work:

- [`M0 plan`](lean-u2-official-execution-tl0.6.3-m0-plan-2026-07-22.md)
- [`attempt 001`](lean-u2-official-execution-tl0.6.3-m0-attempt-001-2026-07-22.md)
- [`R1 plan`](lean-u2-official-execution-tl0.6.3-m0-r1-plan-2026-07-22.md)

## 1. Reason for the amendment

The R1 plan requires the failed-attempt validator to reject a writable
evidence file. That is valid for the live immutable-store installation, but it
cannot be a portable property of a committed Git checkout. Git tree/index mode
`100644` distinguishes a regular non-executable file from `100755`; it does not
encode the difference between filesystem modes `0444` and `0644`. The
[Git index documentation](https://git-scm.com/docs/user-manual#the-index) shows
ordinary files as `100644`, and the
[`core.fileMode` documentation](https://git-scm.com/docs/git-config#Documentation/git-config.txt-corefileMode)
describes Git's working-tree mode tracking in terms of the executable bit.

Repository-local evidence confirms the mismatch:

- the 18 attempt-001 files were installed and remain `0444` in this live
  worktree;
- `git ls-files --stage` records each as `100644`; and
- `git archive HEAD` consequently exports them as writable regular files.

A normal clone, checkout, archive, or CI workspace therefore cannot reproduce
the live owner-write bit. Requiring `0444` in offline CI would reject valid
content solely because Git reconstructed the only regular-file mode it stores.

## 2. Amended validation rule

This amendment narrows only the R1 plan's word **writable**. All other frozen
identities, byte counts, hashes, seal rules, path closure, symlink rejection,
retry bounds, resource controls, and credit rules remain unchanged.

Validation is split into two explicit phases:

1. **Live installation/execution validation.** Before R1 starts, the runner
   must observe every attempt-001 evidence path as a regular, non-symlinked,
   `0444` file. Every new R1 evidence file must be installed without overwrite,
   changed to `0444`, and revalidated before the run may publish a dependent
   record. The R1 prelaunch/final authority must record that this live mode gate
   passed.
2. **Committed checkout/offline validation.** The validator must require the
   exact 18-path set, regular-file Git mode `100644`, no Git symlink entries,
   exact bytes and content hashes, accepted UTF-8 physical JSON, frozen legacy
   seals, 4,757,134 total bytes, and the frozen manifest digest. It must not
   inspect or reject the checkout's owner-write bit.

The live mode observation is execution evidence; the Git tree and sealed
manifest are the durable content authority. Neither phase may infer semantic
case completion from the failed attempt.

## 3. Required gates before execution

R1 implementation tests must prove both halves independently:

1. live validation rejects `0644`, a symlink, or a non-regular path;
2. offline validation accepts the same byte-exact fixture at ordinary Git
   checkout mode and rejects path, Git-mode, byte, hash, seal, or manifest
   drift;
3. the prelaunch record cannot validate unless the live failed-attempt mode
   gate passed; and
4. no mode result creates an official outcome, parent/provider completion,
   Axeyum result, pair, performance row, axis, gate, or parity credit.

## 4. Execution boundary

This amendment changes no Lean command, worker setting, address-space limit,
timeout, selected case, source/toolchain identity, artifact allowance, attempt
sequence, or stop condition. The R1 implementation still must be committed and
pushed before the one allowed `attempt-002` test process runs.
