# SMT-COMP credited full-population F2 external-input audit

Status: read-only C5 inputs match their frozen authorities; integration and
live F2 remain prohibited

Date: 2026-07-24

Implementation:
[F2 live-capture implementation](smtcomp-credited-full-preparation-f2-live-capture-implementation-2026-07-24.md)

## Objective and boundary

Reduce pre-integration uncertainty by checking the already-frozen C5 external
inputs without exercising any live-capture capability. This audit did not
build or run Axeyum, probe `s5`/`s6`/`s7`, take a thermal sample, run an
incident sentinel, create an F2 attempt, mutate the NAS, admit a preparation,
start an allocation, or launch a solver.

This is not C0 readiness and does not replace C5's full physical rehash after
the operator is integrated on exact clean green main. It records only that the
named read-only inputs were internally consistent at audit time.

## Selection and corpus evidence

The accepted selection root remained the exact content-addressed directory:

```text
/nas3/data/axeyum/harness/official-selection-2026-sq/accepted-322adaa78396bf42d4660d12582e6db1cf2166a765bb912fdfb179975a9c9698
```

The existing official-selection identity checker accepted the canonical
completion payload and reproduced these C5-consumed identities:

| Artifact | Bytes / rows | SHA-256 |
|---|---:|---|
| `complete.json` | 1,172 bytes | `322adaa78396bf42d4660d12582e6db1cf2166a765bb912fdfb179975a9c9698` |
| `official-selected.txt` | 4,066,816 bytes / 45,905 rows | `49744be7b373b2baef41289bfd5d2a7e59619db2859233e892b0592cd34a8b5b` |
| `selected-files.jsonl` | 11,096,728 bytes / 45,905 rows | `540fe29f2bc28e858b103fcd806eab709f58ed69b67d8cb95bd41bcdbaa87f39` |

A separate streaming structural pass checked all 45,905 selected-list and
ledger rows in lockstep. Every row was canonical, ordered, schema-valid, and
matched a present regular non-symlink corpus file of the recorded size. The
files totaled the frozen 15,148,369,947 bytes, from
`non-incremental/ABV/20190429-UltimateAutomizerSvcomp2019/alternating_list_true-unreach-call_true-valid-memsafety.i_4.smt2`
through `non-incremental/UFNIRA/20240414-funcprobs/prove/problem_U93.smt2`.
This pass intentionally did not rehash those 15.1 GB of payload bytes: the
live `materialize_full_selection` call must still do that after C0 and must
reproduce the preregistered full-list and v2-manifest hashes.

The canonical `corpus-audit.json` hash remained
`a086b77cce4d43db05a0bd6ef6b7752f207b141b82ef9c9c7825ca069df3faf5`.
Its seal and dependency chain revalidated:

| Artifact | SHA-256 |
|---|---|
| `archives.json` | `a7f5441bf9de832cc1f1043a53fbf6237a1c45ac6b3358c3fef40682203ad562` |
| `corpus.jsonl` | `a69e768f95a4a44a15c8d5690df2b91494f3e6b3e7d685b4285829d2386d0ad5` |
| `summary.json` | `386fae9d7c42d938bc4ed5a56e7c6fa0142cff9cee919ffaa857aadc9e0dbbef` |

The corpus root retained exactly one `non-incremental` directory with the 89
logic directories named by the summary. The authority still reports 450,472
files and 82,270,961,563 bytes with `selection_observed=false`.

## Repaired-P0, binaries, and sentinels

The registered `validate_repaired_p0_authority` path derived the comparison
again from:

```text
/nas3/data/axeyum/harness/official-selection-2026-sq/repaired-p0-prep-20260723-75e544a8-v2
```

It revalidated all frozen cell roots and matched the committed canonical
comparison byte-for-byte. The two external executable inputs remained regular,
executable, non-symlink files with their frozen identities:

| Input | SHA-256 |
|---|---|
| cvc5 | `7562a8b0b835e3eaad5f1a7b4616cd762350cf567b6be03d7e8ee24fa5ced5ee` |
| Bitwuzla | `d98164badcd34c12ccbbd9e5aab9373854bb187e79f99ccda4ec2aa9951c0eab` |

All three sentinel inputs also retained the preregistered bytes:

| Sentinel | SHA-256 |
|---|---|
| QF_ABVFP query 26 | `6f0b87776052d1770e8503bcc593ad842cc649d533c41fa4a898808397524b8b` |
| QF_BVFP query 26 | `31ce580816bfb0647001f64ef480cdd779fe2f31da320354ea1ea63cd9da34ae` |
| QF_AUFLIA pipeline-invalid | `dc7f8f51be688669321c8a9a15f2543fc070bc3a4c55b81c763604c34fa73bde` |

`target-codex/release/examples/smtcomp_cli` existed, but its July 23 mtime and
unregistered hash
`d705d700f67cf75c0510dd40b0a1a523ebea5f19acbb037ba24f2875475fb756`
make it stale, non-authoritative input. It was not executed. C5 must build a
fresh release binary from the exact integrated commit after C0 passes.

## Mutation and integration boundary

The shared
`/nas3/data/axeyum/harness/official-selection-2026-sq/credited-full-preparations`
parent was absent before and after the audit. No preparation or partial
attempt exists.

At the final ref check, local `HEAD`, the local topic, its tracking ref, and
the live remote topic all equaled
`79f5d31f69d6c312b0a22e00dbd5d44455e7f072`. Cached and live remote main both
equaled `08af3665e553aa1266e45aa46b6467f1ebc5551b`, and the topic was not an
ancestor of main. Therefore C0 still fails before its gate phase and none of
the clean external-input results authorize live capture.

## Exact next actions

1. Let the integration owner finish the independent exact-main repairs and
   establish a green main commit.
2. Integrate the corrected F2 topic, including R2 and the audited result
   closures, then run complete `just check` on the real combined commit.
3. Require clean equality of local `HEAD`, local `origin/main`, and live remote
   main before building the release executable.
4. Only then run the reviewed C5 command. Its full physical selected-byte
   rehash, host evidence, thermal samples, and eight sentinel executions remain
   mandatory inside the frozen window.
5. Verify any resulting `launch_authorized=false` root in a second process and
   integrate that exact result before considering F3 acceptance.
