# QF_NIA A3 causal census attempt v1 — invalidated by ingest abort

## Verdict

The v1 census is **invalid and must not be analyzed, resumed, concatenated, or
credited**. The exact-list process emitted 59 of 67 records and then aborted on
row 60. No causal bucket or implementation cluster may be selected from that
prefix.

The invalid partial file was
`/tmp/axeyum-qf-nia-a3-trace-v1.jsonl`: 59 lines, 76,366 bytes, SHA-256
`3a8c7d5013e050dad20ec7226baf9e4e2909509cbe1aed9062d36970986f714f`.
It remains temporary failure evidence only; the hash does not make an
incomplete population admissible.

## Failure

The exact failing row was row 60:

```text
/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/QF_NIA/20210219-Dartagnan/ReachSafety-Loops/array_3-1-O0.smt2
```

The process terminated with exit 134 under the preregistered 8 GiB wrapper:

```text
memory allocation of 4362076176 bytes failed
```

The row reproduced the same abort 1/1 in isolation, proving this was not a
cumulative leak from the preceding 59 cases.

## Root cause

The 10,002,338-byte source contains 99,421 top-level commands and 1,676,894
S-expression nodes. The iterative reader and every command through index 99,413
completed. Command 99,414 is the first giant assertion and contains a
16,525-argument integer `distinct`. The parser eagerly lowered it into
136,529,550 pairwise disequalities, approximately 409 million interned
equality/not/and nodes, without an admission ceiling. The abort occurred while
the term interner grew for that expansion.

## Repair evidence

Commit `63c82a6ef113bba8cf80fa6871674d9c4514c1f9` implements ADR-0378:

- 65,536 deterministic pair-expansion ceiling;
- full sort validation and exact duplicate short-circuit;
- balanced conjunctions for admitted expansions;
- `SmtError::ResourceLimit` mapped to `UnknownKind::ResourceLimit`;
- explicit `ingest-resource-limit` JSONL records in `explain_corpus`.

The original row now exits 0 under the same 8 GiB wrapper in 1.22 seconds at
148,272 KiB peak RSS:

```json
{"status":"ingest-resource-limit","verdict":"unknown","detail":"`distinct` with 16525 arguments requires 136529550 pairwise expansions; deterministic limit is 65536"}
```

Focused evidence at the repair commit is 228/228 SMT-LIB tests, 98/98 solver
text-front-door tests, 3/3 `explain_corpus` tests, affected-crate all-feature
Clippy, plan authority, and links. These gates establish the repair boundary;
they do not retroactively validate the v1 trace.

## Disposition

The parser policy changed after v1 preregistration, so v1 cannot simply restart
under the old label. A versioned v2 protocol must bind the fixed binary, accept
only complete route traces or explicit ingest-resource-limit records, and run
all 67 rows fresh from row 1.
