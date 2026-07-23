# Lean U2 TL0.6.4 M1 R2 plan — lossless hit-reference compaction

Status: **preregistered representation correction; accepted semantic counts and
all non-credit boundaries are frozen**

Date: 2026-07-23

Parents:
[M1 content plan](lean-u2-native-surface-classification-tl0.6.4-m1-plan-2026-07-23.md)
and [generated-wrapper correction](lean-u2-native-surface-classification-tl0.6.4-m1-generated-wrapper-r1-plan-2026-07-23.md).

## 1. Trigger

The first complete canonical authority was valid and pushed, but its 54.72 MB
file exceeded GitHub's recommended 50 MB per-file threshold. The representation
stored a domain-separated 64-hex record seal on each of 90,909 hits even though
every file already seals its ordered hit list and its complete file record.
Case evidence then repeated those hit seals.

This is redundant representation overhead, not additional evidence.

## 2. Authorized correction

R2 may make exactly these schema-local changes:

1. remove the per-hit `record_sha256` field;
2. retain every hit's signal/version, confidence/disposition, surface effect,
   exact byte interval, line/column, matched length and digest, context digest,
   and matcher route unchanged;
3. retain the domain-separated `signal_hits_sha256` over the complete ordered
   hit list and the enclosing sealed file record;
4. replace each case evidence `hit_record_sha256` reference with the exact
   zero-based `hit_index` in that file's ordered sealed hit list; and
5. validate index bounds, signal/surface/file identity, promotable role, list
   seal, file seal, case evidence-list seal, and top-level seals.

No compression container, Git LFS object, omitted hit, truncated digest, or
lossy aggregation is authorized. Ordinary JSON and offline validation remain
required.

## 3. Frozen semantic projection

Reproduction from the exact pinned checkout must retain, byte-for-byte at the
semantic field level:

- 7,004 tracked file rows and 3,723 case rows;
- 90,909 total hits and every per-signal hit count;
- all media, decoder, role, scope, generated-wrapper, direct-surface, and
  closure-surface counts;
- all 3,723 `complete-census` / `dependency-closure = not-run` states; and
- zero native outcomes, pairs, performance rows, complete populations/axes,
  satisfied terminal gates, and parity credit.

The canonical record/list seals may change because the representation changes.
The implementation must add a regression comparing a semantic projection of
the pre- and post-compaction authorities or freeze the complete expected
aggregate vector in tests.

## 4. Acceptance

R2 is accepted only if:

- focused mutation tests reject an out-of-range or retargeted `hit_index`;
- offline validation and pinned-source reproduction agree exactly;
- the canonical authority is below 50,000,000 bytes;
- generator, M0/M1/complete-parity, parity-doc, link, and whitespace gates pass
  subject only to already named unrelated historical drift; and
- no current or historical claim is promoted.

The already pushed large blob remains historical; R2 does not rewrite or force
push shared history.
