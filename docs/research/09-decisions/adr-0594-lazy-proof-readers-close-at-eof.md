# ADR-0594: Lazy proof readers close at EOF

Status: accepted
Date: 2026-08-26

## Context

The recursive proof-tree CLI constructs readers lazily so building a large tree does not open
every proof file. Live inspection nevertheless found 561 descriptors in the sequential S-box
checker after it had traversed hundreds of leaves. `LazyProofReader` retained its `File` after
EOF until the surrounding tree node was dropped. The current host's descriptor limit is high
(524,288), so this had not yet failed, but descriptor use scaled with traversal shape rather
than active proof streams.

## Decision

Close the underlying `BufReader<File>` as soon as either `Read` or `BufRead` observes EOF. Retain
an explicit `exhausted` bit so a later read remains at EOF instead of reopening the path from the
beginning. `consume` remains valid after a nonempty `fill_buf` and is harmless after EOF.

## Evidence

The example-level control exercises both `Read::read_to_end` and repeated `BufRead::read_line`,
asserts the file handle is gone at EOF, and confirms subsequent reads remain empty. The focused
test and warning-denied example Clippy pass.

The already-running S-box checks use the previous binary. They are not restarted for this
resource repair and remain uncredited until terminal acceptance.

## Consequences

Future tree checks hold descriptors for active streams rather than every traversed proof. Proof
bytes, parsing, checking order, and verdict semantics are unchanged.
