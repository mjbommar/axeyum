# Lean strict positivity: M3 official/import-boundary result

Status: complete; M4 closure and handoff next

Date: 2026-07-22

Machine-readable observations:
[`lean-strict-positivity-m3-v1.json`](lean-strict-positivity-m3-v1.json)

Parents:

- [TL2.11 execution plan](lean-strict-positivity-tl2.11-plan-2026-07-22.md);
- [proposed ADR-0352](../research/09-decisions/adr-0352-preregister-lean-strict-positivity.md);
- [M2 public/generated result](lean-strict-positivity-m2-2026-07-22.md).

## Official source result

The repository's checksum-pinned installer produced:

```text
Lean (version 4.30.0, x86_64-unknown-linux-gnu,
commit d024af099ca4bf2c86f649261ebf59565dc8c622, Release)
```

Every M0-frozen source ran twice from a fresh directory under the registered
`systemd-run --user --scope` policy (`MemoryHigh=3G`, `MemoryMax=4G`,
`MemorySwapMax=512M`) with `/usr/bin/time -v`, `-j1`, and an explicit output
module. The exact observations are:

| run | source | exit | outcome | diagnostic stream | max RSS KiB |
|---:|---|---:|---|---|---:|
| 1 | `construct-matrix-positive` | 0 | accepted | n/a | 468120 |
| 1 | `negative-domain` | 1 | rejected | stdout | 88584 |
| 1 | `negative-mixed` | 1 | rejected | stdout | 86692 |
| 1 | `negative-deep` | 1 | rejected | stdout | 88512 |
| 2 | `construct-matrix-positive` | 0 | accepted | n/a | 468432 |
| 2 | `negative-domain` | 1 | rejected | stdout | 88652 |
| 2 | `negative-mixed` | 1 | rejected | stdout | 86056 |
| 2 | `negative-deep` | 1 | rejected | stdout | 88880 |

All six rejecting runs contain the preregistered kernel diagnostic:

```text
has a non positive occurrence of the datatypes being declared
```

The initial shell summary looked only at stderr and therefore printed
`diagnostic=no`; Lean emits these kernel diagnostics on stdout. Inspection of
the preserved paired logs corrected the stream classification without rerunning
or changing any source. The committed observation validator now freezes the
correct stream and has mutation teeth for removing it.

The pinned installer first encountered a short-write while extracting its
small bootstrap executable under the heavily used `/tmp` tmpfs. Repeating the
same checksum-pinned installer with scratch space under ignored `target/`
succeeded. The installed version and commit are checked before source
execution; no source, compiler option, or result expectation changed.

## Mandatory differential

`real_lean_strict_positivity_crosscheck` makes this population a permanent
official-Lean gate. It:

- requires the exact version and commit, not only a `lean` executable;
- copies all four immutable repository sources into fresh module directories;
- runs all four twice with one Lean worker and a 4 GiB Lean memory ceiling;
- requires two positive `.olean` files and six non-positive diagnostics;
- fails closed under `AXEYUM_REQUIRE_LEAN=1` when the binary is absent;
- emits the stable summary
  `sources=4|runs=8|accepted=2|rejected=6|diagnostics=6`.

The official-Lean CI job now invokes this test explicitly beside the existing
inductive and Nat-literal differentials.

## Synthetic importer propagation

Official Lean cannot export a declaration its kernel rejects, so importer
propagation necessarily uses a synthetic format mutation and receives no
official-wire credit. The test binds the exact official direct-recursive stream
(`91df1e...7db08`), inserts expression 114 for `(MiniNat -> MiniNat) ->
MiniNat`, and changes only `MiniNat.succ`'s constructor type reference from 85
to 114 before its group record.

The unmodified control completes with 11 admitted declarations. The mutation
returns exactly:

```text
ImportError::Kernel {
  line: 151,
  declaration: "MiniNat",
  source: NonPositiveInductiveOccurrence { field_index: 0, ... }
}
```

No `CompletedImport` is returned. The observation manifest and tests reject an
attempt to relabel this as official wire evidence or to report publication.

## Immutable construct-matrix regression

The previously frozen official construct-matrix registration remains bound by
SHA-256 `e76d334f...ef0d1`. Its product test again runs a completed 11-
declaration direct-recursive control before every decline, repeats the five
selected decline rows, and preserves all ten controls and ten typed outcomes.
Strict positivity therefore changes only the intended known-bad classification;
it does not silently widen recursive-indexed, reflexive, mutual, nested, or
well-founded admission.

## Bounded gates

```text
AXEYUM_REQUIRE_LEAN=1 cargo test -p axeyum-lean-kernel \
  --test real_lean_strict_positivity_crosscheck -- --nocapture
  -> 1 passed; sources=4, runs=8, accepted=2, rejected=6, diagnostics=6

cargo test -p axeyum-lean-import --test strict_positivity_propagation
  -> 1 passed

cargo test -p axeyum-lean-import --test official_construct_matrix
  -> 1 passed

cargo clippy [the two new Rust test targets] -- -D warnings
  -> pass

python3 -m unittest scripts.tests.test_lean_strict_positivity_m3
  -> 6 passed

python3 scripts/check-lean-strict-positivity-m3.py --check
  -> 4 sources, 8 official runs, synthetic rejection, matrix unchanged
```

Rust execution used at most two build jobs and the 4 GiB wrapper/cgroup.
`git diff --check` passes.

## Remaining gate

M3 still does not accept ADR-0352 or mark TL2.11/T6.0.2 complete. M4 must run
the final focused kernel/importer/doctest, clippy, rustdoc, parity,
foundational-resource, and link gates; accept or reject the ADR from its exits;
close the research question; synchronize every roadmap/status surface; and
verify local, tracking, and remote revision equality after the final push.
