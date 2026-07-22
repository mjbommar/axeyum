# Lean recursive induction hypotheses: M4 computation and assurance result

Status: complete; M5 final bounded gates and ADR/TL2.12 disposition are next

Date: 2026-07-22

Parent:
[TL2.12 execution plan](lean-recursive-induction-hypotheses-tl2.12-plan-2026-07-22.md)

Importer prerequisite:
[M3 result](lean-recursive-induction-hypotheses-m3-2026-07-22.md)

Decision gate:
[ADR-0353](../research/09-decisions/adr-0353-preregister-lean-recursive-induction-hypotheses.md)

## 1. Result

M4 closes separate, reproducible official-source and Axeyum-product computation
evidence for both registered recursive shapes.

- pinned Lean 4.30 compiles the unchanged explicit-recursor source twice;
- the two retained official computation streams still match their M0 hashes;
- Axeyum imports each stream twice to an identical `ImportReport` and
  declaration-identity manifest;
- the imported `rfl` theorem value infers at its exported type;
- the equality sides are definitionally equal; and
- recursive normalization of the selected application spine reaches the exact
  registered normal form.

The source result and Axeyum result are reported separately. Neither is inferred
from the other.

## 2. Pinned Lean source confirmation

The exact M0 source
[`lean-v4.30-recursive-ih-computation.lean`](fixtures/lean-v4.30-recursive-ih-computation.lean)
was compiled twice with pinned Lean 4.30 commit
`d024af099ca4bf2c86f649261ebf59565dc8c622`, one worker, and the registered
systemd `MemoryHigh=3G` / `MemoryMax=4G` / `MemorySwapMax=512M` scope.

| Run | Exit | Wall | Maximum RSS KiB | OLEAN SHA-256 |
|---|---:|---:|---:|---|
| 1 | 0 | 0.22 s | 462,632 | `8b5136f7e66b18c9ad00b7f67b732ebb0fd9ff437128a80bdce831f011c7f573` |
| 2 | 0 | 0.21 s | 462,832 | `8b5136f7e66b18c9ad00b7f67b732ebb0fd9ff437128a80bdce831f011c7f573` |

One pre-run used the Rust-oriented `ulimit -v` wrapper rather than the
registered Lean systemd scope and failed before compilation with a thread-
creation error. No source or semantic result was produced. Returning to the
preregistered runner produced the two successful rows above; the resource
protocol was not changed after observation.

## 3. Frozen stream identities and imports

| Shape | Stream SHA-256 | Bytes/records | N/L/E/D | Admitted | Two-run result |
|---|---|---:|---:|---:|---:|
| recursive-indexed | `1ab5a38b50d4d2c7ba01ef2831bb5af5d3c56ce1b9879c1942070519a9f6df19` | 15,944/284 | 60/4/211/8 | 18 | 2/2 complete |
| reflexive/higher-order | `3cb06283f1e757d79d28335dfe77ccd00231a8d323c2310dddced6473933c003` | 17,722/314 | 67/3/232/11 | 20 | 2/2 complete |

Both streams have zero axioms and complete declaration-identity manifests. The
Vector recursor retains one parameter, one index, one motive, two minors, and
rule field counts `[0, 3]`. The Acc recursor retains two parameters, one index,
one motive, one minor, and rule field count `[2]`.

## 4. Exact Axeyum computation

The computation test does not merely find the selected theorem name. For each
completed kernel it:

1. retrieves the exported theorem declaration;
2. infers the theorem proof value and compares it with the theorem type;
3. decomposes the `Eq` type into type, left, and right arguments;
4. checks the two sides by trusted definitional equality;
5. checks the right side against the preregistered normal form; and
6. recursively normalizes the application spine so recursive calls beneath a
   constructor head are also forced.

| Shape | Theorem | Exact normalized result |
|---|---|---|
| recursive-indexed | `AxeyumRecursiveIHComputation.vectorHeightComputes` | `MiniNat.succ MiniNat.zero` |
| reflexive/higher-order | `AxeyumRecursiveIHComputation.accPropertyComputes` | `True` |

The focused Rust gate runs both twice. Including a fresh test-profile compile,
the timed command completed in 0.43 s at 144,304 KiB maximum RSS; the test
binary itself reported 0.04 s. These are bounded validation measurements, not a
Lean-versus-Axeyum performance comparison.

## 5. Machine assurance update

The historical ADR-0351 product observation remains intact in
[`lean-official-construct-matrix-v1.json`](lean-official-construct-matrix-v1.json).
A separate `tl2_12_update` binds:

- implementation revision `cca3ee6d33d22be696b75c6af95883dcf9d3b72a`;
- exact construct and computation test paths;
- current typed outcomes and complete reports;
- both computation stream hashes/sizes/record counts;
- selected theorems and normal forms;
- two-run source/product requirements; and
- Lean/Rust timing and RSS observations.

The checker recomputes file hashes, sizes, records, exact report contracts, and
assurance implications. Fourteen mutation tests reject outcome, report,
computation, hash, assurance, stage, source, wire, pin, resource, and population
drift.

The regenerated
[`lean-official-construct-matrix.md`](generated/lean-official-construct-matrix.md)
now reports:

- seven rows: six official-source accepts and one official-source rejection;
- four independently admitted rows;
- two separately computation-checked rows;
- two current transactional declines, including the retained nested format
  misclassification;
- `recursive-indexed` and `reflexive-higher-order` as
  `dual-admitted-computation-checked`;
- the direct control and pre-elaborated well-founded row as
  `independently-admitted`; and
- mutual/nested as bounded typed declines.

The well-founded row remains explicitly limited to import of the already-
elaborated root through `Acc.rec`; it gains no source-frontend or general
well-founded-lowering credit.

## 6. Claim boundary and handoff

M4 establishes independent generation, exact official recursor comparison,
and selected official computation for the registered single-family Vector- and
Acc-shaped population. It also establishes import of one pre-elaborated
well-founded stream as a downstream consequence.

It does not establish mutual induction, nested-inductive lowering, native
well-founded source elaboration, `Init`/mathlib population coverage, or full
Lean kernel/workflow parity.

M5 must run the final bounded kernel/importer, machine-contract, generated-
resource, formatting, clippy, rustdoc, and link gates; then accept, reject, or
defer ADR-0353 and synchronize the TL2.12/TL2.13 handoff from those results.
