# Official Lean construct matrix: M0 and Stage A result

Status: M0 reproduced; Stage A source freeze complete; no new export or Rust
product measurement performed

Date: 2026-07-22

Parent:
[official construct-matrix execution plan](lean-official-construct-matrix-plan-2026-07-22.md)

Registration:
[`lean-official-construct-matrix-v1.json`](lean-official-construct-matrix-v1.json)

Decision:
[proposed ADR-0351](../research/09-decisions/adr-0351-preregister-official-lean-construct-matrix.md)

## Outcome

M0 reproduced the two historical official streams byte-for-byte twice and
repeated their current Rust imports without drift. Stage A then froze seven
case IDs, two exact source files, six positive/control roots, one official
source-negative case, the tool pins, commands, resource envelope, and retention
bounds. The pinned official Lean compiler accepts the positive source and
rejects the negative source at the kernel strict-positivity check.

No new NDJSON stream was produced, inventoried, or shown to the Rust importer.
Consequently this checkpoint grants source-freeze evidence only. It does not
grant recursive-indexed, reflexive, mutual, nested, or well-founded wire,
translation, admission, or computation credit.

## M0 provenance and reproduction

The checkpoint ran from branch `repro/smtcomp-scoring` at
`3d23b1d3a8d2c7f897fa7be3f2a2e80c3739c32e`, with local HEAD and its tracking
ref equal before source work began.

The verified pins were:

- repository toolchain: `leanprover/lean4:v4.30.0`;
- Lean version: `4.30.0`;
- Lean commit: `d024af099ca4bf2c86f649261ebf59565dc8c622`;
- `lean4export` tag: `v4.30.0`;
- exporter commit: `a3e35a584f59b390667db7269cd37fca8575e4bf`;
- exporter format: `3.1.0`.

Both official regeneration runs matched each retained stream exactly:

| Control | Source SHA-256 | Stream SHA-256 | Reproductions |
|---|---|---|---:|
| flat | `342337c885dd88d3ddc7c7b49aec52b57867206ebc3ae50f81f55e85e236dfb5` | `c582b5d5ab19cba61183d592d70c17eb7d101b8a1ad61e8c4c6022dfe95a8280` | 2/2 exact |
| direct-recursive | `a8f48840c2f367feb704ad4062b9ca90ba62a802dd99475e848df726529c96bf` | `91df1e44219483b213000b94b06016f9569dc648d0680d9ae91ff3198817db08` | 2/2 exact |

The current Rust importer also repeated each baseline twice with identical
reports:

```text
flat: names=14 levels=2 expressions=43 declaration_records=5 admitted=8 axioms=1 axiom_ids=1 declaration_ids=8
direct-recursive: names=30 levels=4 expressions=130 declaration_records=5 admitted=11 axioms=0 axiom_ids=0 declaration_ids=11
```

These are historical-control checks, not measurements of the new construct
families.

## Stage A source identities

| Source | Module | SHA-256 | Official result |
|---|---|---|---|
| [`lean4export-v4.30-construct-matrix.lean`](fixtures/lean4export-v4.30-construct-matrix.lean) | `AxeyumConstructMatrix` | `08c6eeaed9d980a631dff14b30de1e3d8da37011b8ad03b84dbdc03c90bff13d` | accepted, exit 0 |
| [`lean4export-v4.30-construct-matrix-negative.lean`](fixtures/lean4export-v4.30-construct-matrix-negative.lean) | `AxeyumConstructMatrixNegative` | `4c94c6563583b34cbd500075bb76b6a71b7476e7694bcff91253c460d718c71b` | rejected, exit 1 |

The positive module contains deliberately small custom families rather than a
broad `Init`, `Std`, or mathlib closure:

- `MiniVector` and a closed recursive-indexed witness;
- an Acc-shaped `MiniAcc` higher-order/reflexive witness;
- mutually recursive `EvenTree` and `OddTree` with a closed reduction theorem;
- a `Rose` family nested beneath a custom `NestList` and a closed reduction
  theorem;
- an explicit `WellFounded.fix` definition over a minimal empty relation and a
  closed reduction theorem.

The negative module contains only a constructor argument with the declared
datatype in function-domain position. Pinned Lean rejected it with:

```text
(kernel) arg #1 of 'AxeyumConstructMatrixNegative.NonPositive.mk' has a non positive occurrence of the datatypes being declared
```

The exact selected roots and witnesses are frozen in the registration. Source
changes after this commit require a new hash and an explicit plan/decision
amendment; they cannot be made after observing a product result merely to turn
a row green.

## Resource-bounded official compilation

Both source checks used one Lean worker inside a user cgroup with
`MemoryHigh=3G`, `MemoryMax=4G`, and `MemorySwapMax=512M`. The positive compile
used 471,712 KiB peak RSS; the intended negative rejection used 88,972 KiB.

The repository's `scripts/mem-run.sh` was not used for these Lean commands.
That wrapper applies `ulimit -v`, which caps virtual address space rather than
resident memory and caused pinned Lean 4.30 to abort while creating a thread
even with `-j1`. The cgroup is the hard resident-memory control for this
milestone. This is a wrapper compatibility distinction, not a relaxation of
the 4 GiB limit.

The registration stores the exact resource-runner and compiler argument
vectors. Transient sources were copied to valid Lean module filenames in fresh
`/tmp/axeyum-lean-stage-a.XXXXXX` directories; `.olean` output was not retained
in the repository.

## Fail-closed Stage A contract

[`scripts/check-lean-official-construct-matrix.py`](../../scripts/check-lean-official-construct-matrix.py)
validates:

- exact Lean/exporter pins and repository `lean-toolchain` agreement;
- the 4 GiB/one-worker Lean and two-job Rust policies;
- the 1 MiB per-stream and 2 MiB aggregate retention bounds;
- historical source and stream identities plus two-run M0 counts;
- positive and negative source hashes and official outcomes;
- the exact ordered seven-case population, selected roots, and witnesses;
- absence of all Stage B wire and Rust product observations;
- rejection of unknown fields rather than silently extending assurance.

Eight focused tests cover the valid registration, source-hash drift,
historical-report drift, case-population/order/uniqueness drift, premature
wire/product observations, unknown fields, pin/resource/retention drift, and
loss of the kernel positivity rejection.

## Next gate

M2 is now the only primary next action:

1. compile fresh transient inputs from the frozen positive source;
2. export every selected positive root twice under the registered cap;
3. require byte-identical outputs;
4. run only the independent Python reader/census;
5. freeze exact hashes, sizes, record populations, topology, dependency roots,
   and observed wire features in Stage B;
6. commit and push Stage B before any new stream reaches the Rust importer.

ADR-0351 remains proposed. Its acceptance still requires the Stage B mechanics,
product measurement contract, and generated impossible-promotion gate; Stage A
alone does not satisfy those exits.
