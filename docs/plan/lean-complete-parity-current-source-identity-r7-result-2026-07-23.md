# Lean complete-parity current-source identity R7 result

Date: 2026-07-23

Status: **Lean implementation and validation complete on the pushed topic
branch; full green-before-merge gate blocked by pre-existing out-of-lane
formatting; no process outcome or parity credit**

Plan:
[R7 current-source identity plan](lean-complete-parity-current-source-identity-r7-plan-2026-07-23.md)

Amendment:
[R7 retained-store scope correction](lean-complete-parity-current-source-identity-r7-amendment-2026-07-23.md)

Contract:
[complete Lean 4.30 parity](lean4-complete-parity-contract-2026-07-22.md)

## 1. Verdict

R7 repairs the post-integration `resume_fs.py` source-identity drift without
changing the shared SMT primitive, any accepted authority, any retained
evidence byte, or any Lean-parity credit.

The repair now enforces both sides of the identity boundary:

- accepted historical TL0.7.3/TL0.7.4/TL0.6.3 results retain SHA-256
  `1968e7b6424c2dd9273bff5041e96fc21b83ec01b2205dcc840d5dc942be1aec`;
- current repository validation admits only reviewed successor
  `b05c32185d75d5790f26ba25b6891c373712a565942400f4b08fa49bdc3c0ea6`;
- retained store cells derive their expected worker and primitive hashes from
  the already validated result implementation revision; and
- new result construction remains bound to an ancestor revision containing
  every current source byte.

The exact original ROOT-relative worktree-path repair also remains effective:
the complete-parity generator passes from a clean detached checkout whose
absolute root differs from the evidence-producing and owning worktrees.

## 2. Trigger and semantic compatibility

SMT-COMP commit `9e578a58` added the optional keyword-only
`eligible_targets` argument to `recover_orphan_temporaries`. Its default is
`None`. The Lean store continues to call the function without that argument,
so its all-temporary recovery semantics are unchanged. The atomic install
functions imported by the Lean acceptance and U2 validators were not changed
by that commit.

The first visible failure was the store test's direct comparison of current
bytes to the historical hash. After the first current-only correction, the
complete-parity generator exposed a deeper identical conflation in retained
cell validation. The R7 amendment preregistered that expanded boundary before
`lean_execution_store.py` changed.

No broad hash bypass was added. An arbitrary current hash fails the focused
mutation controls, and an unknown, non-ancestor, or source-mismatched result
revision continues to fail before result construction.

## 3. Implementation history and current identities

The pushed topic history is:

| Commit | Scope |
|---|---|
| `eb4566a2` | preregister the current-source identity repair |
| `e7db3f69` | split current primitive identity in acceptance/U2/M2 and tests |
| `ed2fb8ee` | preregister the retained-store validation amendment |
| `97b2b1a0` | bind retained store source hashes to the validated result revision |
| `1fd4db38` | refresh only current-source identities in the generated terminal registry |

Final current source identities are:

| Source | SHA-256 |
|---|---|
| `scripts/smtcomp_repro/resume_fs.py` | `b05c32185d75d5790f26ba25b6891c373712a565942400f4b08fa49bdc3c0ea6` |
| `scripts/lean_execution_store.py` | `274009d97fc40db01b82c6ea650127815e84a5dbb56eef5f1d60f962a6a3cd1b` |
| `scripts/lean_execution_acceptance.py` | `976ace65ea93f08393efa5cd25895c10183b10a8b21c726367787f8277e686e3` |
| `scripts/lean_u2_official_execution.py` | `1f44b340daeae2c03eb3157515609f158cdaf4733575aa9c36cccc510e301ad9` |
| `scripts/lean_u2_official_execution_m2.py` | `c3b1b5919b9a676c22e0d881c4de7833cb9b4f76f89f2af4f7a8d651938cb123` |

The generated registry changes eight current validator/test hash rows and no
population, observation, comparison, or credit field.

## 4. Immutable-authority and evidence check

Every accepted authority remained byte-identical:

| Authority | SHA-256 |
|---|---|
| TL0.7.3 store | `e167c2054537d628bf1e0621bd6fb864bc8f38847aaf690b8767687ef1d1a647` |
| TL0.7.4 acceptance | `bd3f01fc5ac61bbcfdf23a82055fd58d47cf8167240727ec35e51ceb2a4be05f` |
| TL0.6.3 M0 | `61c7bb015dee1cb767b6c460a08f2c4416a62f1c41e040c817fd5b0d6ea24f8d` |
| TL0.6.3 M0 R3 | `fe04cd96fb9f08c8a0e834ec11f954c3c8172912332da28fc2a92adf0cedb475` |
| TL0.6.3 M2 R1 | `df5f95b9ee4f96e576119e7225eac98f0329a1eadbfd901703287627af852dd6` |
| TL0.6.3 M2 R3 | `13ac5126e964aa997504dc3e8da06524849fbe91015cfff53e8ed026c4f8eae2` |
| TL0.6.3 M2 R6 | `af7a532175f959b78058f27c5bc90af2f2f36b1d88b69dd2a785d5d4699a8b83` |

Sorted file-level SHA-256 aggregate checks also remained identical before and
after the repair:

| Retained root | Files / bytes | Aggregate SHA-256 |
|---|---:|---|
| TL0.7.3 store | 65 / 43,978 | `1854fdb8728a48a83315766372d4a4e8c3b014123154d3c8851a44ad1e9a69cb` |
| TL0.7.4 accepted | 26 / 52,549 | `89359ab91643276f3376a15c2003b040a2a3fffbad7942ec5794719a08466cd3` |
| TL0.7.4 failed attempt | 41 / 89,974 | `a0c5352b4d570c9a05f32ff03b3738d36a255185cc5ba8a9e9160d1637987dbe` |
| TL0.6.3 M0 accepted | 23 / 4,778,395 | `814e759fdd7bfb1c3b56b9f1895a1729b43a6bf3afaf6e26be13891175f54484` |
| TL0.6.3 M0 failed attempt | 18 / 4,757,134 | `d5ea80378fec68e138937fc8827790ea38e50076cd6359b262f705d608dce896` |
| TL0.6.3 M2 R1 | 152 / 5,307,372 | `d3b5b8ed5cf1e1f7b9d0f86277b64def10839f83f2a9d160d296dc78efe01696` |
| TL0.6.3 M2 R3 | 17 / 4,908,035 | `d53f89367073172dd4f3b514a6446b896462d89d5426c168592fb0fba669cfe0` |
| TL0.6.3 M2 R5 | 151 / 5,228,286 | `a6d5f2107a9cfbe830262b039c85ce9d72b30de9dce8e3bfcdb6d022b3c4afa2` |
| TL0.6.3 M2 R6 | 152 / 5,246,140 | `8933ee2bf423489bad7ed48b8adc251725330cf3759584dfe967ec1d4a3338ea` |

## 5. Validation

The focused current-source/store suite passes 93 tests with one expected
opt-in live sentinel skip. It covers the SMT filesystem primitive, Lean store,
acceptance, U2, and M2 validators, including a fresh synthetic 16-cell SIGKILL
matrix across the worktree and `/dev/shm` storage classes.

`just parity-docs && just links` passes in the owning worktree. This includes:

- 24 TL0.7.3 store tests and exact retained-result replay;
- 24 TL0.7.4 acceptance tests with one expected skip and exact authority replay;
- 26 base U2 tests, all R2/R3 and M2--M2 R6 replay layers;
- native-surface/content/dependency/header and normalization gates;
- 25 terminal complete-parity tests;
- construct, positivity, recursive, mutual, and nested-inductive gates;
- generated registry and prose-consistency checks; and
- the repository link checker.

A clean detached checkout at
`/tmp/axeyum-lean-r7.Q6I569/checkout` also passed:

```text
LEAN_COMPLETE_PARITY|populations=10|complete_populations=0|axes=12|complete_axes=0|paired_cells=0|gates_satisfied=0|terminal_ready=false
```

The detached checkout was clean and removed after validation.

The repository-wide `just check` gate reaches `cargo fmt --all --check` and
stops on the same pre-existing formatting drift in one benchmark file and
eight CAS files recorded by R6:

- `crates/axeyum-bench/examples/audit_dominance.rs`;
- `crates/axeyum-cas/src/combinatorics.rs`;
- `crates/axeyum-cas/src/gosper.rs`;
- `crates/axeyum-cas/src/lib.rs`;
- `crates/axeyum-cas/src/ntheory_advanced.rs`;
- `crates/axeyum-cas/src/ntheory_more.rs`;
- `crates/axeyum-cas/src/orthopoly.rs`;
- `crates/axeyum-cas/src/series.rs`; and
- `crates/axeyum-cas/src/special.rs`.

R7 owns no Rust and does not reformat another lane's files. Consequently the
Lean-specific gates are green, but the topic branch must not merge until the
integration owner obtains a green repository-wide gate after that separate
baseline drift is resolved.

## 6. Nonclaims and handoff

R7 launched no Lean, Axeyum, M2.1--M2.7, solver, installer, exporter,
toolchain, network, or retained-evidence process. Temporary synthetic store
workers grant no official or native outcome.

This repair makes the cross-lane validator green; it does not establish Lean
parity. All U0--U9 populations, A0--A11 axes, paired cells, and G1--G10 gates
remain incomplete or zero, and `terminal_ready` remains false.

The pushed topic branch is ready for integration review, not yet merge. After
the out-of-lane formatting baseline is repaired, the integration owner must
run the complete green-before-merge gate, merge in the chosen order, and replay
current `main`. Only then does the next Lean-parity action remain explicit
authorization and validation of the already preregistered TL0.6.4 M2.1 process
program. M2.2 must receive a separate source-first input authority before any
execution or downstream native pair.
