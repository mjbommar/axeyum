# NIA-GROEBNER-GATE: does raising the ideal-refuter admission gate decide any QF_NIA file?

Lane NIA-GROEBNER-GATE, running ADR-2112 Part F's handed-forward probe: our
Gröbner route (`cas_ideal_refutation`, `crates/axeyum-solver/src/cas_poly.rs:640`,
into `unit_ideal_cofactors` at `:707`) is reached on 115 of 200 `QF_NIA` T1
rows and decides 0, refused by an 8/8/8 admission gate on 114 of 116 undecided
rows. Three env levers already exist. **This lane measures, rather than
argues, whether raising them decides anything, and at what cost.**

Status: IN PROGRESS. This file is the skeleton, committed early per the lane
brief; the ladder table and verdict are filled in once the sweep completes.

## 1. The gate, read

Three named constants in `crates/axeyum-solver/src/cas_poly.rs`, all set to
**8** in `119858e2c` ("feat(cas): multivariate ideal refutation with a
re-checkable certificate", 2026-08-13) and each wired to an env override in
`c734c45f9` ("feat(config): 64 completeness caps become a one-command A/B, not
a rebuild"):

| constant | `cas_poly.rs` | what it bounds | protects against |
|---|---:|---|---|
| `MAX_IDEAL_GENERATORS` | `:541` | asserted EQUATIONS admitted as Gröbner-basis ideal generators | a system with too many generators ever entering Buchberger |
| `MAX_IDEAL_ATOMS` | `:572` | distinct opaque ATOMS (monomial variables) across the whole system | Buchberger under `lex` is doubly exponential in variable count in the worst case — the doc comment names this the ceiling that "actually bounds the search," the step budget below is the backstop |
| `MAX_IDEAL_INEQUALITIES` | `:555` | asserted INEQUALITIES considered as combination terms (also used to `truncate` the list post-admission) | blow-up in the positivity-certificate combination search |

All three are `config_registry.rs` entries with `protects: Protects::Completeness`,
`on_exceed: OnExceed::DeclineRoute` — crossing any one **declines the route**,
it never risks a wrong answer: every candidate `cas_ideal_refutation` finds is
independently re-derived by `check_cas_ideal_certificate` before acceptance
(`guarded_by` in the registry), so raising these levers can only cost time,
never soundness. Below the admission gate, four separate FIXED step ceilings
(`ideal_limits()`, `cas_poly.rs:587`: `reduction_steps=6_000`,
`pair_iterations=1_500`, `basis_size=32`, `poly_terms=256`) bound the
Buchberger search itself — those are not levers, and a raised admission gate
degrades to a step-ceiling decline rather than a hang, confirmed below.

Env overrides: `AXEYUM_MAX_IDEAL_GENERATORS`, `AXEYUM_MAX_IDEAL_ATOMS`,
`AXEYUM_MAX_IDEAL_INEQUALITIES` — unset reproduces the shipped 8/8/8 byte for
byte (`config_lever`'s contract).

Smoke-tested directly against one undecided row
(`QF_NIA/20170427-VeryMax/ITS/From_T2__firewire.t2__terminationS_13_0.smt2`):
the admission decline detail changes exactly where predicted —

| lever value | `cas-ideal-refuter` decline detail |
|---:|---|
| 8 / 16 / 32 | `nonlinear system exceeds the deterministic generator/atom/inequality ceilings` |
| 64 / 1,000,000 | `cofactor-tracked Gröbner reduction hit the basis-size ceiling` |

confirming the lever is reached and that raising it past admission moves the
refusal to the fixed step ceiling rather than removing it.

## 2. The ladder

Ladder: shipped (8/8/8), 16/16/16, 32/32/32, 64/64/64, "unbounded"
(1,000,000/1,000,000/1,000,000 — no sentinel exists for the `usize` lever;
this value is above every measured atom/generator/inequality count in the
corpus). Each rung run interleaved shipped-vs-gateN, alternating which arm
goes first per file, on the 116 undecided `QF_NIA` T1 rows
(`bench-results/nia-trace-20260915/undecided-116.txt`), 24 s / 8 GiB
`ulimit -v`, `--trace`, through `scripts/ledger-run-one.sh` so every row lands
in `bench-results/ledger/nia-groebner-gate-<rung>.tsv` with
`sweep_id=nia-groebner-gate-<rung>` and `arm` in `{shipped, gate<rung>}`.

Binary: release `smtcomp_cli`, commit `3c3ba0eb2` (local main after merge),
sha256 `340bdd11053cac94aaece2281a24a46cd79546ae26013e1b5724f3815ce2cf1d`.

Cores: **s7**, physical core pairs `1,9` (shard 1, files at odd position in
the 116-list) and `3,11` (shard 2, even position), run in parallel; the four
rungs run serially, one after another, on each shard. Driver scripts in
`scripts/run-ladder-master.sh` and `scripts/run-arm-pair.sh` in this
directory (also copied to `server7:~/nia-groebner-gate-20260915/` to run
against the pinned cores, since this worktree is local to the dev box and s7
does not share this filesystem).

### Ladder table

TODO — filled in once the sweep completes.

| rung | files admitted (of 116, ADMITS vs REFUSES) | now DECIDES | ADMITS-but-fails | STABLE-GAIN | STABLE-LOSS | median ms | p90 ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| shipped (8) | | | | — | — | | |
| 16 | | | | | | | |
| 32 | | | | | | | |
| 64 | | | | | | | |
| unbounded | | | | | | | |

### Cross-division check (QF_NRA, UFNIA)

TODO — shipped arm and best arm, full 200-row lists, same envelope.

## 3. Verdict

TODO.

## 4. Ship decision

TODO — 0 stable losses across all three divisions and ≥ 1 stable gain is the
bar; filled in once §2 and §3 are measured.
