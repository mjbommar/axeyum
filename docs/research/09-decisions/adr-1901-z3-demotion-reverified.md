# ADR-1901: Roadmap 4.1 is already closed by ADR-1813; re-verified at `60fe8bdf2`, none of its five falsifiers has fired, and its one consequence-to-act-on has landed

Status: accepted (confirms ADR-1813; no new decision)
Index-summary: Roadmap item 4.1 was closed a day earlier by ADR-1813, not left open — this is the independent re-verification a referee can re-run, not a second decision. The Z3 surface is byte-for-byte unmoved since (42 files, 75 `use z3` lines, 59 feature-gated suites, 35 differential), the four-call solver surface holds on all five arithmetic suites, and ADR-1813's falsifier 4 has not fired. What HAS changed: `AXEYUM_REQUIRE_Z3` now exists (`common_z3/mod.rs`, `96da7e741`) with a negative control and a per-host capability row, so roadmap item 0.7 is stale. The roadmap's own 4.1 row remains wrong on two counts — "three differential suites" (35) and "no assumptions anywhere" (one site).
Index-status: accepted — confirms ADR-1813
Date: 2026-09-10

## Context

Roadmap item 4.1 of
[`docs/solver-comparison-2026-09/11-roadmap-and-plan.md:107`](../../solver-comparison-2026-09/11-roadmap-and-plan.md)
asks for the Z3 demotion path to be decided and recorded.

**It already was.**
[ADR-1813](adr-1813-the-z3-oracle-demotion-path.md) closed it on 2026-09-09:
Z3 keeps its ADR-0002 oracle lane, Yices2 is not a candidate (measured — no
strings, no FP, no datatypes), cvc5 is a lateral move and is named the
*additive* second oracle, and ADR-0002's demotion clause becomes a stated
trigger that has not fired.

This ADR is therefore **not a second decision on the same question**. Writing
one would create two records governing one choice, which is precisely what the
"ADRs are immutable; reversals supersede" convention exists to prevent. What is
useful — and what this file is — is the thing a durable decision record does not
carry on its own: an **independent re-measurement at a later commit**, by
someone who did not take the decision, of the facts the decision rests on. This
repository's standing rule is that a prior measurement is a claim to re-run, not
a number to quote. ADR-1813 is a month-zero decision resting on four counts and
a five-suite grep; this is that grep, re-run.

## Decision

**ADR-1813 stands unamended. No new decision is taken here.**

Three things are recorded instead:

1. **The dependence surface has not moved.** Every count ADR-1813 took on
   2026-09-09 reproduces exactly at `60fe8bdf2` (2026-09-10). Its falsifier 4
   — "the `use z3::` surface grows past the four calls: a tactic, a core, a
   proof, a push/pop" — has **not** fired.
2. **ADR-1813's "consequence to act on" has landed**, and the roadmap has not
   caught up. Item 0.7 still says "There is **no `AXEYUM_REQUIRE_Z3`**". There
   is one.
3. **The roadmap's 4.1 row is wrong in the two places ADR-1813 said it was**,
   and remains uncorrected in the roadmap file. Anyone reading 4.1 rather than
   ADR-1813 will inherit both errors. They are restated below so that a reader
   who finds this ADR first is not misled either.

## Evidence

All commands run from the repository root at `60fe8bdf2`. Each is one line and
re-runnable; none needs a build.

### 1. The surface, re-counted

| Quantity | ADR-1813 (2026-09-09) | Here (2026-09-10, `60fe8bdf2`) | Command |
|---|---|---|---|
| files with a `use z3` line | 42 | **42** | `grep -rlE '^\s*use z3' --include=*.rs crates/ \| wc -l` |
| `use z3` lines | 75 | **75** | `grep -rhcE '^\s*use z3' --include=*.rs crates/ \| paste -sd+ \| bc` |
| test files gated on `feature = "z3"` | 59 | **59** | `grep -rl 'feature = "z3"' --include=*.rs crates/axeyum-solver/tests/ \| wc -l` |
| of those, named `differential` | 35 | **35** | the same, piped to `grep -c differential` |

### 2. The four-call surface, re-verified per suite

Per-file counts of the Z3 *solver-object* calls, and of every call ADR-1813's
falsifier 4 names:

| suite | `Solver::new` | `set_params` | `assert` | `check()` | core | proof | push | pop | assumptions | Tactic/Goal |
|---|---|---|---|---|---|---|---|---|---|---|
| `qf_lra_differential_fuzz` | 3 | 2 | 2 | 2 | 0 | 0 | 0 | 0 | 0 | 0 |
| `simplex_lra_fallback_differential` | 1 | 1 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 |
| `qf_uflra_differential_fuzz` | 1 | 1 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 |
| `difference_logic_differential_fuzz` | 1 | 1 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 |
| `qf_lia_differential_fuzz` | 1 | 1 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 |

A case-insensitive search for `tactic|goal::` returns two hits in
`qf_lra_differential_fuzz.rs`, at `:404` and `:418` — **both are prose in
comments** ("the default (no-logic) tactic"), not API calls. Reported because an
uninspected nonzero count is how a false positive becomes a fact.

### 3. Workspace-wide, beyond the five suites

`grep -rhoE '\.set_[a-z0-9]+\("[a-z_]+"' --include=*.rs crates/` — the whole
parameter-key surface is three keys: **`timeout` (19 sites), `random_seed` (3),
`rlimit` (1)**. (ADR-1813 reported 43 `timeout` sites; that is a *method*
difference — it counted the string anywhere, this counts `Params` setter calls.
Neither number is wrong; quote the method with the number.)

Solver-object and model calls anywhere in `crates/`:

| call | sites | where |
|---|---|---|
| `get_unsat_core` | **0** | — |
| `get_proof` | **0** | — |
| `Tactic` / `Goal` / `Optimize` | **0** | — |
| z3 `push` / `pop` | **0** | every `.push()`/`.pop()` hit in a z3-importing file is on our own `IncrementalBvSolver` or a `Vec` — confirmed by signature (`incremental.rs:1707` returns `Result`, `:1727` returns `bool`; z3's do neither) |
| `check_assumptions` | **1** | `crates/axeyum-bench/examples/cnf_stream_bench.rs:331` — the pre-existing counter-example ADR-1813 already recorded |
| `get_model` | 3 | `z3_backend.rs:257`, and two in `quantified_uflia_model_finder_differential_fuzz.rs` (`:585`, and `:1420` which is a `println!`) |
| `Model::eval` | 5 | 4 in `z3_backend.rs`, 1 in the same fuzz |
| `get_statistics` | 1 | `z3_backend.rs:225` |

The term-construction surface is wider than the solver surface and always was:
`FuncDecl`, `Sort`, `Symbol`, `DatatypeBuilder`, `ast::{Ast, Array, BV, Bool,
Int, Real, Datatype, Dynamic}`, `forall_const` (18) / `exists_const` (9), and
the global-param trio (`set_global_param`, `get_global_param`,
`reset_all_global_params`). None of this is a *demotion* obstacle — it is term
building, which any SMT-LIB text surface replaces for free — but ADR-1813's
"four-call surface" phrase should not be read as "four symbols".

### 4. What changed since ADR-1813: `AXEYUM_REQUIRE_Z3` exists

ADR-1813's Consequences section ends with an explicit **"Consequence to act
on: add `AXEYUM_REQUIRE_Z3=1` on the same shape"**. It has landed:

- `crates/axeyum-solver/tests/common_z3/mod.rs` (commit `96da7e741`) —
  `DEFAULT_Z3_BIN = "/usr/bin/z3"`, `AXEYUM_Z3_BIN` override, and
  `AXEYUM_REQUIRE_Z3=1` turning an absent binary into a **panic**, with the
  skip message spelling out that "this run establishes nothing".
- **13 test files** consume it (`grep -rln 'mod common_z3\|common_z3::'`).
- `scripts/check-z3-differential-gate.sh` runs the 13 suites under
  `AXEYUM_REQUIRE_Z3=1`, and `:152-165` is a **negative control**: it points
  `AXEYUM_Z3_BIN` at a missing path and requires the suite to FAIL with the
  variable set and PASS without it. Both halves.
- `docs/contributor-guide/fleet-hosts.md:144`, `:230` now record the `z3`
  *executable* as a per-host capability and name **s2 and s6 as absent** —
  exactly the "exposure is not known, which is itself the finding" that
  ADR-1813 flagged.

**Roadmap item 0.7 is therefore stale** and should be marked done. Its text
still reads "There is **no `AXEYUM_REQUIRE_Z3`**".

### 5. The roadmap's 4.1 row, restated

Two errors ADR-1813 already found, still present in the roadmap file, repeated
here because this ADR is what a reader of 4.1 is pointed at:

- **"our three differential suites"** — there are **35** differential suites
  gated on `feature = "z3"`, plus 13 more driving the `z3` *binary* over
  SMT-LIB text. The three named in `CLAUDE.md` are the linear-arithmetic ones,
  never the whole dependence.
- **"no … assumptions … anywhere in the workspace"** — false;
  `cnf_stream_bench.rs:331`.

Both are still true of the roadmap at `60fe8bdf2`. Neither changes ADR-1813's
decision, which turns on the *five arithmetic suites'* surface, and that half
verifies.

## Alternatives

- **Write a second substantive ADR on 4.1.** Rejected. Two accepted ADRs
  deciding one question is an ambiguity with no owner; the convention is
  supersession, and there is nothing here to supersede — ADR-1813 is correct on
  every count re-measured.
- **Write nothing and report verbally that 4.1 is closed.** Rejected, narrowly.
  The re-measurement is the part with a shelf life: ADR-1813's numbers were
  taken once, and falsifier 4 is a *standing* condition that someone has to
  re-check periodically. A dated file with the exact commands is how that check
  gets cheaper the second time. This ADR is that file.
- **Amend ADR-1813 in place with the `AXEYUM_REQUIRE_Z3` update.** Rejected:
  ADRs are immutable once accepted.
- **Reopen the replacement question because the surface is wider than four
  symbols (§3).** Rejected on the merits, not on process. `DatatypeBuilder`,
  `forall_const` and the rest are *term construction*; a text-surface oracle
  replaces all of it with printing, which is what the 13 subprocess suites
  already do. The demotion cost is unchanged.

## Consequences

- **4.1 is closed and should be struck from the Phase 4 queue**, pointing at
  ADR-1813.
- **Roadmap 0.7 should be marked done**, pointing at `96da7e741` and
  `scripts/check-z3-differential-gate.sh`.
- **Falsifier 4 now has a re-runnable form.** The four one-line commands in §1
  and the per-file table in §2 are the check; a lane touching the oracle can run
  them in seconds. If any count moves, ADR-1813's falsifier 4 has fired and the
  demotion question genuinely reopens.

**What is LOST by deciding this way.** Nothing about the oracle changes, so
every cost ADR-1813 accepted is still being paid: we stay linked to a C++ solver
for oracle duty, the two-surface split (42 crate files + 13 subprocess files)
persists, and single-oracle blindness remains real — its commitment 3 (a first
cvc5-adjudicated suite) still has no implementation. Confirming a decision is
not progress on it, and this ADR should not be cited as if it were.

## What would falsify this ADR

It is a measurement, so it falsifies the ordinary way: **any of §1's four counts
or §2's five rows differing on a later commit.** That is falsifier 4 of
ADR-1813, and it means the dependence deepened rather than being held.
