# ADR-1813: The Z3 oracle keeps its lane; the demotion trigger is restated as an observation and has not fired

Status: accepted
Index-summary: Z3 is not replaced — Yices2 cannot cover our string/FP/datatype suites (measured against the binaries on this host) and cvc5 is a lateral move; ADR-0002's demotion clause becomes a stated, checkable trigger that has NOT fired; cvc5 is named the additive second oracle over the SMT-LIB text surface; and the 13 `/usr/bin/z3` fuzzes that skip-and-pass are recorded as a gate that cannot fail
Date: 2026-09-09

## Context

[ADR-0002](adr-0002-ground-up-identity-oracle-bootstrap.md) made the linked Z3
backend "bootstrap scaffolding with a planned demotion path": M0 backend →
differential oracle → CI cross-check, with each demotion happening "when the
evidence pipeline replaces the trust the oracle was providing". That last clause
was never turned into an observation, so the demotion has been a stated
intention with no check that could say whether it was due.

Item 4.1 of
[`docs/solver-comparison-2026-09/11-roadmap-and-plan.md`](../../solver-comparison-2026-09/11-roadmap-and-plan.md)
asks for the decision to be recorded, on the basis that our dependence on Z3 is
a four-call surface and therefore trivially portable. This ADR closes it.

### What the dependence actually is, measured at `6dd85fc78` (2026-09-09)

The roadmap's figures were re-measured. Three have moved or were wrong.

| Claim (roadmap 4.1) | Measured today | Verdict |
|---|---|---|
| 71 `use z3::` lines | **75** lines across **42** files | stale, minor |
| Z3's model read at 3 sites | **2**: `crates/axeyum-solver/src/z3_backend.rs:256` and `crates/axeyum-solver/tests/quantified_uflia_model_finder_differential_fuzz.rs:1420` — and the second is a `println!` diagnostic whose value never reaches a verdict | stale, and the correction matters: only ONE site consumes a Z3 model |
| "no … assumptions … anywhere in the workspace" | **FALSE.** `crates/axeyum-bench/examples/cnf_stream_bench.rs:331` calls `solver.check_assumptions(&assumptions)` — Z3's native assumption API, driving an incremental clause-stream comparison | **wrong as written** |
| "our three differential suites" | **59** test files in `crates/axeyum-solver/tests/` are gated on `feature = "z3"`, **35** of them differential | the three named suites were never the whole dependence |

The part of the claim the decision turns on does survive verification, and it
survives on **five** suites rather than three — `qf_lra_differential_fuzz`,
`simplex_lra_fallback_differential`, `qf_uflra_differential_fuzz`, and the two
that landed under roadmap item 2.6, `difference_logic_differential_fuzz` and
`qf_lia_differential_fuzz`. Across all five, the Z3 *solver-object* surface is
exactly four calls: `Solver::new()`, `set_params(&params)`, `assert(..)`,
`check()` — four, six, six and six occurrences respectively, and nothing else.
No tactic, goal, probe, unsat core, proof, push/pop or assumption appears in any
of them. Their term-construction surface is `Bool`, `Int`, `Real`, the `Ast`
trait, and (UFLRA only) `FuncDecl` + `Sort`. There is no `(set-logic …)`, so the
oracle we lean on is Z3's default `smt_context` route into `theory_lra` and its
exact simplex.

Workspace-wide, the entire Z3 *parameter* surface is three keys: `timeout` (43
sites), `random_seed` (3: `z3_backend.rs:202`, `cnf_core_bench.rs:73`,
`cnf_stream_bench.rs:225`), and `rlimit` (1). Every one has a direct
command-line equivalent in both cvc5 and Yices2.

### The dependence is two surfaces, not one

The roadmap counted only the Rust crate. There is a second, entirely separate
surface: **13 test files drive the `z3` binary over SMT-LIB text**, at a
hardcoded `const Z3_BIN: &str = "/usr/bin/z3";` — `fp_differential_fuzz`,
`seq_differential_fuzz`, `regex_membership_differential_fuzz`,
`word_equation_differential_fuzz`, `string_differential_fuzz`,
`online_string_front_door_fuzz`, `qf_s_online_differential_fuzz`,
`qf_s_online_membership_differential_fuzz`,
`qf_s_replace_fold_differential_fuzz`, `qf_slia_length_lia_differential_fuzz`,
`qf_slia_lex_order_differential_fuzz`, `qf_nia_iand_differential_fuzz`,
`qf_nia_pow2_differential_fuzz`.

This matters twice. It is the surface that is *easy* to repoint — any SMT-LIB
solver reads it — and it is the surface where the oracle is **not gating
anything on most hosts** (see Consequences).

### What a replacement would have to cover — measured, not assumed

Probed directly against the binaries this host carries
(`/nas3/data/axeyum/harness/bin/cvc5` 1.3.4, `.../yices-smt2` 2.7.0,
`/usr/bin/z3` 4.13.3), 2026-09-09:

| Probe | z3 | cvc5 | Yices2 |
|---|---|---|---|
| `QF_S`: `(= (str.++ s "a") "ba")` | `sat` | `sat` | `(error "unknown logic: QF_S")` |
| `QF_FP`: `(fp.isNaN x)` on `Float32` | `sat` | `sat` | `(error "unknown logic: QF_FP")` |
| `QF_DT`: three-constructor enum, two constructors excluded | `sat` | `sat` | `(error "unknown logic: QF_DT")` |
| `QF_NIA`: `(= (* x x) 17)` | `unsat` | `unsat` | `unsat` |

**Yices2 is not a candidate replacement.** It is fast and exact on arithmetic —
and [ADR-1732](adr-1732-second-reference-per-division-not-a-replacement.md)
already pins it as the *parity reference* for QF_LRA, QF_UF and QF_RDL, where
the SMT-COMP 2026 numbers put it at or ahead of cvc5 — but it has no string,
floating-point, or datatype theory at all. Those cover the 13 text-surface
suites outright. Swapping to Yices2 would silently delete the oracle from every
one of them, and the deletion would be invisible: those suites already treat an
unusable oracle as a pass.

## Decision

**Z3 keeps its ADR-0002 oracle lane unchanged; we neither replace it nor drop
the oracle role — instead this ADR converts ADR-0002's demotion clause into a
stated, checkable trigger that has NOT fired, and names cvc5 as an *additive*
second oracle over the SMT-LIB text surface, never a substitute.**

Four commitments:

1. **No replacement.** Yices2 cannot cover the theories our suites need
   (measured above). cvc5 can, but replacing Z3 with cvc5 is a lateral move: it
   swaps one independent mature solver for another, buys no new independence,
   and costs the 42-file `use z3::` binding surface, for which cvc5 has no
   maintained Rust equivalent.
2. **The demotion trigger is restated as an observation.** ADR-0002 said
   demotion happens when "the evidence pipeline replaces the trust the oracle
   was providing". Concretely: **the oracle may be demoted from differential
   duty on a route when every `unsat` that route can emit carries a certificate
   an independent checker accepts, AND that checker's gate has been shown able
   to fail.** Both halves are required, and the second is currently unmet in a
   way that makes the trigger not merely unfired but *unobservable*:
   `crates/axeyum-cnf/tests/carcara_checked_rules_parity.rs:117-127` prints
   `[skip] references/carcara not present` and returns green, and
   `crates/axeyum-solver/tests/carcara_crosscheck.rs:175` skips with
   `AXEYUM-CARCARA-SKIPPED no carcara binary`. `references/` in this tree
   contains one file, `README.md`. Until roadmap items 0.2 and 0.3 land,
   demotion is **premature on every route**.
3. **The second oracle is cvc5, additive, over the text surface.** The risk Z3
   poses now is not identity creep — a four-call surface behind a non-default
   feature is not creep — it is **single-oracle blindness**: a wrong answer we
   and Z3 share is invisible to every gate we own. cvc5 is already an in-tree
   reference (`crates/axeyum-bench/examples/cvc5_smt_stream_bench.rs`,
   `cvc5_qfbv_timeout_sweep.rs`; the default `PARITY.md` reference under
   ADR-1732) and the subprocess-over-SMT-LIB pattern already exists in 13 files.
   A new differential suite should adjudicate against **both** where the theory
   permits, and a DISAGREE between the two oracles is a finding about the
   generated benchmark, not about us. This sits squarely inside ADR-0002's
   "backend / differential-oracle / CI-cross-check" allowance and expands
   nothing.
4. **Nothing in the default build changes.** `z3 = ["full", "dep:z3"]`
   (`crates/axeyum-solver/Cargo.toml:60`) stays a non-default, feature-gated
   leaf dependency; the C/C++-free default build is untouched.

## Evidence

- The four-call surface, verified across all five arithmetic suites by grepping
  `Solver::new|set_params|\.assert(|\.check()|check_assumptions|get_model|get_proof|unsat_core|\.push(|\.pop(`
  over `qf_lra_differential_fuzz.rs`, `simplex_lra_fallback_differential.rs`,
  `qf_uflra_differential_fuzz.rs`, `difference_logic_differential_fuzz.rs` and
  `qf_lia_differential_fuzz.rs`: the only solver-object hits are
  `Solver::new()`, `set_params`, `assert` and `check()`.
- The `check_assumptions` counter-example at `cnf_stream_bench.rs:331`, which
  falsifies the "no assumptions anywhere in the workspace" half of the claim.
- The three-key `Params` surface, counted workspace-wide (`timeout`,
  `random_seed`, `rlimit`).
- The four theory probes above, run against the three binaries on this host.
- ADR-1732's SMT-COMP 2026 computation, which is why Yices2 is already pinned
  for arithmetic parity and why this ADR does not re-derive its standing.

## Alternatives

- **Replace Z3 with cvc5.** Rejected: lateral. It would cost the Rust binding
  surface and gain nothing measurable, because cvc5 and Z3 are equally
  independent of us. cvc5's right role is the *second* oracle (commitment 3),
  where it adds independence rather than relocating it.
- **Replace Z3 with Yices2.** Rejected on measurement: no strings, no FP, no
  datatypes. It would un-gate 13 differential suites, silently.
- **Drop the oracle role entirely.** Rejected, and this is the alternative that
  would have been a real mistake. It presupposes the evidence pipeline has taken
  over, and Phase 0 of the roadmap exists because our external-checker gates
  currently skip and pass. Dropping the oracle before the checkers can fail
  removes the only referee we have while leaving the ledger unfalsifiable —
  precisely the failure mode CLAUDE.md names ("a checker that cannot fail is
  worse than no checker").
- **Port everything to the text surface now and delete the `z3` crate
  dependency.** Deferred, not rejected. It is a real simplification — it would
  make the oracle solver-agnostic in one step — but it is 42 files of mechanical
  work carrying a wrong-verdict risk in the translation, and it buys nothing
  until a second oracle is actually wired. Revisit once commitment 3 has one
  suite.

## Consequences

**What this buys.** The demotion question stops being reopened per lane: there
is one sentence to check against (commitment 2), and it is falsifiable. New
differential suites have a stated adjudication policy.

**What is LOST by deciding this way.**

- **We stay linked to a C++ solver for oracle duty for at least another phase.**
  Every host that runs the arithmetic fuzzes needs `libz3`. The fleet-capability
  problem in `docs/contributor-guide/fleet-hosts.md` is not reduced by this
  decision; it is accepted for now.
- **We forgo the simplification of a single, solver-agnostic text oracle.** The
  two-surface split (42 crate files + 13 subprocess files) persists, and the
  crate half will have to be paid for eventually if we ever want two oracles in
  the *arithmetic* suites, since cvc5 has no maintained Rust binding.
- **Single-oracle blindness remains real until commitment 3 has a first suite.**
  This ADR names the fix; it does not implement it. Anyone quoting "DISAGREE=0"
  from an arithmetic fuzz today is quoting agreement with exactly one
  implementation, and should say so.

**A gate that cannot fail, found while measuring this.** All 13 SMT-LIB-text
fuzzes hardcode `/usr/bin/z3` and, when it is absent, print to stderr and
**return** — e.g. `fp_differential_fuzz.rs:393-396`:

```rust
if !z3_available() {
    eprintln!("[fp-fuzz] {Z3_BIN} unavailable; skipping seed '{note}'");
    return;
}
```

The test then passes. There is no `AXEYUM_REQUIRE_Z3`, although the identical
skip-or-fail pattern already exists for two other external tools
(`AXEYUM_REQUIRE_ABC`, `tests/abc_crosscheck.rs:231`; `AXEYUM_REQUIRE_CARCARA`,
`tests/carcara_crosscheck.rs:142`). On a host where `z3` is not at that exact
path, all 13 string / seq / regex / FP / NIA differentials are green and check
nothing. **Consequence to act on:** add `AXEYUM_REQUIRE_Z3=1` on the same shape
and set it wherever the z3-gated suites are treated as a gate. This is a
Phase 0-class defect that Phase 0 did not enumerate; it belongs beside items 0.2
and 0.3. It is recorded here rather than fixed here because this ADR writes no
code.

## What would falsify this decision

Any one of these says we chose wrong:

1. **A wrong verdict that both we and Z3 produce, caught by cvc5 or by a corpus
   `:status`.** That is single-oracle blindness realised, and it would say
   commitment 3 should have been commitment 1 — a second oracle before anything
   else.
2. **Z3 and cvc5 measured to disagree with each other on more than a negligible
   share of a differential suite's generated instances.** That would mean the
   suites generate queries whose SMT-LIB semantics are genuinely contested, and
   "adjudicated by the oracle" is the wrong frame for them regardless of which
   oracle is chosen.
3. **Phase 0's checkers land, every `unsat` on some route carries a certificate
   an independent checker accepts, and that route's Z3 fuzz still catches a real
   defect.** That falsifies commitment 2's trigger: certificate coverage would
   have been shown *not* to replace the trust the oracle provides, and the
   trigger would need a stronger condition than "every unsat is certified".
4. **The `use z3::` surface grows past the four calls** — a tactic, a core, a
   proof, a push/pop — in anything that is not an explicitly scoped experiment.
   That means the dependence is deepening rather than being held, and
   ADR-0002's "keep the oracle in its lane" clause has failed in practice.
5. **Yices2 gains a string or FP theory**, or the string/FP/DT suites are
   retired. Either removes the measured reason Yices2 is not a candidate, and
   the replacement question reopens on speed grounds.
