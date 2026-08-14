# agent-d — Lean bridge — what is established

Host s0. Toolchain: `~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean`,
Lean 4.30.0 commit d024af09, which is the repository's own `lean-toolchain` pin.
Commits: `baf2bf644` (L3 + L1) and `2e4dfee22` (external replay) on `main`.

Every claim below is an exit code or a test count. Nothing here rests on a doc
comment, and where a doc comment was the evidence, that is called out.

## 1. The Rado module now typechecks in real Lean. Exit 0.

```
before   $ lean proofs/shell_closed_form.lean     EXIT=1, 22 errors, 0.175 s
after    $ lean shell_closed_form.lean            EXIT=0,            0.138 s
                'shell_closed_form' does not depend on any axioms
```

The module is re-emitted from the in-tree writer
(`cargo test -p axeyum-lean-kernel --test rado_shell_arithmetic export_probe`
with `AXEYUM_LEAN_EXPORT_DIR`), 40,047 bytes, 61 lines, no `sorry`, no `axiom`.

**`#print axioms shell_closed_form` has now executed for the first time and
reports no axioms.** Before, the error cascade meant the theorem was never
declared and the command could not find its subject.

Non-vacuity: mutating the theorem *statement* (`AxNat.pow x0 (succ x1)` ->
`AxNat.pow x0 x1`) gives `EXIT=1`, "Type mismatch". Logs:
`logs/baseline-lean.txt`, `logs/after-l3-lean.txt`; artifact in `artifacts/`.

### What was actually wrong (four defects, not three)

1. **The flatness guard documented at `lean_pp.rs:214-216` and `:420-421` was
   never implemented.** `render_real_inductive` had no parameter/index test at
   all. Parameters are now printed before the colon from
   `Declaration::Inductive::num_params`, indices after it, and constructor types
   have the parameter prefix stripped and are rendered with the inductive's
   parameter binders in scope. The remaining `None` paths (mutual group, short
   telescope) are now implemented guards and both doc comments were rewritten.
2. **`.{u}` on the self-reference** inside an inductive's own constructor —
   during elaboration `Eq` is a local, so it takes no `@` and no universe
   arguments.
3. **Codegen.** The module opens `noncomputable section`. Verified separately
   that Lean 4.30 does not object to a computable `def` inside one, and that an
   unclosed section at EOF is accepted.
4. **Parenthesized partial applications — the one nobody had found.** After 1-3
   Lean still failed with `Unknown constant CoeFun`, the error the coordinator
   read as evidence that surface syntax is architecturally hostage to coercion
   insertion. It is a printer bug. Lean inserts a constant's pending *implicit*
   arguments as soon as a parenthesized application is complete:

   ```
   #check @Eq.refl.{1} AxNat AxNat.zero      -- Eq AxNat AxNat.zero AxNat.zero
   #check (@Eq.refl.{1} AxNat) AxNat.zero    -- error: Unknown constant `CoeFun`
   ```

   Both rendering engines now print one flat left-associated spine. Related:
   Lean makes an inductive's parameters implicit in its constructors regardless
   of the declared binder annotation (`@Eq.refl : ∀ {x0} {x1}, …`), so
   regenerated constructors joined the `@` set beside regenerated recursors.

`crates/axeyum-lean-kernel/tests/real_lean_parametric_inductive_crosscheck.rs`
is the regression: a **parametric and indexed** inductive rendered as a real
Lean `inductive`, with string assertions that fail on the unfixed writer without
Lean, plus a real-Lean check and a negative control (dropping the `@` must be
rejected by the same binary — it is).

### Cost of the fix, and the red main it caused

Spine flattening changes every rendered module. **Eleven** frozen
`(len, fnv1a)` render pins moved, not four: four in `axeyum-solver/tests/*.rs`
(found and updated in the first pass) and seven in
`reconstruct/tests.rs::*_family_generated_source_is_byte_stable`, which I missed
because I did not run `cargo test -p axeyum-solver --lib --features full` — the
gate CLAUDE.md names for solver changes. `main` was red for it.

All eleven are now resolved and the seven are **replaced** rather than
re-pinned: each gate diffs against a committed `.lean` fixture, and
`crates/axeyum-solver/tests/lean_module_fixtures.rs` runs every fixture through
the real Lean binary (15 accepted, `#print axioms` confirmed to execute) with a
negative control that swaps an assumed hypothesis into the proof term and
requires Lean to reject it.

The new bytes were established correct by A/B, not by blessing
(`logs/render-pin-ab-evidence.txt`): with `lean_pp.rs` as the only variable,
the old printer makes all seven pins pass; all 15 modules are identical after
normalising parentheses and `@`; real Lean accepts all 15 old and all 15 new;
and real Lean returns **byte-identical `#print axioms` output for every old/new
pair**. The A/B also found what I would otherwise have asserted falsely — four
datatype modules gained `@` on constructors, because that family is the only one
emitting real Lean `inductive`s.

## 2. The premise of the task was too pessimistic: the export path already worked for 163 modules

F-C1/F-C3 said "axeyum to Lean: broken". Measured, with the real binary and
`AXEYUM_REQUIRE_LEAN=1` so a missing binary is a failure rather than a skip:

| suite | tests |
|---|---|
| `real_lean_inductive_crosscheck` / `nat_literal` / `structure_eta` / `strict_positivity` | 1 + 1 + 1 + 1 |
| `diophantine_lean_reconstruct` | 5 |
| `int_inequality_lean_reconstruct` | 14 |
| `lean_crosscheck` | 13 (+1 corpus-scale, run separately) |
| `regex_emptiness_lean_reconstruct` | 4 |

39 tests, 0 failures — and `lean_crosscheck -- --ignored` reports
`checked 163 of 163 modules … 0 FAILED` across 70 families, both before and
after my printer change. Four of those are tamper controls where real Lean
*rejects* a mutated module.

Vacuity control run, not assumed: `AXEYUM_LEAN_BIN=/nonexistent/lean` with
`AXEYUM_REQUIRE_LEAN=1` makes the suite FAIL.

The accurate statement is therefore not "the outward direction does not exist"
and not "it works": **an export path exists and is exercised on 163 modules;
the one shape it could not express was a parametric or indexed inductive
rendered as a real `inductive`, which only the Rado module used.** The
cross-check corpus was structurally incapable of reaching the defect because
every fixture inductive is a flat enum (`add_inductive(name, &[], 0, …)`) —
a failure mode predicted in writing at
`docs/prover-track/research/06-kernel-gap-analysis.md` item 7.

## 3. The lean4export NDJSON emitter, and what the round-trip proves

`crates/axeyum-lean-kernel/src/lean_export.rs` emits official `lean4export`
NDJSON 3.1.0 from a checked environment: dense back-referencing name/level/
expression records, one atomic record group per inductive family group and for
the quotient package, deterministic `NameId` dependency order, explicit stack
traversals, and a typed `ExportError` for every construct it cannot represent.

**Round trip (`crates/axeyum-lean-import/tests/export_round_trip.rs`, 7 tests):**
each of the **17** committed official v4.30 fixtures is imported, re-emitted,
and imported again; the ADR-0350 canonical identity manifests match on all 17 —
mutual, nested (auxiliary recursors), reflexive/higher-order, well-founded,
projections, nat literals, quotient. Emitter and importer share no code.

**What the round trip does not prove, measured rather than argued.** Breaking
the emitter deliberately:

| mutation | tests failed |
|---|---|
| `numIndices` -> 0 | 6 of 7 |
| derived `k` -> always false | **2 of 7** |

A round trip is blind to every field the importer does not re-derive: `k`,
`isReflexive`, `letE.nondep`. So `k` and `isReflexive` are compared **field for
field against the official fixtures** — 71 families, 75 recursors, 12 K-like.
`isReflexive` was a real defect found exactly that way (I emitted a constant
`false`; Lean marks `MiniAcc` reflexive). `nondep` is unmodelled by the kernel
and emitted `false`; it is the one remaining descriptive divergence.

**Byte identity: 0 of 17, structurally.** Lean's exporter picks its own
name/level/expression traversal order and emits a different record count (65 vs
66 on `axeyum-probe`, 175 vs 171 on `construct-matrix-recursive-indexed`).
Matching Lean's alphabetical JSON field order was cheap and is done, so records
diff line by line. The invariant is the identity manifest.

Fail-closed: 6 unit tests in `lean_export.rs` plant environment states through
the untrusted insert (free variable, string literal, stray recursor, half
quotient package, dependency cycle) and require a typed error, not a silent
omission.

## 4. External acceptance is not scoped-and-deferred. It runs.

L1b was briefed as "scope it and stop". It turned out to be reachable with the
pinned toolchain alone: `import Lean` works from a bare `lean --run` script, and
`Lean.Environment.addDeclCore` plus `mkEmptyEnvironment` are exactly the entry
points needed. No lake project, no network, no third-party checker, no
`lean4export` install.

`scripts/lean/replay-lean4export.lean` parses our NDJSON and hands every
declaration to **Lean's own kernel**. Nothing is elaborated. Nothing is
compiled. It starts from an empty environment, so nothing can be satisfied by
Lean's `Init`, and the quotient package comes from the stream (the double-add
trap the coordinator flagged cannot arise). Constructors and recursors inside an
`inductive` record are deliberately *not* replayed: Lean regenerates them, which
is stronger, because any later declaration mentioning our exported recursor then
has to check against Lean's own.

```
all 17 official v4.30 fixtures                     accepted
the axeyum Rado development (3,854 records)        accepted: 74 declaration
                                                   records, 10 inductive groups,
                                                   97 constants, 0.9 s, EXIT=0
```

Tamper control — `shell_closed_form` given another theorem's closed, well-typed
proof:

```
line 3691: REAL LEAN KERNEL REJECTED the declaration: (kernel) declaration type
mismatch, 'rado.shell_closed_form' has type
  (a a_1 : Nat) → @Eq Nat (Nat.add (Nat.mul a a_1) a) (Nat.add (Nat.mul a a_1) a)
but it is expected to have type
  (a a_1 : Nat) → @Eq Nat (rado.shellT a a_1)
      (Nat.add (Nat.pow a (Nat.succ a_1))
        (Nat.mul (Nat.succ (Nat.succ Nat.zero)) (Nat.mul a (rado.geo a a_1))))
EXIT=1
```

That is Lean's kernel restating **our** theorem and refusing the wrong proof.
`crates/axeyum-lean-kernel/tests/real_lean_kernel_replay.rs` makes it a gate,
including the negative control. Raw log: `logs/lean-kernel-replay.txt`.

## 5. What remains

* **The Rado theorem is not yet replayed as a *gate*.** The 74-record replay
  above is a measured one-off in the log; the committed test replays a
  two-theorem development. Wiring the Rado export into the gate is small.
* **`letE.nondep`** is emitted `false` because the kernel does not model it. It
  is descriptive, but it is a divergence from Lean's own bytes and should either
  be modelled or documented in an ADR.
* **The replay script is not in `just check`.** It needs Lean, which is not a
  default dependency; it belongs in the same optional lane as the other
  `AXEYUM_LEAN_BIN` suites, and that lane needs to be mandatory *somewhere*
  (R0.1 in `docs/plan/lean-kernel-requirements-2026-08-13.md`).
* **Mutual inductives are still axiom-rendered** by `lean_pp` (an implemented,
  documented guard now, not a claimed one). The NDJSON route has no such limit —
  it round-trips mutual groups today.
* **Byte identity with `lean4export`** would need Lean's traversal order
  replicated. Low value; the identity manifest is the contract.
* **Nothing here says the solver's SAT results reach Lean.** What reaches Lean's
  kernel is the reconstructed proof term. The DRAT-checked refutation is
  upstream of that, and the join between them is Track 1's business, not this
  slice's.
