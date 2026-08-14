# agent-d — Lean bridge — diary (append-only)

## 21:1x — orientation

Read the campaign README, CLAUDE.md, F-C1/F-C2/F-C3, the coordinator's raw log
and its "Correction: I overstated the Lean seam" entry. Task is L3 (make the
readable projection valid Lean) then L1 (emit official lean4export NDJSON 3.1.0
and round-trip it through `axeyum-lean-import`).

Working copy: `git archive HEAD` (a0c247a382b0) into
`…/scratchpad/agent-d/tree`. NOT the shared snapshot at `…/scratchpad/snap`,
which already contained a `target/` from another lane at 20:29 — building there
would have collided on cargo's lock. Campaign rule 7.

`git status` at start: only `crates/axeyum-lean-kernel/tests/rado_sharp_factorization.rs`
is dirty. The `env.rs`/`inductive.rs`/`lib.rs`/… WIP the brief warned about has
been committed since the brief was written (HEAD is a0c247a38, brief cites
febbcc991). I still treat those files as another lane's and touch only
`lean_pp.rs` plus new files.

## 21:2x — baseline reproduced (measurement, not a message)

```
$ AXEYUM_LEAN_EXPORT_DIR=…/artifacts cargo test -p axeyum-lean-kernel \
    --test rado_shell_arithmetic export_probe -- --nocapture
running 1 test … lean module bytes: 43279 … ok (1 passed)
$ lean shell_closed_form.lean      # v4.30.0, d024af09
EXIT=1 ; 22 error lines
```

Identical to the coordinator's finding, from a freshly re-emitted module, so the
defect is in the emitter and not in a stale file. Log:
`logs/baseline-lean.txt`.

The producer is `crates/axeyum-lean-kernel/tests/rado_shell_arithmetic.rs:1512`
(`export_probe_renders_a_real_lean_module`), calling
`render_lean_module_compact_with_inductives("shell_closed_form", goal, proof,
&[nat, eq])`.

Root cause confirmed at source level before touching anything:
`lean_pp.rs:409 render_real_inductive` documents at lines 415-421 that it only
renders "non-parametric, non-indexed" inductives and otherwise "returns None" —
**the guard is not implemented**. It renders any inductive by printing the whole
kernel type after the colon (so every parameter becomes an index) and the whole
constructor type verbatim (so the self-reference keeps its `.{u}` and the
parameter telescope is repeated). `num_params` is available on
`Declaration::Inductive` (`env.rs:191`) and is referenced zero times in
`lean_pp.rs`.

## 21:3x — the coordinator's item 5 (`AXEYUM_LEAN_BIN`) is real, and it is bigger than "8 skipped suites"

`grep -rn AXEYUM_LEAN_BIN` finds 8 suites. Ran all of them against
`~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean` with
`AXEYUM_REQUIRE_LEAN=1` (so a missing binary is a failure, not a skip):

| suite | result |
|---|---|
| `axeyum-lean-kernel` real_lean_inductive_crosscheck | 1 passed |
| `axeyum-lean-kernel` real_lean_nat_literal_crosscheck | 1 passed |
| `axeyum-lean-kernel` real_lean_structure_eta_crosscheck | 1 passed |
| `axeyum-lean-kernel` real_lean_strict_positivity_crosscheck | 1 passed |
| `axeyum-solver` diophantine_lean_reconstruct | 5 passed |
| `axeyum-solver` int_inequality_lean_reconstruct | 14 passed |
| `axeyum-solver` lean_crosscheck | 13 passed, 1 ignored (corpus-scale) |
| `axeyum-solver` regex_emptiness_lean_reconstruct | 4 passed |

39 tests, 0 failures. Vacuity control run, not assumed:
`AXEYUM_LEAN_BIN=/nonexistent/lean AXEYUM_REQUIRE_LEAN=1` makes
real_lean_inductive_crosscheck **FAIL** ("AXEYUM_REQUIRE_LEAN=1 but no Lean
binary was found"), so the passes are not the skip path.

This falsifies the strong reading of F-C1/F-C3 ("axeyum to Lean: broken").
Real Lean 4.30.0 accepts axeyum-generated modules today for LRA / LIA / EUF /
UFLIA interpolants, diophantine refutations and regex-emptiness, **including
four tamper negative controls where real Lean rejects a mutated module**
(`lean_crosscheck.rs:3035,3144,3264,3406`). `#print axioms` also runs in those
suites — `real_lean_inductive_crosscheck.rs:121` asserts the theorem name
appears in `#print axioms` output.

What is actually broken is narrower and now precisely stated: **modules that
emit a *parametric or indexed* inductive as a real Lean `inductive`.** The
Rado shell module is the only one that does (it passes `&[nat, eq]`, and `Eq`
has 2 parameters and 1 index). Everything else uses flat inductives or the
axiom rendering.

Started `lean_crosscheck -- --ignored` (corpus-scale) in the background.

## 21:5x — L3 done. Lean 4.30.0 accepts the Rado shell module. Exit 0.

Four defects, all in `lean_pp.rs`, all measured one at a time against real Lean:

1. **The flatness guard documented at `:214-216` and `:420-421` was never
   implemented.** `render_real_inductive` had no parameter/index test at all —
   its only `return None` paths were "not an Inductive" / "not a Constructor".
   I chose the *fix it properly* branch rather than the documented fallback:
   parameters are now printed before the colon from
   `Declaration::Inductive::num_params`, indices after it, and the constructor
   types have the same parameter prefix stripped and are rendered with the
   inductive's parameter binders in scope. Both doc comments were rewritten to
   describe what the code now does, and the residual `None` cases (mutual group,
   telescope shorter than `num_params`) are now real, implemented guards.
2. **`.{u}` on the self-reference.** Constants in a new `locals` set render bare
   — no `@`, no universe arguments — because inside its own block the inductive
   is a local.
3. **Codegen.** The module header now opens `noncomputable section`. Verified
   separately that Lean 4.30 does *not* object to a computable `def` inside one
   and that an unclosed section at EOF is accepted.
4. **The one nobody had found: parenthesized partial applications.** After 1-3
   Lean still failed with `Unknown constant CoeFun` — the error the coordinator
   hit by hand and read as "the elaborator inserts coercions, surface syntax is
   a dead end". It is not. `(@Eq.refl.{1} AxNat) AxNat.zero` fails because Lean
   inserts a constant's pending *implicit* arguments as soon as a parenthesized
   application is complete, so the parenthesized head elaborates to
   `Eq AxNat ?x ?x` — not a function — and Lean reaches for `CoeFun`. Measured
   directly:

   ```
   #check @Eq.refl.{1} AxNat AxNat.zero    -- Eq AxNat AxNat.zero AxNat.zero
   #check (@Eq.refl.{1} AxNat) AxNat.zero  -- error: Unknown constant `CoeFun`
   ```

   The printer emitted `((f a) b)`. Both rendering engines now print one flat
   left-associated spine (`app_spine`). Related: Lean makes an inductive's
   parameters implicit in its constructors regardless of the declared binder
   annotation (`@Eq.refl : ∀ {x0} {x1}, …`), so regenerated constructors joined
   the `@` set alongside regenerated recursors.

Result, on the re-emitted module (40,047 bytes, 61 lines):

```
$ lean shell_closed_form.lean
'shell_closed_form' does not depend on any axioms
EXIT=0        real 0m0.138s
```

`#print axioms shell_closed_form` has now executed for the first time and
reports **no axioms**. Non-vacuity control: mutating the theorem *statement*
(`AxNat.pow x0 (succ x1)` -> `AxNat.pow x0 x1`) gives `EXIT=1`, "Type mismatch".
Logs: `logs/after-l3-lean.txt`; artifact re-emitted in `artifacts/`.

Correction to the record: the coordinator's `CoeFun` observation and the
conclusion drawn from it ("`lean file.lean` is elaboration, not a kernel check,
so surface syntax is hostage to coercion insertion") were a *printer* bug, not
an architectural limit. The first half of the sentence stays true and matters
for L1; the conclusion does not follow.

## 22:1x — L1: the NDJSON emitter, and what the round-trip does and does not prove

New file `crates/axeyum-lean-kernel/src/lean_export.rs` (+2 lines in `lib.rs`)
emits official `lean4export` NDJSON 3.1.0 from a checked environment: dense
back-referencing name/level/expression records, one atomic record group per
inductive family group and for the quotient package, deterministic dependency
order over `NameId`s (no hash-map iteration order anywhere), explicit stack
traversals so a corpus-scale proof term cannot overflow.

New suite `crates/axeyum-lean-import/tests/export_round_trip.rs` (7 tests) plus
6 fail-closed unit tests inside `lean_export.rs`.

**Import-export-import over Lean's own output passes on all 17 committed
official v4.30 fixtures** — including mutual, nested (auxiliary recursors),
reflexive/higher-order, well-founded, projections, nat literals and the
quotient package — with ADR-0350 identity manifests equal.

Two things the round trip does NOT prove, found by deliberately breaking the
emitter and re-running (this is the part worth recording):

* Mutating one metadata field (`numIndices` -> 0) fails **6 of 7** tests. So the
  suite is not vacuous.
* Mutating the derived K-like flag (`k` -> always false) fails only **2 of 7** —
  the two tests I added *because* the importer treats `k` as descriptive. A
  round trip alone is blind to every field the importer does not re-derive.
  Those fields are `k`, `isReflexive`, `letE.nondep`. `k` and `isReflexive` are
  now compared **field for field against the official fixtures** (71 families,
  75 recursors, 12 K-like), which is a comparison against Lean's own bytes, not
  against ourselves. `nondep` remains unmodelled and is emitted `false`.

`isReflexive` was a genuine defect that only this comparison caught: I emitted a
constant `false`, and Lean marks `AxeyumConstructMatrix.MiniAcc` reflexive. It
is now derived (a constructor field that is a *function* returning the family).

Byte identity against the fixtures: **0 of 17**, and the reasons are structural
rather than fixable — Lean's exporter chooses its own name/level/expression
traversal order and emits a different number of records (e.g. 65 vs 66 on
`axeyum-probe`, 175 vs 171 on `construct-matrix-recursive-indexed`). Matching
Lean's alphabetical JSON field order *was* worth doing and is done, so records
are diffable line by line. The invariant is the identity manifest, as briefed.

Collateral, and it needs to be flagged: spine flattening (the L3 `CoeFun` fix)
changes every rendered Lean module, so four frozen `(len, fnv1a)` render pins
moved. All four are 7-12% *smaller* (1,080,361 -> 1,004,665 bytes on the
diophantine module) because the parenthesis nest is gone. Updated with measured
values, not guesses.

## 22:4x — L1b was not a research toolchain after all: real Lean's kernel now checks our export

The brief said scope external acceptance and stop; the coordinator upgraded it
to "Environment.replay via leanprover/comparator, but get the round trip first".
Both underestimated what the pinned toolchain already has. Probed instead of
assumed:

* `import Lean` works from a bare `lean --run file.lean` — no lake project, no
  network. (`Lean/Replay.olean` and `LeanChecker.olean` ship in
  `~/.elan/toolchains/leanprover--lean4---v4.30.0/lib/lean`, and
  `l_Lean_Environment_replay` / `l_Lean_Environment_addDeclCore` are in
  `libleanshared.so`.)
* `Environment.addDeclCore : Environment → USize → Declaration →
  Option IO.CancelToken → optParam Bool true → Except Kernel.Exception
  Environment` — the kernel checker, no elaboration, no codegen.
* `mkEmptyEnvironment` removes the `Quot` double-add trap entirely: nothing is
  inherited from `Init`, so the quotient package comes from the stream.

`scripts/lean/replay-lean4export.lean` (228 lines) parses our NDJSON and feeds
Lean's own kernel. Constructors and recursors inside an `inductive` record are
deliberately NOT replayed — Lean regenerates them, which is stronger, because a
later declaration mentioning our exported recursor then has to check against
Lean's.

Measured:

```
all 17 official v4.30 fixtures                accepted
axeyum Rado development (3,854 records)       accepted: 74 declaration records,
                                              10 inductive groups, 97 constants,
                                              0.9 s, EXIT=0
```

Tamper control (shell_closed_form given another theorem's closed, well-typed
proof) — Lean's kernel restates *our* theorem and refuses:

```
(kernel) declaration type mismatch, 'rado.shell_closed_form' has type
  (a a_1 : Nat) → @Eq Nat (Nat.add (Nat.mul a a_1) a) (Nat.add (Nat.mul a a_1) a)
but it is expected to have type
  (a a_1 : Nat) → @Eq Nat (rado.shellT a a_1) (Nat.add (Nat.pow a (Nat.succ a_1)) …)
EXIT=1
```

Two earlier tampers (bad `value`/`type` index) were rejected for loose bound
variables — a well-formedness rejection, not a type-checking one. I kept going
until I had a rejection that is unambiguously the type checker, because the
weaker rejection would not have supported the claim.

Committed as a gate (`real_lean_kernel_replay.rs`), negative control included.

## 22:5x — hygiene notes and gates

* Gates: `-p axeyum-lean-kernel -p axeyum-lean-import` = 38 test binaries, 0
  failures, with `AXEYUM_REQUIRE_LEAN=1`; clippy `--all-targets --all-features`
  clean; `RUSTDOCFLAGS=-D warnings cargo doc` clean; `lean_crosscheck --ignored`
  163/163 modules 0 failed both before and after the printer change.
* Disk: the shared scratchpad hit an EDQUOT mid-build ("Disk quota exceeded"
  from cargo, which looks like a compiler error). Moved my tree to
  `~/.cache/axeyum-agent-d`. Worth knowing for other lanes — /tmp is a 62G
  tmpfs shared by every agent, and four agents' `target/` directories fill it.
* Between my two commits the live copy of `lean_pp.rs` and my snapshot copy
  diverged by a helper-function extraction (someone or something refactored the
  long function in the working tree). Semantically identical, and HEAD carries
  the version I tested end to end — but "copy from snapshot, then commit"
  needs a diff check, not a copy, when the worktree is shared.
* Commits: `baf2bf644` (L3 + L1) and `2e4dfee22` (replay). Both pathspec-only,
  both verified with `git show --stat`; no other lane's files touched.

## 23:0x — collision with the codex lane, found and repaired

While I was working, the other lane committed `a10f12912 refactor(lean): keep
shared expression writer lint-clean`, which extracted
`write_application_with_shares` out of the function my L3 change had grown past
clippy's line limit. My replay commit then copied `lean_pp.rs` from my build
snapshot and **silently reverted their refactor**, replacing it with an
`#[allow(clippy::too_many_lines)]`. Semantically identical, but it was their
deliberate change and it was the better shape.

Restored in a follow-up commit, gates re-run (clippy clean; 39 suites, 398
tests, 0 failures).

Lesson, and it generalises to every lane: **"edit in a snapshot, copy the file
back" is not safe on a shared checkout even when the file is yours.** Copying
overwrites; only a diff shows what you are about to destroy. `git diff` before
`cp`, or edit the live file and build from a snapshot that is refreshed from it.

Related environment note: one `cargo test --doc` run failed with
`ld terminated with signal 7 [Bus error]` — that is the shared /tmp tmpfs at
80% capacity, not a code failure. It passes with `TMPDIR` on disk. Another
instance of a tool reporting something other than the real cause; the message
said "linking failed", the cause was a full filesystem.

## 23:2x — I turned main red, and the failure was the fourth instance of today's pathology

Coordinator: seven `*_family_generated_source_is_byte_stable` tests in
`cargo test -p axeyum-solver --lib --features full` fail on my flat-spine change.
Reproduced immediately: 187 passed, 7 failed, exactly the named seven.

**My miss, plainly.** CLAUDE.md names `cargo test -p axeyum-solver --lib
--features full` as *the* pre-merge gate for solver changes, and says in so many
words that a wrong-unsat once shipped because a lane ran targeted `--test <file>`
sweeps but not `--lib`. I ran the eight `AXEYUM_LEAN_BIN` suites, the 163-module
corpus crosscheck, both lean crates in full, clippy and doc — and skipped the one
gate the file tells you not to skip, because I had classified my change as a
lean-kernel change. It was not: `lean_pp` output is solver-visible.

**I did not paste the new numbers.** Built the A/B instead — one tree at HEAD
with `lean_pp.rs` as the only variable, swapped between 0535af82a and HEAD, each
gate run alone with its modules dumped:

* control: with the old printer restored, all seven pins pass. The pins are a
  pure function of the printer.
* content: all 15 modules identical after normalising parentheses and `@`
  (11 of 15 need no `@` normalisation).
* semantics: real Lean accepts all 15 old and all 15 new, and returns
  **byte-identical `#print axioms` output for every pair**.
* corpus: 163/163 before and after.

The `@` difference is confined to the four datatype modules — the only family
that emits real Lean `inductive`s, so the only one affected by Lean making
constructor parameters implicit. That the A/B *found* something I had not
predicted is the argument for doing it rather than asserting "it's just parens".

**Instrument replaced, per my own F-D4.** Each gate now diffs against a
committed `.lean` fixture (first differing line + the bless command in the
failure message), and `tests/lean_module_fixtures.rs` runs every committed
fixture through real Lean — 15 accepted, `#print axioms` confirmed to execute,
no `sorryAx` — with a negative control that swaps one assumed hypothesis into
the proof term and requires Lean to reject it. The inventory assertions run
without Lean so an emptied fixture directory cannot pass quietly.

**The through-line the coordinator named, in my own words.** Four forms today,
same disease — an assertion nothing can interpret:

1. a doc comment describing a flatness guard the code never had;
2. `which lean` returning nothing, recorded as a fact about the machine;
3. a corpus of 163 modules that could not reach the defect because every
   fixture inductive is a flat enum;
4. a `(length, hash)` pin whose failure message is two integers — and whose
   previous move was resolved by *writing a note next to the new number*.

In each case the artifact asserted something true-ish and supplied nothing a
reader could check it against. Fixtures, `#print axioms` output, and negative
controls all share the property the hash lacks: when they change, you can see
what changed and decide whether it is right.

Gates after the fix: `-p axeyum-solver --lib --features full` **1121 passed,
0 failed** (re-verified at HEAD f20f2bef1 after other lanes' commits); clippy
`--all-targets --all-features` clean; rustdoc `-D warnings` clean; all eight
`AXEYUM_LEAN_BIN` suites green; `lean_crosscheck --ignored` 163/163.

## 23:3x — attribution note on 5f07145e1

The coordinator attributed `5f07145e1` ("swept agent-f's ADR-index line") to my
lane. It is not mine: my commits are `baf2bf644`, `2e4dfee22`, `c33553e72` and
`test(solver): replace the render pins…`. `5f07145e1` is *feat(lean): prove Nat
order antisymmetry*, touching `nat_prelude.rs`, its tests, `PLAN.md`,
`docs/research/09-decisions/README.md` and `adr-0410-*` — the R1/R2 Lean
requirements lane. Every commit in this checkout carries the same git author, so
lane attribution by `git log --author` cannot work; the file set is the only
signal. Recorded in FEEDBACK as F-D7, together with the real finding underneath
it, which stands regardless of who did it: the ADR index README is a shared
append point that pathspec discipline does not protect.
