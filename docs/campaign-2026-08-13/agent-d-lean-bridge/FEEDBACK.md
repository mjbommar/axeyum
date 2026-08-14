# agent-d feedback for the axeyum roadmap — 2026-08-13

Cited by file and line. Ordered by what I would do next.

## F-D1 (P0) — A prose-only guard is a wrong-answer generator, and we have a class of them

`crates/axeyum-lean-kernel/src/lean_pp.rs:214-216` (before this session) told
callers that "only non-parametric, non-indexed inductives are emitted as real
`inductive`s; a listed inductive that is parametric or indexed falls back to the
axiom rendering (a defensive guard)". `:420-421` repeated it inside the
function. **The function contained no such test.** Its only `return None` paths
were "this name is not an `Inductive`" and "a listed constructor name is not a
`Constructor`".

The consequence was not a cosmetic defect: a parametric family was emitted with
its whole telescope after the colon, so every parameter became an *index*, Lean
generated a different recursor, and the only non-trivial artifact this project
ever handed to official Lean was rejected. It survived because the entire
cross-check corpus builds flat enums (`add_inductive(two, &[], 0, prop, …)` in
`real_lean_inductive_crosscheck.rs:41-48`), so the corpus was structurally
incapable of reaching the guard.

This is the CLAUDE.md "tools have lied more often than the solver has been weak"
list, one level deeper: the *comment* lied, and no measurement contradicted it
because the corpus could not reach the code.

**Concrete asks**

1. A comment describing a check the code does not perform should be treated like
   a wrong verdict, not like a stale doc. Add it to the CLAUDE.md gotchas list
   in those words.
2. Where a guard is claimed, the test that exercises the *rejected* branch is
   part of the guard. `render_real_inductive` now has real `None` paths (mutual
   group, telescope shorter than `num_params`) — and they need a test that
   reaches them; I have not written one for the mutual case.
3. Sweep for siblings. The pattern to grep is a doc comment containing "falls
   back", "guard", "only … are", or "otherwise returns `None`" in a function
   with no matching branch. I found this one because I was pointed at it.

## F-D2 (P0) — Eight cross-check suites were dark for want of one environment variable

`docs/plan/lean-kernel-requirements-2026-08-13.md:75` records that eight suites
consult `AXEYUM_LEAN_BIN` and **skip**. They do not need to. The pinned
toolchain is installed at `~/.elan/toolchains/leanprover--lean4---v4.30.0`, and
with `AXEYUM_LEAN_BIN` pointed at it plus `AXEYUM_REQUIRE_LEAN=1` all eight run:
39 tests, 0 failures, and `lean_crosscheck -- --ignored` checks **163 of 163
modules across 70 families**. The earlier "toolchain absent (verified)" finding
in `docs/plan/next-actions-from-the-rado-paper-2026-08-12.md` A2 measured `PATH`,
not the machine.

**Ask:** make `AXEYUM_LEAN_BIN` resolution part of the repo's tooling rather
than each developer's shell — a `justfile` recipe that discovers
`~/.elan/toolchains/*/bin/lean` and exports it, and a `just check-lean` that
runs the eight suites with `AXEYUM_REQUIRE_LEAN=1`. R0.1 in the same document
(":972") asks for exactly one lane where these cannot pass by being inert; this
is that lane, and it is now cheap.

## F-D3 (P1) — External kernel acceptance is one 230-line Lean script, not a research project

F-C2 concluded that the external leg needs Trepplein / nanoda / lean4lean or
oleans, and that `lean4export` is not installed. All true, and all avoidable.
The pinned toolchain already ships everything needed:

* `import Lean` works from a bare `lean --run script.lean` — no lake project, no
  network (`Lean/Replay.olean`, `LeanChecker.olean` are present, and
  `l_Lean_Environment_replay` / `l_Lean_Environment_addDeclCore` are in
  `libleanshared.so`);
* `Lean.Environment.addDeclCore : Environment → USize → Declaration →
  Option IO.CancelToken → optParam Bool true → Except Kernel.Exception
  Environment` is the kernel type checker, with no elaboration and no codegen;
* `mkEmptyEnvironment` gives a base with nothing inherited from `Init`, which
  also removes the `Quot` double-add trap entirely.

`scripts/lean/replay-lean4export.lean` (committed) does this and accepts all 17
official fixtures plus our 3,854-record Rado export. **The roadmap should stop
listing third-party checkers as the prerequisite for external acceptance.** They
remain valuable as *diverse* checkers — a second implementation disagreeing with
Lean is worth knowing about — but they are no longer the critical path.

## F-D4 (P1, DONE) — Frozen `(len, fnv1a)` render pins are the wrong instrument

`crates/axeyum-solver/tests/diophantine_lean_reconstruct.rs:55`,
`quant_affine_growth_lean.rs:31`, `quant_eq_partition_lean.rs:49`,
`quant_residue_lean.rs:42` freeze a rendered module's byte length and FNV hash.
A legitimate printer improvement (flat application spines, which is what made
Lean accept the parametric module) moves all four, and the failure message is
two opaque integers. They caught nothing here that the real-Lean cross-check did
not catch better, and they cost a hunt.

**Ask:** replace them with (a) the real-Lean check, which these tests already
have next door, and (b) a *bounded* size assertion (`source.len() < 2_000_000`)
if the point is to notice blow-up. If exact-bytes determinism is the point, say
so and assert `render(x) == render(x)` instead, which does not move when the
renderer legitimately improves.

**Update, same day: this bit me and is now fixed.** Seven more of these pins
live in `crates/axeyum-solver/src/reconstruct/tests.rs`
(`*_family_generated_source_is_byte_stable`); I did not know about them because
I ran the eight named Lean suites and the 163-module corpus but skipped
`cargo test -p axeyum-solver --lib --features full`, which CLAUDE.md names as
*the* pre-merge gate for solver changes. `main` went red for it.

All seven are replaced by committed `.lean` fixtures plus
`crates/axeyum-solver/tests/lean_module_fixtures.rs`, which puts every fixture
through the real Lean binary with a negative control. Two things worth carrying
forward from doing it:

* Establishing that the *new* bytes are correct took an A/B with `lean_pp.rs`
  as the only variable, and it found something I had not predicted: four of the
  fifteen modules also gained `@` on constructors. "It is only parentheses" was
  wrong, and I would have written it into the commit message if I had not
  measured. Log: `logs/render-pin-ab-evidence.txt`.
* The decisive check turned out to be **`#print axioms` output equality between
  old and new**, from the real binary — same theorem, same assumptions. That is
  the property these gates were reaching for; a hash was a proxy for it.

Remaining sibling pins to convert (not done, small): none found by
`grep -rn "fnv1a\|stable_source_hash" crates/` after this change — the four in
`axeyum-solver/tests/*.rs` and the seven in `reconstruct/tests.rs` were all of
them. If a new one is proposed, the answer is a fixture plus a Lean check.


## F-D5 (P2) — A round trip cannot see what the importer does not re-derive

`crates/axeyum-lean-import/src/lib.rs:874-880` treats `isReflexive` as
descriptive, and nothing compares `k`. So an emitter that got both wrong would
pass an import-export-import round trip: measured, mutating `k` fails 2 of my 7
tests while mutating `numIndices` fails 6 of 7. I emitted `isReflexive:false`
constantly and only the field-by-field comparison against the official fixtures
caught it.

**Ask:** whenever a validation is described as "differential", write down which
fields the two sides actually compare. For this format the uncompared set is
`k`, `isReflexive`, `letE.nondep` — and `nondep` is still unmodelled by the
kernel and emitted `false`. That is a small, honest ADR.

## F-D6 (P2) — The paper's Lean paragraph and A2 need a rewrite, in both directions

`docs/plan/next-actions-from-the-rado-paper-2026-08-12.md` A2 is wrong twice:
the toolchain was present, and the export was rejected. But the correction that
went into `docs/plan/lean-export-external-validation-2026-08-13.md` overshoots
in the other direction — "the export route, not the file, is what needs to
change" and "`lean file.lean` is not a kernel check" together read as *surface
syntax is a dead end*. It was four printer bugs, and the module now checks with
exit 0.

Suggested wording for the paper, all three parts measured today:

> Lean to axeyum: our kernel independently admits Lean's own mathematics from
> official `lean4export` v4.30 exports (17 fixtures, dual-admitted).
> axeyum to Lean, surface syntax: 163 of 163 rendered modules are accepted by
> Lean 4.30.0, including the closed-form shell theorem, which `#print axioms`
> reports as depending on no axioms.
> axeyum to Lean, kernel: the same development is replayed into Lean's own
> `Environment.addDeclCore` from our `lean4export` NDJSON, with a tamper control
> that Lean's kernel rejects.

## F-D7 (P2) — Lane attribution is not recoverable from git, and the ADR index is a shared append point

Two separate things, both surfaced by `5f07145e1` being reported to me as mine.

**Attribution.** It is not mine (mine are `baf2bf644`, `2e4dfee22`, `c33553e72`
and the render-pin replacement); `5f07145e1` is *feat(lean): prove Nat order
antisymmetry*, touching `nat_prelude.rs`, `PLAN.md`, the ADR index and
`adr-0410-*`, which is the R1/R2 requirements lane. Every commit in this shared
checkout carries the same `user.name`/`user.email`, so nothing in `git log`
distinguishes lanes and the file set is the only signal. Cheap fix, and it would
have saved this exchange: have each agent append a trailer to its commits
(`Agent: agent-d-lean-bridge`), or set `GIT_AUTHOR_NAME` per lane. Worth adding
to `docs/contributor-guide/multi-agent-worktrees.md`.

**The real finding underneath, which stands whoever did it.**
`docs/research/09-decisions/README.md` is an *index* every ADR-producing lane
appends one line to. Pathspec commits stop an agent sweeping files it did not
touch; they do nothing when two agents legitimately touch the *same* file
concurrently, and the loser's line is either lost or swept into the winner's
commit — here it left `check-links.sh` failing on HEAD for ~13 minutes. Options,
cheapest first: (a) one ADR per file with the index generated by
`scripts/check-links.sh`'s sibling rather than hand-maintained; (b) an index
format where each ADR contributes its own file (`docs/research/09-decisions/
index.d/adr-0410.md`) concatenated at build time; (c) an explicit lock. The same
argument applies to `PLAN.md`, which is worse because it is the one file the
session protocol tells every lane to edit.
