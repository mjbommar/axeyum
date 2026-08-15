# Diary: the front door was answering a different question

Lane: `lra-dispatch`. Date: 2026-08-15. Decision:
[ADR-0458](../research/09-decisions/adr-0458-lean-modules-declare-whether-they-contain-reasoning.md).

## The defect, as two lanes found it

`prove_unsat_to_lean_module` is the obvious entry point for "turn this unsat into
a Lean proof". Pointed at a pure-`Real` conjunctive `QF_LRA` query it returned
`ProofFragment::LraDpll`, whose module is this, in full:

```lean
axiom axeyum.reconstruct.prop._0 : Prop
axiom axeyum.reconstruct.hyp._1 : axeyum.reconstruct.prop._0
axiom axeyum.reconstruct.hyp._2 : Not axeyum.reconstruct.prop._0
theorem axeyum_refutation : False :=
  axeyum.reconstruct.hyp._2 axeyum.reconstruct.hyp._1
```

It kernel-checks. It is `sorry`-free. It contains no arithmetic, and it is
byte-identical for **29** unrelated routes. The `infeasibility` lane hit it
walking a scheduling core to the kernel and measured that
`ProofFragment::Lra` — the genuine Farkas reconstructor — occurred in the whole
tree at exactly two places, its produce and its consume site, with **no test
asserting that any query reaches it**. The `ordered-ring-reconstruct` lane hit it
from the other side, declined to generalize a shim ("an axiom-free theorem that
says nothing"), and wrote that fixing the dispatch was now *more* worth doing.

Two things needed doing, and they are different things: make the route reach the
reconstructor, and stop a contentless module from passing as a proof. The second
is the larger of the two, because 28 other routes emit the same shim and the
`Lra` fix does nothing for them.

## 1. The dispatch

`scan_arithmetic_proof_fragment` tried `lra_dpll_refutation_certifies` before
falling through to `ProofFragment::Lra`, so the lazy-SMT arm — which certifies
conjunctive systems perfectly well — shadowed the genuine arm for exactly the
queries the genuine arm was built for. `Lra` was reachable only as the final
`else`, which is why no test could reach it.

There is a new arm ahead of the lazy-SMT one, and the shape of its predicate is
the whole design:

```rust
} else if lra_farkas_reconstruction_certifies(arena, assertions) {
    ProofFragment::Lra
} else if lra_dpll_refutation_certifies(arena, assertions) {
```

`lra_farkas_reconstruction_certifies` has two gates in cost order. First
`lra_farkas_certificate` must return a self-checked certificate — cheap, and the
same decision the lazy-SMT arm runs anyway. Then **the reconstruction itself must
build and the kernel must infer it to `False`.** The second gate is the point: a
certificate whose *shape* `reconstruct_lra_proof` declines (a later slice) would,
under a cheap sort-and-shape test alone, have been routed into a hard error where
it previously reached a working — if contentless — route. Trial-building means the
reordering can only move queries from "shim" to "arithmetic", never to "declined".
It costs a second reconstruction, and I took that cost deliberately rather than
thread built kernel state out of a classifier that is a pure predicate on
`&TermArena`.

The gating helper is now shared: `lra_term_infers_false` is called both by the
classifier and by `gate_and_render_lra_module`, so the check that decides a query
belongs on this route is literally the check that later accepts it.

**Measured.** `x < 0 ∧ 0 ≤ x` and `x+y ≤ 0 ∧ 1 ≤ x ∧ 1 ≤ y` both reach
`ProofFragment::Lra` through `scan_proof_fragment` and through
`prove_unsat_to_lean_module`. The emitted module carries `axiom Real : Sort (1)`,
`Real.add_le_add`, `Real.lt_irrefl`, one `axeyum.reconstruct.lra.hyp._N` per
asserted row, and one `axeyum.reconstruct.lra.x._N` per variable. Two of the
seven new tests assert exactly that content, because "kernel-checked and
`sorry`-free" is true of the shim too and therefore proves nothing.

Three existing tests asserted `LraDpll` for `x < 0 ∧ 0 ≤ x` and now assert `Lra`.
Nothing else moved: the two cvc5 `QF_LRA` audit rows in `lean_crosscheck`
(`ite-lift`, `simple-lra`) are genuinely Boolean-structured and stay on
`LraDpll`, and `DisjunctiveLra` is unaffected (it is tried earlier, and the
Farkas predicate declines a disjunction outright).

And on the instance this started from — the 60-row `schedule-deadline` model, its
measured-irreducible 5-row core, via
`examples/infeasibility_farkas_lean.rs --require-kernel`:

```
facade fragment     Lra
facade module       46 line(s)
facade content      carries ordered-field content
facade self-label   theory-reconstruction
strict facade       ACCEPTED as Lra
kernel-lean route   REACHED (term infers to False)
```

That is the line the `infeasibility` lane had to print as `LraDpll` /
`STRUCTURAL SHIM`.

## 1a. The example's own shim detector was broken, and the cross-check found it

I wrote "keep the shim detection, and keep it as two independent instruments,
because a detector only exercised while it reports the bad case is one nobody
notices going blind." It found one on its first run — its own.

`infeasibility_farkas_lean` classified a module by looking for a line beginning
`axiom hyp` whose type mentions ` le ` or ` lt `. The reconstructor mints
`axeyum.reconstruct.lra.hyp._N`, so that prefix **never matched**, and the
theorem's term is on the following (indented) line, so the `theorem ` arm never
matched either. The predicate returned `false` for a genuine arithmetic module.
It gave the right answer for exactly as long as the answer was "shim", and the
first run after the dispatch fix printed `STRUCTURAL ATTESTATION` for a module
full of `Real.le` — caught only because the second instrument disagreed.

It now classifies on the declared **name** and the declared **type**
(`…lra.hyp._N : Real.le …`), which is what the example's own axiom-counting code
a hundred lines further down had been doing correctly all along. The two-detector
check is now graded rather than symmetric: `arith_content` with a
`structural-attestation` label is impossible by construction and always an error;
the converse is an error only when the facade routed to `Lra` (the case this
example pins), because the structural scan only knows the LRA reconstructor's
naming and would otherwise mis-fire on a non-LRA theory route.

## 2. What happened to the shim

**Kept, marked, and no longer available from the honest entry point.** Removing
it was not defensible on evidence: it is load-bearing for 29 routes, four of
which (`LraDpll`, `ArithDpll`, plus the datatype and array structural families)
are exercised under a real Lean binary by `lean_crosscheck`, and for those routes
the Rust certificate genuinely *is* the evidence — the module was never the
carrier. What was wrong was not that it exists; it is that it was
indistinguishable from a proof.

Four changes, at four different distances from the caller:

**The artifact says what it is.** Every structural attestation now opens with

```
-- axeyum-lean-module-content: structural-attestation
-- refuter: lra_dpll
--
-- WARNING: this module contains NO theory reasoning. ...
```

A caller holding only the rendered source can classify it. This matters more
than the typed API: modules get written to files, pasted into issues, and
attached to facts, and at that point the type is gone.

**The type says what it is.** `LeanModuleContent::{TheoryReconstruction,
StructuralAttestation}` and `ProofFragment::lean_module_content() ->
Option<LeanModuleContent>` — an exhaustive match, so a new fragment does not
compile until someone states which of the two it is. `None` is
`ProofFragment::Unsupported`, which emits no module at all.

**The two are cross-checked on every call.** `gate_module_content` reads the
class off the rendered artifact and compares it to the table, and
`reconstruct_proof_fragment_to_lean_module` refuses to return a module whose
class disagrees (`ReconstructError::ModuleContentMismatch`). The table is
hand-written and hand-written tables drift; this one fails loudly the first time
a drifted route is exercised, rather than relabelling a shim as arithmetic. It is
the same discipline as printing the un-generalized footprint beside the
generalized one: a classification you never see contradicted is not a
measurement.

**The honest entry point declines.** `prove_unsat_to_lean_theory_module` returns
`ReconstructError::NoTheoryContent { fragment }` rather than a module with
nothing in it. This is the `Evidence`/`CheckOutcome` distinction the brief named:
"nothing to check" is not "checked and failed", and it is certainly not
"checked". The decline says nothing against the refutation — the query is still
`unsat` and the route's certificate still verified — only that the certificate
has no Lean reconstruction yet.

`prove_unsat_to_lean_module` keeps its signature (199 call sites in-workspace)
and its behaviour, with the caveat now in its own doc comment under a heading
that says the returned module is not always a proof of your query.

The consumer surface is marked too: `axeyum_property::LeanModule` gained
`content()` and `theory_source()` (the source *only* when it reconstructs the
reasoning), and `LeanSummary` gained a `content` field, because a summary that
reported `status: Available` plus a fragment name plus a byte count could not
distinguish a proof from a shim, and that is precisely what a frontend shows.

### Can a caller still receive a shim believing otherwise?

Not without ignoring four separate signals — but I will not claim it is
*impossible*, because it is not. `prove_unsat_to_lean_module` still returns
`(ProofFragment, String)` and a caller who ignores the marker, the doc, the typed
classifier and the strict door will get a shim, exactly as before. Making it
type-impossible means changing that return type at 199 call sites across five
crates in a shared checkout, which is a refactor, not this lane. What is now true
is that no caller can do it *without the fact being in their hands* in the
artifact, in the API, and in the error type — and that the cross-check makes the
classification a live measurement rather than a comment.

## 3. The QF_LIA gap is not an integer-reasoning gap

The `infeasibility` lane recorded its two integer instances as having "no Farkas
path at all", `lra_farkas_certificate` being real-only, and called it a fragment
boundary. I scoped it, and the boundary is in a different place than that says.

Both integer instances' **LP relaxations are infeasible**, and z3 4.13.3 returns
the *identical* core from the relaxation that it returns from the integer
problem:

| instance | integer core | relaxed (`Int` -> `Real`) core | same rows |
|---|---:|---|---|
| `roster-icu-night.smt2` | 5 | `unsat`, 5 rows | yes |
| `loadplan-hazmat.smt2` | 14 | `unsat`, 14 rows | yes |

So neither refutation needs integrality. Each is a rational Farkas combination —
and a rational Farkas refutation is valid in **any** ordered commutative ring
with 1, which is exactly the 22-law interface `generalize_over_ordered_ring`
already abstracts over, and of which ℤ is exactly the model ADR-0456 built.

What actually blocks the route is a **sort gate, not a theory gap**:
`crates/axeyum-solver/src/lra.rs` accepts a constraint only when
`arena.sort_of(term) == Sort::Real` (`is_real`, line 1169) and only for the
`Op::Real*` order opcodes; an `Op::IntLe` over `Int` variables falls to
`"assertion is not a conjunctive linear real constraint"`. The pigeonhole
character of the load plan is a red herring for this purpose — z3 refutes the
relaxation.

So the slice, for whoever takes it, is narrow and well-shaped: teach the
conjunctive decision procedure to collect `Op::Int*` constraints into the same
`LinR` rows (the coefficients are already rationals), and reconstruct the
resulting certificate over the ordered-ring interface, instantiating at `Int`
rather than `Real`. It needs no integer-specific reasoning, no cuts, and no new
kernel feature. What it does need is a **soundness-negative** pass first: an
integer system that is LP-**feasible** and integer-infeasible must keep declining
this route (that is `Diophantine`/`IntInequality` territory), and one that is
LP-feasible and integer-feasible must not be refuted at all. I did not build it;
I am recording that it is a sort bridge plus an instantiation, not a fragment.

## Where this stops

1. **`prove_unsat_to_lean_module`'s return type is unchanged**, so the shim is
   still reachable by a caller who reads none of the four signals. See above; I
   would rather say this than imply a guarantee the types do not give.
2. **The 28 non-arithmetic structural routes are marked, not fixed.** Every one
   of them still hands back a module containing none of its reasoning. Marking
   converts a silent misreport into a visible gap, which is the prerequisite for
   closing it and is not the same as closing it.
3. **The dispatch fix reaches conjunctive real systems only.** A Boolean-
   structured `QF_LRA` row with two or more clauses is outside both the
   conjunctive Farkas path and `DisjunctiveLra` (which handles exactly one
   clause), and still lands on `LraDpll`. The natural next slice is
   multi-clause `DisjunctiveLra`, not more dispatch work.
4. **Trial reconstruction costs a second build**, and I did not isolate that
   cost. It *completes* on the 60-row `schedule-deadline` core — the facade
   returns `Lra` with a 5,105,082-byte kernel module, so the double build is
   inside a run that finishes — but I did not time the classifier separately
   from the reconstruction, and I am not going to imply a number I did not take.
   If it turns out to matter, the fix is to let the classifier return the built
   context, not to weaken the predicate.
5. **The hypothesis-footprint gap both prior lanes named is untouched.** The
   `lra.hyp._N` axioms are still canonical `le L zero` props with generated names
   and no link back to the originating assertion. Reaching the real reconstructor
   makes that gap *reachable from the front door*, which arguably raises its
   priority.

## Two things I found on `main` that are not mine

Both are recorded here because a lane that trips over a red gate and says nothing
leaves the next lane to rediscover it.

**`main` is red on three golden module pins.** A full `--no-fail-fast` sweep of
`axeyum-solver --features full` reports **280 suites, 3,822 tests passing, 3
failures**, and all three are the same defect:

| suite | test | pinned bytes | actual |
|---|---|---:|---:|
| `quant_affine_growth_lean` | `repair_const_nterm_reconstructs_and_routes` | 79,801 | **174,524** |
| `quant_eq_partition_lean` | `sdlx_reconstructs_genuine_nested_quantifiers_and_routes` | 51,989 | **112,303** |
| `quant_residue_lean` | `committed_clock_rows_reconstruct_and_route` | 33,339 | **83,060** |

Measured, not assumed. A `git archive HEAD | tar --touch -x` snapshot with **only
this lane's files overlaid** reproduces the first one byte-for-byte, and the same
snapshot with those files **restored from `HEAD`** reproduces all three
byte-for-byte — i.e. they fail at committed `HEAD` with none of my work present.
Every one of the three asserts on a **direct** call into `int_reconstruct`, which
is not on any path this lane touches, and every one roughly doubles (2.1x-2.5x),
which says one upstream change, not three. The likely origin is `d326c74af`
("settle the WHNF cache key, then land K-like reduction"). Modules that double in
size are a substantive change, so re-pinning three hashes without their owner
understanding *why* would be exactly the wrong move — and CLAUDE.md's rule ("parse
the value the failing test prints, never type it") is about a pin you *meant* to
move.

**The `F:schedule-critical-chain-infeasible` axiom count has drifted 30 -> 26.**
The fact records "21 ordered-field prelude + 4 variable + 5 hypothesis"; the
example now measures **17 + 4 + 5**. The `checker_command` still passes, because
what it asserts is `hypotheses == core.len()` (5 == 5) — so this is a stale
`notes`/`axiom_footprint`, not a failing gate, and it is the kind of drift that
survives precisely because the checker pins the other number. Same origin class
as above; the fact belongs to the `infeasibility` lane.

## Controls

- `cargo test -p axeyum-solver --lib --features full`: **1148 -> 1155**, green
  (seven new in `reconstruct::tests::lra_dispatch_tests`).
- `cargo test -p axeyum-solver --features full --no-fail-fast`: **280 suites,
  3,822 tests passing, 3 failed** — the three golden pins above, all reproduced
  at committed `HEAD`.
- `cargo test -p axeyum-property --all-features`: 23 tests, green.
- `cargo clippy -p axeyum-solver -p axeyum-property --all-targets --features full
  -- -D warnings`: clean. Run in the snapshot, because `-D warnings` on this
  worktree fails in another lane's uncommitted `axeyum-cas/src/geometry_certify.rs`.
- `scripts/check-lean-gate.sh` under Lean 4.30.0: **12 suites, 49 tests, 113
  real-Lean checks (floor 105) — OK**, unchanged by this lane. Also run in the
  snapshot: on the worktree the gate cannot run at all right now, because another
  lane's in-flight `axeyum-lean-kernel` edit does not compile
  (`cannot find type StringLiteralTable in module tc`), which takes three suites
  to zero tests and the count to 43. That is worth saying plainly — the gate's
  own "zero tests is a failure" ratchet is what surfaced it.
- `validate-facts.py`: **98 facts, 0 errors**, `kernel-lean=32`, 31 axiom-free.
- `scripts/check-links.sh`: all links ok.
- `infeasibility_farkas_lean --require-kernel` on `schedule-deadline.smt2`: exits
  0 with `facade fragment Lra`.

## I swept another lane's line anyway, and the mechanism is new

`c391b36d4` contains a one-line edit to `docs/reference/examples.md` that belongs
to the `axeyum-cas` lane (`geometry_cofactor_routes`: "killed at 8 minutes" ->
"killed at 7.5 minutes ... without returning"). Nothing was lost or corrupted —
their line is committed exactly as they wrote it, and their worktree matches
`HEAD` — but it is attributed to `lra-dispatch`. Disclosed rather than rewritten,
following `ae589be97`'s precedent and CLAUDE.md's absolute bar on history
rewrites in a shared checkout.

**What is new is that I did the documented defence and it did not work.** I ran
`git diff docs/reference/examples.md`, saw the foreign hunk, and did *not*
`git add` the file. I split the diff at `-U0`, dropped the other lane's hunk by
name, and applied only mine with `git apply --cached --unidiff-zero`. The index
then held exactly my one line — `git diff --cached --stat` said `1 insertion(+),
1 deletion(-)`, and I checked.

Then I ran `git commit -m … -- <paths>`, and the commit came out with two lines
changed.

**`git commit -- <pathspec>` does not commit the index. It commits the WORKTREE
content of those paths, discarding what you staged for them.** That is documented
git behaviour and it is the exact opposite of what the multi-agent rule in
CLAUDE.md leads you to expect: the rule says "pathspec-only commits, always",
and the pathspec is precisely the thing that threw my careful staging away. So
the guidance has a hole in it — index-level hunk staging, the one tool that
*can* separate two lanes inside one file, is silently defeated by the very
incantation the rule mandates.

Reproduced in a throwaway repo, with the pathspec as the only variable. Two lines
changed in the worktree, ten padding lines apart so they are separate hunks; one
hunk staged via `git apply --cached --unidiff-zero`; index confirmed at
`1 insertion, 1 deletion`:

| commit form | what landed |
|---|---|
| `git commit -m … -- f.txt` | **both** lines — the staged hunk and the other one |
| `git commit -m …` (no pathspec) | **only** the staged line |

Same setup, same index, opposite result. Recorded with the control because a
claim about a tool is worth what its negative case is worth.

So: to commit one hunk of a shared file, stage it, confirm the index with
`git diff --cached --stat`, and commit with **no pathspec**. The risk moves from
"the worktree silently overrides you" to "another lane staged something", which
is at least visible in `git diff --cached`. Or — better — don't share the file.

## What I would tell the next person

**A shared emitter is a shared claim.** One helper,
`reconstruct_checked_structural_certificate_to_lean_module`, produces
byte-identical output for 29 routes. That is good engineering and it is exactly
why the defect scaled: fixing the LRA dispatch alone would have left 28 routes
misreporting, and it would have looked like the problem was solved. When a defect
turns out to live in a shared helper, the fix belongs in the helper even if your
lane is named after one of its callers.

**"It kernel-checked" is a property of the artifact, not of the claim.** The shim
passes every test we normally write — it type-checks, it has no `sorryAx`, it
declares a theorem of type `False`. Every one of those assertions is true and
none of them is about the query. The tests I added assert *content*: named
prelude laws, one hypothesis axiom per asserted row, the variables. That is the
only kind of assertion that could have failed on the shim.
