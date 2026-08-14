# Batch 2 — queued, fires as batch-1 slots free

Capacity is 2-3 agents at a time. Batch 1 is agent-a (off-diagonal Schur),
agent-b (R_4(5,4)=741), agent-c (the `a^k` line). Each of these launches when a
slot opens, in this priority order.

## B2-1 — the Lean export route (L1/L3), highest value, fully unblocked

Coordinator measurement F-C1 established that `lean proofs/shell_closed_form.lean`
fails with 22 errors in 0.175 s and that the cause is architectural: surface
syntax hands the artifact to Lean's *elaborator*, not its kernel.

### Reconnaissance done by the coordinator — read this before starting

**The bridge is already built in one direction.** `axeyum-lean-import` consumes
official `lean4export` NDJSON 3.1.0 fail-closed, and the repository ships
**genuine v4.30 fixtures matching the installed toolchain** —
`docs/plan/fixtures/lean4export-v4.30-*.ndjson` (construct matrix, mutual
cross-computation, nested repeated container, recursive IH vector/acc) — with a
test suite behind them (`crates/axeyum-lean-import/tests/lean4export_v31.rs`,
`official_construct_matrix.rs`, `official_mutual_inductive_groups.rs`,
`official_nested_inductive_groups.rs`, `official_recursive_computation.rs`,
`wire_mutation_corpus.rs`). So **Lean-to-axeyum works and is tested**;
axeyum-to-Lean is the missing half.

**`leanchecker` is NOT the validator to aim at.** Its strings show it operates
on `.olean` files ("Could not find any oleans for:"), i.e. it re-checks compiled
modules; it does not read export text. `lean --help` offers `-o` (write olean)
and `--json` (diagnostics as JSON) — there is no built-in export flag in 4.30;
`lean4export` is a separate tool and is not installed. Do not burn hours
discovering this.

**The strongest validation needs no external tool at all.** Emit `lean4export`
NDJSON 3.1.0 from `axeyum-lean-kernel`, read it straight back through
`axeyum-lean-import`, and compare **ADR-0350 canonical identity manifests** —
structural content digests and direct-dependency digests per declaration, which
by construction ignore wire and arena allocation order. Emitter and importer
were written against the same external spec but share no code, so a round-trip
that reproduces the identity manifest is a real differential test, not a
tautology. That is the deliverable to aim at first.

Then, and only then, the external leg: emitting a form some third-party checker
(Trepplein, nanoda, lean4lean) will accept, or producing oleans via Lean itself.
Scope that second; the round-trip is what makes the claim.

Job: emit official **`lean4export` format 3.1.0** from `axeyum-lean-kernel`,
validate by round-trip identity manifest as above, then re-emit the Rado
shell-bound module so the paper's Lean paragraph becomes a claim about a kernel
rather than about a parser.

Also L3: fix the three surface defects (`noncomputable`, the `Eq.{u}`
self-reference, parameter-vs-index inductive form) so the readable projection is
also valid Lean.

**Hazard:** `crates/axeyum-lean-kernel/{env,inductive,lib,quotient,string_prelude,tc,tests}.rs`
carry another lane's uncommitted WIP (the Lean requirements track, R1/R2).
This agent must build from a `git archive HEAD` snapshot and coordinate before
committing anything in that crate. `lean_pp.rs` is already corrected and
committed at `febbcc991`.

## B2-2 — van der Waerden, and it inherits agent-a's work

`w(2;3,t)` is **off-diagonal**: colour 1 forbids 3-term APs, colour 2 forbids
t-term APs. So it needs exactly the per-colour `ColouringProblem` extension
agent-a is landing — which makes it the cheapest possible proof that the
generalization was worth doing, on a second family in a different area of
mathematics.

Two jobs, in order:
1. **Certify a known value with zero external tools.** `w(2;3,19) = 349` is the
   last computed value in the series; `W(4,3)=76`, `W(2,5)=178`, `W(3,4)=293`
   are the diagonal ones. As far as I can establish, none has ever been
   certified by a fully pure-Rust, self-checked pipeline. Formulas are tiny.
2. **Probe `w(2;3,20)`**, open since 2011, conjectured exact at 389. 778
   variables, ~42k clauses — trivial to encode, brutal to search. A probe with
   an honest cell census is the deliverable; a result would be a headline. Do
   not let it eat the budget for job 1.

## B2-3 — `R_4(6(x-y)=5z) = 1501`

The second open cell of the k=4 row. Lower bound already banked as
`rado-r4-a6-b5-frontier` (`> 1500`), free from Theorem 1, written down rather
than searched. Needs one cover at n=1501.

**Sequenced after agent-b**, because it should use the adaptive tree cover
rather than re-running the flat depth-6 approach, and because it wants the same
class of hardware.

## B2-4 — Ahmed-Zaman-Bright (SC^2 2025) Conjecture 1.1 at a = 31

`R_3(ax+by=bz) = a^3+a^2+(2b+1)a+1` for coprime `a > b >= 3` with
`a^2+a+b > b^2+ba`. Their Theorem 1.3 **proves the lower bound**, so each point
is one refutation. They computed `a <= 30`; the frontier is `a = 31`
(n ~ 31,000, 3 colours, ~10M width-3 clauses). Three colours are far cheaper
than four, and they explicitly declined 4+ colours "due to rapid growth" —
which is where our k=4 machinery is the differentiator.

Needs a new `ColouringFamily` for `a x + b y = b z`. Sequenced after agent-a so
the trait is settled.
