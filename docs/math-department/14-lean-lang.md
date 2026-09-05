# 14 — The Lean language, as a boundary

Reviewer: the twelve chairs, each asked one question — *what would "Lean
compatible" have to mean before you would use this from Lean, or bring
Mathlib into it, and what stops you today?*
Verdict, 2026-09-05: **a kernel that agrees with Lean's on everything it has
been asked, an importer that reads Mathlib one statement at a time, and no
way for anyone outside this repository to reach either from Lean. Three Lean
gates have been red on `main` since the toolchain pin moved on 2026-09-03.**
Last measured: 2026-09-05 at `f67ce41d2`

> "You built a second Lean kernel and checked it against the first. Good.
> Now I open Lean, and I cannot import a single one of your theorems, and you
> cannot read a single one of my files. Which of us is the boundary for?"

This file is different from files 01 to 12, and different from 13. Those ask
what the *library* proves, or what the *CAS* computes. This one asks what the
**Lean boundary** does — the pinned official Lean this project cross-checks
against, the `lean4export` import route from Mathlib, the rendering of our
own declarations back into Lean, and the language itself as an input. It
exists because the Lean roadmap is four documents written between 2026-07-21
and 2026-08-30 that no longer agree with each other or with the tree, and
because the reviewers in this folder each have a stake in the boundary that
none of those documents was written to serve.

The four documents, and where each stands:

| document | date | status it claims | what is true |
|---|---|---|---|
| [compatibility roadmap](../plan/lean-system-compatibility-roadmap-2026-07-21.md) and its [L0–L10 implementation plan](../plan/lean-system-implementation-plan-2026-07-21.md) | 2026-07-21 | "active" | the plan's own tally is 21 done, 5 partial, 96 to do; not edited since 2026-08-13 |
| [complete-parity contract](../plan/lean4-complete-parity-contract-2026-07-22.md) and [registry](../plan/lean-complete-parity-v1.json) | 2026-07-22 | terminal claim `disabled` | correct, and should stay the terminal definition; last edited 2026-08-15 |
| [kernel requirements](../plan/lean-kernel-requirements-2026-08-13.md) | 2026-08-13 | WIP | its "absent" library rows are now mostly present (97 modeq, 67 gcd, 121 div/mod facts) and its driving theorem landed on 2026-09-04 |
| [library-artifact compatibility roadmap](../plan/library-artifact-compatibility-roadmap-2026-08-30.md) (C0–C5, ADR-0717) | 2026-08-30 | accepted | C0–C3 landed the same day; C4 blocked on a population; C5 not started. This is where the work actually is |

The ordering the fourth document chose — *interoperate at the artifacts that
carry mathematical meaning before imitating the language that produced them*
— is the right one and this file adopts it. The K2–K6 ladder (native parser,
elaborator, tactics, Lake, LSP, compiler) stays as the parity contract's
terminal definition and is not the queue.

## What the Lean boundary has today

Measured 2026-09-05 at `f67ce41d2`; the commands are in *How to re-measure*.

| surface | value |
|---|---|
| pin, cross-check | `lean-toolchain` = `leanprover/lean4:v4.34.0-rc1` ([ADR-1594](../research/09-decisions/adr-1594-the-crosscheck-pin-moves-to-lean-4-34-0-rc1-and-follows-the-pin-file.md)) |
| pin, Mathlib corpus | Lean `4.30.0`, mathlib4 `c5ea0035`, `lean4export` `a3e35a58`; every `F:ml430-*` fact is keyed to it |
| compatibility matrix | 13 rows: K0 1/1, K1 6/6, K2 0/2, K3 0/1, K4 0/1, K5 0/1, K6 0/1 |
| real-Lean suites in the kernel crate | 18 files (`real_lean_*`, `kernel_differential*`); gate floors 261 checks and 37 theory families |
| kernel differential corpus | 32 cases, 8 subsystems; 1 registered incompleteness (`Quot.sound` absent) ([ADR-0780](../research/09-decisions/adr-0780-the-kernel-differential-corpus-finds-real-defects-and-two-guards-survive-uncaught.md)) |
| trusted core | 5,526 function-body lines, 9 files ([ADR-1600](../research/09-decisions/adr-1600-the-kernels-metatheoretic-status-what-is-trusted-and-what-is-not.md)) |
| our theorems replayed in pinned Lean | `creal` carrier only: population 2,045, replayed 1,972, 48 `Type`-valued theorems Lean refuses as theorems, 25 blocked behind them ([ADR-0760](../research/09-decisions/adr-0760-independent-replay-is-graded-per-declaration-by-name.md)) |
| credited roots exported, reimported, Lean-checked | 9 (C2) |
| thin Lean adapter | one 8-category goal pack over one subject, `Nat.add_comm` (C3, [ADR-0935](../research/09-decisions/adr-0935-the-thin-lean-adapter-composes-c2s-two-checked-paths-and-adds-nothing-else.md)) |
| Mathlib mirrors in the ledger | 756 facts: 499 proved, 257 open; fidelity gate PASS, 742 hash-verified, 14 unpinned |
| statements in Lean surface syntax | 769 facts (`lean4-surface`); 1,971 in kernel-core rendering (`lean4`); **no native parser for either** — only real Lean can read the surface form, and it lives on one fleet host with a built Mathlib |
| labeled imports from Lean/Mathlib | 7 facts, `proof_route: imported-kernel-lean`, footprint `[propext, Classical.choice, Quot.sound]`, never counted as ours; largest closure 3,142 declarations ([ADR-1090](../research/09-decisions/adr-1090-ivt-evt-row-4-labeled-import-lands-mathlib-topology-admits-clean.md)) |
| Mathlib at scale | a full `lean4export Mathlib` is 680,925 declarations in ~4 min on s5; the declaration graph built so far is 446 declarations and 2,451 edges from 7 roots |
| native producers | `linarith`, `ring`, `simp`, `decide`, tactic combinator: 18,497 lines emitting kernel terms — over *this* kernel's preludes, not Lean goals; the matrix's K3 row does not mention them |
| **red today** | `scripts/install-pinned-lean.sh` rejects the `-rc1` pin (CI's real-Lean job red since `792224e73`); `gen-lean-complete-parity.py --check` and `check-lean-official-construct-matrix.py --check` exit 1 on a clean tree; in CI both are masked by `check-parity-freshness.py`, red since at least 2026-09-01 on the Z3 ledger |

## What each chair would say

One line each. Every absence was checked against the tree on 2026-09-05, not
against the July documents.

| # | chair | what "Lean compatible" would mean to them | what stops them |
|---|---|---|---|
| 01 | number theory | close the 257 open Mathlib mirrors; read the next thousand | statement extraction loses Mathlib's enclosing `variable` block, so a coercion-carrying statement re-parses as nothing (no screen exists); typeclass-headed statements have no record-spine target |
| 02 | constructive analysis | **export.** "Among the most complete constructive analyses anywhere" is worth nothing to a Lean user until it is a Lake package they can `import` | `creal` replays into Lean at 1,972 of 2,045, but as a census artifact, not a library; 48 theorems are `Type`-valued and Lean's kernel refuses them as theorems |
| 03 | classical analysis | bring measure theory in as labeled scaffolding | 7 imports exist and each carries Mathlib's three axioms; no decision says whether an originated theorem may *depend* on an imported one, so imports cannot compose with anything we prove |
| 04 | algebra | Mathlib's `Group` and our `AlgS.Group` should be the same thing on the wire | Mathlib is typeclass-headed and our spine is records; no correspondence is written down; the differential registers `Quot.sound` as a known incompleteness and stops there |
| 05 | geometry | render `CPoint` results into Lean | Mathlib's plane is `EuclideanSpace ℝ (Fin 2)` over classical ℝ; no statement of ours is the same statement as theirs, and nothing records the mapping |
| 06 | topology | an honest **typed decline**: "not statable here" rather than a failed import | the import route declines on unsupported constructs, not on absent carriers; a topological statement fails somewhere inside 3,000 declarations |
| 07 | combinatorics | `Nat.Finset` ↔ Mathlib `Finset` as a named bridge | the mirror-fidelity gate protects ℕ/ℤ statements by hash; nothing says when a `Finset` mirror is a different object |
| 08 | probability | same as 03 | same as 03, plus the ℚ-valued shelf has no Mathlib counterpart at all |
| 09 | category theory | universe levels that agree with Lean **exactly** | one divergence found by a gate this week (`PSigma` at `Sort (max u v)` vs Lean's `Sort (max 1 u v)`); the `max-to-imax` mutant is open; `imax` normalization is over-complete (requirements §4.6) |
| 10 | logic | the kernel *is* the paper; the paper needs the public conformance corpus, both halves | 32 hand-authored differential cases against a corpus of 189 (121 accept / 62 reject / 6 either) nobody has run; no divergence ledger |
| 11 | applied | `by axeyum` as a real tactic, and LRAT proofs Lean consumes | C3 is a Rust-side sidecar protocol with one subject; no Lean-side tactic, no Lake package, no LRAT hand-off |
| 12 | the chair | one pin, green gates, and one sentence saying what "Lean compatible" means | two pins, three red gates, and a claim surface (PLAN.md, the K3 row, next-action A9) still describing July |
| 13 | the CAS | its certificates reconstruct into kernel terms; Lean would see them only through 11's tactic | same as 11 |

## The Next Ten, in priority order

Ranked by how many chairs an item serves, then by what it unblocks. Items 1
and 2 are the preconditions for any of the rest being *citable*; items 3 to 6
are the ones that put something in a Lean user's hands; 7 to 9 are the
kernel-and-language work the logician and the category theorist need; 10 is
what makes the whole thing a claim rather than a folder.

- [ ] **1. One pin, and every Lean gate green under it.** Accept a release-
      candidate suffix in `scripts/install-pinned-lean.sh`; make the construct
      matrix read `lean-toolchain` the way the seven suites now do; amend
      ADR-1594's "no workflow edit needed". Then write down, once, that there
      are **two** pins — the cross-check toolchain and the Mathlib corpus —
      and which one every existing 4.30 claim refers to. Serves 12, and every
      other item here depends on it.
- [ ] **2. Replay every proved theorem in pinned Lean, or name the reason.**
      Extend the `creal` census to every prelude, `missing=0` enforced, with
      the `Type`-valued theorems as a typed class rather than a footnote. The
      chair's headline — 2,487 axiom-free results — becomes "and Lean's kernel
      accepts N of them" with N read from a run. Serves 10, 12, 02.
- [ ] **3. Publish the constructive analysis as a Lean library.** Render the
      `creal` prelude as `.lean` source that pinned Lean elaborates, with
      `#print axioms` empty on the Lean side, packaged for Lake. Reviewer 02's
      verdict is the strongest in the department and today no one outside can
      use the thing it praises. Serves 02, 05, 03.
- [x] **4. A carrier correspondence ledger.** *Done 2026-09-05 (ADR-1665).*
      `artifacts/carrier-correspondence/carrier-correspondence-v1.json` holds
      16 rows — `CReal` ↔ `Real`, `Nat.Finset` ↔ `Finset`, `Nat.Multiset` ↔
      `Multiset`, `AlgS.Group` ↔ `Group`, `AlgS.CommRing` ↔ `CommRing`,
      `AlgS.Field` ↔ `Field` (a constructive field with an EXISTENTIAL
      inverse over apartness, landed the same day in `53c851e5b`/ADR-1627 —
      this ledger's own first pass missed it from a stale merge base and was
      corrected before merge, see ADR-1665), `CPoint` ↔
      `EuclideanSpace ℝ (Fin 2)`, `Nat.Graph` ↔ `SimpleGraph`, `Complex` ↔
      `Complex`, Rat matrices ↔ `Matrix`, the ℚ probability shelf ↔ `PMF`,
      `Metric` ↔ `MetricSpace`, `IntSpace` ↔ the Bochner integral, `Nat.RM` ↔
      Mathlib's computability library (the brief's own "no counterpart"
      assumption was wrong — Mathlib has a general halting-problem theorem —
      and the row corrects it), `Provable`/`ipc_*` ↔ Mathlib's
      Heyting/ModelTheory, plus a bonus `Nat.Rado` `no-counterpart` row —
      graded *same-statement* (2), *constructively-stronger* (2),
      *different-object* (11) or *no-counterpart* (1), each with a witness
      theorem pair verified against the live kernel projection or, where the
      declaration postdates that projection's last regeneration, a fresh
      `shape_search` build.
      `scripts/check-carrier-correspondence.py --check` gates it exactly the
      way `check-mirror-statement-fidelity.py` gates the ℕ/ℤ mirrors, with
      nine mutation-verified guards. Serves 02, 03, 05, 07, 08; reviewer 03's
      "a different theorem" is now a table (`CC:creal-real`), not a sentence.
- [ ] **5. The statement-import blocker census, and the first screen.** Run
      every one of the 257 open mirrors plus a fresh Mathlib draw through
      statement-only import and count the decline reasons. Ship the
      coercion/`variable`-block screen at extraction time. Then C4's first
      demand-gated elaboration feature is chosen by count, not by taste.
      Serves 01, 07, 04.
- [ ] **6. `by axeyum` as a Lean tactic.** Turn the C3 sidecar protocol into
      a Lake package exposing a tactic that ships the elaborated goal to
      Axeyum and hands back a term Lean checks; first fragments linear
      arithmetic and `ring` over ℕ and ℤ, then LRAT-carrying `bv_decide`-style
      goals. Nothing is trusted on the Lean side. Serves 11, 13, 01.
- [ ] **7. The public conformance corpus and a divergence ledger.** Run
      Lean 4's own kernel test cases, report both the accept and the reject
      half, publish a gated `divergences.md` in lean4lean's shape with the
      rule that an unlisted divergence is a bug; close the open `max-to-imax`
      mutant and decide the `imax` over-completeness. Serves 10, 09.
- [ ] **8. The imported-axiom composition ADR.** Imports carry
      `[propext, Classical.choice, Quot.sound]` and are never counted as ours;
      ADR-1601 makes *our* classical principles hypotheses. What is undecided
      is whether an originated theorem may depend on an imported one and how
      its footprint is then reported. Until it is, measure theory can enter
      only as an island. Serves 03, 08, 06.
- [ ] **9. A native reader for the statement fragment.** Parse the kernel-core
      rendering (1,971 facts carry it) back into kernel terms with a
      render → parse → same-term gate, then the surface subset the Mathlib
      mirrors use, sized by item 5's census. This is the first K2 cell, it
      removes the one-host dependence for attesting a draw, and it is
      demand-gated as C4 requires. Serves 12, 01, 11.
- [ ] **10. Say what "Lean compatible" means, once.** The K profile, the
      replay census, the import tier and the two pins in one paragraph on
      the claim surfaces; the July roadmap and implementation plan marked
      historical under the C-series ordering; the K3 row decided for native
      producers (they are K3-shaped over this kernel, not over Lean goals,
      and the row should say which). Serves 12.

**What is deliberately not on this list.** A native elaborator, Lake, the
language server, the compiler and runtime, and a full Mathlib build (K4–K6):
the C5 gate says these wait until the adapter has real use and item 5's
census shows repeated friction, and no chair asked for them. The U2 official-
execution programme (3,723 CTest cases, 111 not-run attempts, zero credit
since July) should be marked historical rather than resumed. General `.lean`
input beyond item 9's fragment. Anything that would make the empty-footprint
count depend on Lean's axioms.

## The blocker

**None of a mathematical kind. One of hygiene, two of design, one of fleet.**

- **Two pins and a claim surface written for one.** Every "pinned Lean
  4.30.0" in the contract, the matrix, the adapter goal pack and the
  status files now means one of two different things. Item 1 is a morning's
  work and it is a precondition for citing anything below it.
- **Mathlib's statement conventions versus record spines.** Typeclass-headed
  statements, coercions fixed by an enclosing `variable` block, and universe
  polymorphism are how Mathlib is written; this library's spines are records
  over explicit carriers by design ([ADR-1495](../research/09-decisions/adr-1495-abstraction-over-structures-is-already-expressible-the-gap-is-surface.md)).
  The gap is surface, and it has to be measured (item 5) before it is built
  (item 9).
- **Trust composition.** Two footprint regimes exist — empty for originated
  theorems, Mathlib's three axioms for imports — and no rule says whether
  they may touch. Item 8.
- **Real Lean with a built Mathlib lives on one host.** `command -v lean` is
  empty on hosts that have it, a provisioned checkout is not a built Mathlib,
  and attestation of a draw takes 3.6 s on s5 and cannot run anywhere else
  ([lean-surface-attestation.md](../contributor-guide/lean-surface-attestation.md)).

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-05 | File created. Baseline: K0 1/1, K1 6/6, K2–K6 0; `creal` replay 1,972 of 2,045; 9 credited roots Lean-checked; 756 mirrors (499 proved / 257 open); 7 labeled imports; no native parser, no Lean-side tactic, no Lake package. Three Lean gates red on `main` since the pin moved (`792224e73`, 2026-09-03): the install script regex, `gen-lean-complete-parity --check`, `check-lean-official-construct-matrix --check`; CI's real-Lean job was green on the commit before and red on that commit; the two `--check` gates are masked in CI by the Z3 parity-freshness failure that predates them. Reported, not repaired, by the review this file came out of. | `f67ce41d2`; `gh run list --workflow ci.yml`; the commands below |
| 2026-09-05 | **Next Ten item 4 landed** (ADR-1665): the carrier correspondence ledger, 16 rows, gated by `scripts/check-carrier-correspondence.py --check` (nine mutation-verified guards, every mutation killing exactly one control test) exactly the way the ℕ/ℤ mirror-fidelity check gates `F:ml430-*`. `Nat.RM` DOES have a Mathlib counterpart (`Mathlib/Computability/Halting.lean`'s general halting-problem theorem, contra the brief's assumption), so that row is `different-object` rather than `no-counterpart`. Grade counts: same-statement 2, constructively-stronger 2, different-object 11, no-counterpart 1. | `artifacts/carrier-correspondence/carrier-correspondence-v1.json`; `python3 scripts/check-carrier-correspondence.py --check`; `python3 scripts/tests/mutation_controls.py carrier-correspondence` |
| 2026-09-05 | **Correction, same day, before merge**: this ledger's own first pass on `AlgS.Field`↔`Field` was wrong, from a stale worktree — `AlgS.Field` landed on `main` in `53c851e5b` (ADR-1627) after this lane's merge base and was measured absent. After `git merge --no-edit main` and a fresh `shape_search` release build (declarations `4291 -> 4379`), `AlgS.Field` is confirmed live (`FOUND 1`, positive control `AlgS.Group` also `FOUND 1`) with an EXISTENTIAL inverse over apartness (`mulInvEx : ∀ a, apart a zero → ∃ b, equiv (mul a b) one`), not proved tight for `CReal`. `CC:algs-field-field` is regraded `different-object` (was `same-statement` over the wrong, Eq-based `Alg.Field`): stronger hypothesis, weaker conclusion than Mathlib's total-inverse `Field`, the same non-comparable pattern ADR-1030 used for EVT. The general lesson — merge local `main` before measuring an absence — recurred a second time, independently, caught before merge rather than after. | `artifacts/carrier-correspondence/carrier-correspondence-v1.json`; fresh `shape_search` build post-merge |

## How to re-measure

```sh
# the two pins
cat lean-toolchain
python3 -c "import json;print(json.load(open('docs/plan/lean-complete-parity-v1.json'))['target'])"

# the matrix and the two status generators (each run BARE, exit read directly)
python3 scripts/gen-lean-compatibility.py --check
python3 scripts/gen-lean-complete-parity.py --check
python3 scripts/check-lean-official-construct-matrix.py --check

# the real-Lean gate and its suites (confirm a NONZERO check count)
scripts/check-lean-gate.sh --print-toolchain
ls crates/axeyum-lean-kernel/tests | grep -cE 'real_lean|kernel_differential'
grep -n 'CHECK_FLOOR=\|THEORY_FAMILY_FLOOR=' scripts/check-lean-gate.sh

# our theorems replayed in pinned Lean (creal only today; ~4 min)
cargo test -p axeyum-lean-kernel --test real_lean_replay_census

# the mirrors, the surface/core split, the imports
python3 scripts/check-mirror-statement-fidelity.py
python3 - <<'PY'
import json, glob, collections
lang, route, ml = collections.Counter(), collections.Counter(), collections.Counter()
for f in glob.glob('artifacts/facts/*.json'):
    d = json.load(open(f)); lang[(d.get('formal') or {}).get('language')] += 1
    route[d.get('proof_route', '?')] += 1
    if f.split('/')[-1].startswith('F-ml430'): ml[d.get('epistemic_status')] += 1
print(lang.most_common()); print(route.most_common()); print('ml430', dict(ml))
PY

# absence probes -- a hit must be READ, not counted, and every negative
# needs a positive control (lean_pp.rs's renderer is the control here):
grep -rn 'pub fn parse' crates/axeyum-lean-kernel/src/lean_pp.rs crates/axeyum-lean-import/src/lib.rs
grep -rln 'render_lean' crates/axeyum-lean-kernel/src/lean_pp.rs
ls scripts/lean/ | grep -ci tactic        # no Lean-side tactic
find . -name lakefile.lean -not -path './references/*' | wc -l
```

## Related

- [12-the-chair.md](12-the-chair.md) — the two questions every item here has
  to answer: what is assumed, and what did you do that nobody else did
- [10-logic-and-foundations.md](10-logic-and-foundations.md) — the kernel as
  the paper, and why the conformance corpus is item 7
- [11-applied-and-computational.md](11-applied-and-computational.md) — the
  producers that item 6 would expose to Lean
- [02-constructive-analysis.md](02-constructive-analysis.md) — the library
  item 3 would publish
- [13-computer-algebra.md](13-computer-algebra.md) — the same shape of file,
  for the other tool
- [`docs/plan/generated/lean-compatibility.md`](../plan/generated/lean-compatibility.md)
  — the status authority for the K profiles
- [ADR-0517](../research/09-decisions/adr-0517-lean-has-two-checkers-and-the-kernel-is-the-one-we-target.md),
  [ADR-0603](../research/09-decisions/adr-0603-classical-theorems-land-as-graded-statement-families.md),
  [ADR-0604](../research/09-decisions/adr-0604-lean-is-the-surface-syntax.md),
  [ADR-1601](../research/09-decisions/adr-1601-classical-logic-enters-as-a-hypothesis-not-as-an-axiom.md)
- [`docs/formalized-math-2026-08/diary-import-scale.md`](../formalized-math-2026-08/diary-import-scale.md)
  — what a full Mathlib export costs
