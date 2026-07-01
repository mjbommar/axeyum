# P2.7 · Phase A — First-class string/sequence sort + String+LIA combination

**Size:** M–L · **Depends on:**
[P1.6 theory combination](../../track-1-engine/P1.6-theory-combination.md) ·
**Blocks:** Phases B–E. **Closes the `str.len`-unsat gap.**

> The enabling refactor. Strings become real IR terms (a `Seq(elem)` sort), and the
> length theory talks to the LIA solver Nelson-Oppen-style over shared `len(x)`
> terms. Until this lands, everything downstream is awkward.

## Task A.1 — first-class `Sort::Seq(elem)` / `Sort::String` in `axeyum-ir`

- Add `Sort::Seq(Box<Sort>)` and `Sort::String = Seq(Unicode)` (code points
  `0x00000–0x2FFFF`, total-ordered — see [01-literature.md §5](01-literature.md)).
- Add the term operators (`str.++`, `str.len`, `str.at`/`seq.nth`, `seq.unit`,
  `seq.empty`, comparisons, `str.in_re`, extended functions) as IR nodes with
  string-*valued* results — resolving the `Parsed = Term | Str` friction by making
  strings ordinary terms.
- Ground evaluator support (so models replay), sharing-preserving SMT-LIB
  read/write (`axeyum-smtlib`).
- **ADR** (the P2.7 boundary ADR): records the `Seq`-sort decision, the Unicode
  alphabet + total order, and the `axeyum-strings` crate boundary.

| exit | a String/Seq sort exists; bounded ops re-expressed over it with identical verdicts; round-trips SMT-LIB |

#### Blast radius + slicing strategy (scoped 2026-07-01)

Adding a variant to `axeyum_ir::Sort` (`crates/axeyum-ir/src/sort.rs:121`) is a
**workspace-wide** change: **~138 files** reference `Sort::*` variants, and every
**exhaustive** `match` on `Sort` becomes a compile error the moment the variant is
added. So A.1 must be sliced to keep each commit compiling:

1. **Slice A.1a — the bare variant + total order.** Add `Sort::Seq(Box<Sort>)`
   (and `Sort::String = Seq(Unicode-BV)` or a distinct `Unicode` element sort), the
   `ArraySortKey` mirror, `Ord`/`Hash`/display, and the interner support. Then sweep
   every broken exhaustive `match` and add a `Sort::Seq(_) => …` arm that **declines
   cleanly** (`IrError::Unsupported`, `Unknown`, or the natural "not this fragment"
   path) in every crate that does not yet handle sequences (bv, fp, cnf, aig, most
   of solver, evm, verify). This commit **adds no capability** — it just keeps the
   build green with the sort present. Gate: full workspace `cargo build` + `test`.
   *Tip:* grep the compiler errors, not the 138 files — only exhaustive matches
   break; many uses are constructors or `matches!` that don't.
2. **Slice A.1b — eval + a couple of constructors.** Ground-evaluator arms for
   `seq.unit`/`seq.empty`/`str.++`/`str.len` over the new sort (so models replay),
   behind the existing bounded encoder as the decision path for now.
3. **Slice A.1c — SMT-LIB read/write** round-trip for the sort + core ops.
4. **A.2** (`len`↔LIA Nelson–Oppen) and the ADR follow once the sort is load-bearing.

Do **not** attempt A.1a–c in one commit: the value is a green workspace at each
step. The `axeyum-strings` crate boundary is deferred to when the word-level solver
(Phase B) actually needs it — A.1 lives in `axeyum-ir` + the bounded encoder.

## Task A.2 — `len`-term extraction + Nelson-Oppen link to LIA

- Treat `len(x)` as a shared integer term between the (future) string solver and
  the existing **LIA online solver**. Push `len` through `++`
  (`len(x++y) = len(x)+len(y)`), through constants, etc., as part of the
  normalization invariant.
- Wire the combination so length facts flow both ways (string → LIA constraints on
  `len`; LIA → string length bounds). This is a **direct application of P1.6**;
  closing the BV/String+LIA gap is the headline deliverable.

| exit | the `str.len` **unsat** test that is `unknown` today **decides** (the gap-analysis Gap 10 marker) |

## Task A.3 — Parikh / semilinear length over-approximation (cheap UNSAT)

- For regex and bounded fragments, compute the **Parikh image** (letter-count
  semilinear set) and push it to LIA as an over-approximation. An UNSAT here is a
  cheap, **independently checkable** certificate (the easiest first Track-3
  evidence target) — and it fires *before* expensive regex unfolding.

| exit | length-only UNSAT instances decided cheaply; the LIA abstraction is retained as a certificate |

## Task A.4 — routing + bounded pre-check

- `axeyum-solver` routes string queries: **bounded encoder pre-check** for
  provably-small instances (fast, keeps current wins) → **`axeyum-strings`** word-
  level solver → `unknown`. The pre-check must never *override* a word-level
  verdict, only short-circuit when it is provably sound to do so.

| exit | dispatch is sound (pre-check only short-circuits soundly); no regression on the bounded suite |

## Soundness

- Every model still replays through the ground evaluator (now over the new sort).
- The String+LIA combination must be **stably-infinite / polite**-correct for the
  shared `len` sort (Int) — document the combination argument in the ADR.
- `str_differential_fuzz` vs Z3 stays DISAGREE=0 across the refactor.

## Exit criteria for Phase A

1. First-class `Seq`/`String` sort in the IR; bounded ops re-expressed over it,
   regression-clean; SMT-LIB round-trips.
2. **`str.len` unsat decides** (the BV/String+LIA gap closed via P1.6).
3. Parikh length over-approximation gives cheap, checkable UNSAT.
4. `axeyum-strings` crate boundary + Unicode-alphabet ADR merged; foundational DAG
   updated.

This phase ships the *infrastructure*; Phase B (the word-equation core on top) is
what makes strings genuinely unbounded.
