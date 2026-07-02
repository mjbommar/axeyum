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
   **LANDED (`c88ebcf8`):** `Sort::Seq(ArraySortKey)` (Copy-preserving — a `Box<Sort>`
   would have broken `Sort: Copy` at every use site) + `Sort::string()` =
   `Seq(BitVec(18))`; 39 decline-cleanly arms across 16 crate files, each mirroring
   its `Int`/`Real`/`Array` sibling (`SortMismatch`/`None`/`unreachable!`/`panic!`
   per the site's existing convention; structural arms recurse into the element).
   Workspace + `--all-targets` green, axeyum-ir tests pass, clippy `-D` clean.
2. **Slice A.1b — the first sequence *capability*.** NB the `Op` enum has **no**
   dedicated string ops today (the bounded encoder lowers via BV), so A.1b is more
   than eval arms: add `Op` variants (`seq.empty`/`seq.unit`/`str.++`/`str.len`) +
   arena builders, a **`Value::Seq`** (sequences route through `FullValue`, since
   `needs_value_storage(Seq) == true`), and ground-evaluator support (so models
   replay) — behind the existing bounded encoder as the decision path for now.
   **LANDED (`abb23ddb`):** `Op::{SeqLen, SeqEmpty(ArraySortKey), SeqUnit, SeqConcat}`
   + `Value::Seq(Vec<Value>)` + sort-checked builders (`seq_len`/`seq_empty`/
   `seq_unit`/`seq_concat`) + `sort_of` inference + ground-evaluator
   (`str.len(a++b) = |a|+|b|`, `str.len(seq.empty) = 0`); the `Op`/`Value` breaks
   swept decline-cleanly across 14 files (z3 backend rejects seq ops at the
   translate gate before `apply`, so no panic). Workspace `--all-targets` + axeyum-ir
   tests (incl. 3 seq tests) + clippy `--all-features -D` green. *Known deferral:*
   `Value::sort()` on an **empty** `Value::Seq` can't recover its element sort from
   the value alone (falls back to the `String` element with a `TODO` — not
   load-bearing, the term's `SeqEmpty` key carries the true sort); a precise
   empty-seq value-sort needs the element key in the variant (a later ADR).
3. **Slice A.1c — SMT-LIB write half landed; parse half BLOCKED on a representation
   fork (found 2026-07-01, `3d0ad49c`).** The **write** side is done+safe: the
   first-class ops render as `seq.len`/`seq.++`/`seq.unit`/`seq.empty` (these
   `Op::Seq*` variants are produced only by the arena builders, never by any bounded
   encoder, so the rename touches no bounded output). **The parse side is
   deliberately NOT done — and cannot be a confined edit — because of the collision
   below.**

   ### ⚠ Architectural finding: `Sort::Seq` (A.1a) collides with the ADR-0029 bounded sequence encoder

   A.1a's premise (and this doc's earlier A.1c note) was that `(Seq E)`/`seq.*` were
   *unowned*. **They are not.** A mature, committed **bounded finite-Sequences
   front-end (ADR-0029)** already:
   - routes `parse_sort` `(Seq E)` → a **packed `Sort::BitVec`** (like the bounded
     `String` encoder maps `String` → packed BV), and
   - parses **every** `seq.*` name (`seq.len`/`++`/`unit`/`empty`/`nth`/`at`/
     `extract`/`rev`/`update`/`prefixof`/`suffixof`/`contains`) and lowers them to BV
     ops, with extensive soundness tests (`smtlib.rs`); `(Seq (_ BitVec 8))` is even
     *reserved* (byte-width 8 is owned by `String`).

   So there are now **two representations of a sequence**: ADR-0029's bounded
   packed-BV (the front-end/decision path) and A.1a's first-class `Sort::Seq` (the
   IR-level unbounded representation). One `(Seq E)` syntax cannot yield both. **This
   fork is the real content of A.2 and needs a new ADR** — options: (a) `(Seq E)`
   parses to `Sort::Seq` and the bounded encoder becomes a lowering *pass* over it
   (unifies the two, biggest change); (b) keep ADR-0029 as the default and introduce
   `Sort::Seq` only where unboundedness is needed (a routing predicate); (c) a
   provably-bounded ⇒ ADR-0029, else ⇒ first-class split. Do NOT re-route
   `parse_sort` until that ADR is written.
4. **A.2** (`len`↔LIA Nelson–Oppen) — the Phase-A **exit criterion** (`str.len`-unsat
   gap). **Reordered by the finding above:** A.2 now *also* owns the ADR-0029↔`Sort::Seq`
   reconciliation ADR (the representation fork). Once `len`↔LIA can decide the
   first-class path, the fork can resolve to route unbounded/`len`-constrained
   `(Seq E)` to `Sort::Seq` while the bounded encoder stays the fast pre-check.

> **Pre-existing lint (unrelated to this keystone, flagged 2026-07-01):** the A.1b
> sweep surfaced a `clippy::needless_raw_string_hashes` warning at
> `crates/axeyum-smtlib/tests/smtlib.rs:2781` under `clippy --all-targets` (not the
> standard `--all-features -D` gate, which is clean). It is on `main` independent of
> the strings work; fix it as clippy hygiene when convenient.

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

**LANDED (2026-07-01, ADR-0052).** Three cooperating pieces:
`bv2nat_blast.rs` (solver) rewrites linear-over-`bv2nat` integer atoms to
*equivalent* pure-BV comparisons at an overflow-safe width — both directions
decide, `unsat` carries DRAT; `LenAbs` (parser) builds the **unbounded length
abstraction** as terms lower (`len(x++y)=len(x)+len(y)`, literals decode,
`=`/`prefixof`/`suffixof`/`contains` atoms → `fresh_bool ∧ length-fact`
relaxation, content bridges → free ints); `StringGate` (solver front door)
confirms every bounded-string `unsat` bound-independent (abstraction refutes /
bound-bite detector / content-only relax) or downgrades to honest `unknown`.
**The Gap-10 marker now asserts `Unsat`** (`str_len_sat_direction_decides`).

⚠ **The A.2 build surfaced a pre-existing wrong-unsat class on HEAD** (violating
ADR-0029's "longer ones are `Unsupported`, never wrong"): e.g. `(= s "abcde") ∧
(= t "fghij") ∧ (str.prefixof (str.++ s t) u)` answered `unsat` while Z3 says
`sat` (`u` may exceed the 8-byte bound). The class is **fixed** by the ADR-0052
bite detector for every channel with recorded length facts — length atoms,
cross-width comparisons, **regex** (`in_re` atoms carry the regex's match-length
interval, `min ≤ len(s) ≤ max`, computed from the AST), and the
**`substr`-family** (`len(substr) ≤ len(s)`, `len(at) ≤ 1`,
`len(replace(s,a,b)) ≤ len(s)+len(b)`, `len(from_code) ≤ 1`) — 8 regression
tests in `bv2nat_blast_bounds.rs`. The `axeyum-bench` harness applies the same
gate (`confirm_bounded_string_verdict`) so QF_S measurements match the shipped
front door. **Residual** (small): fact-less opaque results (`replace_all`,
`seq.extract`/`update`/`rev`) and packed *sequence* constants (not decoded;
string constants are). Next slice: those facts + width widening to recover the
`sat` side of the downgraded instances. The fuzz generator now draws length
constants past the bound (0..=11) to keep the class probed.

**Residual recoveries LANDED (2026-07-02, ADR-0052 follow-up).** Of the 21
declared-`unsat` `cvc5-regress-clean` instances the gate downgraded, three sound
bound-independent recoveries land 5 files (`str004`, `str005`, `re-comp/comp-all`,
`re-in-rewrite` ×2): (a) a **step-1a LIA projection** in `StringGate` — drop the
pure-BV well-formedness assertions (a sound weakening; the mixed BV+unbounded-Int
combination made the exact refuters decline, e.g. `xx = xx ++ yy ∧ len yy >
len xx`); (b) an **empty-string exact equality** fact (`s = "" ⟺ len(s) = 0`, no
fresh Boolean, so `len(s) = 0 ∧ s ≠ ""` refutes); (c) an **empty-language regex
fold** — `str.in_re s R` with `L(R) = ∅` (unbounded-reachability emptiness of the
NFA) returns constant `false`, a non-coarse ground atom (`re.comp re.all`,
`re.inter` of disjoint languages). 8 new regression tests in
`bv2nat_blast_bounds.rs` (each recovery + its soundness pair). The remaining 16 are
regex-*content* (inclusion/intersection emptiness across separate `in_re` atoms)
and lexicographic (`str.<=`) refutations — **Phase B / A.3**, not length facts;
relaxing `in_re`/`str.<=` coarseness is unsound (a fixed-prefix ∩ fixed-suffix
regex forces an over-bound word with a contiguous interval the bite detector
misses).

The ADR-0029↔`Sort::Seq` representation fork is resolved in ADR-0052: the
bounded encoder stays the default decision path *behind the gate*; `Sort::Seq`
is the unbounded representation grown behind it; `parse_sort` re-routes only
when Phase B's word-level solver can decide what the bounded pre-check declines
(the gate's `unknown`s are exactly that routing signal).

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
