# QF_SEQ curated slice (committed, reproducible)

Curated, **committed** SMT-LIB finite-Sequences slice for the measured
head-to-head of the `axeyum-smtlib` front end + `axeyum_solver` against the
Z3 4.13.3 binary. This is the **first** `(Seq E)` measurement — the division
opened this session by generalizing the proven bounded packed-bit-vector string
layout (ADR-0029) from bytes to fixed-width `E`-elements: a bounded `(Seq E)` is
the same structure a bounded `String` uses (`String` ≈ `Seq` of bytes).

- `cvc5-regress-clean/` — **15** clean files: **9** from the cvc5 sequences
  regression suite (`references/cvc5/test/regress/cli/regress0/{seq,strings}`, a
  gitignored shallow clone) plus **6** hand-authored `seq.nth`/`seq.at` files
  (slice 2, each with a Z3-confirmed `:status`). Filtered to: a fixed-width
  element sort (`Int`, `Bool`, or `(_ BitVec w)`); only the wired sequence
  operators (slice 1 + `seq.nth`/`seq.at`; no
  `seq.update`/`seq.rev`/`seq.replace`/`seq.indexof`); a machine-readable
  `(set-info :status sat|unsat)` ground truth; and only plain commands (no
  `push`/`pop`, `get-value`, quantifiers, or datatypes). Files are prefixed with
  their declared `:status`.

```sh
target/release/axeyum-bench \
  corpus/public-curated/non-incremental/QF_SEQ/cvc5-regress-clean \
  --logic QF_S --backend solver --compare-z3 --timeout-ms 10000 --jobs 4 \
  --out bench-results/baselines/qf-seq-cvc5-regress-clean-solver-vs-z3-10s.json
```

## QF_SEQ numbers (axeyum solver vs Z3, 10 s)

Slice 1 (open, 9 files): `files=9 sat=6 unsat=0 unknown=2 unsupported=1 agree=6
DISAGREE=0`. Slice 2 (`seq.nth`/`seq.at`, 15 files):

```
files=15 sat=10 unsat=1 unknown=3 unsupported=1 errors=0 agree=11 DISAGREE=0
```

**DISAGREE=0** against both Z3 and the declared `:status`. Decided rose 6 → 11
(the five new `seq.nth`/`seq.at` decides — four `sat`, one `unsat` — all agree
with Z3). The three unknowns and one unsupported are sound declines (never a
wrong verdict):

- `unsat__nth__oob-functional.smt2` — decided `unsat`: the **same** out-of-bounds
  `(seq.nth s 0)` cannot equal both `7` and `9` (`seq.nth` is a function — the
  fresh out-of-bounds symbol is shared per syntactic application).
- `sat__nth__oob-unconstrained.smt2` — decided `sat`: out-of-bounds `seq.nth` is
  **unconstrained**, so `(= (seq.nth s 0) 7)` on an empty `s` is satisfiable. A
  zero-padded model would force a wrong `unsat`; the fresh-free-value model does
  not.
- `unsat__nth__congruence.smt2` — `unknown`: the eager Ackermann congruence
  (`s=t ∧ i=i' ⇒ oob(s,i)=oob(t,i')`) over a **symbolic** index is too large for
  the bounded search to close — a sound decline, never a wrong `sat`.
- `seq-ex2.smt2` — `seq.++` of two max-bound sequences whose summed length
  exceeds the packed-sort bit ceiling → `Unsupported` (Unknown to the consumer).
- `seq-ex4.smt2` — a `seq.extract`-over-symbolic-length UNSAT the bounded model
  cannot complete → `unknown`.
- `seq-nemp.smt2` — asserts `(seq.len x) = 16`, beyond the bounded max length,
  so the bounded-integer search reports `unknown` (crucially **not** a wrong
  `unsat`).

## The sequence fragment that is wired (ADR-0029, bounded)

A `(Seq E)` over a fixed-width element sort `E` is one `BitVec(len_width(m) +
m·ew)` packing a length (low) and up to `m` content elements (above), with the
same canonical well-formedness (length ≤ m; padding elements zero) a bounded
`String` carries — so `=`/`distinct` decide via plain bit-vector (in)equality.

- **Element widths** `ew`: `(_ BitVec w)` → `w`, `Bool` → 1, `Int` → 16
  (two's-complement, bounded). The byte width `8` is reserved for `String`.
- **Modeled operators** (denotation-preserving over the packed layout, mirroring
  their `str.*` counterparts with the element width swapped in for `8`):
  `seq.empty`, `seq.unit`, `seq.++`, `seq.len`, `seq.extract`, `=`/`distinct`,
  `seq.prefixof`, `seq.suffixof`, `seq.contains` (slice 1), and `seq.nth`/`seq.at`
  (slice 2).
- **`seq.nth` (slice 2, sound out-of-bounds).** `(seq.nth s i)` is the SMT-LIB
  **partial** function: in-bounds (`0 ≤ i < len(s)`) the `i`-th element (the
  position mux); out-of-bounds an **unconstrained, fresh** value of the element
  sort (`BitVec(ew)`), keyed per syntactic `(s, i)` so identical applications
  share it (`seq.nth` is a function). Semantically-equal-but-distinct operands are
  reconciled by an **eager Ackermann** pass that appends
  `(s=s' ∧ i=i') ⇒ oob(s,i)=oob(s',i')` over every registered pair. Zero-padding
  is explicitly **not** used (it would force a wrong `unsat` for out-of-bounds
  reads). `seq.at` (slice 2) is total: in-bounds the length-1 sub-sequence
  `[s[i]]`, out-of-bounds the empty sequence (mirrors `str.at`).
- **Declined (slice 3):**
  `seq.update`/`seq.rev`/`seq.replace`/`seq.replace_all`/`seq.indexof` — clean
  `Unsupported` (Unknown), never a wrong verdict.
- Element sorts with no sound fixed-width packing — `Real`, `String`, a nested
  `(Seq …)`, an uninterpreted/parametric sort, or `(_ BitVec 8)` — and sequences
  whose packed sort would exceed 128 bits, decline cleanly (Unknown), never wrong.
