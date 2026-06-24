# QF_SEQ curated slice (committed, reproducible)

Curated, **committed** SMT-LIB finite-Sequences slice for the measured
head-to-head of the `axeyum-smtlib` front end + `axeyum_solver` against the
Z3 4.13.3 binary. This is the **first** `(Seq E)` measurement — the division
opened this session by generalizing the proven bounded packed-bit-vector string
layout (ADR-0029) from bytes to fixed-width `E`-elements: a bounded `(Seq E)` is
the same structure a bounded `String` uses (`String` ≈ `Seq` of bytes).

- `cvc5-regress-clean/` — **9** clean files from the cvc5 sequences regression
  suite (`references/cvc5/test/regress/cli/regress0/{seq,strings}`, a gitignored
  shallow clone), filtered to: a fixed-width element sort (`Int`, `Bool`, or
  `(_ BitVec w)`); only the slice-1 sequence operators (no
  `seq.nth`/`seq.at`/`seq.update`/`seq.rev`/`seq.replace`/`seq.indexof`); a
  machine-readable `(set-info :status sat|unsat)` ground truth; and only plain
  commands (no `push`/`pop`, `get-value`, quantifiers, or datatypes). Files are
  prefixed with their declared `:status`.

```sh
target/release/axeyum-bench \
  corpus/public-curated/non-incremental/QF_SEQ/cvc5-regress-clean \
  --logic QF_S --backend solver --compare-z3 --timeout-ms 10000 --jobs 4 \
  --out bench-results/baselines/qf-seq-cvc5-regress-clean-solver-vs-z3-10s.json
```

## First QF_SEQ numbers (axeyum solver vs Z3, 10 s, this session)

```
files=9 sat=6 unsat=0 unknown=2 unsupported=1 errors=0 agree=6 DISAGREE=0
```

**DISAGREE=0** against both Z3 and the declared `:status`. The six decided files
are all `sat` and agree with Z3. The remaining three are sound declines (never a
wrong verdict):

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
  `seq.prefixof`, `seq.suffixof`, `seq.contains`.
- **Declined (slice 2):** `seq.nth`/`seq.at` (SMT-LIB leaves out-of-bounds
  `seq.nth` **unconstrained**, which the zero-padded layout cannot model without
  a per-`(s,i)` unconstrained default — a wrong `unsat` risk), and
  `seq.update`/`seq.rev`/`seq.replace`/`seq.replace_all`/`seq.indexof`.
- Element sorts with no sound fixed-width packing — `Real`, `String`, a nested
  `(Seq …)`, an uninterpreted/parametric sort, or `(_ BitVec 8)` — and sequences
  whose packed sort would exceed 128 bits, decline cleanly (Unknown), never wrong.
