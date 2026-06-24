# QF_SEQ curated slice (committed, reproducible)

Curated, **committed** SMT-LIB finite-Sequences slice for the measured
head-to-head of the `axeyum-smtlib` front end + `axeyum_solver` against the
Z3 4.13.3 binary. This is the **first** `(Seq E)` measurement — the division
opened this session by generalizing the proven bounded packed-bit-vector string
layout (ADR-0029) from bytes to fixed-width `E`-elements: a bounded `(Seq E)` is
the same structure a bounded `String` uses (`String` ≈ `Seq` of bytes).

- `cvc5-regress-clean/` — **29** clean files: **10** from the cvc5 sequences
  regression suite (`references/cvc5/test/regress/cli/regress0/{seq,strings}`, a
  gitignored shallow clone — `array3.smt2` is the slice-3 `seq.update` addition)
  plus **6** hand-authored `seq.nth`/`seq.at` files (slice 2), **8**
  hand-authored `seq.update`/`seq.rev` files (slice 3), and **5** hand-authored
  `seq.replace` files (slice 4), each with a `:status` ground truth. Filtered to:
  a fixed-width element sort (`Int`, `Bool`, or `(_ BitVec w)`); only the wired
  sequence operators (slice 1 + `seq.nth`/`seq.at` + `seq.update`/`seq.rev` +
  `seq.replace`; no `seq.replace_all`/`seq.indexof`); a machine-readable
  `(set-info :status sat|unsat)` ground truth; and only plain commands (no
  `push`/`pop`, `get-value`, quantifiers, or datatypes). Files are prefixed with
  their declared `:status`. **Note:** Z3 4.13.3 does not support `seq.update` or
  `seq.rev` (it errors on those constants), so those files have **no Z3
  head-to-head** — the binary declines and the instance is `oracle_skipped`; the
  `:status` ground truth (cvc5-semantics-derived) is the binding soundness check.
  (Z3 4.13.3 *does* support `seq.replace`, so the `seq.replace` files carry a
  full head-to-head.)

```sh
target/release/axeyum-bench \
  corpus/public-curated/non-incremental/QF_SEQ/cvc5-regress-clean \
  --logic QF_S --backend solver --compare-z3 --timeout-ms 10000 --jobs 4 \
  --out bench-results/baselines/qf-seq-cvc5-regress-clean-solver-vs-z3-10s.json
```

## QF_SEQ numbers (axeyum solver vs Z3, 10 s)

Slice 1 (open, 9 files): `files=9 sat=6 unsat=0 unknown=2 unsupported=1 agree=6
DISAGREE=0`. Slice 2 (`seq.nth`/`seq.at`, 15 files): `files=15 sat=10 unsat=1
unknown=3 unsupported=1 agree=11 DISAGREE=0`. Slice 3
(`seq.update`/`seq.rev`, 24 files):

```
files=24 sat=15 unsat=4 unknown=4 unsupported=1 errors=0 agree=19 DISAGREE=0
```

**DISAGREE=0** against both Z3 (where Z3 supports the ops) and the declared
`:status`. Decided rose 11 → 19 — the slice-3 additions: `seq.update`/`seq.rev`
decide five `sat` (`array3`, `ground-reverse`, `ground-replace`, `oob-noop`,
`span-truncate`) and three `unsat` (`not-identity`, `wrong-result`,
`span-truncate`); plus a QF_S file (`issue6653-3-seq`) that the wider seq support
now decides. The unknowns and one unsupported are sound declines (never a wrong
verdict):

- `unsat__rev__not-identity.smt2` — decided `unsat`: `rev([1,2]) = [1,2]` is
  false; a no-op model of `seq.rev` would wrongly satisfy it.
- `unsat__update__wrong-result.smt2` / `unsat__update__span-truncate.smt2` —
  decided `unsat`: the asserted result contradicts the `STRING_UPDATE` overlay /
  span-truncation semantics.
- `sat__update__oob-noop.smt2` — decided `sat`: an out-of-bounds index makes
  `seq.update` a no-op (`(seq.update [1,2] 5 [9]) = [1,2]`), total semantics.
- `unsat__update__distinct-elems.smt2` — `unknown`: it threads `(seq.len x)`
  through the `Int` bridge (the bounded-integer search cannot close it) — a sound
  decline, never a wrong `sat`.

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
  `seq.prefixof`, `seq.suffixof`, `seq.contains` (slice 1), `seq.nth`/`seq.at`
  (slice 2), `seq.update`/`seq.rev` (slice 3), and `seq.replace` (slice 4).
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
- **`seq.update`/`seq.rev` (slice 3, both total, no OOB subtlety).**
  `(seq.update s i t)` overlays the sequence `t` onto `s` starting at index `i`,
  **truncated to fit** within `s` (length unchanged), and is a **no-op** when
  `i < 0` or `i ≥ len(s)` — exactly cvc5's `STRING_UPDATE`. `t` may be any
  `(Seq E)` (the corpus uses `(seq.unit e)`, the length-1 span); the general span
  is modeled. A **constant** index uses a pure-BV encoding (no `bv2nat`/integer
  bridge) so a ground update stays bit-blastable. `(seq.rev s)` reverses the first
  `len(s)` elements (`out[j] = s[len−1−j]`, a permutation; length unchanged) via a
  pure-BV `k+j+1 = len` mux. Both copy the length field verbatim and preserve the
  canonical padding, so `=`/`distinct` keep deciding via plain BV (in)equality.
- **`seq.replace` (slice 4, first-occurrence splice).** `(seq.replace s a b)`
  replaces the **first leftmost** occurrence of the sub-sequence `a` in `s` with
  `b` (the element-wise analogue of `str.replace`): `a` not present → `s`
  unchanged; `a` empty → `b ++ s` (prepend); result length `len(s) − len(a) +
  len(b)` when found. Encoded as a bounded first-match mux feeding an element-wise
  splice keyed by the symbolic boundaries `P` (the match start) and `P + len(b)`;
  sound for literal or symbolic `a`/`b`. The result max length is `max(m_s, m_s −
  len(a)_min + m_b)`; when it exceeds the packed-sequence bit ceiling (e.g. a
  *growing* replace over a full-length `(Seq Int)`, whose 16-bit elements already
  fill the 128-bit cap at `m = 7`) the op declines cleanly to `Unsupported`
  (Unknown), never a truncated (wrong) sequence. Some ground unsat cases come
  back `unknown` (the `Int`-bridge in the splice keeps them off the pure
  bit-blast path) — sound, agreeing with the `:status`, never a wrong verdict.
- **Declined (slice 4+):** `seq.replace_all`/`seq.indexof` — clean `Unsupported`
  (Unknown), never a wrong verdict.
- Element sorts with no sound fixed-width packing — `Real`, `String`, a nested
  `(Seq …)`, an uninterpreted/parametric sort, or `(_ BitVec 8)` — and sequences
  whose packed sort would exceed 128 bits, decline cleanly (Unknown), never wrong.
