# ADR-1935: the congruence precondition is EXACTNESS of the expansion, not scalarity of the fields — so the datatype-field half comes first

Status: accepted
Index-summary: ADR-1920 named "Ackermann congruence over expanded datatype arguments … restricted to datatypes whose fields are all scalar" as BUILD NEXT, and the DT blocker census sized the refusal it addresses at **143 of 600** sampled files. Those are not the same number. Measured before any code (`docs/research/03-measurements/the-adr-1920-slice-is-6-of-600-files-2026-09-12.md`): of the 438 files declaring a UF with a datatype-sorted parameter, the "all fields scalar" precondition holds for **6** — zero in `AUFDTLIRA`, zero in `UFDT`, six in `UFDTLIRA` — because these are SPARK/Ada verification conditions whose records carry `(declare-sort …)` uninterpreted fields (`integer`, `us_private`, `natural`) and `(Array Int integer)` fields, exactly what the restriction excludes. Admitting those field sorts raises the eligible population to **136**. So the two "halves" the census said to price together are not complements: **the field half is the congruence half's prerequisite**, and doing them in ADR-1920's order buys 6 files. Decision: (1) every field sort with an expansion variable is decided by ONE predicate, `field_sort_expands`, which now admits uninterpreted sorts and arrays whose component sorts mention no datatype; (2) the checked precondition for emitting congruence is `datatype_expansion_is_exact` — every field of every constructor has a variable — which is the property ADR-1920's soundness argument actually needs, scalarity being sufficient for it but not necessary; (3) a UF whose RESULT sort mentions a datatype is refused, not Ackermannized. Fixed on the way, and found by ADR-1920's own gate test rather than by reasoning: the `dt_symbols.is_empty()` early return handed the inner model straight out, which with an expanded query leaked `!dt_ack_*` internal symbols and omitted the function's interpretation — a `sat` that could not be checked by evaluating the original term.
Date: 2026-09-12

## Context

[ADR-1920](adr-1920-a-datatype-sorted-uf-signature-is-admitted.md) lifted the IR's
refusal of datatype-sorted UF signatures, moved the capability gate into
`datatype_native`, and closed with a precise next step:

> The next capability is stated precisely because §5 measured it: **Ackermann
> congruence over expanded datatype arguments** … The shape is already
> half-built — `build_dt_eq` compares tag plus scalar fields, which is **exact**
> for a datatype with no datatype-typed field. …
>
> **The soundness condition is not optional and is the reason this ADR does not
> just do it.** For a datatype that *does* have datatype-typed fields,
> `build_dt_eq` is a **relaxation** — weaker than real equality — and a weaker
> antecedent makes the congruence constraint *stronger* than the true axiom,
> which can produce a wrong `unsat`. So the slice must be restricted to
> datatypes with scalar fields only, and the restriction has to be a checked
> precondition rather than a comment.

[The corrected blocker census](../03-measurements/the-dt-blocker-census-was-measuring-the-ladder-2026-09-12.md)
§5 then sized two capabilities across the three divisions where the dispatch
ladder runs to the end, and said to price them together:

| capability | AUFDTLIRA | UFDTLIRA | UFDT | of 600 |
|---|---:|---:|---:|---:|
| UF applied to a datatype argument | 32 | 54 | 57 | **143** |
| array/UF-sorted datatype FIELDS in `datatype_native` | 70 | 29 | 53 | **152** |

Both are honest counts of *which refusal fired first*. Neither is a count of
files a fix would win, and for the first row the difference is this ADR.

## What was measured, before any code

[the-adr-1920-slice-is-6-of-600-files-2026-09-12.md](../03-measurements/the-adr-1920-slice-is-6-of-600-files-2026-09-12.md),
a static scan of the three pinned 200-file parity lists. Each declared datatype
is classified by its field sorts; each file by the *worst* datatype that appears
as a `declare-fun` parameter, because a file only decides if every application
it makes is handled.

| | AUFDTLIRA | UFDTLIRA | UFDT | of 600 |
|---|---:|---:|---:|---:|
| files declaring a UF with a datatype parameter | 171 | 112 | 155 | **438** |
| … every such datatype is **scalar-only** (ADR-1920 applies) | **0** | **6** | **0** | **6** |
| … every such datatype is expandable **if array/UF fields land** | 92 | 19 | 19 | **130** |
| … at least one has a **datatype field** (neither half helps) | 79 | 87 | 136 | **302** |

Scalar-only datatypes are not rare — 2,038 of the 5,306 declarations are
scalar-only. What is rare is a *file whose UF parameters are all scalar-only*,
because these divisions are SPARK/Ada verification conditions where a record
with an `Int` field sits beside one with an `(Array Int integer)` field and the
same file's functions take both.

The rejected field sorts were checked in the files rather than assumed:
`integer`, `natural`, `positive`, `character`, `us_private`, `us_type_of_heap`
are `(declare-sort … 0)` **uninterpreted sorts**, not `define-sort` aliases for
`Int`. An alias would have made this a non-problem, which is why it was checked.

## Decision

### 1. One predicate decides which field sorts have an expansion variable

`field_sort_expands` admits `Bool`/`BitVec`/`Int`/`Real`,
`Sort::Uninterpreted(_)`, and `Sort::Array { .. }` whose component sorts mention
no datatype. Everything else — `Float`, `RoundingMode`, `Seq`, and an array *of*
datatypes — is refused.

Three things have to agree about a field sort: whether `register_datatype`
admits the datatype, whether `build_sym_vars` declares a variable for the field,
and whether the equality encoding may be called exact. ADR-1920's measured
lesson is that two predicates written twice in different words do not stay one
predicate — `Features::note_sort` recursed into an array's component sorts while
the route's content scan did not, and the result was a non-terminating cycle
that no soundness test could find because it presented as a crash. So there is
one function and the other two call it.

An array whose element sort mentions a datatype is excluded for that same
reason, not for symmetry: its expansion variable would carry datatype content
into the residual, the dispatcher diverts on exactly that, and
`refuse_if_datatype_survives` would have to catch it.

`Float`/`RoundingMode`/`Seq` stay refused because no lane has measured a
datatype over them end to end, and ADR-1920's rule is that a gate is lifted on a
measurement, not on a symmetry.

### 2. The congruence precondition is exactness

`ackermannize_datatype_applications` replaces every `f(a₁…aₙ)` that has a
datatype-sorted argument with a fresh witness symbol and asserts, for each pair
of applications of one function, `(⋀ᵢ aᵢ = bᵢ) → (wₚ = w_q)`. The argument
equalities are left as plain `Op::Eq` terms, so the tag/field expansion encodes
them through the existing `build_dt_eq` — there is no second equality encoding
to keep in step with the first.

Every datatype-sorted argument must be a free variable of a datatype for which
`datatype_expansion_is_exact` holds: **every field of every constructor has an
expansion variable**. That is the property ADR-1920's soundness argument needs.
Scalarity is sufficient for it and is not necessary, and writing the
precondition as scalarity would have frozen the 6-file number into the code as a
comment-shaped invariant that no later change could widen.

With exactness the transformation is equisatisfiable both ways:

- *original ⇒ reduced.* Map `wₚ` to `f(a₁…aₙ)`'s value. Each antecedent is real
  equality of the arguments — that is what exactness buys — so every congruence
  clause holds by `f` being a function.
- *reduced ⇒ original.* Define `f` at each expanded tuple as that site's witness
  value; the congruence clauses make the definition consistent wherever two
  tuples are equal, so it is a function.

The second direction is not left as an argument: `register_ack_interpretations`
builds exactly that interpretation from the witness values, and the `sat` replay
evaluates the original applications under it.

### 3. A datatype-valued UF result is refused, not Ackermannized

Its witness would itself be a datatype-sorted term, which the tag/field
expansion would have to pick up in a scan that has already run. The census puts
`is`/`select` over a non-variable datatype term at 37 of 600 — a separate row,
and a separate capability.

### 4. The expansion is bounded

Ackermann is quadratic in the number of applications of one function and these
divisions apply one accessor to hundreds of records. `MAX_ACK_PAIRS` (20,000)
refuses above the bound with an `Unsupported` the harness reads as a decline,
rather than building a term explosion that spends the whole budget and yields
nothing. The bound is on pairs rather than applications because pairs are what
costs.

## What the gate test found that reasoning did not

`terminates_on_a_uf_applied_to_a_datatype_variable` (ADR-1920) runs the simplest
query the four divisions can produce, `(assert (p o))`. After the change it
stopped returning `Unsupported` — the intended outcome — and returned a `sat`
whose model had **no interpretation for `p`** and **a leaked `!dt_ack_*`
internal symbol**.

The cause: `decide_with_eq_mode`'s `dt_symbols.is_empty()` branch returns
`solve(...)`'s result directly, and an Ackermann-expanded query reaches it
(`p(o)` reduces to a Boolean witness variable, leaving no datatype symbols at
all). That path skips `project_and_replay`, which is where both the internal-symbol
filter and the model assembly live. A `sat` model that cannot be checked by
evaluating the original term violates a hard rule of this repository, and it
would have shipped: no reasoning in this ADR's first draft predicted it, and the
new suite's own tests did not reach that path either.

The branch now goes through `project_and_replay`, whose datatype loops are
no-ops on an empty scan — the same code rather than a second copy of it. The
gate test asserts the verdict **and** the model, so the next lane cannot
re-break it quietly.

## The measured result

1,000 files, both arms back to back on the same pinned core pair, arm order
alternating per file, 10 s / 8 GiB, on three idle homogeneous boxes. Protocol
and rows: [`bench-results/dt-capability-20260912/`](../../../bench-results/dt-capability-20260912/README.md).

| division | n | base | new | delta | gain | loss | flip | base wall | new wall |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| AUFDTLIRA | 200 | 41 | **69** | **+28** | 28 | 0 | 0 | 135 s | 224 s |
| UFDTLIRA | 200 | 72 | **82** | **+10** | 10 | 0 | 0 | 83 s | 122 s |
| UFDT | 200 | 26 | **27** | **+1** | 1 | 0 | 0 | 388 s | 480 s |
| QF_DT *(control)* | 200 | 169 | 169 | 0 | 0 | 0 | 0 | 52 s | 52 s |
| UF *(control)* | 200 | 88 | 88 | 0 | 0 | 0 | 0 | 1,374 s | 1,377 s |

**+39 net, 0 decided→undecided, 0 flips.** All 39 newly decided files were
re-run at 24 s against both oracles and their declared status: axeyum `unsat`,
z3 `unsat`, cvc5 `unsat`, declared `unsat`, **39 of 39, 0 disagreements on three
independent checks**. Neither arm disagrees with a declared `:status` anywhere in
the 1,000 rows. The base arm reproduces the committed board rows exactly
(41 / 72 / 26), which is what says the two arms measure what the board measured.

**The cost is wall clock and it is not small**: +66 %, +46 % and +24 % on the
three target divisions. A query the field refusal used to end in 44 ms now runs
the whole twenty-rung ladder. Both controls moved within noise, so the cost is
confined to the divisions this change touches — and `UFDT` pays +24 % for one
file. This is the same trade ADR-1927 recorded and it is to be quoted with the
gains, not separately.

**The A/B found a defect no reasoning in this ADR predicted.** Run 1 was
+28 / +10 / **−1**: a `UFDT` file `main` answers `unsat` returned `backend
failure: datatype sat model replay failed`. The replay was right to reject the
candidate; the bug was that a replay failure on the EXACT path raises
`SolverError::Backend`, which ends the dispatch, so the ladder never reached the
route that decides the file. An Ackermann-expanded query's model reconstruction
is partial by construction — a site whose arguments do not all evaluate
contributes no entry — so **an Ackermann-expanded query is a RELAXED one and a
replay failure is a decline**. Two reconstruction holes were closed with it: an
unbound function reads as "the model does not satisfy the query", and a witness
nothing constrained made the replay read a default at a key the search never
chose. Fixed, the binary rebuilt, and the whole 1,000-file run repeated from
scratch rather than patched.

### The residual census, on the new arm

| refusal | files |
|---|---:|
| UF applied to a datatype term that is **not a free variable** | **173** |
| congruence over a datatype argument whose expansion is not exact | 50 |
| a UF whose RESULT sort mentions a datatype | 47 |
| e-matching instantiation did not refute within the round budget | 39 |
| `is`/`select` over a non-variable datatype term | 22 |

The top row is new — the refusal it names did not exist before this change — and
it is a **constructor term as a UF argument** (`p(mk(a,b))`), whose argument
equality is structurally exact and cheap. That is the next slice, and it is
larger than either half of this one. Read the table the way ADR-1927 says: it
names which refusal fires first, not how many files a fix would win.

## Consequences

### What is now possible

- Datatype records over uninterpreted sorts and over arrays decide, which is the
  SPARK/Ada record shape in `AUFDTLIRA` and `UFDTLIRA`.
- Congruence over a datatype argument decides, for any datatype whose expansion
  is exact — which the field half is what makes common.
- `(assert (p o))` returns a checkable `sat` rather than a refusal.

### What is still refused

- The **302 of 600** files whose UF parameter datatype has a datatype-typed
  field. Neither half reaches them; they need exact recursive equality — bounded
  unfolding with a depth certificate, or a native datatype theory with
  congruence and acyclicity — and that is a third capability, not a slice of
  either of these. **The honest ceiling for this work on the UF axis is 136 of
  600.**
- Datatype-valued UF results (37 of 600).
- Arrays of datatypes as fields, `Float`/`RoundingMode`/`Seq` fields, and any
  query over `MAX_ACK_PAIRS` congruence pairs.

### What this ADR does not claim

- It does not claim a decide-rate win of 136 files. 136 is the population the
  precondition now admits; what the route does with each of them is the A/B, and
  a file can clear this refusal only to meet the next one.
- `(Array Int Int)`-valued fields reach the array route and stop there on `sat`:
  the residual is non-bit-vector array content and the lazy array route answers
  `unknown`. That limit belongs to the array theory, not to this change, and
  `field_an_array_valued_field_reaches_the_array_route` asserts the absence of
  the *refusal* rather than the presence of a verdict for exactly that reason.
- The 600 are three stride-pinned 200-file samples, not the divisions.

## Evidence

- `crates/axeyum-solver/tests/dt_capability_1935.rs` — 20 tests. The `sound_*`
  ones assert the absence of the wrong answer, because the fragment is entitled
  to refuse; `congruence_*` and `field_*` are the positive controls that decide,
  so the file cannot be satisfied by a route that refuses everything.
- `scripts/tests/mutation_controls.py`, suite `dt-capability-1935` — six
  mutations, one per guard, all six killed.

  **Four of them SURVIVED the first run**, and that is recorded here rather than
  quietly fixed. With each deleted, all 16 tests then in the file still passed,
  because each guard is an EARLY and PRECISE refusal of a shape a LATER and
  vaguer one also refuses: the array-of-datatype field exclusion is caught again
  by `refuse_if_datatype_survives`, the result-sort and free-variable arms again
  by `scan_fragment`, and — the one worth stating plainly — **the exactness
  precondition is not what stands between the solver and a wrong `unsat` today**.
  ADR-1930's structural-equality encoding is a free Boolean carrying only
  necessary conditions, so an inexact congruence antecedent is never *forced*
  true and the clause degenerates to vacuous rather than to a wrong answer. The
  soundness is ADR-1930's and the replay's. What this precondition buys is that
  every congruence clause we emit has an antecedent that provably IS real
  equality, which is what makes the argument above reviewable, and insurance
  against a future change to that encoding.

  So what each of the four uniquely produces is its MESSAGE — and by decision 2
  of ADR-1920 that is the product, because these divisions' blocker census is
  read off exactly these strings and a census cannot distinguish a capability
  that is missing from one that is merely reached later. Four tests now pin the
  messages, and each kills exactly one mutation.

  One of the four calls `check_with_datatype_native` directly rather than
  `solve`. That is also a finding: every query that reaches the
  datatype-valued-result guard through the front door is decided by an earlier
  rung, because a selector over a UF result is just another uninterpreted term
  to EUF. A test that reached it through `solve` by accident would have been
  measuring the ladder.
- [`bench-results/dt-capability-20260912/`](../../../bench-results/dt-capability-20260912/README.md)
  — the A/B protocol, all 1,000 per-file rows for both runs, the oracle
  re-validation of every gain, and the runner and analysis scripts.
- `docs/research/03-measurements/the-adr-1920-slice-is-6-of-600-files-2026-09-12.md`
  — the sizing, and `scripts/measure/dt-field-sort-census.py` that produced it.
