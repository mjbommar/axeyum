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

- `crates/axeyum-solver/tests/dt_capability_1935.rs` — 16 tests. The `sound_*`
  ones assert the absence of the wrong answer, because the fragment is entitled
  to refuse; `congruence_*` and `field_*` are the positive controls that decide,
  so the file cannot be satisfied by a route that refuses everything.
- `scripts/tests/mutation_controls.py`, suite `dt-capability-1935` — six
  mutations, one per guard.
- `docs/research/03-measurements/the-adr-1920-slice-is-6-of-600-files-2026-09-12.md`
  — the sizing, and `scripts/measure/dt-field-sort-census.py` that produced it.
