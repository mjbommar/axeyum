# The ADR-1920 slice is 6 of 600 files; the array/UF-field half is its prerequisite, not its complement

**Measured 2026-09-12, lane `dt-capability`, at `611b72958`.** The sizing pass
that ADR-1920's "BUILD NEXT" and
[the DT blocker census](the-dt-blocker-census-was-measuring-the-ladder-2026-09-12.md)
§5 both asked for, done before a line of code.

**In one line: ADR-1920 specified the congruence slice as "restricted to
datatypes whose fields are all scalar", and across the three divisions where the
ladder now runs to the end that restriction holds for *6 of 600* sampled files —
so the slice as specified is not a 143-file capability, it is a 6-file one, and
the array/UF-field half is what turns it into a 136-file one.**

## 1. The question

The census named two capabilities and said to price them together:

| capability | AUFDTLIRA | UFDTLIRA | UFDT | of 600 |
|---|---:|---:|---:|---:|
| UF applied to a datatype argument | 32 | 54 | 57 | **143** |
| array/UF-sorted datatype FIELDS in `datatype_native` | 70 | 29 | 53 | **152** |

Those are **refusal counts** — which arm of `scan_fragment` fired first on each
file. They say how often each refusal is reached. They do not say how many files
a fix would win, and for the first row the gap between the two is the whole
result below.

ADR-1920's soundness argument is exact and is not in dispute:

> `build_dt_eq` compares tag plus scalar fields, which is **exact** for a
> datatype with no datatype-typed field. … For a datatype that *does* have
> datatype-typed fields, `build_dt_eq` is a **relaxation** — weaker than real
> equality — and a weaker antecedent makes the congruence constraint *stronger*
> than the true axiom, which can produce a wrong `unsat`. So the slice must be
> restricted to datatypes with scalar fields only.

The question this note answers is the arithmetic one ADR-1920 did not do:
**how many of the sampled files have such a datatype?**

## 2. Method

A static scan of the three pinned 200-file lists
(`bench-results/parity-lists/{AUFDTLIRA,UFDTLIRA,UFDT}.txt`, the same lists the
boards and the census used, committed at `49a0e2698` / `62e55bdd1`). For each
file:

1. parse every `declare-datatypes` and record each declared datatype's
   constructor/field layout;
2. classify **each declared datatype** as
   - `scalar-only` — every field of every constructor is `Bool`/`Int`/`Real`/
     `(_ BitVec n)`, i.e. exactly ADR-1920's precondition and exactly what
     `register_datatype` admits today;
   - `expandable-with-array-or-uf` — no field is datatype-sorted and no field
     sort *mentions* a datatype, but at least one is `(Array …)` or a
     `declare-sort` uninterpreted sort;
   - `dt-field` — some field is datatype-sorted, or is an array whose element
     sort mentions a datatype;
3. collect every `declare-fun` with a datatype-sorted **parameter**, and
   classify the file by the *worst* such parameter datatype.

Step 3 is the file-level unit because a file only decides if every UF
application it makes is handled; congruence emitted for one function and refused
for another still refuses the file.

**What this over- and under-counts, stated up front.** A declared UF with a
datatype parameter need not be *applied* to one in the assertions, so 438 is an
upper bound on the population the runtime refusal sees (143). And the
classification is per *declaration*, not per *use site*, so a file whose only
reachable applications are over an eligible datatype is scored by an ineligible
one it never applies. Both errors move the eligible counts **up**, never down —
which is the direction that matters here, because the finding is that the
eligible count is small.

Script: `scripts/measure/dt-field-sort-census.py` (committed with this note).

## 3. The result

Files that declare a UF with a datatype-sorted parameter, classified by whether
ADR-1920's precondition holds for every such parameter datatype:

| | AUFDTLIRA | UFDTLIRA | UFDT | of 600 |
|---|---:|---:|---:|---:|
| files declaring a UF with a datatype parameter | 171 | 112 | 155 | **438** |
| … every such datatype is **scalar-only** (ADR-1920 applies) | **0** | **6** | **0** | **6** |
| … every such datatype is expandable **if array/UF fields land** | 92 | 19 | 19 | **130** |
| … at least one has a **datatype field** (neither half helps) | 79 | 87 | 136 | **302** |

**Six.** One per cent of the UFDTLIRA list, zero in the other two.

The declared-datatype population says the same thing from the other side:

| | AUFDTLIRA | UFDTLIRA | UFDT |
|---|---:|---:|---:|
| datatype declarations, `scalar-only` | 1,009 | 1,004 | 25 |
| … `expandable-with-array-or-uf` | 1,953 | 1,390 | 345 |
| … `dt-field` | 1,214 | 800 | 561 |

Scalar-only datatypes are not rare — there are 2,038 of them. What is rare is a
*file whose UF parameters are all scalar-only*: these are SPARK/Ada verification
conditions, where a record with a scalar field sits next to one with an
`(Array Int integer)` field and the same file's functions take both.

## 4. What the non-scalar fields actually are

The most common non-scalar field sorts, AUFDTLIRA:

| count | field sort |
|---:|---|
| 1,284 | a datatype |
| 907 | scalar |
| 306 | `integer` |
| 226 | `us_private` |
| 200 | `us_type_of_heap` |
| 157 | `natural` |
| 138 | `(Array Int integer)` |
| 84 | `(Array Int natural)` |
| 61 | `(Array Int character)` |

`integer`, `natural`, `positive`, `character`, `us_private`,
`us_type_of_heap` are **`(declare-sort … 0)` uninterpreted sorts**, not
`define-sort` aliases for `Int` — checked directly in the files. So the
SPARK/Ada records are not "arrays of integers"; they are records over
uninterpreted sorts and over arrays *of* those uninterpreted sorts. Both are
rejected by the same arm:

```rust
Sort::Bool | Sort::BitVec(_) | Sort::Int | Sort::Real => field_sorts.push(*sort),
Sort::Datatype(inner) => { … }
_ => return Err(unsupported(
        "native datatype solving supports scalar (Bool/BitVec/Int/Real) and \
         datatype fields; array/UF datatype fields are not yet supported")),
```

UFDT is a different family (the Barrett/Reynolds codatatypes: `A$`, `Nat$`,
`B$`, `Dtree$`) and is dominated by genuine datatype fields — 561 of its 931
declarations — which is why it has the largest `neither half helps` column.

## 5. The conclusion, and it inverts the build order

ADR-1920 presents the scalar-field restriction as a *conservative slice of* the
congruence capability, and the census presents the array/UF-field row as a
*complementary* capability to be priced alongside it. The measurement says
neither framing is right:

**The array/UF-field capability is a PREREQUISITE of the congruence capability,
not its complement.** Shipping ADR-1920's slice first, exactly as specified,
buys 6 files. Shipping the field capability first raises the congruence slice's
own eligible population from **6 to 136** — a factor of 22 — because the
soundness precondition that matters is not "all fields are scalar" but **"every
field of every constructor has an expansion variable"**, and the field
capability is what puts an expansion variable on an array- or uninterpreted-
sorted field.

That restatement is the design decision, and it is ADR-1935:

> the checked precondition for emitting congruence over a datatype argument is
> **exactness of the expansion**, not scalarity of the fields.

Exactness is also the property the soundness argument actually needs. ADR-1920's
"all fields scalar" is a *sufficient* condition for exactness under the
expansion as it stood on 2026-09-12; it stops being necessary the moment another
field sort gains a variable, and writing the precondition as scalarity rather
than as exactness would have frozen the 6-file number into the code as a
comment-shaped invariant.

Neither half reaches the 302 files whose UF parameter datatype has a
**datatype-typed** field. Those need exact recursive equality — bounded unfolding
with a depth certificate, or a real native datatype theory with congruence and
acyclicity — and that is a third capability, not a slice of either of these.
**The honest ceiling for this lane is 136 of 600 on the UF axis**, on top of
whatever the field capability wins on its own.

## 6. Caveats

- Static over-approximation, both errors pointing the same way (§2).
- The 600 are three stride-pinned 200-file samples of 23,361 files, not the
  divisions. They are the same samples the boards and the census used, which is
  what makes the numbers comparable; they are not a census of SMT-LIB.
- `UFDTNIRA` is excluded, as it is in the census: it is more than half
  clock-bound and this capability is not what it is waiting on.
- The 6 scalar-only files are a real, testable population and are what the
  ADR-1920 slice would have been measured on. They are not a big enough sample
  to carry a board claim either way.
