# ADR-1210: Transpose invariance needs the COLUMN law, and the row law cannot supply it

Status: accepted
Date: 2026-08-31
Index-summary: `Rat.det_transpose` — `det (matTranspose A) n = det A n` at a
symbolic dimension — is admitted axiom-free, together with cofactor expansion
along the first COLUMN. Five declarations. **ADR-1185's closing sizing is
corrected**: it said transpose invariance was "strictly downstream" of
`Rat.det_row_expansion`, and the row law is not used and cannot be — expansion
along a column of `A` IS expansion along a row of `Aᵀ`, so reaching for it is
circular. What the row law constrains is one summand at a time, never the
column sum. The column law is its own induction, and it is markedly CHEAPER
than the row law rather than downstream of it: because the two exchanges run
on different axes, `matMinor_row_col_comm` needs no `Nat.ble` hypothesis and
no case split, and the route has no `laplaceSummand`, no `unskip`, no `Nat.beq`
diagonal guard and no `sumRange_congr_lt`. Three of ADR-1120's four laws are
now proved; only multiplicativity remains, blocked on a missing type.
Index-status: accepted

## Context

[ADR-1120](adr-1120-the-general-n-determinant-is-a-function-plus-a-bound.md)
declared `Rat.det` at symbolic `n` and named four open laws.
[ADR-1135](adr-1135-a-determinant-congruence-is-what-the-absence-of-funext-costs.md)
closed `det matId n = 1` and recorded that multiplicativity is blocked on an
aggregate type this kernel does not have.
[ADR-1155](adr-1155-general-row-expansion-is-one-fubini-once-the-range-is-full.md)
landed the index and range layers of Laplace expansion, and
[ADR-1185](adr-1185-general-row-expansion-closes-and-the-guard-had-to-be-a-recursion.md)
closed general-row expansion in twenty declarations.

ADR-1185's last consequence reads:

> **Transpose invariance is now strictly downstream.** … `det (transpose A) n`
> expands along a column of `A`, its inner sums are `matSkip`-reindexed, and
> filling them to the full range is the same move. `Rat.det_row_expansion`
> gives the other half directly — a column of `A` is a row of `Aᵀ`.

This ADR is that task, executed, and the first thing it did was refute that
sizing.

## The correction: the row law is circular here, and it is not needed

"A column of `A` is a row of `Aᵀ`" is exactly the statement being proved. Using
`det_row_expansion` on `Aᵀ` gives

```text
det Aᵀ (succ m) = Σ_q altSign (q+i) · Aᵀ(i,q) · det (matMinor Aᵀ i q) m
                = Σ_q altSign (q+i) · A(q,i)  · det (matMinor A q i) m     [IH]
```

which is expansion of `A` along **column `i`** — and knowing that equals
`det A (succ m)` is the thing to be shown. Every route through the row law
closes this loop.

Nor does the row law constrain the column sum indirectly. The `p`-th column
summand `altSign p · A(p,0) · det (matMinor A p 0) m` is precisely the `c = 0`
slice of the row-`p` expansion, so the row law relates each summand to its own
**siblings across `c`**, and says nothing about the sum across `p`. Section 9
of the route-check script measures both halves of this.

So the crux is a separate law:

```text
Rat.det_col_expansion : ∀ m A,
  det A (succ m) = sumRange (fun p => altSign p * (A p 0 * det (matMinor A p 0) m)) (succ m)
```

and, once it exists, transpose invariance is three moves.

## Decision

**Land the column law and close transpose invariance.** Five declarations in
`crates/axeyum-lean-kernel/src/rat_prelude/matrix_det.rs`, all admitted by the
trusted gate, all with an empty `Kernel::axiom_footprint`:

| declaration | statement |
| --- | --- |
| `Rat.matMinor_row_col_comm` | the double minor, pointwise, **with no hypothesis** |
| `Rat.det_minor_row_col_comm` | … through `det_congr` |
| **`Rat.det_col_expansion`** | **cofactor expansion along the first COLUMN** |
| `Rat.matMinor_transpose` | `matMinor Aᵀ 0 q r c = matTranspose (matMinor A q 0) r c` — `Eq.refl` |
| **`Rat.det_transpose`** | **`det (matTranspose A) n = det A n`** |

The headline type, read from the kernel rather than from this table:

```text
(n : AxNat) -> (A : AxNat -> AxNat -> Rat) ->
  Rat.det (Rat.matTranspose A) n = Rat.det A n
```

## Why the column law is CHEAPER than the row law, not downstream of it

ADR-1185 needed twenty declarations; this needed five, and the five are
smaller. The reason is structural and worth stating, because it predicts which
of the remaining laws will be cheap.

In a double **row** expansion, both steps delete a column, so the two column
deletions land in one index space and must be **ordered against each other**:
that is where `matSkip_comm`'s `Nat.ble a b = true` hypothesis comes from, and
with it the `unskip` left inverse, the `Nat.beq` diagonal guard, the
`laplaceSummand` on the whole square, and `sumRange_congr_lt` (because the
range fill only holds below the bound).

Here one expansion deletes a **row** and the other a **column**. The two
exchanges are on different axes and neither constrains the other, so the whole
double-minor identification is

```text
matMinor (matMinor A 0 (succ q)) p 0 r c = matMinor (matMinor A (succ p) 0) 0 q r c
```

which is `matSkip_succ_succ` once per axis — **unconditionally**, no `Nat.ble`
premise, no case split. Verified over all 1,296 index tuples below 6 (§5b of
the check script).

Two more consequences of the same fact:

- **No diagonal guard is needed.** ADR-1185 had to show the `p = q` cell
  vanishes, because both expansions ran over the same indices. Here the
  surviving row index and surviving column index are independent, and the only
  cell needing separate treatment is the one both **head peels** remove — and
  the two peeled heads are the *same term*, `altSign 0 * (A 0 0 * det (matMinor
  A 0 0) (succ m'))`, so nothing has to be proved about them at all.
- **`sumRange_congr` suffices**, not `sumRange_congr_lt`. The termwise identity
  holds at every `(c, p)` with no bound.

This lane declares **no new `Definition`**, which is why its second mutation
probe had to be designed differently (below).

## The step, in the shape the Rust builds

At `m = succ m'`, with `n1 = succ m'` and `n2 = succ n1`:

1. `det_succ` opens the row-`0` expansion of `det A n2`.
2. `sumRange_peel_head` peels index `0` off **both** sides. The heads are
   identical terms.
3. Under the left tail, the induction hypothesis expands `det (matMinor A 0
   (succ c)) n1` along **its** first column; under the right tail, `det_succ`
   expands `det (matMinor A (succ p) 0) n1` along **its** first row. Two
   `mul_sumRange` pulls on each side take the cofactor coefficients inside.
4. `sumRange_swap`, once. That is the entire reindexing.
5. The termwise agreement, `l_eq_r_term`, is eight moves:
   `det_minor_row_col_comm` exchanges the double minor, `mul_perm4` swaps the
   two cofactor coefficients, and six `neg_mul`/`mul_neg`/`altSign_succ` steps
   carry the single `Rat.neg` from `altSign (succ c)` over to `altSign (succ
   p)`. Both `altSign_succ` rewrites are written out rather than left to
   `Eq.refl`, so a change in `altSign`'s shape fails here loudly.

The transpose step is then: `det_succ` on `Aᵀ` (whose row-`0` entries are `A`'s
column `0` by delta and beta alone), `matMinor_transpose` + `det_congr` +
the induction hypothesis under one `sumRange_congr`, and `det_col_expansion`.

The base cases are both `Eq.refl`. `det A 1` and the column sum at bound `1`
reduce to the *same* term; `det _ 0` is `one` on both sides.

## The route checks, re-executable

```sh
python3 docs/research/09-decisions/adr-1210-det-transpose-checks.py   # 0 failures
```

Written and run **before** any Rust, per ADR-1185's own finding that a plan's
"verified numerically" is itself a claim. It transcribes `matSkip`, `matMinor`,
`altSign`, `det` and `matTranspose` at exactly the definitions the Rust uses,
and §0 checks that transcription against an independent Leibniz determinant —
so a wrong simulation cannot silently agree with a wrong proof.

Six negative controls, each measured rather than asserted: a swapped `matSkip`
must falsify the target (220 of 240), the crux (218 of 240) and the index
identity (216 of 1,296); the alternation dropped (216 of 240) and shifted by
one (229 of 240) must falsify the column sum; and §8 confirms the sampled
matrices are not accidentally symmetric (235 of 240), without which every
transpose check is vacuous.

## The mutation table, both columns

ADR-1155's refined standard: **a rejected declaration and a false statement are
different findings**, and a declaration rejected while its theorem stays true
adds no coverage. Both columns are measured. The declaration column comes from
one run with `declare_matrix_det` rewritten to REPORT each rejection instead of
short-circuiting (43 `declare_*` calls, all `MUT_OK` at baseline); the
statement column from §10 of this ADR's script.

**Mutation A — `Rat.matSkip`'s two `bool_select_nat` branches swapped**, the
probe ADR-1135 and ADR-1185 both use.

| declaration | declaration under mutation | statement under mutation | coverage added |
| --- | --- | --- | --- |
| `matMinor_row_col_comm` | `UnknownConst` — confounded by `matSkip_succ_succ` failing | **FALSE**, 112 of 256 | yes, on the statement |
| `det_minor_row_col_comm` | `UnknownConst` — confounded | **FALSE**, 45 of 75 | yes, on the statement |
| `det_col_expansion` | `UnknownConst` — confounded | **FALSE**, 205 of 240 | yes, on the statement |
| `matMinor_transpose` | ADMITTED | TRUE (0 of 75) | none — correctly |
| `det_transpose` | `UnknownConst` — confounded | **FALSE**, 229 of 240 | yes, on the statement |

**Four of five are `UnknownConst`, so this probe says nothing about them on the
declaration axis.** That is the signal ADR-1185 names, and it applies here for
a different reason: this lane declares no new `Definition`, so there is no
`unskip`-shaped second target to mutate. The fifth,
`matMinor_transpose`, is ADMITTED **and** its statement stays TRUE — correctly,
since it never mentions which branch `matSkip` takes, only that both sides take
the same one.

**Mutation B — the column summand's ENTRY index transposed**, so
`col_zero_expansion_fn` reads `A 0 r` where it must read `A r 0`. The
statement-shaping Rust helper is what stands in for ADR-1185's `unskip` probe.

| declaration | declaration under mutation | statement under mutation |
| --- | --- | --- |
| `det_col_expansion` | **REJECTED** (`TypeMismatch`), on its own merits | **FALSE**, 215 of 240 |
| `det_transpose` | **REJECTED** (`TypeMismatch`), on its own merits | **TRUE** — its statement never mentions the helper |
| `matMinor_row_col_comm`, `det_minor_row_col_comm`, `matMinor_transpose` | ADMITTED — correctly | TRUE |
| the other 38 declarations in this file | ADMITTED — correctly | — |

Mutation B is exactly discriminating on the declaration axis: two refused, both
naming their own type error, and 41 correctly admitted. But note what the two
columns say together about `det_transpose`: mutation B breaks its **proof**
while leaving its **theorem** true, so it adds no statement coverage there —
only mutation A does, at 229 of 240. Neither probe alone covers both
declarations on both axes; the pair does.

### What the controls do NOT catch

- **Neither mutation probes `Nat.ble`'s guard ORDER inside `matSkip`.**
  `det_eq_det2` remains the discriminator for that, exactly as ADR-1135 said
  and ADR-1185 repeated.
- **No index-layer statement in this file separates a sign error.** The new
  sign evidence is `det_transpose_and_the_column_expansion_evaluate_and_pin_the_sign`,
  which asserts the column sum with the alternation shifted by one equals
  `-13` — POSITIVELY, not as a failed `def_eq`, since a failing `def_eq` has no
  early exit and a pathological control is a documented hazard here.
- **A total cannot separate the column expansion from the row expansion**, and
  for the pinned 3×3 it does not: both come to `13`, and the summand multiset
  is `{1, 0, 12}` either way. Only the per-index values differ — row
  `(1, 12, 0)` against column `(1, 0, 12)` — so the test pins **both**
  directions, and swapping the two builders fails it.
- **A transpose test over a symmetric matrix is vacuous.** The same test first
  asserts `matTranspose A 0 1 = 0` and `≠ 2 = A 0 1`.
- The `matMinor_transpose` pins use `matMinor Aᵀ 0 2 = [[2,1],[0,3]]` rather
  than `matMinor Aᵀ 0 1 = [[2,0],[0,1]]`, because the latter is symmetric and
  would not separate a transposed index.
- **The `matrix_det` inventory test still iterates its own list.** Its five new
  entries are correct, but `the_determinant_toolkit_is_axiom_free` cannot see a
  declaration nobody added to it — the defect `CLAUDE.md` records for
  `every_creal_declaration_is_checked_and_axiom_free`. Fixing it needs an
  environment-derived filter for the names this one file owns, and the `Rat.`
  namespace is shared by the whole prelude, so it is a separate task and is not
  attempted here.

## Consequences

- **Three of ADR-1120's four laws are proved**: `det matId n = 1` (ADR-1135),
  general-row expansion (ADR-1185), transpose invariance (here). Cofactor
  expansion along a general COLUMN now follows from `det_transpose` +
  `det_row_expansion` in one composition, and is not declared because nothing
  yet needs it.
- **Only multiplicativity remains, and it is blocked on a missing TYPE rather
  than on effort** (ADR-1135). Nothing in this ADR changes that, and nothing
  here is a step toward it.
- **A sizing that names a downstream direction is a claim about a ROUTE.**
  ADR-1185's was written by the lane that had just done the harder work, about
  a task it had not attempted, and it was pessimistic in cost and wrong in
  dependency at once. This is the standing "a handoff's *blocked on X* is a
  claim about one route" failure arriving from the other side — a handoff's
  *enabled by X*. Verify the enabling, not only the blocking.
- **When two exchanges run on different axes, expect no ordering hypothesis.**
  The `Nat.ble` premise in `matSkip_comm` is not a fact about `matSkip`; it is
  a fact about two deletions competing for one index space. That predicts
  cheapness for any future law relating a row operation to a column operation.

## Cost

The `rat` prelude build, measured on the same machine minutes apart by
disabling exactly these five declarations: **14.19 s** without them, **14.57 s**
with. Four runs across the session ranged 13.96–14.57 s on the identical tree,
so the 0.38 s is an **upper bound within run-to-run spread**, not a resolved
effect. Nothing resembling ADR-0584's runaway shape.

Full sweep: `cargo test -p axeyum-lean-kernel --lib rat_prelude::` —
**156 passed, 0 failed, 213.70 s** (ADR-1185 recorded 154 in 224.83 s; this
lane adds two tests).
