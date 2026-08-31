# ADR-1155: General-row determinant expansion is ONE rectangle Fubini once the range is full — the index and range layers land, the summand identification does not

Status: accepted
Date: 2026-08-31
Index-summary: ADR-1135 left general-row expansion "not blocked by a missing
type and not sized". It is sized here, and the route is shorter than the
classical one. Seven theorems land: `matSkip_comm` (deleting index `b` then
`a` reaches the same injection as deleting `a` then `succ b`, when `a <= b`),
its pointwise and `det`-level lifts, `sumRange_peel_head`, and
`sumRange_matSkip` (summing along the injection that misses `j` and adding
`f j` back recovers the whole sum). Together they turn a cofactor sum -- which
runs over a range ONE SHORT, reindexed by `matSkip` -- into a sum over the FULL
range, so a double cofactor expansion becomes a plain RECTANGLE and
`Rat.sumRange_swap` applies. No triangle decomposition, no `Nat.sub`, and no
adjacent-row-swap ladder: verified numerically, the double expansion along row
`0`-then-`i-1` and the row-`i` expansion are indexed by the SAME ordered pairs
of distinct columns and agree TERMWISE, for every `i`, so ONE induction on the
row index does what the classical proof does with a swap ladder. What remains
is the summand identification (a `Nat.beq`-guarded `W` and two case-split
proofs that the two parametrisations hit it), named precisely.
Index-status: accepted

## Context

[ADR-1120](adr-1120-the-general-n-determinant-is-a-function-plus-a-bound.md)
declared `Rat.det` at symbolic `n` and named four open laws.
[ADR-1135](adr-1135-a-determinant-congruence-is-what-the-absence-of-funext-costs.md)
closed the first (`det matId n = 1`), showed multiplicativity is blocked on an
aggregate type this kernel does not have, and said of the remaining two:

> Transpose invariance and general-row expansion are not blocked by a missing
> type, unlike multiplicativity — but neither was attempted here and neither
> is sized. […] a lane taking law 2 directly will find itself proving law 3
> inside it.

That ordering is right and this lane took law 3. What follows is the sizing
ADR-1135 declined to give, plus the part of it that landed.

## The obstruction ADR-1135 did not name: the range is one short

A cofactor expansion runs over a range of length `n`, and its recursive call
runs over a range of length `n - 1` **reindexed by `matSkip`**. Expand twice
and you get a sum over `[0, n) x [0, n-1)`, whose image is the set of ORDERED
PAIRS OF DISTINCT COLUMNS — but parametrised so that the second coordinate's
meaning depends on the first. The other expansion order parametrises the same
set the other way round. Relating them is the whole content of the law.

The classical move is to split the rectangle at its diagonal into two
triangles and reindex each; that needs a triangular Fubini, which needs
`Nat.sub` in a summation bound and is not in this prelude. The move taken here
is different and much cheaper:

> **Extend each inner sum back to the full range.** `matSkip j` is a bijection
> `[0, n) -> [0, n+1) \ {j}`, so a sum along it plus the value at `j` is the
> whole sum. Once both inner sums run over `[0, n)`, the double sum is a plain
> rectangle and `Rat.sumRange_swap` — the ordinary order-of-summation swap,
> already in the prelude — is the entire reindexing step.

The price is that the summand has to be *defined* at the diagonal, where the
cofactor expansion does not define it, and the natural definition is `0`. That
is a real cost and it is where the remaining work is (below), but it is
bounded, subtraction-free, and needs no type this kernel lacks.

## Decision

**Land the index layer and the range layer as reusable theorems, and record
the summand identification as the named remainder.** Seven declarations in
`crates/axeyum-lean-kernel/src/rat_prelude/matrix_det.rs`, all admitted by the
trusted gate on the first attempt, all with an empty `Kernel::axiom_footprint`:

| declaration | statement |
| --- | --- |
| `Rat.matSkip_zero` | `matSkip 0 x = succ x` |
| `Rat.matSkip_succ_succ` | `matSkip (succ q) (succ x) = succ (matSkip q x)` |
| `Rat.matSkip_comm` | `ble a b = true -> matSkip a (matSkip b x) = matSkip (succ b) (matSkip a x)` |
| `Rat.matMinor_col_comm` | the same, POINTWISE on entries |
| `Rat.det_minor_col_comm` | … carried to `det` through `Rat.det_congr` |
| `Rat.sumRange_peel_head` | `sumRange f (succ n) = f 0 + sumRange (fun k => f (succ k)) n` |
| `Rat.sumRange_matSkip` | `ble j n = true -> sumRange (fun k => f (matSkip j k)) n + f j = sumRange f (succ n)` |

Facts: `F:rat-mat-skip-comm`, `F:rat-sum-range-mat-skip`,
`F:rat-det-minor-col-comm`.

### Three shape choices, each forced

**The hypotheses are BOOLEAN `Nat.ble a b = true`, not `Nat.le a b`.** Both
inductions have to invert their premise in the successor step, and `ble`
inverts by iota-reduction alone: `ble (succ a') zero` reduces to `false`, so
the degenerate branch is a `NatOps::false_true_elim` with no lemma, and
`ble (succ a') (succ b')` reduces to `ble a' b'`, which hands the induction
hypothesis its own premise with no bridging lemma. With `Nat.le` each site
needs an inversion. (`Nat.ble_eq_true_of_le` and `Nat.le_of_ble_eq_true` both
exist, so a caller holding a `Nat.le` is one application away.)

**`sumRange_matSkip` quantifies `f` UNDER the `Nat.rec` motive**, not outside
it. The successor step at `j = succ j'` applies the induction hypothesis at the
SHIFTED function `fun k => f (succ k)`, so a motive with `f` fixed gives a
hypothesis that cannot be used. This is exactly ADR-1135's finding about
`det_congr`'s matrices, arriving one layer down: **whenever a recursion moves
to a different argument, that argument belongs inside the motive.**

**`matMinor_col_comm` keeps the row indices the SAME on both sides.** A
cofactor expansion of a cofactor expansion deletes row `0` and then row `0` of
the minor, so the row half of the double deletion is already identical
term-for-term; only the columns are exchanged. The fully general double-minor
exchange would move the rows too — `(0,0)` becomes `(1,0)` — which is a
different matrix and not what Laplace needs.

### `sumRange_peel_head` exists because `sumRange` peels from the right

`Rat.sumRange f (succ n)` reduces to `sumRange f n + f n`, so this prelude's
defining equations hand you the LAST summand. ADR-1135 wrote
`sumRange_head_of_tail_zero` for exactly this reason and it only reaches the
case where everything past index `0` vanishes. `sumRange_peel_head` is the
general form, and every left-side reindexing needs it — `sumRange_matSkip`
uses it three times.

## The route, verified numerically rather than asserted

    python3 docs/research/09-decisions/adr-1155-laplace-route-checks.py

That script is committed beside this ADR and exits nonzero when any claim
below fails, because CLAUDE.md's rule is that a plan's numeric claims must be
**re-executable rather than believed** — a plan asserting "verified
numerically" was false at 26 of 26 cases six days ago. It simulates `matSkip`,
`matMinor` and `det` over `Fraction` at exactly the definitions
`rat_prelude/matrix_det.rs` uses. Verified to FAIL: swapping the simulated
`matSkip`'s branches makes it exit 1 at the first control.

**The first draft of one of these checks was WRONG and reported 28
mismatches** — the error was in the check (it took `unskip` of the wrong
argument), not in the claim, and catching that is the reason to write the
check down rather than assert the result.

1. **`matSkip_comm` holds at all 126 triples `(a,b,x)` below 6 with `a <= b`,
   and is FALSE at 25 of the triples with `a > b`.** So the premise is
   load-bearing, not decoration. Smallest witness: `(1, 0, 0)` gives `2`
   against `0`.
2. **`sumRange_matSkip` holds at every sampled `(f, j, n)` with `j <= n` and
   fails at 180 of 400 random samples with `j > n`.** Same conclusion for its
   premise.
3. **General-row expansion is true of THIS `det`** — checked against the
   definition at every row, `n = 1..5`, 30 random matrices each. This is worth
   stating because `Rat.det` is a `Definition` and the trusted gate cannot tell
   you a definition is wrong.
4. **The pairing is TERMWISE, and it is general in the row index.** For
   `1 <= i < n`, the double sum obtained by expanding `det A n` along row `0`
   and then expanding each minor along ITS row `i-1`, and the double sum
   obtained by expanding along row `i` and then each minor along row `0`, are
   indexed by the SAME set of ordered distinct column pairs and their terms are
   EQUAL, pair by pair — 225 `(n, i, matrix)` cases, `n = 2..6`.

Point 4 is the finding that shortens the work, and it contradicts the natural
plan. **The classical proof proves the row-1 case and then walks a general row
up to the top with a ladder of adjacent row swaps, each swap negating the
determinant.** None of that is needed. The two double sums agree termwise for
EVERY `i` at once, so general-row expansion is a single induction on `i` whose
step is one rectangle Fubini. The adjacent-swap machinery — and with it row
antisymmetry, which is the expensive part of the classical route — is not on
the critical path for this law.

Two supporting identities inside point 4, each checked separately:

- The two double minors' ROW maps agree at every `(i, r)`:
  `matSkip 0 (matSkip (i-1) r) = matSkip i (matSkip 0 r)`. That is
  `matSkip_comm` at `a = 0`, `b = i-1`, and at `i = 1` it is even definitional
  (both sides reduce to `succ (succ r)`).
- The sign identity `altSign p * altSign (unskip p a) = altSign (1 + a + b)`
  where `p = matSkip a b` and `unskip p a` is `a`'s index in the range missing
  `p`. 0 mismatches over `a, b < 8`. It is independent of `i`, because the
  `i`-dependent factor `altSign (i-1)` appears on both sides.

## What remains, named exactly

The assembly needs a summand defined on the whole square. Writing `p` for the
row-`0` column and `q` for the row-`i` column:

```text
W p q := if Nat.beq p q then 0
         else altSign p * altSign (unskip p q)
               * (A 0 p * (A i q * det (matMinor (matMinor A 0 p) 0 (unskip p q)) m))
unskip p q := if Nat.ble (succ p) q then Nat.pred q else q
```

`Rat.bool_select_rat` and `Nat.pred` both exist, so `W` is expressible; the
`if` is a `Bool.rec`, the same device `Rat.matId` already uses. Four pieces
then close the law, and none of them needs a type this kernel lacks:

1. **`unskip (matSkip j k) = k` and `Nat.beq j (matSkip j k) = false`** — two
   index lemmas, each a case split on `Nat.ble j k` in the shape
   `matSkip_succ_succ` already uses.
2. **`W j (matSkip j k)` is the LHS summand** and **`W (matSkip a b) a` is the
   RHS summand** — two identifications, each a case split on the order of the
   two columns, consuming `det_minor_col_comm` for the determinant factor and
   the sign identity above for the coefficient. The RHS one additionally needs
   the row bridge `matMinor (matMinor A 0 u) 0 v r c = matMinor (matMinor A i u') 0 v' r c`,
   whose row half is `Eq.refl` and whose column half is `matMinor_col_comm`.
3. **An `altSign` parity toolkit** — `altSign (succ (succ n)) = altSign n` from
   `neg_neg`, and an addition rule. `Rat.altSign_succ` is already there and
   both defining equations are `Eq.refl`.
4. **The assembly**: `sumRange_matSkip` under `sumRange_congr` on each side to
   fill the inner ranges, then `Rat.sumRange_swap`, then `det_congr` nowhere at
   all — the matrices have already been identified at step 2.

**This is a sizing, not a claim that it is cheap.** Step 2 is the bulk: two
proofs with a case split each, over terms carrying four indices and a
determinant. What can be said with confidence is what is NOT needed:
no triangular Fubini, no `Nat.sub` in any summation bound, no row-swap
antisymmetry, no adjacent-swap ladder, and no aggregate type.

## Consequences

- **Take `sumRange_matSkip` as the standard move for any `matSkip`-reindexed
  sum, in both remaining laws.** Transpose invariance has the same shape:
  `det (transpose A) n` expands along a column of `A`, its inner sums are
  `matSkip`-reindexed, and filling them to the full range is what makes them
  comparable.
- **Do not build a triangular Fubini for this.** It was the obvious route and
  it is strictly more machinery than the problem needs. If one is ever wanted
  for another reason, `Rat.sumRange_diagonal` plus `sumRange_peel_head` is the
  cheapest path to it (the antidiagonal grouping already carries the `Nat.sub`
  bookkeeping), but nothing here requires it.
- **Do not prove row antisymmetry on the way to row expansion.** It is the
  classical route and it is not the shortest one here; measured above, the
  pairing is termwise for every row index simultaneously.
- ADR-1135's four-law list becomes: one proved (`det matId n = 1`); **general
  row expansion sized, with its index and range layers landed and the summand
  identification named**; transpose invariance still unattempted but now
  strictly downstream of the same two layers; multiplicativity blocked on a
  missing aggregate type.

## What the new theorems do NOT add, MEASURED

ADR-1135 recorded that `Rat.matMinor_matId` survives the `Rat.matSkip`
branch-swap mutation (`bool_select_nat cond (succ x) x` becomes
`bool_select_nat cond x (succ x)`) and therefore adds no index coverage, and
that "one bad declaration poisons the shared prelude build" so that only the
FIRST rejection is nameable. That second part is a limitation of how the
mutation was run, not a fact about the mutation, and it is fixed here:
`declare_matrix_det`'s 24 steps were rewritten in an isolated snapshot to
REPORT each rejection instead of short-circuiting, so one run gives a full
table. (Snapshot deleted afterwards; `git status` clean. Mutating the shared
checkout would break sibling lanes' builds — CLAUDE.md's standing rule.)

**A rejected declaration and a false statement are different findings, and
conflating them overstates coverage.** So each row below records both: whether
the kernel rejected the declaration under the mutation, and — checked
independently by simulating the mutated `matSkip` — whether the STATEMENT is
still true. A declaration that is rejected while its statement stays true adds
no coverage against that mutation; its proof merely names the branches in
order.

| declaration | declaration under mutation | statement under mutation | coverage added |
| --- | --- | --- | --- |
| `matSkip_zero` | REJECTED (`DeclarationValueMismatch`) | **FALSE** (`skip 0 x` becomes `x`) | **yes** — the cheapest discriminator for this bug class in the file, and the only `Eq.refl` one |
| `matSkip_succ_succ` | REJECTED (`DeclarationValueMismatch`) | **TRUE** at all 64 pairs below 8 | **no** — the `bool_cases` motive names the branches in order, so the proof breaks while the theorem stays true |
| `matSkip_comm` | rejected, but only via the missing `matSkip_succ_succ` (`UnknownConst`) | **FALSE**, 36 counterexamples with `a <= b` below 6, smallest `(0,0,0)`: `0` against `1` | **yes**, on the statement |
| `matMinor_col_comm` | `UnknownConst`, confounded the same way | **FALSE**, 148 of 400 random instances | yes, on the statement |
| `det_minor_col_comm` | `UnknownConst`, confounded the same way | **FALSE**, 125 of 400 random instances | yes, on the statement |
| `sumRange_peel_head` | **ADMITTED** | TRUE — mentions no `matSkip` at all | none, by construction |
| `sumRange_matSkip` | REJECTED (`TypeMismatch`) | **FALSE**, 228 of 300 random instances | **yes** |

Two things in that table are worth carrying forward.

**The prediction was wrong about `matSkip_succ_succ`, in the direction that
flatters the work.** Reasoning from the semantics alone says it survives
(`succ` passes through the selection under either reading, and it does — 64 of
64). Running the mutation says the declaration is REJECTED. Both are true and
only the pair is honest: the kernel refuses the proof term because the motive
handed to `Bool.rec` is written branch-by-branch, and a swapped definition
puts the branches the other way round. Recording only the rejection would have
claimed index coverage this theorem does not have — the same overstatement
ADR-1135 caught itself making about `matMinor_matId`.

**Three of the seven rejections are confounded** by an upstream declaration
the mutation had already removed, which is why the statement column exists at
all. The per-step table tells you WHICH declaration first failed; it does not
tell you whether a later one would have failed on its own merits. Simulating
the mutated definition does, it costs ten lines of Python, and it is the same
technique that catches a vacuous negative control.

Three further rows from the same run, outside this lane's work but new:
`det_eq_det2`, `matMinor_eval_example`, `det_eval_example` and
`det_eval_example4` are all rejected, while `det_eval_singular` (value `0`),
`det_congr`, `matMinor_matId` and `det_matId` are all ADMITTED. So ADR-1135's
finding generalises: **the whole `det matId n = 1` cluster survives the branch
swap**, and `det_eq_det2` remains the discriminator, exactly as it said.

The three `def_eq` controls in
`rat_prelude_tests::the_laplace_index_layer_hypotheses_are_load_bearing` are
about a different failure — a premise that could be dropped, or a reindexing
that could be forgotten — and each states its scope at the declaration. **None
of them separates a sign error**, because no sign appears in any of these
seven statements; `det_eval_example`, whose value is `13`, remains the theorem
that does.
