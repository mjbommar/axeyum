# The theory layer of CDCL(T): what the reference solvers do, what we do

Survey lane `research-theory-solvers`, 2026-09-08. Read-only; no builds, no
tests, no production change proposed. Written for an implementer of
**reusable, configurable** components: one simplex, one congruence closure, one
theory trait — not one engine per division.

**Claim tags.** `[C]` read from source, cited `path:line`. `[P]` from a paper
or its abstract. `[I]` my inference from `[C]`/`[P]` — argued, not measured.
Where I did not check something I say **did not verify**.

**Sources.** `references/z3` (existing clone), `references/cvc5` and
`references/yices2` (cloned by this lane on 2026-09-08 with
`git clone --depth 1`; `cvc5` is already in `scripts/fetch-references.sh`,
`yices2` is not). Citations to those are relative to `references/<name>/`.
Citations to our own tree are relative to the repository root.

Yices2 matters more than its market share suggests: Dutertre and de Moura wrote
both the CAV'06 paper and that implementation, so `simplex.c` is the reference
text for the algorithm we already claim to implement.

---

## 0. The one-paragraph answer

Our simplex **is** the Dutertre–de Moura algorithm and is correct
(`crates/axeyum-solver/src/simplex.rs:1-4`, `:295`, `:601`) `[C]`. What it is
missing is the *engineering* that makes the algorithm fast, and every missing
piece is **shared infrastructure across QF_LRA, QF_LIA, QF_UFLRA and QF_UFLIA
at once**: sparse rows with column occurrence lists, a non-Bland pivot rule
with a Bland fallback, and row-based implied-bound propagation. The measured
QF_LRA bottleneck already recorded in our own source —
`350 × 425` tableau, **1.41 ms per pivot**, 21.7 s of a 24 s budget across
6,571 checks at only **2.3 pivots each**
(`crates/axeyum-solver/src/simplex.rs:589-596`) `[C]` — is a *cost per pivot*
problem, not a pivot *count* problem, and cost per pivot is exactly what the
dense representation determines. That is finding #1 and it is not close.

The second largest lever is congruence closure: our EUF theory rescans **all**
atoms and **all** asserted disequalities on every call
(`crates/axeyum-solver/src/euf_egraph.rs:516-535`, `:551-575`) `[C]`, where Z3
detects both at merge time off the parent lists. QF_UF is 162/200 and QF_UFLIA
122/180 in the current ledger (`docs/plan/global/10-status.md:59-63`).

The third is theory combination: we have model-value grouping
(`crates/axeyum-solver/src/theory_combination.rs:120-128`) but **not** the one
trick that makes MBTC work in practice — randomising the model inside each
variable's slack before grouping, so that coincidences that are *forced*
survive and coincidences that are *accidental* do not
(`references/z3/src/smt/theory_arith_aux.h:2114-2160`) `[C]`.

A fourth finding is negative and saves effort: **do not start with cuts or
sum-of-infeasibilities.** cvc5 implements no Gomory or MIR cuts of its own;
Yices's multi-cut path is compiled out behind `if (false && ...)`
(`references/yices2/src/solvers/simplex/simplex.c:9111`); Z3 disables Gomory
entirely while its Diophantine solver is productive
(`references/z3/src/math/lp/int_solver.cpp:240-244`). And cvc5 — whose authors
wrote the sum-of-infeasibilities paper — ships `--use-soi` **false**, using SoI
only as a last-ditch pass (`arith_options.toml:197-201`,
`theory_arith_private.cpp:3441-3483`). Three implementations, three independent
decisions not to lead with either. What all three *do* run is
**bound strengthening → Diophantine pre-solve → branch** (§5.4).

A fifth is a **correction to the brief's framing**: "a shared simplex
usable by LRA/LIA/IDL/RDL" is not what any reference solver does. All three
specialise difference logic away from simplex and pick between them on static
features of the input (§3.7). Our `dl_online.rs` already does the right thing,
and the measured QF_IDL bottleneck is the Boolean core, not the theory
(`docs/research/11-design-review/2026-09-05-sat-smt-performance-and-architecture-review.md:303-309`).
So IDL/RDL should be **removed** from the shared-simplex scope. (Nuance worth
keeping: Z3 routes a *declared* `(set-logic QF_IDL)` to its LP solver and only
uses the graph solver on the auto-config path — `smt_setup.cpp:319-323` vs
`:325-381`. The specialisation is a performance choice made from static
features, not a capability boundary. `[C]`)

---

## 1. Ranked findings — expected value across divisions per unit effort

Divisions in scope and their current standing
(`docs/plan/global/10-status.md:59-66`, ledger of 2026-09-05, solver commit
`9914a1c0e`): QF_LRA 91/145 = 62.8%, QF_IDL 70/123 = 56.9%, QF_RDL
107/154 = 69.5%, QF_UFLIA 122/180 = 67.8%, QF_UF 162/200 = 81.0%. QF_LIA and
QF_UFLRA are not weak edges in that list.

| # | Change | Divisions moved | Shared? | Effort | Why it ranks here |
|---|---|---|---|---|---|
| 1 | **Sparse tableau rows + column occurrence lists** in `simplex.rs` | QF_LRA, QF_LIA, QF_UFLRA, QF_UFLIA, QF_LIRA | **Shared** — one file | M | Attacks the one bottleneck we have already profiled (84% of QF_LRA timeout wall clock in `LraTheory::final_check`/`feasibility`), and the recorded numbers say the cost is per-pivot, not per-check |
| 2 | **Heuristic entering-variable rule with a Bland fallback** | same as #1 | **Shared** — one function | S | ~40 lines. Yices's rule is a column-length count, not a ratio test (§3.2). Ours is Bland unconditionally, which is the *slow* rule |
| 3 | **Row-based implied-bound propagation** | same as #1, plus QF_IDL indirectly | **Shared** | M | Ours only compares bounds on the *same* linear form (`lra_online.rs:792-870`); it cannot derive a bound on `x` from a row's bounds on `y, z`. This is the standard theory-propagation lever |
| 4 | **Merge-driven EUF conflict/propagation** (use lists, class-attached disequalities) | QF_UF, QF_UFLIA, QF_UFLRA, QF_ABV, UF | **Shared** — one crate | M | Replaces two full rescans per assert with O(1) amortised work at merge |
| 5 | **Model randomisation before interface-equality proposal** | QF_UFLIA, QF_UFLRA, UF | **Shared** | S | The missing half of MBTC; ~60 lines against an existing `propose_interface_equalities` |
| 5b | **Care graph: filter interface pairs structurally before splitting** | QF_UFLIA, QF_UFLRA, UF, QF_ABV | **Shared** | M | cvc5's default and only combination mode. Three filters (same operator, both trigger terms, not already equal/disequal) over a per-operator argument trie cut the `O(n²)` pair set to pairs a congruence could actually fire on (§7.3). We currently hand every model-value group to a depth-capped DFS |
| 6 | **Per-logic parameter table driven by static input features** | all 12 | **Shared** — a table | S | Both Z3 and Yices ship one and it is a pure config artifact (§8.4). We have `config_registry.rs` and no such table |
| 7 | **Negative EUF propagation (atom forced `false`)** | QF_UF, QF_UFLIA, UF | **Shared** | M | Explicitly deferred in our source (`euf_egraph.rs:512-514`) |
| 8 | **Round-to-nearest branch lemma (cvc5's "BRAB")** | QF_LIA, QF_UFLIA, QF_LIRA | Division-specific, tiny | **S** | `(or (= v n) (<= v n-1) (>= v n+1))` with a phase hint on the equality, where `n` is the *nearest* integer — `references/cvc5/src/theory/arith/branch_and_bound.cpp:49-122`, option `--arith-brab` **default true**. A one-lemma change, on by default in cvc5, and it subsumes the unit-cube intuition |
| 9 | **Diophantine / integer-equation pre-solve before branching** | QF_LIA, QF_UFLIA | Division-specific | L | **All three** reference solvers run it and rank it above cuts (§5.4). cvc5's `--dio-solver` and Z3's `lp.dio` are both **on by default**; Z3 turns Gomory *off* while dio is productive |
| 10 | **Sum-of-infeasibilities simplex as a second mode** | QF_LRA, QF_LIA | Shared (mode on the same tableau) | L | Demoted on evidence: cvc5 authored the SoI paper and ships `--use-soi` **false**, using SoI only as the last-ditch pass (§A2). Do #1–#3 first; SoI inherits their representation anyway |
| 11 | **Mixed-integer Gomory cuts** | QF_LIA | Division-specific | M | **Demoted hard.** cvc5 generates *no* Gomory cuts of its own (only GLPK replay, off by default); Yices's multi-cut path is `if (false && ...)`; Z3 disables Gomory while its Diophantine solver is productive. Three implementations, three ways of not using them |

Deliberately **not** ranked: anything for QF_IDL/QF_RDL in the theory layer.
Our DL solver is already a correct Cotton–Maler incremental negative-cycle
detector with unit-multiplier Farkas certificates
(`crates/axeyum-solver/src/dl_online.rs:1-60`) `[C]`, and the 2026-09-05
profile puts 87% of QF_IDL timeout wall clock in `CdclT::unit_propagate`'s
clause rescan, not in the theory
(`docs/research/11-design-review/2026-09-05-sat-smt-performance-and-architecture-review.md:303-309`)
`[C]`. Sending theory-layer effort at QF_IDL would be aiming at the wrong
half of the system.

---

## 2. What we already have

Inventoried from source; every absence below was grepped for, not assumed.

### 2.1 The simplex is real, and it is DdM

`crates/axeyum-solver/src/simplex.rs:1-4` names the CAV'06 paper. `[C]`

- `struct Tableau` at `simplex.rs:295` with the full DdM state: `basic`,
  `row`, `value` (β), `lower`/`upper`, `is_basic`, `rel_rhs`. `[C]`
- Main loop `Tableau::run` at `simplex.rs:497`; `pivot_and_update` at
  `simplex.rs:601`, explicitly the paper's `pivotAndUpdate`. `[C]`
- Warm/incremental wrapper `Incremental` at `simplex.rs:893`, `check` at
  `simplex.rs:962`. `[C]`
- Budgets `MAX_TABLEAU_CELLS = 4_000_000` (`:74`) and
  `MAX_PIVOTS = 2_000_000` (`:81`). `[C]`
- Fourier–Motzkin (`lra.rs:905`) is now only the over-cap fallback
  (`simplex.rs:53-55`), not the primary path. `[C]`

Delta-rationals are present and correct: `struct Delta { c, k }` at
`simplex.rs:201`, meaning `c + k·δ`, with lexicographic `cmp` at `:237` and
strict bounds converted at `set_row_bound` (`:393`). `[C]` A concrete δ is
chosen in `materialize` (`simplex.rs:729`). `[C]`

Farkas certificates are extracted from the conflicting row at
`Tableau::farkas` (`simplex.rs:799`) with the correct sign discipline
(`:809-831`) and are **self-verified** before being returned (`:832-837`,
verifier `check_farkas` at `:1042`). `[C]` That is better discipline than any
of the three reference solvers, all of which trust their own row arithmetic.

### 2.2 The three gaps inside `simplex.rs`

**(a) Dense rows, no column index.** `row: Vec<Vec<Rational>>` at
`simplex.rs:307`. `rows_sparse` (`:317`) holds only the immutable *input*
structure and is not the search representation. There is no `HashMap`,
`BTreeMap`, or occurrence array in the file — its only imports are
`std::time::Instant` and `axeyum_ir::Rational` (`simplex.rs:65-67`). `[C]`
Pivot is documented as `O(rows × columns)` (`:580`, `:592`). `[C]`

**(b) Bland's rule unconditionally, for both choices.** The leaving-row scan
takes the first violating basic variable in index order (`simplex.rs:511-524`);
`select_entering` (`:550`) returns the smallest-index usable nonbasic
(`:551-572`). The doc at `:58-59` states termination rests on Bland. There is
no Dantzig rule, no steepest edge, no largest-coefficient rule, and therefore
no heuristic-with-Bland-fallback. `[C]`

**(c) No push/pop inside the simplex.** Grepping `backtrack`, `undo`, `scope`,
`trail` in `simplex.rs` returns nothing relevant. `[C]` The incremental
interface is bound mutation — `assert_bound` (`:947`) and `retract` (`:956`) —
and scope management lives in `LraTheory` (`lra_online.rs:379`, `:421`,
`:1214`, `:1220`), reconciled per check by `SimplexEngine::sync`
(`lra_online.rs:300-332`), which finds the shared prefix of the bound stack and
retracts/re-asserts the rest. `[C]` This matches what Yices and Z3 do in
spirit (§3.5) and is **not** a gap; it is the right layering.

### 2.3 The theory trait — already widened

`pub trait TheorySolver` lives, oddly, in
`crates/axeyum-solver/src/euf_egraph.rs:67`. It already carries the ADR-1701
widening: `assert` (`:82`), `push`/`pop` (`:84`/`:86`), `propagate` (`:91`),
**`final_check`** (`:103`), **`propagate_into(&mut PropagationQueue)`**
(`:117`), **`explain(ExplanationId)`** (`:135`), `take_new_atoms` (`:145`),
`engine_counters` (`:159`). `[C]`

So the interface criticism in the 2026-09-05 review (§3.2 D2) is **closed**;
what remains is that the *theories* under it are slow, not that they cannot
express what they need. One live caveat: `LraTheory`'s
`defer_to_final_check` is **off by default** and only the `CdclT`-driven
adapter opts in, because `uflra_online`'s combination loop and `lra_online`'s
own `Dpll` search never call `final_check` and would silently lose
per-assert completeness (`lra_online.rs:397-406`). `[C]` That is a real
constraint on any change here.

Implementors of the trait: `EufTheory` (`euf_egraph.rs:593`), `LraTheory`
(`lra_online.rs:1164`), `LiaTheory` (`lia_online.rs:1473`), `DlTheory`
(`dl_online.rs:1612`), `StringTheory` (`string_theory.rs:721`),
`CombinedIncremental` (`combined_theory.rs:697`), `CombinedIncrementalLia`
(`combined_theory_lia.rs:720`), `CombinedUfbvTheory` (`ufbv_online.rs:883`),
plus the thin adapters `CdcltLraTheory` (`lra_theory.rs:168`) and
`CdcltLiaTheory` (`lia_theory.rs:113`). `[C]`

### 2.4 Our theory propagation is same-form only

`LraTheory::propagate_bounds` (`lra_online.rs:816`) propagates an unassigned
order atom when the tightest asserted bound **on the same canonical linear
form** already entails it (`:840-866`), capped at
`MAX_BOUND_PROPAGATIONS_PER_CALL = 256` (`:104`). `[C]` The doc is explicit:
"one rational comparison per atom, **no simplex probe and no tableau scan**"
(`:801-802`). `[C]`

That is `f ≤ u ∧ u ≤ b ⟹ f ≤ b`. It cannot derive a bound on one variable
from a row's bounds on the others, which is what Yices's
`simplex_strengthen_bounds` and Z3's `bound_analyzer_on_row` do. This is
finding #3.

### 2.5 EUF: correct engine, quadratic driver

The congruence engine in `crates/axeyum-egraph/src/lib.rs` is genuinely
Nieuwenhuis–Oliveras: proof forest fields `proof_parent` (`:246`) and
`proof_edge` (`:248`) kept **separate from** the union-find (`:231-232`),
`Edge::Congruence` (`:197`), structured `ProofStep::Congruence` (`:220`), an
undo journal (`ParentPushed`, `:261`), and an independent re-validator
`check_congruence` (`:14`). `[C]` Explanations go to the LCA (`:12-13`). `[C]`

The **solver-side driver** is where the cost is:

- `EufTheory::propagate` (`euf_egraph.rs:516`) iterates **every** registered
  atom on every call and asks `egraph.equal(a, b)`. `[C]`
- `first_conflict` (`euf_egraph.rs:551`) iterates **every** asserted
  disequality, then does an **all-pairs** `O(k²)` scan over distinct constants
  (`:568-575`). `[C]` It is called from `assert`.
- Disequality entailment — propagating an atom `false` — is explicitly
  deferred (`:512-514`). `[C]`

Z3 does none of this by rescanning: disequalities are attached to the class
(`add_th_diseqs`, `references/z3/src/ast/euf/euf_egraph.cpp:611`) and
congruence is rediscovered only over the *parents of the smaller class*
(`remove_parents`/`reinsert_parents`, `euf_egraph.cpp:559`/`:581`). `[C]`

### 2.6 Combination: proposal without randomisation

`crates/axeyum-solver/src/theory_combination.rs` is labelled work-in-progress
at `:7`. `propose_interface_equalities` (`:120`) groups shared terms by their
**concrete model value**, keyed `BTreeMap<(u32, u128), Vec<TermId>>` over
`Value::Bv { width, value }` (`:126-131`) — that is the MBTC proposal step
under a different name, but note it is **bit-vector-typed only**: a real- or
integer-valued shared term does not group here at all. `[C]` Grepping `mbtc`,
`arrangement`, `model_based` returns nothing.
`classify_interface_equalities` (`:220`) then checks proposals against
congruence closure.

`[I]` So the module that carries the Nelson–Oppen/MBTC name covers EUF↔BV,
while the divisions in scope for this survey (QF_UFLIA, QF_UFLRA, UF) are served
by the separate `combined_theory.rs` / `combined_theory_lia.rs` DFS. Findings #5
and #5b apply to those two files, not to `theory_combination.rs`.

The working combination is `combined_theory.rs` (EUF+LRA) and
`combined_theory_lia.rs` (EUF+LIA): interface case-split DFS with a
`MAX_SPLIT_DEPTH` cap (`combined_theory.rs:49`) and a decline when there are
too many pairs (`:152`). `[C]` There is no general N-theory framework;
EUF↔BV has shared-term detection only.

### 2.7 Duplication worth knowing about before you touch anything

Three δ-rational implementations (`simplex.rs:201`, `lra.rs:2473`,
`dl_online.rs:129`) and three LRA feasibility engines (`simplex.rs` DdM,
`lra.rs:905` Fourier–Motzkin, and a second dead DdM at `lra.rs:2531` with no
Farkas extraction and no in-crate callers besides two `lib.rs` re-exports).
`[C]` Two CDCL(T) drivers (`cdclt.rs` and the `axeyum_cnf` core via
`native_cdclt.rs`), self-documented at `native_cdclt.rs:5-10`; four routes are
still on the old one (`ufbv_online.rs:1378`, `uflra_online.rs:1354`,
`uflia_online.rs:1709`, `qinst_egraph.rs:2487`). `[C]`

Also: `crates/axeyum-solver/src/` has 177 top-level files, of which roughly
three-quarters are certificate/scenario/proof-emission modules, not engine
code. The engine is about twenty files. Do not read the directory listing as a
map of the engine.

---

## 3. Simplex for LRA in the reference solvers

### 3.1 Tableau representation — sparse rows *and* sparse columns, cross-linked

Yices's `matrix_t` (`references/yices2/src/solvers/simplex/matrices.h:153-172`)
is the design to copy. `[C]`

```c
typedef struct row_elem_s {
  int32_t c_idx;    // column index
  int32_t c_ptr;    // pointer into column[c_idx]
  rational_t coeff;
} row_elem_t;                      // matrices.h:88-92

typedef struct col_elem_s {
  int32_t r_idx;   // row index
  int32_t r_ptr;   // index into row[r_idx]
} col_elem_t;                      // matrices.h:94-97
```

The essential detail is the **cross-link**: a row element stores where it lives
in its column, and a column element stores where it lives in its row. So
deleting or updating an entry is O(1) from either side, which is what makes
pivoting on a sparse matrix affordable. `[C]` Both rows and columns are
free-list-managed arrays with `nelems`/`size`/`capacity`/`free`
(`matrices.h:107-125`). `[C]`

`matrix_t` also carries `base_var[i]` (basic variable of row `i`) and
`base_row[v]` (row where `v` is basic, or −1) — the basic/nonbasic split as two
mutually inverse arrays (`matrices.h:153-172`) `[C]` — plus an auxiliary
`index[]` array used only *during* a row operation to find "does this row
already contain column `j`?" in O(1), which must be restored to all −1 outside
row operations (`matrices.h:134-140`). `[C]`

Default row/column capacity is 10 (`matrices.h:178`, `DEF_MATRIX_ROW_SIZE`).
`[C]`

**Z3 uses the identical shape**, which is the second independent
confirmation. `static_matrix<T, X>`
(`references/z3/src/math/lp/static_matrix.h:88-89`) holds
`std_vector<row_strip<T>> m_rows` and `std_vector<column_strip> m_columns`, with
`[C]`:

```cpp
template <typename T> class row_cell {
    unsigned m_j;       // row cell: the COLUMN index; column cell: the ROW index
    unsigned m_offset;  // index of the MIRROR cell in the other strip
    T        m_coeff;   // only rows carry the coefficient
};
typedef row_cell<empty_struct> column_cell;   // static_matrix.h:41 — 8 bytes
```

Same cross-link as Yices, with the refinement that a column cell is only
`(row, offset)` and the coefficient is read through the row:
`get_val(cc) == m_rows[cc.var()][cc.offset()].coeff()`
(`static_matrix.h:107-109`, invariant checked at
`static_matrix_def.h:441-455`). `[C]` Insert cross-links both cells
(`static_matrix_def.h:489-497`); delete is **swap-with-last in both strips**
with both mirror offsets patched (`static_matrix_def.h:458-487`). `[C]`

**The one trick to copy verbatim.** Row-to-row elimination uses a persistent
scatter array, `m_work_vector_of_row_offsets: Vec<i32>` of length `#columns`,
held at all `-1` between operations
(`static_matrix.h:88`, used in `pivot_row_to_row_given_cell`,
`static_matrix_def.h:51-86`) `[C]`:

```cpp
scan_row_strip_to_work_vector(rowii);          // offsets[col] = position in rowii
for (const auto& iv : m_rows[i]) {             // the pivot row
    unsigned j = iv.var();  if (j == pivot_col) continue;
    int j_offs = m_work_vector_of_row_offsets[j];
    if (j_offs == -1) add_new_element(ii, j, alpha * iv.coeff());  // fill-in
    else              addmul(rowii[j_offs].coeff(), iv.coeff(), alpha);
}
for (k in 0..prev_size_ii) m_work_vector_of_row_offsets[rowii[k].var()] = -1;
for (k in rowii.len()..0) if (is_zero(rowii[k].coeff())) remove_element(rowii, rowii[k]);
```

That is what makes a sparse row combine in O(nnz(row_i) + nnz(row_ii)) rather
than O(nnz × log) or O(columns). The lazy reset — restoring only the entries
you touched — is the part that is easy to get wrong. `[C]`

Z3's pivot itself is `pivot_column_tableau(j, piv_row)`
(`lp_core_solver_base_def.h:250-286`): divide the pivot row so the pivot
coefficient is exactly 1, swap `j`'s cell to position 0 of its column strip,
then `while (column.size() > 1)` eliminate from the back — each call removes
exactly one cell so it terminates. `[C]` `change_basis` is an O(1) swap of two
entries in `m_basis`/`m_nbasis` plus the `m_basis_heading` encoding
(`>= 0` = row index, `< 0` = `-(position_in_nbasis)-1`)
(`lp_core_solver_base.h:384-399`, `:346-362`). `[C]`

**Contrast with ours.** `simplex.rs:307` is `Vec<Vec<Rational>>`. On the
recorded `350 × 425` instance that is 148,750 `Rational` cells touched per
pivot regardless of how many are nonzero. `[C]` `[I]` If those rows are as
sparse as LRA rows typically are, the sparse representation is the whole 1.41 ms.
**What to measure before committing:** the mean nonzero count per row on the
same instance. That measurement is the go/no-go for finding #1 and it does not
require any code change beyond a counter.

### 3.2 Pivot selection — the heuristic is not a ratio test

This is the most directly copyable, smallest-diff finding in the survey.

Yices's entering-variable score
(`references/yices2/src/solvers/simplex/simplex.c:3880-3925`) `[C]`:

> score of `x` = number of **non-free** basic variables that depend on `x`,
> plus 1 if `x` is itself not free (a variable is *free* if it has no upper or
> lower bound). The variable with the **smallest** score is selected; ties are
> broken **uniformly at random** among all variables with that score.

The implementation (`simplex.c:3889-3925`) walks the *column* of `x` — which is
only affordable because columns are materialised (§3.1) — and short-circuits as
soon as the running score exceeds the incumbent (`simplex.c:3908`). `[C]`
Reservoir sampling does the uniform tie-break (`simplex.c:4008-4014`). `[C]`

This is a **fill-in minimising** rule, not a Dantzig or steepest-edge rule. It
is picking the pivot that will damage the sparsity of the tableau least. That
is why it pairs with §3.1 and why it is cheap.

Termination is recovered by switching to Bland's rule on a *repeat-leaving*
counter, not on an iteration count
(`references/yices2/src/solvers/simplex/simplex.c:4315-4331`) `[C]`:

- `repeats` is incremented whenever a variable leaves the basis for at least
  the second time in this call (tracked by a per-variable mark, `simplex.c:4319-4324`).
- When `repeats > bthreshold`, `use_blands_rule` is set for the rest of the
  call (`simplex.c:4325-4330`).
- `SIMPLEX_DEFAULT_BLAND_THRESHOLD = 1000`
  (`references/yices2/src/solvers/simplex/simplex_types.h:908`) `[C]`, scaled
  by the problem size at the top of each feasibility call: `× 1000` above
  10,000 variables, `× 100` above 1,000 (`simplex.c:4243-4249`). `[C]`
- `use_blands_rule` is reset to `false` at the *start* of every
  `simplex_check_feasibility` (`simplex.c:4239`), so a single hard call does
  not permanently poison the solver. `[C]`

Under Bland the same functions score `y` by its own index (`simplex.c:3982-3993`
and `:4065-4076`) — one code path, two scoring functions. `[C]`

**Z3 independently arrived at the same two rules.** Its entering choice
(`references/z3/src/math/lp/lp_primal_core_solver.h:183-228`) ranks candidates
by (a) the number of **non-free basic variables** in the candidate's column
— `get_num_of_not_free_basic_dependent_vars`, capped with an early exit
(`:143-156`) — then (b) **column nonzero count**, then (c) **reservoir
sampling** among ties (`m_settings.random_next(++nchoices) == 0`). `[C]` The
source comment gives the second motivation explicitly: "a short row produces
short infeasibility explanation" (`:186-187`). `[C]`

Z3's Bland switch uses the same trigger and the **same constant**: a counter of
*repeated leaving columns*, `m_bland_mode_threshold = 1000`
(`lp_primal_core_solver.h:645`), condition at `:374-382`, reset per solve in
`init_tableau_rows` (`:626-630`). `[C]` Z3's *older* simplex uses 1000 too
(`references/z3/src/math/simplex/simplex.h:118`,
`simplex_def.h:906-921`). `[C]`

`[I]` Two independent implementations converging on *fill-in-minimising
entering + random tie-break + Bland after 1000 repeated leavings* is about as
strong a signal as this survey can produce. Copy it.

Z3 also exposes `arith.greatest_error_pivot` (default `false`) and
`arith.simplex_strategy` (default 0)
(`references/z3/src/params/smt_params_helper.pyg:117`, `:124`) `[C]`, but in the
SMT hot path the strategy is **forced** to `tableau_rows`:
`lar_solver::find_feasible_solution` does
`flet f(settings().simplex_strategy(), simplex_strategy_enum::tableau_rows)`
(`references/z3/src/math/lp/lar_solver.cpp:470-472`) `[C]`. The cost-driven
loop runs only for `maximize_term`. So there is effectively **one** pivot rule
to port, not two.

**Implementation note for us.** Yices's score needs the column occurrence
lists, so #2 depends on #1 in its full form. A degraded version that does not:
score a candidate by the number of *rows* in which it has a nonzero
coefficient, computed once per check rather than per pivot, and re-used until
the basis changes. `[I]`

### 3.3 Delta rationals — the representation and the final instantiation

All three reference solvers use the same pair representation we do. Yices:

```c
typedef struct {
  rational_t main;   // c
  rational_t delta;  // d
} xrational_t;       // references/yices2/src/terms/extended_rationals.h:37-41
```

with `xq_set_q_plus_delta` / `xq_set_q_minus_delta`
(`extended_rationals.h:240`, `:248`). `[C]` cvc5 has `delta_rational.h` in
`src/theory/arith/` `[C]`. Ours is `simplex.rs:201`. This half is settled.

The half worth copying is **how the concrete ε is chosen**. Yices computes one
global positive ε that works for every constraint simultaneously
(`references/yices2/src/solvers/simplex/simplex.c:12610-12645`) `[C]`:

1. Start `ε = 1` (`simplex.c:12625-12627`).
2. If an egraph is present, first shrink ε so that model values that must be
   **distinct** stay distinct: for `(a₁+b₁δ) ≠ (a₂+b₂δ)`, force
   `ε < (a₂−a₁)/(b₁−b₂)` (`epsilon_for_diseq`, `simplex.c:12081-12104`;
   driver `epsilon_for_egraph`, `:12113-12127`). `[C]`
3. For every unmarked variable, shrink ε so the concrete value stays inside its
   concrete bounds: given `a + bδ ≤ c + dδ` in the extended order, if `b > d`
   then require `ε ≤ (c−a)/(b−d)`; if `b ≤ d` any positive ε works
   (`epsilon_for_le`, `simplex.c:12147-12166`; driver
   `simplex_adjust_epsilon`, `:12172-12186`). `[C]`
4. Then instantiate `v = a + b·ε` for every variable (`simplex.c:12258-12278`).
   `[C]`

**Z3 does the same thing with a tighter formula and a second loop.** The
representation is `numeric_pair<T>` = `(x, y)` meaning `x + y·δ`, lexicographic
order, in `references/z3/src/math/lp/numeric_pair.h:115-251` (note: in `lp/`,
not `util/`), with `floor`/`ceil` that respect the infinitesimal (`:301-321`).
`[C]` Strictness is written into `y` at bound-assertion time: `LT` adds `-1`,
`GT` adds `+1` to `y_of_bound`
(`references/z3/src/math/lp/lar_solver.cpp:2388-2446`). `[C]`

The δ shrink is one function
(`references/z3/src/math/lp/lar_core_solver.h:189-198`) `[C]`:

```cpp
void update_delta(mpq& delta, numeric_pair<mpq> const& l, numeric_pair<mpq> const& u) const {
    if (l.x < u.x && l.y > u.y) {
        mpq delta1 = (u.x - l.x) / (l.y - u.y);
        if (delta1 < delta) delta = delta1;
    }
}
```

applied per column against both its bounds in `find_delta_for_strict_bounds`
(`lar_core_solver.h:212-221`). `[C]` Initial δ is `m_settings.m_epsilon`,
default `mpq(1)` (`lp_settings.h:256`), settable via `arith.epsilon`
(`references/z3/src/params/smt_params_helper.pyg:110`, DOUBLE, default `1.0`;
converted as `rational(max(1, 100000*eps), 100000)` at `lp_settings.cpp:37-38`).
`[C]`

**The second loop is the part we may be missing.** `lar_solver::init_model`
(`lar_solver.cpp:1545-1581`) then **halves δ until distinct `(x,y)` pairs map to
distinct rationals** `[C]`:

```cpp
m_delta = find_delta_for_strict_bounds(m_settings.m_epsilon);
for (j) m_set_of_different_pairs.insert(r_x(j));
do {
    collision = false;
    m_set_of_different_singles.clear();
    for (const impq& rp : m_set_of_different_pairs)
        m_set_of_different_singles.insert(rp.x + m_delta * rp.y);
    if (sizes differ) { m_delta /= mpq(2); collision = true; }
} while (collision);
```

with the invariant stated at `lar_solver.cpp:1530`:
`(x,y) != (x',y') => (x + delta*y) != (x' + delta*y')`. Flattening is then
`v.x + m_delta * v.y` (`lar_solver.cpp:510`). `[C]` Z3 also ships the cheap
variant that skips this loop, `get_model_do_not_care_about_diff_vars`
(`:1583-1593`). `[C]`

`[I]` So **all three** reference solvers spend explicit work making δ preserve
**disequalities** — cvc5 computes it lazily at model-extraction time from the
union of the disequality queue's RHSs, every shared term's value, and every
variable's assignment and bounds
(`TheoryArithPrivate::deltaValueForTotalOrder`,
`references/cvc5/src/theory/arith/linear/theory_arith_private.cpp:4610-4656`;
cached in `ArithVariables` and invalidated on every bound or assignment change,
`partial_model.h:232-236`, `partial_model.cpp:346-352`, `:783`) `[C]` —, by three different means (Yices scans egraph pairs; Z3 halves
until the flattening map is injective on observed values; cvc5 takes the
minimum separation over a sorted set of all relevant values). Z3's is simplest
to port and does not need the egraph; cvc5's lazy caching is the right
*timing* — δ is computed once at model extraction, never incrementally. This is a concrete answer to the open question in
our §B: if `materialize` (`simplex.rs:729`) only respects bounds, adding Z3's
halving loop is ~15 lines and removes a whole class of QF_UFLRA round-trips.

**Why this matters to us specifically.** Step 2 is the part we would need for
QF_UFLRA/QF_UFLIA: without it, the arithmetic model can accidentally equate two
terms the egraph has as distinct, and the combined model is unsound-looking (it
is caught, but it costs a round). Our `materialize` (`simplex.rs:729`) chooses
δ small enough for the *bounds*; whether it also accounts for disequalities is
**did not verify**.

### 3.4 Explanations — minimal by row sign, by construction

Yices's conflict set (`simplex.c:4119-4149` for the "cannot increase" case,
`:4160-4190` for "cannot decrease") is exactly the DdM minimal explanation
`[C]`:

> For the conflicting row with basic variable `x` below its lower bound: for
> every other column `y` in that row, take the **lower** bound index of `y` if
> its coefficient is positive and the **upper** bound index if negative; then
> add the lower-bound index of `x` itself.

Nothing else is in the core. There is no post-hoc minimisation pass, because
the row's sign structure already proves that each of those bounds is necessary
for *this* refutation. `[C]` The symmetric case swaps lower/upper
(`simplex.c:4160-4190`). `[C]`

Note the shape: bounds are identified by an **index into a bound stack**
(`arith_var_lower_index` / `arith_var_upper_index`, then `enqueue_cnstr_index`
against `solver->bstack`), so the explanation is a set of small integers and
the mapping back to literals is one indirection. `[C]`

**Z3 uses the same rule and does not minimise further — deliberately.**
`imp::get_infeasibility_explanation_for_inf_sign`
(`references/z3/src/math/lp/lar_solver.cpp:181-197`) `[C]`:

```cpp
for (auto& [coeff, j] : inf_row) {
    int adj_sign = coeff.is_pos() ? inf_sign : -inf_sign;
    u_dependency* w = adj_sign < 0 ? m_columns[j].upper_bound_witness()
                                   : m_columns[j].lower_bound_witness();
    for (auto d : linearize(w)) exp.add_pair(d, coeff);
}
```

The **Farkas coefficient is the row coefficient** and its sign selects which
bound witness of that column is responsible — literally the DdM rule, with the
multipliers retained (`explanation` keeps `(constraint_index, mpq)` pairs;
`references/z3/src/math/lp/explanation.h:25-122`). `[C]`

And the correction worth recording: **Z3's core is not minimal by
construction**, and Z3 knows it. `theory_lra.cpp:3708` reads
`// lp().shrink_explanation_to_minimum(m_explanation); // todo, enable when perf is fixed`,
and `shrink_explanation_to_minimum` is **not defined anywhere in the tree**.
`[C]` What Z3 does instead is bias the *entering* choice toward short rows so
the certificate is small in the first place
(`lp_primal_core_solver.h:186-187`). `[C]`

`[I]` Combined with cvc5 shipping `conflict-process=none` (§7.3), that is three
independent implementations declining to post-process theory cores. Do not
build a theory-lemma minimiser; make the producer emit short rows.

**Ours matches this when it fires** (`simplex.rs:809-831`, mapping to rows with
nonzero multiplier at `simplex.rs:983-990`) `[C]`. The gap is when it does not
fire: `Tableau::farkas` returns empty if the infeasible basic variable is not a
slack (`simplex.rs:801-805`) or if any nonbasic **problem** variable appears in
the row (`:823-827`), and `LraTheory::rows_to_core` then widens the core to the
**entire asserted set** (`lra_online.rs:984-993`), instrumented as
`final_check_core_widenings` and documented as "a weak-lemma source"
(`euf_egraph.rs:206-210`). `[C]`

`[I]` A full-set core is a lemma that blocks exactly one total assignment. On a
search that reaches final check thousands of times (6,571 on the recorded
instance) that is close to no learning at all. **Before optimising the
simplex, read that counter on the QF_LRA miss population** — if it is
frequently nonzero, fixing the two decline conditions is cheaper than #1 and
may dominate it. I did not run it; this is the single highest-value cheap
measurement the survey produces.

### 3.5 Backtracking — the basis persists; only bounds are trailed

Yices `simplex_backtrack` (`simplex.c:10302-10336`) delegates to
`simplex_go_back` and then backtracks the offset-equality propagator; it does
**not** restore the tableau. `[C]` `simplex_push` (`simplex.c:10347-10377`)
saves five integers — variable count, atom count, saved-row count, and two
propagation pointers — via `arith_trail_save`. `[C]`

`[I]` The invariant that makes this correct is the DdM one: the tableau is a
set of *equations* implied by the problem, independent of which bounds are
asserted, so it never needs undoing. Only the bound stack and the
basic/nonbasic split's *value* consequences do, and a relaxed bound can never
invalidate a satisfied assignment.

**This is exactly our design already** — `retract` (`simplex.rs:956`) with the
comment "Relaxing can never invalidate the current assignment, so this needs no
value repair" `[C]`, plus the shared-prefix reconciliation in
`SimplexEngine::sync` (`lra_online.rs:300-332`) `[C]`. The one thing to check
is the cost of `sync` when the shared prefix is short: it retracts and
re-asserts everything above it, and `assert_bound` is O(m) (`simplex.rs:947`).
`[I]` On a search that backjumps deeply and often, that is O(scope × m) per
check. Yices avoids it by having the SAT core hand the theory an *assertion
queue* with a propagation pointer (`solver->assertion_queue.prop_ptr`,
`simplex.c:9959-9968`) rather than a bound set to diff against. `[C]`

### 3.6 Bound propagation and when it runs

Yices's propagation entry `simplex_propagate` (`simplex.c:9922-10010`) shows
the ordering that matters `[C]`:

1. process the assertion queue,
2. process egraph assertions,
3. fix the nonbasic assignment,
4. `simplex_make_feasible`,
5. **only then**, if `SIMPLEX_PROPAGATION` is enabled, `simplex_do_propagation`,
6. and if propagation set `solver->recheck`, fix the assignment and re-run
   `make_feasible` (`simplex.c:9989-10005`).

Step 6 is the subtle part: implied bounds on **integer** variables can be
strengthened enough to invalidate the current assignment, so propagation and
feasibility are mutually recursive. `[C]`

The configuration is the interesting finding. `SIMPLEX_DEFAULT_OPTIONS` is
`SIMPLEX_DISABLE_ALL_OPTIONS` — **every** option off, including propagation
(`references/yices2/src/solvers/simplex/simplex_types.h:901-913`). `[C]`
Propagation is opt-in per logic (§8.4) and is restricted to rows no longer than
`SIMPLEX_DEFAULT_PROP_ROW_SIZE = 30` (`simplex_types.h:909`,
plumbed at `references/yices2/src/context/context_solver.c:524-527`). `[C]`

Z3's equivalent: `arith.propagation_mode`, UINT, default **1** — "0 - no
propagation, 1 - propagate existing literals, 2 - refine finite bounds"
(`references/z3/src/params/smt_params_helper.pyg:111`) `[C]` — plus
`arith.bprop_on_pivoted_rows`, default `true` (`:126`) and `arith.propagate_eqs`,
default `true` (`:109`). `[C]` And per-logic, Z3 turns propagation **off** for
some shapes: `setup_QF_LIA(st)` sets `m_arith_bound_prop = BP_NONE` when the
problem is all binary clauses and units with a large coefficient sum
(`references/z3/src/params/smt_params.cpp:305-308`). `[C]`

**Z3's row-length cap is 300, not 30**
(`max_row_length_for_bound_propagation`,
`references/z3/src/math/lp/lp_settings.h:245`), with an additional
`row_has_a_big_num(row_index)` guard, both applied in
`lar_solver::calculate_implied_bounds_for_row`
(`references/z3/src/math/lp/lar_solver.h:112-121`). `[C]` Rows become
candidates when a bound on one of their columns changed
(`detect_rows_with_changed_bounds`, `lar_solver.cpp:1266-1278`) and, if
`arith.bprop_on_pivoted_rows` is on, when a pivot touched them
(`lp_core_solver_base_def.h:278-279`). `[C]`

The derivation is the classical one, in
`references/z3/src/math/lp/bound_analyzer_on_row.h:196-220` `[C]`: subtract
every monoid's maximum from the row's RHS, then divide the residue by each
coefficient to get that variable's implied bound. Strictness flows through: a
bound with a nonzero δ component sets `strict`, counted so the target column's
own contribution is discounted (`monoid_max`/`monoid_min`, `:104-146`).

**The pattern to copy is the lazy explanation.** `limit_j`
(`bound_analyzer_on_row.h:298-321`) does not build the explanation; it captures
a **closure** over the row and hands it to `implied_bound` `[C]`:

```cpp
auto explain = [row, bound_j, coeff_before_j_is_pos, is_lower_bound, strict, lar]() {
    int bound_sign = is_lower_bound ? 1 : -1;
    int j_sign = (coeff_before_j_is_pos ? 1 : -1) * bound_sign;
    u_dependency* ret = nullptr;
    for (auto const& r : *row) {
        if (r.var() == bound_j) continue;
        int sign = j_sign * (is_pos(r.coeff()) ? 1 : -1);
        ret = lar->join_deps(ret, sign > 0 ? lar->get_column_upper_bound_witness(r.var())
                                           : lar->get_column_lower_bound_witness(r.var()));
    }
    return ret;
};
m_bp.add_bound(u, bound_j, is_lower_bound, strict, explain);
```

`implied_bound` stores `std::function<u_dependency*()> m_explain_bound`
(`references/z3/src/math/lp/implied_bound.h:24-59`) `[C]`, and
`lp_bound_propagator::add_bound` (`lp_bound_propagator.h:150-190`) keeps only
the **best bound per (column, direction)** in
`m_improved_lower_bounds`/`m_improved_upper_bounds` before anything is
explained. `[C]` At the SMT layer the explanation is computed **once per
implied bound** and reused for every literal it implies
(`theory_lra::propagate_lp_solver_bound`, `theory_lra.cpp:2477-2548`,
the `first` flag). `[C]`

`[I]` Our trait already has the handle-based lazy `explain`
(`euf_egraph.rs:135`); the closure form is the same idea with no handle table.
Either way the discipline is: *derive many bounds, explain few.*

**The lesson for us is not "propagate more".** It is: *row-based propagation is
expensive enough that both reference solvers gate it on a row-length bound and
a per-logic switch.* Finding #3 should ship with a row-length cap and a
config-registry entry from day one, not as an always-on behaviour.

### 3.7 IDL/RDL are not solved by simplex — correcting the brief

All three reference solvers keep a **specialised** difference-logic engine and
choose between it and simplex on static features.

**Yices** has `src/solvers/floyd_warshall/` as a separate solver directory
`[C]` and chooses architecture in `create_auto_idl_solver`
(`references/yices2/src/context/context.c:6180-6217`) `[C]`:

- coefficient bound ≥ 2^30 → simplex, "because of arithmetic overflow";
- ≥ 1000 variables → simplex, "too many variables for FW";
- ≤ 200 variables, or **zero equalities** ("usually means a scheduling
  problem") → Floyd–Warshall;
- otherwise by **atom density** = atoms/variables: ≥ 10.0 → Floyd–Warshall,
  else simplex.

For RDL (`context.c:6222-6255`) the same shape with density threshold **7.0**
and no overflow branch. `[C]`

**Z3** chooses among five arithmetic plugins for QF_IDL alone
(`references/z3/src/smt/smt_setup.cpp:325-380`) `[C]`: `theory_mi_arith` when
proofs are enabled; `theory_dense_si` or `theory_dense_i` when the problem
`is_dense()` and auto-config-simplex is off (the small-int variant chosen by
`arith_k_sum_is_small()`); otherwise `theory_i_arith` (big-integer simplex).
QF_RDL similarly picks between `theory_frdl`, `theory_rdl` and `theory_mi_arith`
(`smt_setup.cpp:267-317`), with an explicit carve-out: the fixed-size-integer
theories cannot be used if the input has rationals, **or if model construction
is enabled**, because computing ε may itself need rationals — the worked example
in the comment is `(x < 1) ∧ (x > 0)` (`smt_setup.cpp:288-294`). `[C]` That is
a soundness trap worth recording independently of anything else here.

Z3 also exposes the whole menu as one option: `arith.solver`, default **6** —
"0 - no solver, 1 - bellman-ford based solver (diff. logic only), 2 - simplex
based solver, 3 - floyd-warshall based solver (diff. logic only) and no theory
combination, 4 - utvpi, 5 - infinitary lra, 6 - lra solver"
(`references/z3/src/params/smt_params_helper.pyg:65`). `[C]` Note the
parenthetical on mode 3: the Floyd–Warshall engine **does not support theory
combination** — the same trade-off Yices makes, stated as a capability.

**Conclusion.** `dl_online.rs` should stay a separate engine. What is worth
importing is the *dispatch*: a static-feature classifier (variable count, atom
density, coefficient magnitude, presence of equalities) choosing between the DL
graph and the simplex, rather than a hand-ordered route list. `[I]` That is
finding #6's arithmetic special case.

---

## 4. Making it fast — the concrete checklist

Ordered by what the reference implementations actually spend their complexity
budget on.

1. **Sparse cross-linked rows and columns** (§3.1). The cross-link
   (`c_ptr`/`r_ptr`) is the non-obvious part; without it, maintaining columns
   under pivoting costs a search per entry and the columns become a liability.
2. **Fill-in-minimising entering choice with random tie-break** (§3.2), plus
   Bland on a repeat-leaving counter with size-scaled threshold.
3. **A priority structure over violated basic variables.** Yices keeps
   `solver->infeasible_vars` as an **int heap** and the main loop pops the
   minimum (`simplex.c:4266`, `int_heap_get_min`), re-adding `x` when it is
   still infeasible after a failed repair (`simplex.c:4288`, `:4306`). `[C]`
   Ours rescans `0..m` from the start on every iteration
   (`simplex.rs:511-524`). `[C]` `[I]` On a 350-row tableau that is 350
   `below_lower`/`above_upper` checks per pivot on top of the pivot itself.
   This is a small, independent win and does not depend on #1.
4. **Short-circuiting scores.** `entering_var_score` takes the incumbent best
   as an argument and bails as soon as it is exceeded
   (`simplex.c:3889`, `:3908`). `[C]` Cheap discipline, worth copying verbatim.
5. **O(rows) value repair, not recompute.** We already do this
   (`simplex.rs:579-597`) and the docstring records that it used to recompute.
   `[C]` No action.
6. **Bounded work per call.** Both the propagation row-length cap
   (`SIMPLEX_DEFAULT_PROP_ROW_SIZE = 30`) and the interrupt check at every
   iteration (`simplex.c:4254-4258`) are shipped defaults, not debug features.
   `[C]`

**Explicitly not on this list:** switching to floating point with rational
recovery. None of the three does it in the DPLL(T) path (Z3 has an
approximate/GLPK replay architecture in the *integer* path — see §5 and the
cvc5 appendix), and it would be incompatible with our self-verified Farkas
discipline. `[I]`

---

## 5. Integer arithmetic

### 5.1 What Yices actually runs, and what it has turned off

`simplex_make_integer_feasible`
(`references/yices2/src/solvers/simplex/simplex.c:9005-9150`) is a strict
ordering `[C]`:

1. `simplex_assignment_integer_valid` — early exit if already integral
   (`simplex.c:9022`).
2. **Bound strengthening** (`simplex_intfeas_strengthening`, `:9046`).
3. **Cheap integrality test** (`simplex_intfeas_integrality_constraints`,
   `:9047`, backed by `integrality_constraints.c`).
4. **Diophantine solver** (`simplex_intfeas_diophantine_check`, `:9048`,
   backed by `diophantine_systems.c` — 3,075 lines).
5. **Bound strengthening again** (`:9049`).
6. **Naive integer search** if the system is underconstrained (`:9052-9058`).
7. Another strengthening round if new bounds were learned (`:9064-9066`).
8. Collect non-integer basic variables; if none, done (`:9078-9086`).
9. `select_branch_variable` (`simplex.c:7399`), then **branch** — or, rarely,
   cut.

Step 9 is the finding. The Gomory path is guarded as
`if (solver->stats.num_branch_atoms >= 20)` and then, for the multi-variable
case, `if (false && v->size > 1 && bb_score > 200000000 && ...)`
(`simplex.c:9110-9112`). `[C]` **The multi-cut path is compiled out.** The
single-variable path survives at `bb_score > 100000000`
(`simplex.c:9123-9133`). `[C]` After branching, Yices charges the SAT core
`+40` synthetic conflicts (`simplex.c:9136`) and `+1000` for a failed cut
attempt (`:9121`) — a restart-pressure hack worth noting.

`[I]` Read that as: after two decades of tuning by the algorithm's own author,
LIA in Yices is **bound strengthening + integrality + Diophantine + branch**,
with cuts as a rarely-taken last resort on a single variable. That is a strong
prior against spending our effort on richer cut families.

### 5.2 What Z3 exposes

`arith.branch_cut_ratio`, UINT, default **2** — "branch/cut ratio for linear
integer arithmetic" (`references/z3/src/params/smt_params_helper.pyg:112`).
`[C]` `arith.int_eq_branch`, BOOL, default `false` — "branching using derived
integer equations" (`:113`). `[C]` `arith.enable_hnf`, BOOL, default `true` —
Hermite Normal Form cuts (`:125`). `[C]` `arith.ignore_int`, default `false`
(`:114`). `[C]`

And per-logic, again feature-driven: `setup_QF_LIA(st)` turns the **GCD test
off** and sets `branch_cut_ratio = 4` when the problem is all unit clauses
(`references/z3/src/params/smt_params.cpp:284-290`). `[C]`

The `math/lp` integer pipeline (`int_solver.cpp`, `gomory.cpp`,
`int_gcd_test.cpp`, `int_branch.cpp`, `int_cube.cpp`, `dioph_eq.cpp`,
`hnf_cutter.cpp`) is covered in appendix §A.

### 5.3 What cvc5 actually runs by default

`TheoryArithPrivate::check` (`references/cvc5/src/theory/arith/linear/theory_arith_private.cpp`,
phases traced by the sub-lane) `[C]`:

real relaxation (dual simplex) → approximate/MIP replay **(off:
`--use-approx` default false, `arith_options.toml:220-225`)** → unate
propagation → **split disequalities** → **Dio conflict** (`--dio-solver`
default **true**, `arith_options.toml:122-127`) → **Dio cutting plane** →
**round-robin branch-and-bound** → restart/decomposition.

Two facts that settle the cut question:

- **cvc5 generates no Gomory or MIR cuts of its own.** Grepping `gomory` and
  `mir` in `src/theory/arith/` hits only the GLPK wrapper — `GmiCutKlass`,
  `struct GmiInfo`, `gmiCut`, `attemptGmi`, `MirCutKlass`, `attemptMir`,
  `applyCMIRRule` in `linear/approx_simplex.cpp` — i.e. cvc5 only **replays**
  cuts GLPK found, and the whole GLPK path is behind `#ifdef CVC5_USE_GLPK`
  and `--use-approx` (default false). `[C]`
- **The branch lemma is the interesting default.** `--arith-brab`, bool,
  category *regular*, **default true**
  (`references/cvc5/src/options/arith_options.toml:508-513`, "whether to use
  simple rounding, similar to a unit-cube test, for integers"). With it on,
  `BranchAndBound::branchIntegerVariable`
  (`references/cvc5/src/theory/arith/branch_and_bound.cpp:49-122`) emits the
  **ternary** lemma `[C]`:

  ```
  (or (= var nearest) (or (<= var nearest-1) (>= var nearest+1)))
  ```

  where `nearest ∈ {floor(v), ceil(v)}`, followed by
  `d_im.preferPhase(literal, true)` (`branch_and_bound.cpp:77`) so the SAT
  solver tries the **equality** branch first. With it off it degenerates to the
  textbook binary split `(or (<= var floor) (not (<= var floor)))`
  (`:124-142`). `[C]` One gotcha if porting: the equality is pushed through
  `d_ppre.ppRewriteEq(eq)` before being made a literal (`:71-73`), and both
  paths assert the rewritten upper bound is a `GEQ` literal (`:62-64`,
  `:128-130`) — the split only works in the rewriter's canonical form. `[C]`

`[I]` A three-way split that offers `= n` first is strictly more informative
than a two-way `≤ n` split when the LP optimum is near an integer, which is the
common case after the relaxation. It costs one extra literal and it is on by
default in a competition solver. That is why it is finding #8 and rated **S**.

### 5.4 The cross-solver verdict on LIA

| technique | Yices | Z3 | cvc5 |
|---|---|---|---|
| bound strengthening / integrality test | on, twice per call | via `patch_basic_columns` | via propagation |
| **Diophantine pre-solve** | **on** (`diophantine_systems.c`) | **on** (`lp.dio` default true) | **on** (`--dio-solver` default true) |
| GCD test | on | on, but **disabled while dio is productive** | (in dio) |
| cube test | — | `int_cube` on a period | subsumed by BRAB rounding |
| HNF cuts | — | on (`arith.enable_hnf` default true) | — |
| **Gomory cuts** | **multi-cut path compiled out**; single-var path only above a score threshold | **off while dio is productive**, re-enabled after 16 unproductive dio calls | **not implemented**; GLPK replay only, off by default |
| **branch and bound** | **on**, the terminal step | **on**, the terminal step | **on**, the terminal step, with BRAB rounding |

`[I]` Three independent teams, one shape: *strengthen, then solve the integer
equations, then branch.* Cuts are the part each of them either disabled,
gated behind a productivity counter, or never wrote. Our fractional Gomory
implementation (`lra.rs:1731-2160`) is therefore not the LIA gap; our lack of a
Diophantine pre-solve and of BRAB-style branching is.

### 5.5 Where we stand

We have: branch-and-bound (`lra.rs:1653`, node cap at `lra.rs:1229`),
fractional Gomory cuts (`lra.rs:1731-2160`, caps `MAX_GOMORY_ROUNDS = 16`,
`MAX_GOMORY_ROWS = 256`, `MAX_GOMORY_COLS = 1024`), a GCD test generalised to
fraction-free row reduction (`lia_gcd.rs:39`, `:307-390`), strict-integer
tightening (`dl_online.rs:34-37`), and an LP-relaxation prefilter before the
offline B&B (`lia_online.rs:191-204`). `[C]`

We do **not** have (grepped: `cooper`, `omega`, `cube`): Cooper elimination,
the Omega test, or the Bromberger–Weidenbach cube test — `cube` appears only as
a benchmark name (`dpll_lia.rs:2621`) and a test mock
(`native_cdclt/tests.rs:118`). `[C]` No mixed-integer/MIR cuts. No Diophantine
pre-solve.

Against §5.1: the ordering `strengthen → integrality → Diophantine →
strengthen → branch` is what Yices found worth shipping, and we have the first
and last but not the middle. `[I]` Of the missing pieces, **bound
strengthening iterated to fixpoint** is the cheapest and shares infrastructure
with finding #3; Diophantine is a 3,000-line component and division-specific.
That is why #8 and #10 rank where they do.

---

## 6. Congruence closure for UF

### 6.1 Z3's enode and the merge

`references/z3/src/ast/euf/euf_enode.h:38-68` `[C]`:

```cpp
unsigned      m_class_size = 1;   // size of the class if this is the root
enode_vector  m_parents;          // use list
enode*        m_next   = nullptr; // cyclic class list
enode*        m_root   = nullptr;
enode*        m_target = nullptr; // proof-forest edge
enode*        m_cg     = nullptr; // congruence representative
th_var_list   m_th_vars;          // theory variables attached to this node
justification m_justification;    // proof-forest edge justification
justification m_lit_justification;
```

Note `m_th_vars` on the enode itself — that is how arithmetic and BV attach to
E-nodes without a side table, and it is what makes theory-equality propagation
a by-product of merge. `[C]`

`egraph::merge` (`euf_egraph.cpp:508-557`) `[C]`:

- immediate conflict if both roots are `interpreted()` (distinct constants) or
  have opposite Boolean values (`:522-531`) — **not** a scan;
- union by class size, with `interpreted()` and value-assigned roots forced to
  win (`:532-536`);
- `remove_parents(r1)` → `push_eq` → `merge_justification` → relink `m_root`
  for the class → swap `m_next` → grow class size → `merge_th_eq` →
  `reinsert_parents(r1, r2)` (`:538-548`).

Congruence is rediscovered in `reinsert_parents` (`euf_egraph.cpp:581-608`):
each parent of the *smaller* class is re-inserted into the signature table
`m_table`, and a collision pushes a new merge onto `m_to_merge`. `[C]`
`remove_parents` (`:559-579`) erases those parents from the table first, marked
with `mark1` so the two passes agree. `[C]`

`merge_th_eq` (`euf_egraph.cpp:607-623`) walks the smaller class's theory
variables: if the root has none for that theory, adopt it and call
`add_th_diseqs`; otherwise emit `add_th_eq` — a theory equality, generated
exactly once, at merge. `[C]`

**Contrast.** We scan all atoms (`euf_egraph.rs:516-535`), all disequalities
and all constant pairs (`:551-575`) on each call. `[C]` `[I]` Finding #4 is
mechanical: attach disequalities to the class (Z3's `add_th_diseqs`), detect
constant-vs-constant at merge (Z3's `r1->interpreted() && r2->interpreted()`
test), and drive propagation from the parents touched by the merge instead of
from the atom list.

### 6.2 The proof forest and LCA explanations

`merge_justification` (`euf_egraph.cpp:692-706`) is the Nieuwenhuis–Oliveras
step verbatim `[C]`:

```cpp
n1->reverse_justification();   // flip the path n1 -> ... -> root(n1)
n1->m_target = n2;
n1->m_justification = j;
```

Reversing the path from `n1` to its root before attaching the new edge is what
keeps the forest a forest with roots at class representatives. `unmerge_justification`
(`:708-723`) undoes it symmetrically: clear `m_target`, then
`n1->get_root()->reverse_justification()`. `[C]`

The explanation is **LCA-bounded, not root-bounded**
(`euf_egraph.cpp:757-800`) `[C]`:

```cpp
enode* egraph::find_lca(enode* a, enode* b) {
    a->mark2_targets<true>();          // mark a's path to the root
    while (!b->is_marked2()) b = b->m_target;   // walk b up to the first mark
    a->mark2_targets<false>();         // unmark
    return b;
}
```

`push_congruence` (`:762-780`) then calls `push_lca` on each argument pair,
with a commutativity special case that tries the crossed pairing first
(`:769-775`). `[C]` The docstring states the reason: "Each pair of children
under a congruence have the same roots and therefore have a least common
ancestor. We only need explanations up to the least common ancestors."

`[I]` This is what makes explanations *small* rather than merely correct.
Our engine documents "`explain`-to-LCA" (`crates/axeyum-egraph/src/lib.rs:12-13`)
so we appear to have it; I did **not** verify the implementation against Z3's,
only the doc comment.

### 6.3 Dynamic Ackermannization

`references/z3/src/ast/euf/euf_ackerman.{h,cpp}` exists in the tree `[C]`;
Z3 also exposes it as a search parameter (Yices's equivalent knobs are
`params.use_dyn_ack` / `params.use_bool_dyn_ack`, set for the egraph+simplex
architectures at `references/yices2/src/frontend/yices_smtcomp.c:1272-1273`).
`[C]` The trigger heuristic and its constants: **did not verify** (this was
assigned to a sub-lane that could not be scheduled; see §B).

We have Ackermann reduction on the offline path (`euf.rs`, and
`crates/axeyum-rewrite`'s `eliminate_arrays` uses it for QF_ABV) but I did not
find a *dynamic* one keyed on search behaviour. Not grepped exhaustively —
treat as **did not verify**.

---

### 6.4 A real divergence: cvc5 does NOT use a reversing proof forest

Worth recording because it is the one place the three reference solvers
disagree on design, and because **we chose Z3's side**.

cvc5's `EqualityEngine` keeps an **undirected** equality graph, not a forest
(`references/cvc5/src/theory/uf/equality_engine.h:439-456`) `[C]`:

```cpp
class EqualityEdge { EqualityNodeId d_nodeId; EqualityEdgeId d_nextId;
                     unsigned d_mergeType; TNode d_reason; };
std::vector<EqualityEdge>   d_equalityEdges;   // :445
std::vector<EqualityEdgeId> d_equalityGraph;   // :456  node -> head of its edge list
```

Every asserted equality pushes **two** edges, so edge `e` and `e ^ 1` are the
two directions of one undirected edge
(`addGraphEdge`, `equality_engine.cpp:1165-1185`). `[C]` Explanation is then a
**BFS** from `t1` to `t2` over that graph (`getExplanation`,
`equality_engine.cpp:1552`, search loop `:1649-1706`), with the single line

```cpp
if ((currentEdge | 1u) != (current.d_edgeId | 1u))   // equality_engine.cpp:1682
```

standing in for the whole "don't walk back the edge you came in on"
mechanism. `[C]` A `MERGED_THROUGH_CONGRUENCE` edge recurses on the two curried
arguments (`:1742-1780`). `[C]` Backtracking is a `resize`:
`d_assertedEqualities.resize(d_assertedEqualitiesCount)` and the edge vector to
`2 * d_assertedEqualitiesCount` (`equality_engine.cpp:1040`, `:1045`). `[C]`
There is also **no path compression** in the union-find — `merge` rewrites the
representative of every member of the smaller class
(`equality_engine.cpp:759-796`), which is O(|class|) but makes `undoMerge` the
exact inverse (`merge<false>`, `equality_engine_types.h:212-226`). `[C]`

`[I]` The trade is explicit: cvc5 buys O(1) backtracking (vector truncation)
and pays a BFS per explanation; Z3 buys near-linear LCA explanations and pays
a path reversal on every merge plus an undo trail. Our `axeyum-egraph` is on
Z3's side (`proof_parent`/`proof_edge` + explain-to-LCA,
`crates/axeyum-egraph/src/lib.rs:12-13`, `:246-248`), with an undo journal
(`:261`). **That is the right side for a backtracking SMT search** provided the
undo is genuinely O(path), and it is not a gap. Recording it so nobody
"discovers" cvc5's design and proposes a rewrite.

The one thing to take from cvc5 here is the **memoization key hazard**: its
explanation cache normalises the pair with `std::minmax(t1Id, t2Id)` when
proofs are off, but **preserves order when proofs are on**, "because proofs are
sensitive to the order of t1 and t2" (`equality_engine.cpp:1563-1602`, citing
their issue #2965). `[C]` If we ever memoise explanations while emitting
Alethe, that is a live bug class.

### 6.5 Disequalities and `distinct` — cvc5's lazy handling

cvc5 explains disequalities through a **separate** structure, not the equality
graph: `d_disequalityReasonsMap` maps a pair to a
`DisequalityReasonRef {d_mergesStart, d_mergesEnd}` range into
`d_deducedDisequalityReasons`, and `explainEquality(..., polarity=false)`
replays each recorded merge (`equality_engine.cpp:1319-1360`). `[C]`

`distinct` is **not** expanded to `O(n²)` disequalities. `DistinctExtension`
(`references/cvc5/src/theory/uf/distinct_extension.h:42`) keeps, per
equivalence-class representative, a count, the set of `distinct` constraints
the class occurs in, and the member terms (`:63-80`), and detects a conflict at
**merge** time when the same `distinct` appears on both sides. `[C]` It is
wired as a merge hook (`theory_uf.cpp:701`) and a check hook (`:164`), and
`DISTINCT` is marked `setIrrelevantKind` so it never reaches the model
(`:94`). `[C]`

`[I]` We have `distinct.rs` (1.2 KB) and `set_cardinality.rs`; whether our
`distinct` is expanded quadratically is **did not verify**. If it is, this is a
cheap QF_UF/UF win with the same merge-hook shape as finding #4.

## 7. Theory combination

### 7.1 Z3: MBTC, and the trick that makes it work

The mechanism is `theory::assume_eqs`
(`references/z3/src/smt/smt_theory.h:526-548`) `[C]`:

> Hash every **relevant and shared** theory variable by its current **model
> value**. Two variables landing in the same bucket, whose enodes are not
> already congruent, become a proposed interface equality, asserted to the SAT
> solver as a **case split** (`ctx.assume_eq`).

The arithmetic override (`theory_arith_aux.h:2197-2226`) collects candidates
into `m_assume_eq_candidates` and then hands them out **one at a time** via
`delayed_assume_eqs` (`:2228-2248`), re-checking `get_value(v1) == get_value(v2)`
at the moment of use, because earlier splits may have moved the model. `[C]`

The trick is line `theory_arith_aux.h:2199-2200`:

```cpp
if (m_liberal_final_check)
    mutate_assignment();
```

`mutate_assignment` (`theory_arith_aux.h:2114-2160`) finds exactly the shared
variables whose model values *coincide*, and **randomly re-assigns** the
non-fixed ones inside their safe interval (`random_update`, using a bounded
random offset — `theory_arith_aux.h:2100-2110`). `[C]` For a basic variable it
instead randomises one of the non-fixed variables in its row (`:2145-2153`).
`[C]` Only coincidences that *survive* randomisation become proposed
equalities.

`[I]` This is the difference between MBTC as described in the paper `[P]` and
MBTC that is fast. Without it, every pair of variables that happen to be 0 in
the current vertex solution — which is most of them, since simplex solutions
sit on vertices — generates an interface equality. With it, only genuinely
entailed equalities do.

The two-pass final check is the companion
(`theory_arith_core.h:1542-1560`) `[C]`: `m_liberal_final_check = true` for the
first `final_check_core()`; if the assignment changed, set it `false` and run
again — so the randomising pass is a *search* pass and the strict pass is the
one that must be sound.

`[P]` de Moura & Bjørner, "Model-based Theory Combination", SMT 2007 /
ENTCS 2008 — the paper motivates this against Nelson–Oppen's requirement that
solvers produce *all* implied equalities.

### 7.2 Yices: the same idea as an explicit reconcile phase

Yices calls it model reconciliation
(`references/yices2/src/solvers/egraph/egraph.c:6053-6071`) `[C]`:

1. Ask the arithmetic solver for a **model partition** — shared terms grouped
   by equal model value (`build_model_partition`, `egraph.c:6061`).
2. For each class, optimistically **merge** pairs in the egraph
   (`egraph_reconcile_class`, `:6004-6022`; `egraph_reconcile_pair`,
   `:5971-5993`), inside a save/restore bracket
   (`egraph_start_reconciliation` `:6081-6087`, `egraph_reconciliation_restore`
   `:6091-6097`).
3. If every class reconciles, the combined model is consistent. If not, the
   failed pairs become **interface lemmas**, bounded by
   `egraph->max_interface_eqs` (`egraph.c:6175-6193`). `[C]`

The bound is per-logic: **15** for QF_UFLIA / QF_UFLIRA / QF_AUFLIA / QF_ALIA
and **30** otherwise (`references/yices2/src/frontend/yices_smtcomp.c:1180-1186`),
and **15** again for the egraph+bitvector architectures (`:1205`). `[C]`
Yices also flips branching heuristic per logic in the same block:
`BRANCHING_NEGATIVE` for the UFLIA family, `BRANCHING_THEORY` otherwise. `[C]`

`[I]` Yices reconciles by *trying the merge* rather than by randomising the
model. Both approaches answer the same question — "is this coincidence
forced?" — and both avoid enumerating arrangements. Ours currently does
neither: `propose_interface_equalities` groups by model value
(`theory_combination.rs:126-128`) and hands every group to a case-split DFS
(`combined_theory.rs`), which is the expensive path both reference solvers
built machinery to avoid.

### 7.3 cvc5: care graph as the default, central equality engine as an option

`references/cvc5/src/options/theory_options.toml:76-86`: `tc-mode`, default
`CARE_GRAPH`, and `CARE_GRAPH` is the **only** mode defined. `[C]`
`ee-mode` (`:63-74`): default `DISTRIBUTED` — "each theory maintains its own
equality engine" — with `CENTRAL` as the alternative, "all applicable theories
use the central equality engine". `[C]`

`conflictProcessMode` (`theory_options.toml:88-104`): default **NONE** — "do
not post-process conflicts from theory solvers" — with `MINIMIZE` and
`MINIMIZE_EXT` available. `[C]` `[I]` That is a direct answer to the brief's
"conflict-clause minimization on theory lemmas": cvc5 has it and ships it
**off**, which is evidence that minimising theory lemmas post-hoc does not pay
when the producer already emits minimal cores (§3.4).

**The care graph is the mechanism, and it is a structural filter.**
`struct CarePair { const TNode d_a, d_b; const TheoryId d_theory; }`
(`references/cvc5/src/theory/care_graph.h:29-53`) canonically orders the pair
in its constructor (`d_a(a < b ? a : b)`, `:33-35`) and the graph is
`std::set<CarePair>` (`:58`), so `(a,b)` and `(b,a)` dedupe for free. `[C]`

`CombinationCareGraph::combineTheories`
(`references/cvc5/src/theory/combination_care_graph.cpp:33-88`) then emits
**one splitting lemma per care pair** `[C]`:

```cpp
for (Theory* t : d_paraTheories) t->getCareGraph(&careGraph);
for (const CarePair& cp : careGraph) {
    Node equality = cp.d_a.eqNode(cp.d_b);
    ... sendLemma(split(equality), cp.d_theory, InferenceId::COMBINATION_SPLIT);
    propEngine->preferPhase(d_valuation.ensureLiteral(equality), true);
}
```

The value is in *which pairs get in*. `Theory::addCarePairArgs`
(`references/cvc5/src/theory/theory.cpp:430-452`) applies three filters
`[C]`:

1. **same operator, same arity** — a pair `x_k ≟ y_k` is proposed only if
   `f(…x_k…)` and `f(…y_k…)` both exist, i.e. only if the equality could
   actually fire a congruence (asserted at `:433-435`);
2. **both are trigger (shared) terms** — `isTriggerTerm(x, d_id)` (`:443-449`),
   and the pair is recorded as
   `getTriggerTermRepresentative(x)`/`(y)`, collapsing whole classes to one
   candidate;
3. **not already decided** — `processCarePairArgs` skips if
   `areEqual(a, b)` (`theory.cpp:454-463`), and `areCareDisequal`
   (`:465-494`) additionally consults
   `d_valuation.getEqualityStatus(x, y)` to skip pairs the owning theory
   already knows are disequal in its model (`:488-493`).

UF goes further and never does an all-pairs loop at all:
`TheoryUF::computeCareGraph` (`theory_uf.cpp:582-684`) indexes applications in
a **per-operator trie keyed by argument representatives** (`TNodeTrie index`,
`:592`), then `nodeTriePathPairProcess` (`:661-679`) descends only into
subtrees that *diverge* — two applications agreeing on the representative at
position `k` are never proposed there, and identical signatures are already
congruent. It exits immediately when there are no shared terms at all
(`:587-590`). `[C]`

`[I]` This is the piece we most clearly lack. Our
`propose_interface_equalities` groups by model value and
`combined_theory.rs` hands the groups to a depth-capped case-split DFS that
declines when there are too many pairs (`:49`, `:152`). The care graph is the
cheaper half of the same job: **before** you consider a model coincidence, ask
whether an equality there could fire any congruence at all. Filters 1 and 3
are a few dozen lines against our existing e-graph; the trie in filter 2 is the
larger piece.

**Arithmetic does not participate in the care graph.** `grep parametric
src/theory/*/kinds.toml` lists uf, arrays, strings, ff, datatypes, sets, sep,
bags — **not arith**. `[C]` cvc5 shares arithmetic equalities through three
other channels (`equality_solver.cpp`, `linear/congruence_manager.h`) `[C]`:

- a **watched-variable** scheme: `addWatchedPair(ArithVar s, TNode x, TNode y)`
  registers the slack `s = x − y`, and then bound events on `s` become
  equality-engine facts — `watchedVariableIsZero(lb, ub)` asserts `x = y`,
  `watchedVariableCannotBeZero(c, d)` asserts `x ≠ y`
  (`congruence_manager.h:73-94`);
- `TheoryArith::getEqualityStatus` (`theory_arith.cpp:447-479`), evaluating
  `(- a b)` under the cached model;
- disequality splitting (`splitDisequalities`, `ARITH_SPLIT_DEQ`).

`[I]` The watched-variable trick is the cheap one: for each shared pair,
introduce **one slack column** and let ordinary bound propagation decide the
equality. It reuses the simplex you already have instead of a model-value hash,
and it produces *entailed* equalities rather than *guessed* ones. It is a
genuine third option alongside Z3's randomise-and-hash and Yices's
try-the-merge.

### 7.4 Nelson–Oppen fallback

`[I]` Both Z3 and Yices treat the model-based step as a *heuristic for choosing
which equalities to split on*, not as a replacement for the completeness
argument: the case split is asserted to the SAT solver, so if the guess is
wrong the search explores the other branch and the procedure remains complete
for stably-infinite theories. The fallback is therefore "the SAT solver", not a
separate Nelson–Oppen module. I did not locate an explicit N-O arrangement
enumerator in either tree — **did not verify**.

---

## 8. The SAT/theory interface

### 8.1 Theory propagation: opt-in, and gated on row size

See §3.6. The headline is that Yices ships **all simplex options off by
default** (`simplex_types.h:913`) `[C]` and Z3 ships `arith.propagation_mode`
at 1 of 3 (`smt_params_helper.pyg:111`) `[C]`. Neither is maximalist.

### 8.1b Assertion is enqueued; simplex runs once per batch

This is the discipline all three share and it is worth stating plainly.

**Z3.** `theory_lra::assign_eh` does nothing but enqueue:
`m_asserted_atoms.push_back(delayed_atom(v, is_true))`
(`references/z3/src/smt/theory_lra.cpp:1030-1033`). `[C]` `propagate_core`
(`:2264-2329`) drains the queue calling `assert_bound` per atom — which only
*activates* the LP constraint and does the O(1) crossed-bounds test
(`:3322-3347`) — and then calls `make_feasible()` **once** for the whole batch
(`:2296`). `[C]` `final_check_eh` (`:1745-1823`) begins with
`if (propagate_core()) return FC_CONTINUE;`. `[C]`

**Yices.** `simplex_propagate` (`simplex.c:9922-10010`) processes the assertion
queue and the egraph queue, fixes the nonbasic assignment, and then calls
`simplex_make_feasible` once (`:9975-9977`). `[C]`

**Z3 also has an adaptive off-switch that we have no analogue of.**
`theory_lra::process_atoms` (`references/z3/src/smt/theory_lra.cpp:2236-2249`)
`[C]`:

```cpp
if (!adaptive()) return true;
if (ctx().get_num_conflicts() < 10) return true;
double f = (double)m_num_conflicts / (double)total_conflicts;
return f >= adaptive_assertion_threshold();
```

If arithmetic's share of recent conflicts falls below a threshold, **atom
processing is skipped entirely** and everything defers to final check. Bound
propagation has a second throttle: `propagation_mode()` returns `BP_NONE` once
`m_num_conflicts >= m_arith_propagation_threshold`
(`theory_lra.cpp:3410`), and Z3 sets that threshold to **1000** for QF_UFLIA
(`references/z3/src/params/smt_params.cpp:314-319`). `[C]`

`[I]` "Stop doing theory work when the theory is not producing conflicts" is a
policy, not an algorithm, and it lives in the driver. Our
`LraTheory::defer_to_final_check` is the static version of the same idea and is
off by default for a documented reason (§2.3). The adaptive version is
strictly more useful and does not have that constraint, because it never
changes *what* is checked — only *when*.

### 8.2 Explanation laziness

Ours already supports it: `TheorySolver::explain(ExplanationId)`
(`euf_egraph.rs:135`), resolved by `CdclT::reason_for` (`cdclt.rs:1293`) only
if conflict analysis reaches the literal, with an unresolvable handle mapping
to `Unknown` and never to `unsat` (`cdclt.rs:2343`). `[C]` `DlTheory`
(`dl_online.rs:1770`) implements it. Whether `LraTheory` does: **did not
verify** (it is not in the grep hits at `lra_online.rs`).

Yices's shape is the alternative: explanations are **bound-stack indices**
collected into `solver->expl_queue` with marks (§3.4), expanded to literals
only when the core builds the clause. `[C]` Same effect, simpler
representation, no handle table.

### 8.3 How many theory lemmas to keep

Z3 does not distinguish theory lemmas from learned clauses for GC purposes.
`references/z3/src/params/smt_params.h:165-169` `[C]`:

```cpp
lemma_gc_strategy m_lemma_gc_strategy = lemma_gc_strategy::LGC_FIXED;
bool              m_lemma_gc_half     = false;
unsigned          m_lemma_gc_initial  = 5000;
double            m_lemma_gc_factor   = 1.1;
```

Fixed strategy, first collection at 5,000 clauses, geometric growth 1.1. `[C]`

Yices instead caches *theory clauses* selectively: `params.cache_tclauses` with
`params.tclause_size` bounding which theory explanations are kept as permanent
clauses — 8 for the simplex and egraph+simplex architectures, **20** for
QF_LIA with periodic integer checking, and 20 for the Floyd–Warshall RDL and
auto-RDL-simplex paths (`references/yices2/src/frontend/yices_smtcomp.c:1136-1143`,
`:1216-1219`, `:1264-1278`). `[C]` Z3's analogue is `m_arith_small_lemma_size`,
set to **30** for QF_IDL (`references/z3/src/params/smt_params.cpp:225`) and
**32** for QF_LRA (`:260`). `[C]`

cvc5 draws the same line at the *propagation* level: `arithPropAsLemmaLength`,
`--arith-prop-clauses=N`, default **8** — "rows shorter than this are
propagated as clauses"
(`references/cvc5/src/options/arith_options.toml:254-260`, used at
`theory_arith_private.cpp:5363`) `[C]` — and it also caps which rows are
eligible for propagation at all: `arithPropagateMaxLength`,
`--prop-row-length=N`, default **16** (`arith_options.toml:114-120`). `[C]`

`[I]` The consistent rule across all three: *keep a theory lemma permanently
only if it is short*, with the threshold in the **8–32** range and tuned per
logic; and *only propagate from short rows*, with the eligibility cap between
**16 (cvc5) and 300 (Z3)** — a 19× spread, which says the cap is genuinely a
tuning knob and not a principle. That is a cheap, self-contained policy we
could add to `cdclt.rs`/`native_cdclt.rs` without touching any theory.

### 8.4 Per-logic parameter tables — the highest ratio of value to effort

Both reference solvers ship one, driven by **static features of the parsed
input**. Z3's (`references/z3/src/params/smt_params.cpp`) `[C]`:

| logic | settings |
|---|---|
| `QF_UF` (`:199-205`) | `relevancy_lvl=0`, `nnf_cnf=false`, `RS_LUBY`, `PS_CACHING_CONSERVATIVE2`, `IA_RANDOM` initial activity |
| `QF_IDL` (`:219-226`) | `relevancy_lvl=0`, `arith_eq2ineq=true`, `arith_propagate_eqs=false`, `arith_small_lemma_size=30` |
| `QF_RDL` (`:207-214`) | same minus the lemma-size line |
| `QF_LRA` (`:242-261`) | as above plus `PS_THEORY` phase selection, `arith_small_lemma_size=32`; **feature-driven**: `relevancy_lvl=2` when the coefficient sum's numerator > 2,000,000 and denominator > 500; geometric non-adaptive restarts and `arith_stronger_lemmas=false` when the input is not CNF |
| `QF_LIA` (`:270-312`) | **three-way feature branch**: deep ITE trees (> 50) → `arith_eq2ineq=false`, `pull_cheap_ite`, `propagate_eqs=true`, `relevancy_lvl=2`; all-units → **GCD test off**, `branch_cut_ratio=4`, `relevancy_lvl=2`; otherwise geometric restarts with factor 1.5. Plus `arith_bound_prop=BP_NONE` for binary+unit CNF with coefficient sum > 100,000 |
| `QF_UFLIA` (`:314-319`) | `relevancy_lvl=0`, `arith_propagation_threshold=1000` |
| `QF_UFLRA` (`:322-326`) | `relevancy_lvl=0`, `arith_reflect=false` |

Yices's equivalent is the `switch (arch)` block in
`references/yices2/src/frontend/yices_smtcomp.c:1130-1290` `[C]`, structured by
*architecture* rather than logic, and re-tuned again after internalization for
the AUTO_IDL/AUTO_RDL cases once the solver choice is known (`:1249-1280`).

Three observations worth carrying into a design:

1. **`relevancy_lvl = 0` almost everywhere.** Z3 turns relevancy propagation
   *off* for every quantifier-free arithmetic logic and re-enables it (=2) only
   on specific input shapes. `[C]`
2. **The features are cheap.** Variable count, clause/unit counts, CNF-ness,
   atom density, coefficient magnitude sum, max ITE depth. All are one linear
   pass over the parsed input. `[C]`
3. **The table is data, not control flow.** It is ~120 lines of assignments in
   one file, versioned, and it is where a decade of competition tuning
   accumulates. `[I]` We have `config_registry.rs` (116 KB) and
   `auto.rs` (436 KB, 52 route labels) but, per the 2026-09-05 review
   (§3.2 D3), dispatch is "a hand-ordered portfolio of one-shot routes" where
   "a declined route's encoding is discarded". A feature-driven parameter table
   is a different artifact from a route list and would compose with it.

### 8.5 Splitting on demand

`[P]` Barrett, Nieuwenhuis, Oliveras, Tinelli, "Splitting on Demand in SAT
Modulo Theories", LPAR 2006, LNAI 4246, 512–526: a theory delegates its
internal case splits to the DPLL engine by encoding them as clauses, possibly
introducing new constants and literals, which "results in drastically simpler
theory solvers".

Both `assume_eq` (§7.1) and branch-and-bound's branch literal are instances.
Yices's `create_branch_atom` (`simplex.c:7170-7216`) creates a fresh Boolean
variable for `x ≤ ⌊v⌋` and hands it to the core rather than branching
internally `[C]`; our `create_branch_atom` analogue is recursive B&B inside
`lra.rs:1653` — i.e. **we branch internally**, on the offline path. `[C]`
`LiaTheory`'s online equality branching (`lia_online.rs:1142`, `:1310`) is
closer to the on-demand shape. `[I]` Converting the offline B&B to emit branch
literals is finding #8's real content, and it is worth more than the cut
families.

---

## 9. Shared vs division-specific — the summary table

| Component | QF_LRA | QF_LIA | QF_IDL | QF_RDL | QF_UF | QF_UFLIA | QF_UFLRA | UF | QF_BV/ABV |
|---|---|---|---|---|---|---|---|---|---|
| Sparse tableau + column index (§3.1) | ✔ | ✔ | – | – | – | ✔ | ✔ | – | – |
| Non-Bland pivot + Bland fallback (§3.2) | ✔ | ✔ | – | – | – | ✔ | ✔ | – | – |
| δ-rational + global ε (§3.3) | ✔ | – | ✔ | ✔ | – | ✔ | ✔ | – | – |
| Row-sign minimal explanation (§3.4) | ✔ | ✔ | – | – | – | ✔ | ✔ | – | – |
| Row-based bound propagation (§3.6) | ✔ | ✔ | – | – | – | ✔ | ✔ | – | – |
| Constraint DB keyed `(var, δ-value, kind)` (§A3) | ✔ | ✔ | – | – | – | ✔ | ✔ | – | – |
| Violated-set heap whose comparator is the rule (§A3) | ✔ | ✔ | – | – | – | ✔ | ✔ | – | – |
| Congruence closure + LCA explain (§6) | – | – | – | – | ✔ | ✔ | ✔ | ✔ | ✔ |
| Merge-driven diseq/constant conflict (§6.1) | – | – | – | – | ✔ | ✔ | ✔ | ✔ | ✔ |
| MBTC with model randomisation (§7.1) | – | – | – | – | – | ✔ | ✔ | ✔ | ✔ |
| Care-graph structural pair filter (§7.3) | – | – | – | – | – | ✔ | ✔ | ✔ | ✔ |
| Lazy `distinct` via merge hook (§6.5) | – | – | – | – | ✔ | ✔ | ✔ | ✔ | ✔ |
| Short-lemma retention policy (§8.3) | ✔ | ✔ | ✔ | ✔ | ✔ | ✔ | ✔ | ✔ | ✔ |
| Feature-driven parameter table (§8.4) | ✔ | ✔ | ✔ | ✔ | ✔ | ✔ | ✔ | ✔ | ✔ |
| DL negative-cycle engine | – | – | ✔ | ✔ | – | – | – | – | – |
| Diophantine pre-solve (§5.4) | – | ✔ | – | – | – | ✔ | – | – | – |
| Branch-as-literal, ternary/BRAB (§5.3, §8.5) | – | ✔ | – | – | – | ✔ | – | – | – |

Rows 1–5 are one file (`simplex.rs`) plus one caller (`lra_online.rs`). Rows
6–8 are one crate (`axeyum-egraph`) plus one module
(`theory_combination.rs`). Rows 9–10 are the driver and a config table. Only
the last three rows are genuinely division-specific.

---

## 10. What I would do first, and what I would measure first

**Measure before building.** Two numbers decide the ordering of #1 vs a much
cheaper fix, and neither requires new code beyond a counter:

1. `final_check_core_widenings` (`euf_egraph.rs:206-210`) over the QF_LRA miss
   population. If it is frequently nonzero, the search is learning
   full-assignment lemmas and the two `farkas()` decline conditions
   (`simplex.rs:801-805`, `:823-827`) are the cheapest large win in the survey
   — cheaper than #1 and possibly larger.
2. Mean nonzero coefficients per tableau row on
   `QF_LRA/2019-ezsmt/blending/1.smt2`, the instance whose 1.41 ms pivot is
   already recorded (`simplex.rs:589-596`). That ratio is the expected speedup
   from #1 and turns a plausible refactor into a costed one.

**Then, in order:**

1. **#2 — the pivot rule.** ~40 lines in `select_entering`
   (`simplex.rs:550`) plus a repeat-leaving counter in `run` (`:497`). No
   dependency on anything else. Two independent implementations agree on the
   rule *and* on the constant 1000 (§3.2).
2. **The violated-basic heap** (§4.3, §A3). Independent of #1, and cvc5's
   comparator-is-the-rule shape gives configurability for free.
3. **#1 — sparse cross-linked rows and columns** (§3.1), with Z3's persistent
   scatter array for the row combine. This is the big one and the one the
   measurements above should gate.
4. **#8 — the BRAB ternary branch lemma** (§5.3). One lemma shape, on by
   default in cvc5, and it does not touch the simplex.
5. **#4 — EUF merge-driven conflict and propagation** (§6.1), replacing the two
   rescans in `euf_egraph.rs:516-535` and `:551-575`.
6. **#5 / #5b — model randomisation and the care-graph filter** (§7.1, §7.3),
   in that order: randomisation is ~60 lines against an existing function, the
   care graph is a new structure.
7. **#6 — the feature-driven parameter table** (§8.4). Pure data; do it once
   the knobs above exist to be tabled.

**Do not** open IDL/RDL theory work off this survey (§3.7, §1). **Do not** start
from Gomory cuts or sum-of-infeasibilities — §5.4 and §A2 are three
implementations' worth of evidence against both as a first move.

---

## Appendix A — reference internals worth porting, with citations

Detail that did not fit the argument above but that an implementer will want.

### A1. Z3 `math/lp` layering

```
theory_lra.cpp (smt/)             — atoms -> constraints, propagate, final_check
  └─ lar_solver                   — public API, columns, bounds, terms, trail, explanations
       ├─ lar_core_solver         — owns A, x, bounds, basis vectors
       │    └─ lp_primal_core_solver<mpq, impq>   — the pivoting loop
       │         └─ lp_core_solver_base<mpq, impq>
       │              └─ static_matrix<mpq, impq> — the sparse tableau
       └─ int_solver              — gcd, patch, cube, hnf, dio, gomory, branch
```
`[C]` There is a **second, unrelated** simplex at `src/math/simplex/simplex.h`
used only by `theory_diff_logic` (for optimisation), `theory_dense_diff_logic`
and `theory_pb`. Do not confuse the two when reading Z3.

Note the type split: coefficients are `mpq`, values and bounds are
`impq = numeric_pair<mpq>` (`lar_core_solver.h:34`, `:41`). `[C]` A δ-rational
never appears in the matrix, only in the assignment and the bounds — which is
what keeps the pivot arithmetic on plain rationals.

### A2. cvc5's three simplex variants, and which one is actually used

Common base `SimplexDecisionProcedure`
(`references/cvc5/src/theory/arith/linear/simplex.h:73`) with one pure virtual,
`findModel(bool exactResult)` (`:175`). `[C]`

- **Dual simplex** (`linear/dual_simplex.cpp:149`), commented
  `// corresponds to Check() in dM06` (`:147`) — textbook DdM. `[C]` Pivot-rule
  escalation is per-variable, not global:
  `useVarOrderPivot = d_pivotsInRound.count(x_i) >= options().arith.arithPivotThreshold`
  (`:176-177`, `arithPivotThreshold` default **2**), switching that variable's
  preference function from `minBoundAndColLength` to `minVarOrder` (Bland)
  (`:187-189`). `[C]` The outer `dualFindModel` runs the heuristic rule for
  `arithHeuristicPivots` pivots then Bland in `arithSimplexCheckPeriod`-sized
  chunks (default **200**) (`:94-121`). `[C]`
- **FC simplex** ("focusing and converging", `linear/fc_simplex.h:66`) — keeps
  a *focus* subset of the error set, with a degenerate-pivot penalty
  (`static constexpr uint32_t PENALTY = 4`, `fc_simplex.h:81-95`). `[C]`
- **SOI simplex** (`linear/soi_simplex.h:65`) — minimises
  `Σ_{e violated} sgn(e)·e`, built as **an ordinary tableau row** by
  `constructInfeasiblityFunction` (`simplex.cpp:245-288`), so the objective is
  just another basic variable. `[C]` Anti-cycling constants are in the header:
  `s_focusThreshold = 6`,
  `s_maxDegeneratePivotsBeforeBlandsOnLeaving = 100`,
  `s_maxDegeneratePivotsBeforeBlandsOnEntering = 10`
  (`soi_simplex.h:~102-106`). `[C]` Its real payoff is conflicts, not speed:
  `greedyConflictSubsets()` (`soi_simplex.cpp:662`) returns **several** conflict
  subsets and `generateSOIConflict` (`:836`) emits a Farkas conflict per
  subset, with an optional QuickXplain minimiser (`quickExplain`, `:602`,
  behind `--soi-qe`, default false). `[C]`

**Selection** is two booleans, not an enum:
`useFC` (`--use-fcsimplex`, default **false**) and `useSOI` (`--use-soi`,
default **false**) (`references/cvc5/src/options/arith_options.toml:189-201`).
`[C]` `TheoryArithPrivate::selectSimplex(bool pass1)`
(`theory_arith_private.cpp:3441-3483`) `[C]`:

```cpp
if (pass1) { useFC ? &d_fcSimplex : useSOI ? &d_soiSimplex : &d_dualSimplex; }
else       { useFC ? &d_fcSimplex : useSOI ? &d_soiSimplex : &d_soiSimplex; }
```

So the shipped configuration is **dual simplex first, SOI as the last-ditch
pass**. `src/smt/set_defaults.cpp` never flips `useFC`/`useSOI`/`useApprox` per
logic (the only arith default it touches is `arithDioSolver`,
`set_defaults.cpp:854-857`). `[C]`

`[I]` The authors of the SoI paper ship it off by default nine years later.
Treat SoI as *a better conflict generator reachable from the same tableau*,
not as a faster feasibility loop — that reading also explains why it is the
fallback rather than the primary.

### A3. cvc5's matrix, error set, and constraint database

**Matrix** (`references/cvc5/src/theory/arith/linear/matrix.h:56-196`):
doubly-linked row *and* column lists over one entry arena with a free list.
`MatrixEntry<T>` carries `d_rowIndex, d_colVar, d_nextRow, d_nextCol,
d_prevRow, d_prevCol, d_coefficient` (`:56-136`); the arena is
`std::vector<MatrixEntry<T>> d_entries` plus
`std::queue<EntryID> d_freedEntries` (`:139-196`). `[C]` `d_mergeBuffer`
(`:393-395`) is cvc5's version of Z3's scatter array, used by
`rowPlusRowTimesConstant` (`:656`). `[C]` The tableau's basic-variable
coefficient is **−1** by convention (`tableau.h:30-35`). `[C]`
`CoefficientChangeCallback` (`matrix.h:38-45`) is the hook that keeps
bound-counting in sync on every coefficient sign change.

**Error set** — there is **no** `arith_priority_queue` in the current tree; it
is `linear/error_set.h`. Two ideas worth taking `[C]`:

1. `typedef BinaryHeap<ArithVar, ComparatorPivotRule> FocusSet;`
   (`error_set.h:94`) — **the heap comparator *is* the pivot rule**,
   parameterised by `options::ErrorSelectionRule`
   (`--error-selection-rule`, default `MINIMUM_AMOUNT`,
   `arith_options.toml:64-89`). Swapping the rule is swapping a comparator, and
   `ErrorInformation` holds a mutable-heap `FocusSetHandle` (`:130`) so keys
   update in place.
2. **Signal/delay.** Variables are not inserted into the heap on every
   assignment change; they are pushed onto `ArithVarVec d_signals` (`:250`),
   which may contain duplicates, and converted to error entries later
   (`popSignal`, `:373`; drained by `standardProcessSignals`, `simplex.h:210`).
   Header comment at `:246-249`: "A variable may appear on the list multiple
   times. This introduces a delay."

`[I]` Both are directly applicable to our `simplex.rs:511-524` linear rescan
(finding #4 in §4). The comparator-is-the-rule idea also gives the
configurability the brief asks for at essentially no cost.

**Constraint database** (`linear/constraint.h`) — the single most reusable idea
in the cvc5 arithmetic code. The canonical key is
**(ArithVar, DeltaRational, ConstraintType)** `[C]`:

```cpp
typedef std::map<DeltaRational, ValueCollection> SortedConstraintMap;  // constraint.h:244
class ValueCollection { ConstraintP d_lowerBound, d_upperBound, d_equality, d_disequality; };  // :181-224
```

Because the value is a `DeltaRational`, **strictness is part of the key** —
`x < 3` normalises to `x ≤ 3 − δ` and needs no separate flag. `[C]` Asserting
the same bound twice returns the existing constraint
(`getConstraint`, `constraint.cpp:1098-1113`); a second syntactically different
atom normalising to the same constraint is attached to it rather than
duplicated (`addLiteral`, `constraint.cpp:1370-1385`; alternate literals kept
in `d_altLiterals` only for cleanup, `:2304-2331`). `[C]` Negations are
cross-linked at construction (`initialize(this, pos, negC)`, `:1134-1135`), so
`negation()` is a pointer read. `[C]` And because the map is sorted by value,
`getBestImpliedBound(v, t, r)` (`constraint.h:1188`) — "the weakest existing
constraint that implies `r`" — is a map lookup, which is what makes bound
propagation cheap.

Antecedents live in **one flat trail with null-terminated runs**: a proof at
position `p` of length `n` is `(NullConstraint, ans[p-(n-1)], …, ans[p])` in
the shared `CDConstraintList d_antecedents` (`constraint.h:276-312`,
`:1054`). `[C]` Farkas coefficients are upper-bound-oriented, with index 0
belonging to the **negation** of the deduced constraint (`:276-312`). `[C]`
`inConflict()` is simply `hasProof() && negationHasProof()` (`:633`). `[C]`

`[I]` Our atoms are per-theory `Vec` indices with side tables. A
`(var, Delta, kind)` database would give us atom dedup, O(1) negation,
best-implied-bound lookup, and a natural home for the Farkas multipliers we
already compute — and it is theory-shared, serving LRA, LIA and the LP
relaxation from one structure.

### A4. Z3's integer pipeline, in order, with its gates

`int_solver::imp::check` (`references/z3/src/math/lp/int_solver.cpp:272-304`)
`[C]`:

```
0. has_inf_int()?                       no  -> sat
1. gcd test            (m_gcd)          if should_apply
2. patch_basic_columns
3. int_cube            (unit cube)      if should_find_cube()
4. find_lcube          (largest cube)   if should_find_lcube()
5. move_non_basic_columns_to_bounds
6. hnf_cut                              if should_hnf_cut()
7. solve_dioph_eq                       if should_solve_dioph_eq()
8. gomory.get_gomory_cuts(2)            if should_gomory_cut()
9. int_branch
```

Every gate is a **period** with exponential back-off on failure `[C]`:
`hit_period(p)` is `m_number_of_calls % p == 0`, or a *randomised*
`random_next(p) == 0` when `random_hammers` is on (`int_solver.cpp:209-215`);
`hnf_cut` doubles `m_hnf_cut_period` on `undef` and resets on success
(`:263-270`); `find_lcube` doubles up to `1<<30` (`:229-238`); `dioph_eq`
doubles its period on `undef` and, after **16** consecutive unproductive calls,
re-enables Gomory and the GCD test (`:178-198`). `[C]`

Defaults: `int_hammer_period = 4` drives the gomory/cube/hnf periods
(`lp_settings.h:248-251`); HNF is limited to **75 rows / 150 columns**
(`:254-255`); `lcube_flips = 16`; `dio_calls_period = 1`. `[C]`

The Gomory derivation is the standard GMI. For an integer column with
`m_fj = frac(-a_j)`, `m_f = frac(x_basic)` (`gomory.cpp:60-87`) `[C]`:

```
at lower:  new_a =  (f_j <= 1-f) ? f_j/(1-f) : (1-f_j)/f      ; m_k += new_a * lb(j)
at upper:  new_a = -((f_j <= f)  ? f_j/f     : (1-f_j)/(1-f)) ; m_k += new_a * ub(j)
```

and for a real column with `a = -coeff` (`:95-134`):

```
at lower:  a>0 -> a/(1-f)   ; a<0 -> -a/f
at upper:  a>0 -> -a/f      ; a<0 ->  a/(1-f)
```

Overflow is guarded by `m_big_number = (max |ceil(a)|)^2` over the row
(`:283-289`); a coefficient exceeding it abandons the cut (`:314-316`). `[C]`
An empty resulting term means `0 ≥ m_k > 0`, i.e. a **direct conflict**
(`:136-140`, raised at `:319-321`). `[C]` A free bonus falls out of the same
scan: if every nonbasic pins the basic variable to its max, `x_k ≤ floor(x_k)`
is valid, and symmetrically for min (`row_polarity`, `:27`, `:89-93`, used at
`:518-521`). `[C]`

Branch-variable choice (`int_branch.cpp:54-125`) is three buckets with
reservoir sampling — small boxed range (span − 2·usage ≤ **1024**), small
absolute value (< 1024), then anything, preferring the smallest magnitude —
selected with probability 2/3 down the list (`:115-123`). `[C]` The branch
direction is a **coin flip**: `is_upper() = random % 2` (`:32-51`). `[C]`

Z3's `dioph_eq.cpp` implements Griggio's approach (`:13-15`), maintaining
`m_e_matrix` (the substituted terms) alongside `m_l_matrix` (each row as a
combination of the *original* terms — the proof certificate), with fresh
variables introduced when no coefficient is `±1`. `[C]` Its elimination pivot
uses a **Markowitz number** `(col_size−1)*(row_size−1)`
(`get_markovich_number`, `:2262-2267`) — the same fill-in-minimising instinct as
the simplex entering rule.

### A5. Z3's incrementality: what is trailed and what is not

The invariant to copy (`lar_solver.cpp:532-603`, `lar_core_solver.h:123-144`)
`[C]`:

- **Trailed**: column creation (`undo_add_column`, `lar_solver.cpp:1929-1948`),
  and bound value + witness + the whole `column` struct
  (`column_update_trail`, `:107-119`) — the trail stores the **old** constraint
  pointer.
- **Stacked**: `m_column_types`, `m_usage_in_terms`, the simplex strategy, and
  the constraint set's counters.
- **Neither restored nor undone**: `m_r_A` (the pivoted matrix), `m_r_basis`,
  `m_r_nbasis`, `m_r_heading`, and the values in `m_r_x` (only resized).

So **the basis persists across pop**. What is repaired instead:
`clean_inf_heap_of_r_solver_after_pop` (`lar_solver.cpp:1853-1887`) drops
out-of-range entries and re-tests the rest; `m_row_bounds_to_replay` re-marks
rows as touched so bound propagation is redone (`:584-586`); status resets to
`UNKNOWN` (`:602`). `[C]`

`[I]` "The tableau is a persistent, monotonically-pivoted object; only bounds,
constraints and columns are trailed" is the one sentence to keep. Our design
already agrees (§3.5).

### A6. Constants, side by side

| Knob | Yices | Z3 | cvc5 |
|---|---|---|---|
| Bland switch trigger | repeated **leaving** variable | repeated **leaving** column | per-variable pivot count |
| Bland threshold | 1000, ×100 above 1k vars, ×1000 above 10k | 1000 | `arithPivotThreshold` = 2 (per variable) |
| Entering rule | non-free basics in column, random tie-break | non-free basics in column, then column nnz, random tie-break | `minBoundAndColLength` |
| Violated-basic structure | int heap, pop min | `lpvar_heap m_inf_heap`, min | `BinaryHeap` whose comparator is the rule |
| Row length cap for propagation | 30 | 300 | 16 |
| Theory lemma kept if shorter than | 8 (20 for QF_LIA) | 30 (IDL) / 32 (LRA) | 8 (propagate-as-clause) |
| Interface-equality budget per final check | 15 (UFLIA) / 30 | — (one `assume_eq` at a time) | one lemma per care pair |
| Initial δ | 1, shrunk per bound + per egraph diseq | 1, shrunk per bound then **halved until injective** | lazy, from the set of all relevant values |
| Integer: cuts | Gomory mostly compiled out | Gomory off while dio productive | none of its own |
| Integer: Diophantine | on | on (`lp.dio`) | on (`--dio-solver`) |
| Branch lemma | binary, fresh atom | binary, direction = coin flip | **ternary** with `=` first (`--arith-brab`) |

Sources for this table are the citations in §§3–5 and A1–A5.

## Appendix B — coverage gaps in this survey

Explicitly not verified, and why. Each is stated so it can be closed by a
single targeted read rather than a re-survey.

**About our tree** (the ones that would change a recommendation):

- Whether our `materialize` (`simplex.rs:729`) accounts for **disequalities**
  when choosing δ (§3.3). Matters for QF_UFLRA/QF_UFLIA only; Z3's fix is ~15
  lines.
- Whether `LraTheory` implements `TheorySolver::explain` (§8.2) — it is not in
  the grep hits at `lra_online.rs`, but I did not read the impl block.
- Whether our `distinct` (`crates/axeyum-solver/src/distinct.rs`) is expanded
  quadratically (§6.5).
- Whether our `crates/axeyum-egraph` LCA explanation matches Z3's in the
  **commutative-argument** case (§6.2); only the module doc comment was read,
  not `explain`'s body.
- The mean nonzero count per tableau row on the recorded QF_LRA instance, and
  the `final_check_core_widenings` rate on the miss population (§10). These are
  measurements, not reads, and they gate finding #1.

**About the reference solvers:**

- Z3 `euf_ackerman` trigger heuristic and constants (§6.3) — the sub-lane for
  Z3's EUF could not be scheduled; §6.1–§6.2 were read directly by this lane,
  §6.3 was not.
- An explicit Nelson–Oppen arrangement enumerator in any of the three (§7.4).
  I did not find one; absence was not proven.
- The Griggio elimination algorithm inside cvc5's `dio_solver.cpp` and Z3's
  `dioph_eq.cpp` `rewrite_eqs`/`tighten_terms_with_S` — only the interfaces,
  the scheduling and the certificate representation were read (§5.4, §A4).
- cvc5's `FCSimplexDecisionProcedure::dualLike` beyond its focus-size dispatch,
  and `soiRound()`'s body (§A2).
- The numeric values of Z3's `lconstraint_kind` enum, which the `kind()/2`
  strictness trick in `implied_bound.h:41-46` depends on.
- Whether `references/cvc5` and `references/yices2` should be added to
  `scripts/fetch-references.sh` — `cvc5` is already listed there and was simply
  never cloned on this host; `yices2` is **not** listed and this lane cloned it
  ad hoc. If Yices is going to be the reference text for our simplex, adding it
  is a one-line change someone should make deliberately.

## Sources

- Dutertre & de Moura, *A Fast Linear-Arithmetic Solver for DPLL(T)*, CAV 2006,
  LNCS 4144 — [springer](https://link.springer.com/chapter/10.1007/11817963_11),
  [pdf](https://yices.csl.sri.com/papers/cav06.pdf)
- de Moura & Bjørner, *Model-based Theory Combination*, SMT 2007 / ENTCS —
  [z3 paper index](https://link.springer.com/content/pdf/10.1007/978-3-540-78800-3_24.pdf)
- Barrett, Nieuwenhuis, Oliveras & Tinelli, *Splitting on Demand in SAT Modulo
  Theories*, LPAR 2006, LNAI 4246 —
  [pdf](https://homepage.cs.uiowa.edu/~tinelli/papers/BarNOT-LPAR-06.pdf)
- King, Barrett & Dutertre, *Simplex with Sum of Infeasibilities for SMT*,
  FMCAD 2013 — [pdf](http://theory.stanford.edu/~barrett/pubs/KBD13.pdf)
- Nieuwenhuis & Oliveras, *Proof-Producing Congruence Closure*, RTA 2005 —
  cited via Z3's implementation (`euf_egraph.cpp:692-800`); note cvc5
  deliberately does **not** implement it this way (§6.4)
- Griggio, *A Practical Approach to Satisfiability Modulo Linear Integer
  Arithmetic*, JSAT 2012 — cited by both integer solvers
  (`references/z3/src/math/lp/dioph_eq.cpp:13-15`,
  `references/cvc5/src/options/arith_options.toml:122-127`)
- Bromberger & Weidenbach, *Fast Cube Tests for LIA Constraint Solving* —
  cited via Z3's `int_cube.cpp:325-347` (half the 1-norm over integer
  variables) and cvc5's `--arith-brab` rounding

**Clone provenance.** `references/z3` was already present.
`references/cvc5` (listed in `scripts/fetch-references.sh` but not cloned on
this host) and `references/yices2` (**not** listed) were cloned by this lane on
2026-09-08 with `git clone --depth 1`; cvc5 resolved to `1689f133`. Both are
gitignored. See Appendix B on whether `yices2` should be added to the script.
