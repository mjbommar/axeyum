# Lane: array-real-gate — the `!features.has_real` gate on the scalar array route

<!-- plan-section: lane-status -->

**Lane array-real-gate (`DONE`, array-real-gate, 2026-09-13).** ADR-1955 pointed
the next lane at `scalar_alia_auflia_arrays_supported`'s `!features.has_real`
and priced it at **19,620 files**: *"the larger prize, not blocked by the IR at
all"*. The guard **is** stale, it **is** lifted, and it was **never the gate that
stopped the query** — and the prize is **zero files**.

**The guard has no written justification anywhere.** It was born with the
ALIA/AUFLIA lazy-ROW route in `c093fa911`, whose entire commit message is
`feat(solver): checkpoint dominance audit and ABV array certs` over a 100-file
diff, with no comment and no edit since. ADR-0010 does not contain the word
"Real"; ADR-1814 lists `has_real` among the **route-selector** flags; ADR-0079's
sort list is backend reach and rejects `Int` in the same breath. Meanwhile the
backend behind it (`check_with_arith_dpll`) is documented as *"integer, real, or
combined `QF_LIRA`"* — the same function the dispatcher calls as `lira-dpll` —
`RowCtx::resolve_select` never branches on the element sort, and the soundness
argument (relaxation transfers `unsat`, every `sat` is replayed) is sort-uniform.

**It was three gates, and ADR-1955 named the one that was never consulted.**
`p5-row-real`'s route trail at `57bd22d37` ends `nra declined (unsupported)` and
**never records `array-fast-path`**. Two earlier returns terminate a Real query
first: the pure-real branch's `Err(Unsupported)` arm after `check_with_nra` (no
UF), and `dispatch_uf_routes`'s `Unknown if features.has_real` (with UF). Both
are ADR-1927's shape — *a rung's fragment refusal is a DECLINE, not the query's
verdict* — recurring in a branch that audit did not reach.

**Two lifted, one documented in place.** Gate 1 now falls through when
`features.has_non_bv_array` (exactly the population the array branch terminates
itself, so a Real query can never reach `check_with_all_theories`, which
hard-errors on `Sort::Real`); gate 3 loses the clause. **Gate 2 was NOT
changed**: its mutation SURVIVED (nine tests, none depend on it) and three probes
built to reach that rung (`r1`, `r6`, `r7`) are each decided earlier by
`uf-arithmetic` or `lia-dpll`. A change nobody can demonstrate is decoration.

    probe                    before   after   z3      cvc5
    p5-row-real              unknown  UNSAT   unsat   unsat
    p6-row-int   (the pair)  unsat    unsat   unsat   unsat
    r1-row-real-uf           unknown  UNSAT   unsat   unsat
    r2-fractional-real       unknown  SAT     sat     sat
    r3-fractional-int (pair) unsat    unsat   unsat   unsat
    r4-unconstrained-pair    unknown  SAT     sat     sat
    r7-row-real-uf-distinct  unknown  UNSAT   unsat   unsat

**Worth: zero files, and the sizing was committed BEFORE the code (`64a0026c9`).**
`real_gate_only` — a non-BV array query refused on the `has_real` clause **and
nothing else** — is **0 in all 28 array-carrying divisions**. Two causes, neither
separated by ADR-1955: (a) AUFLIRA's and AUFNIRA's 19,620 **are** the 27,150
behind the parse refusal, one population counted once per gate — ADR-1945's *two
sequential caps are not two caps*, applied to its own successor; (b) of the 1,367
AUFLIRA and 504 AUFNIRA files that **do** parse, not one contains an array
(`grep -c Array` is 0).

**A/B: 1,200 files, zero rows differ.** Interleaved per file, both binaries back
to back on one pinned core, 24 s / 8 GiB. AUFLIRA 9/9, AUFNIRA 3/3, ALIA 0/0,
ABV 4/4, and the live controls QF_ABV **187/200** and QF_BV **186/200** — delta
+0 in every division, and a per-row comparison finds **0 of 1,200** files where
the two arms return different strings, so there was no single-pairing surprise to
re-check. No verdict contradicts a declared `:status`; no arm disagreement; one
`rc134` (the 8 GiB cap) **in both arms**; zero wrapper kills.

**Gates run, each with its `test result:` line read.** solver `--lib --features
full -- --test-threads=4` **1725 passed**; `corpus_regression` 2; and
`nested_array_gate_map` 7, `real_element_array_row` 9, `arrays` 10,
`array_elim_unsat_proofs` 5, `abv_lazy_row` 9, `abv_lazy_ext` 7,
`array_scenarios` 8. Mutation control `array-real-gate`: baseline green at 9
tests, each changed guard restored kills **exactly one**. The five failing exit
statuses of `ab-summarize.py` are demonstrated firing.
**Did not run:** the z3 differential fuzzes — no linear-arithmetic route was
touched (the diff is two dispatch predicates in `auto.rs`), and workspace clippy,
which the push hook runs.

**Next actions.** (a) `sort.rs` — ADR-1955's Option B interned array-sort id is
now the **only** thing between ALIA/ABV's 7,530 and a verdict, and one of two for
AUFLIRA. (b) Audit the rest of `check_auto` for the ADR-1927 shape: an
`Err(SolverError::Unsupported)` arm that `return`s rather than declining, above a
route that owns the refused construct. Gates 1 and 2 are two instances found by
accident while looking for something else.

<!-- plan-section: landed-changes -->

| 2026-09-13 | array-real-gate | ADR-1960: the Real-element array gate was **three** gates and ADR-1955 named the one never consulted; two lifted, one documented in place after its mutation SURVIVED. Seven probes move or hold, z3 and cvc5 agree with every one. Corpus value **0 files** — `real_gate_only = 0` in all 28 array divisions, because the 19,620 **are** the 27,150 (ADR-1945). A/B 1,200 files, **0 rows differ**, controls QF_ABV 187/200 and QF_BV 186/200 |
