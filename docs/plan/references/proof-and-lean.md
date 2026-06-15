# Proof production & Lean interop

The path from "axeyum produces DRAT for the clausal layer" to "axeyum produces a
machine-checkable, Lean-consumable proof for full SMT queries." Built from
`references/{carcara,lean4,nanoda_lib,lean-smt,cvc5,drat-trim}` and axeyum's
current proof surface.

## Where axeyum starts
- **Clausal layer independently checkable.** `export_qf_bv_unsat_proof`
  (`crates/axeyum-solver/src/proof.rs`) → `(DIMACS, DRAT)`, self-verified by
  in-tree `check_drat` (RUP+RAT, ADR-0011), accepted by `drat-trim`;
  `UnsatProof::recheck` re-validates from text.
- **Reduction not yet certified, only mitered.** `faithfulness.rs` (sampled
  bug-detector); `bitblast_miter.rs` (**exhaustive** DRAT-checked miter vs an
  *independently coded* reference bit-blaster over the full scalar QF_BV op set —
  "sound modulo trust in the reference," axeyum's strongest reduction artifact).
- **Evidence envelope** (`evidence.rs`) already routes per-theory (term-level
  enumeration, DRAT, Farkas, LRA-DPLL) — the right place to add Alethe.
- **No SMT-level proof object, no Alethe, no Lean path yet.** Array/UF/int/fp
  reductions are trusted.

## Proof format landscape & recommendation
| Format | Layer | Checker | Lang | Fit |
|---|---|---|---|---|
| DRAT | SAT/CNF | `drat-trim`, in-tree | C / **Rust (have it)** | Done. Coarse. |
| LRAT | SAT/CNF | `lrat-check` (`references/drat-trim/lrat-check.c`), cake_lpr | C | DRAT + hint chains; faster to check; what Lean SAT importers prefer. Cheap upgrade. |
| **Alethe** | full SMT | **Carcara (Rust)**, Isabelle | text S-expr | **Primary recommendation.** Rust-native checker; explicit `bitblast_*` + `drup`/`drat` rules; matches axeyum's lowering. |
| Eunoia/`.eo` (cpc) | full SMT | **Ethos** (C++) | text | Most complete (covers BV div/rem) but C++ → violates no-C/C++. Use as *spec reference*, not default dep. |
| LFSC | full SMT | lfscc (C++) | text | Legacy; skip. |
| Lean term (CIC) | full SMT | Lean kernel (~5.6k C++) / **nanoda_lib (~6k Rust)** | term | End goal; hardest. Reached via reconstruction, not direct emission. |

**Recommendation: Alethe is the realistic primary target, LRAT the clausal
sub-layer, a Lean bridge the capstone.** Because: Carcara is **Rust** (fits the
no-C/C++ rule); Alethe's BV rules mirror axeyum's existing lowering; Lean interop
composes on top of Alethe rather than instead of it.

**Realism note on lean-smt:** it does **not** consume any text format — it links
cvc5 in-process and walks cvc5's C++ `cvc5.Proof` object graph via FFI. So axeyum
cannot target lean-smt by emitting a file. Targeting Lean means either (a) a *new*
Lean reconstruction tactic for Alethe (large; the rule-by-rule playbook is in
lean-smt's `Smt/Reconstruct/`), or (b) the in-tree nanoda-style Rust kernel.

## Alethe + Carcara (the Rust-native target)
Producer emits three S-expression forms (ref
`references/carcara/carcara/src/ast/printer.rs::AlethePrinter`):
```
(assume <id> <term>)
(step <id> (cl <term>*) :rule <name> [:premises (<id>*)] [:args (<term>*)] [:discharge (<id>*)])
(anchor :step <id> [:args (...)])   ; opens subproof, closed by matching step
```
`(cl)` = empty clause = false; premises by id; rules are **strings** dispatched
through one `&str` match (`references/carcara/carcara/src/checker/shared.rs::get_rule_shared`,
~170 rules). Unknown rules can be `hole` (configurable) — lets axeyum emit partial
proofs and fill rules incrementally.

**Alethe IR to mirror** (`references/carcara/carcara/src/ast/term.rs`): hash-consed
`Rc<Term>` with pointer equality + a separate `polyeq` (equality modulo
reorder/AC/alpha, `ast/polyeq.rs`). axeyum already has the interned arena
(`TermId`); add a polyeq matcher. `Operator` enum already carries SMT-LIB BV names
(`bvadd`, `bvult`, `concat`, `extract`, `@bbterm`, `@bit_of`) — a 1:1 target for
axeyum's `Op`.

**BV certificate shape** (the natural fit): per lowered operator a `bitblast_*`
step `(= <op-term> (@bbterm <bit0> ...))`; clausify the bits; Boolean refutation
via `resolution`/`drup`/`drat` (reuse axeyum's DRAT). Carcara has its own DRUP
checker (`drup.rs`), so the clausal seam composes. **Carcara's BV bit-blast rules
hole out `bvudiv`/`bvurem`/shifts** — axeyum's miter *does* cover div/rem, so for
those ops emit `hole` + attach the miter certificate (a place axeyum can lead).

**Lesson:** emit *elaborated* Alethe from the start (explicit resolution pivots,
explicit symm/trans) — cheaper than relying on Carcara's post-hoc elaborator
(`references/carcara/carcara/src/elaborator/`).

## Lean kernel & nanoda_lib
"Lean accepts the proof" = you produce a CIC `expr` term whose *type* is the goal;
the kernel's `add_theorem` (`references/lean4/src/kernel/environment.cpp:192`)
infers the type and checks definitional equality (`type_checker.cpp:1056`). **No
separate proof format** — fully-elaborated terms only (12 `expr` kinds,
`expr.h:84`). Trusted kernel ≈ **5.6k LoC impl + 2.3k headers**; semantic core
≈ 3.6k; biggest blob `inductive.cpp` (1249).

**nanoda_lib** — clean-room **pure-Rust** Lean type-checker, ~9.2k LoC total
(~6k kernel+parser: `tc.rs` 1327, `inductive.rs` 1677, `expr.rs` 778, `level.rs`
275, `quot.rs` 274, `env.rs` 284, `parser.rs` 934). A *checker*: reads Lean's
export format and runs the CIC acceptance condition (`tc.rs:83 check_declar`).
Pure Rust (`num-bigint`, `serde`, `fxhash`) — **fits no-C/C++.** Gives axeyum (a)
the acceptance criterion and (b) a ~6k-LoC reference for an in-tree Rust Lean
kernel. Does **not** give proof-term *construction* (the hard part). nanoda's
`'a`-lifetime arena would rework to axeyum's `Copy` handles.

## lean-smt bridge
`Preprocess → Translate (Lean→SMT-LIB) → solve → Reconstruct (proof→Lean term)`
(`references/lean-smt/Smt/`). **Hard-wired to cvc5-as-a-library** via `lean-cvc5`
FFI; walks the in-memory `cvc5.Proof` graph, does **not** parse text. Reconstruction
pattern (the reusable playbook): registered `@[smt_proof_reconstruct]` handlers per
theory (`Smt/Reconstruct/{Prop,Builtin,UF,Arith,Int,Quant,Datatype,BitVec}.lean`);
each rule → a pre-proved Lean lemma; unmatched → `addTrust` → `sorry`-backed
residual. BV is least complete (bit-blast discharged by Lean's own `simp`+`BitVec`
lemmas; DSL rewrites return trust holes). **Viable Lean targets for axeyum:** a new
Alethe→Lean reconstruction tactic (lean-smt's per-rule lemma library is the guide),
or the in-tree nanoda kernel. Interim honest story: lean-smt's `+trust` mode
(admit on unsat).

## Per-reduction proof obligations
cvc5's central pattern (copy wholesale): **every reduction is a proof step whose
conclusion a small self-contained checker re-derives from the rule's args;
otherwise it is a typed `TrustId` hole** (`references/cvc5/src/proof/trust_id.h`)
graded by **pedantic level** (0=hard fail … 10=minor) — making the trust surface
*enumerable and countable*. Status per reduction (the maturity signal):

| axeyum reduction | cvc5 rule(s) | cvc5 status | Alethe rule | axeyum obligation |
|---|---|---|---|---|
| **Bit-blast (BV→AIG/CNF)** | `BV_BITBLAST_STEP`, `MACRO_BV_BITBLAST` | fine-grained checked in Eunoia; coarse trusted | `bitblast_*` | **Have the miter** — convert to per-op `bitblast_*` steps; div/rem/shifts = hole + miter cert. |
| **Array elim (ROW, ext)** ADR-0010 | `ARRAYS_READ_OVER_WRITE{,_1,_CONTRA}`, `ARRAYS_EXT` | **fully checked** | `ARRAYS_ROW/IDX/ROW_CONTRA/EXT` | One ROW/IDX step per resolved read; checker re-derives `select(store…)`. Tractable. |
| **Ackermann (UF elim)** ADR-0013 | `PREPROCESS_ACKERMANN` | **TrustId hole** in cvc5 too | `cong`/`eq_congruent` | Each congruence constraint provable as `eq_congruent`; fresh-var introduction is the seam. |
| **Int-blast (BV↔Int)** | `INT_TO_BV_ELIM`, `UBV_TO_INT_ELIM` | rewrites checked; core = `TrustId::INT_BLASTER` hole | partial | Rewrites checkable; the pass itself = trust hole (matches cvc5). |
| **FP→BV (fpa2bv)** ADR-0023/0026 | FP+RARE rules | partly trusted | — | Lower priority; miter-style faithfulness is the interim. |
| **CNF (Tseitin)** | `CNF_*` | **checked** | `and_pos`/`or_pos`/… | Emit a CNF rule per Tseitin clause; `tseitin_encode` already knows the gate. |
| **SAT refutation** | `CHAIN_RESOLUTION` / `DRAT_REFUTATION` | checked / external | `resolution`/`drup`/`drat` | **Have DRAT.** Keep as `DRAT_REFUTATION` leaf, or upgrade to LRAT→resolution. |

**The seam principle:** cvc5 composes SAT proof and theory proof *at the clause
level* — each input clause "justified by reduction proof X." axeyum already has
the named clause→AIG replay maps — exactly the join points. cvc5's
`DRAT_REFUTATION` (`{F|D,P}` = DIMACS+DRAT) is *literally* axeyum's current
`UnsatProof`.

## Phased proof/Lean roadmap (sized; → drives Track 3)
- **P0 — Reduction trust ledger (*S*).** Typed `TrustId`-style enum + pedantic
  level per reduction; every trusted reduction emits a named, countable step.
  Ref `references/cvc5/src/proof/trust_id.h`.
- **P1 — LRAT upgrade (*S–M*).** Extend `solve_with_drat_proof` to emit LRAT +
  in-tree `check_lrat` (ref `references/drat-trim/lrat-check.c`); keep DRAT.
- **P2 — Alethe term + proof IR + emitter (*M*). ⟵ CRITICAL PATH.** `axeyum-alethe`
  crate: Alethe `Term`/`ProofCommand`/`ProofStep` (mirror
  `references/carcara/carcara/src/ast/`), printer, `Op`→Alethe map, polyeq matcher.
- **P3 — Alethe for QF_BV (*M*).** Convert the miter machinery to `bitblast_*` +
  Tseitin CNF steps + Boolean `resolution`/`drup`/`drat`; div/rem/shifts = hole +
  miter side-cert. Validate by running **Carcara** (Rust) in CI over axeyum output.
- **P4 — Embedded Alethe checker subset (*M*).** Reimplement a checking subset of
  Carcara's rules in-tree (`resolution`, `cl`, `bitblast_*`, `cong`/`trans`/`refl`,
  CNF rules, `drup`) so axeyum self-checks its own QF_BV Alethe.
- **P5 — Alethe for the reductions (*M*, per theory).** Arrays first
  (`ARRAYS_ROW/IDX/EXT`), then Ackermann (`eq_congruent`), then int-blast rewrites;
  each retires a `TrustId`. Keep holes (with side-evidence) for fpa2bv / int-blast
  core, matching cvc5's honest boundary.
- **P6 — Lean path (*L*). Capstone.** P6a: vendor a nanoda-style kernel
  (`references/nanoda_lib/src/`, ~6k LoC) as `axeyum-lean-kernel` with `Copy`
  handles. P6b: Alethe→Lean reconstruction (CIC proof terms), guided by
  `references/lean-smt/Smt/Reconstruct/`. Until then, the honest Lean story is
  `+trust` + axeyum's re-checkable Alethe artifact.

**Net trajectory:** DRAT+miter (today) → LRAT + trust ledger → **Alethe emitter
(critical path)** → Carcara-checked QF_BV → self-checked QF_BV → per-theory
reduction proofs → Lean-checkable terms.

### Key file references
- axeyum: `crates/axeyum-solver/src/{proof,evidence,faithfulness,bitblast_miter}.rs`,
  `crates/axeyum-cnf/src/{drat,proof_sat}.rs`.
- Carcara: `references/carcara/carcara/src/{ast/term.rs, ast/printer.rs,
  checker/shared.rs, checker/rules/bitvectors.rs, drup.rs, elaborator/}`.
- Lean: `references/lean4/src/kernel/{type_checker.cpp, expr.h, environment.cpp}`;
  `references/nanoda_lib/src/{tc.rs, expr.rs, parser.rs}`.
- Bridge: `references/lean-smt/Smt/Reconstruct/{Prop,BitVec}.lean`,
  `Smt/Reconstruct/BitVec/Bitblast.lean`, `Smt/Tactic/Smt.lean` (`+trust`).
- cvc5: `references/cvc5/src/proof/trust_id.h`,
  `references/cvc5/src/theory/{arrays,bv}/proof_checker.cpp`,
  `references/cvc5/src/prop/proof_cnf_stream.cpp`,
  `references/cvc5/proofs/eo/cpc/{rules/BitVectors.eo,programs/Bitblasting.eo}`.
- LRAT: `references/drat-trim/lrat-check.c`.
