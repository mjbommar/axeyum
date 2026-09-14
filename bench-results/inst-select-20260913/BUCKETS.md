## M2 -- what cvc5 instantiated with, classified

`Q` in the query, `G` in our ground set but not the query, `N` neither,
`S` a cvc5-invented Skolem (its own class -- it has no counterpart in
the query by construction, so calling it `N` would manufacture the
finding this lane exists to test).

Files with a cvc5 refutation dump: **115**.
Of those, files where our run produced a ground set: **95**;
without one: **20** -- reported separately, two-way only.


### Three-way, over the 95 files with our ground set

| bucket | distinct terms | share | instantiation slots | share |
|---|---:|---:|---:|---:|
| **Q** | 2963 | 40.7% | 64697 | 35.7% |
| **G** | 142 | 1.9% | 5019 | 2.8% |
| **N** | 2544 | 34.9% | 60618 | 33.4% |
| **S** | 1637 | 22.5% | 50931 | 28.1% |
| *total* | 7286 | | 181265 | |

### Two-way, over all 115 files (needs no ground set)

| bucket | distinct terms | share | slots | share |
|---|---:|---:|---:|---:|
| **Q** | 4387 | 45.7% | 93156 | 42.9% |
| **not-Q** | 3481 | 36.2% | 71235 | 32.8% |
| **S** | 1741 | 18.1% | 52806 | 24.3% |

### Bucket N is CONTAMINATED, and by how much

cvc5 prints arithmetic in a sum-of-monomials normal form — `(+ -1 (typeof S))`,
`(* -1 x)` — where the source writes `(- (typeof S) 1)`. Those are the SAME
term and compare unequal as strings, so an N with an arithmetic head is
evidence of a printer disagreement at least as much as of an absence.

- bucket N, all heads: **2544** distinct terms
- of those, head in `+ - * div mod /`: **727** (28.6% of N)
- **N with a non-arithmetic head: 1817** — the defensible residue

Re-reading the three-way split with the contaminated part set aside
entirely (Skolems excluded, since they are their own class):

| bucket | distinct | share of Q+G+N(non-arith) |
|---|---:|---:|
| **Q** (in the query) | 2963 | 60.2% |
| **G** (we built it, not in the query) | 142 | 2.9% |
| **N** (non-arithmetic head) | 1817 | 36.9% |

**Q+G = 63.1%** of that residue: terms we either read or built.

### Files with ANY bucket-N term

**55 of 95** files with a ground set contribute any
term we neither read in the query nor ever built.

- `UFLIA/sledgehammer/Fundamental_Theorem_Algebra/smtlib.1282463.smt2` — 592 of 624 distinct, e.g. `(* -1 (f72 f73 (f58 f59 (+ -1 (f72 f73 (f58 f59 2))))))`, `(* -1 (f72 f73 (f58 f59 (+ 1 (* 2 (f72 f73 (f58 f59 2)))))))`, `(* -1 (f72 f73 (f58 f59 1)))`, `(* -1 (f72 f73 (f58 f59 2)))`
- `UFLIA/sledgehammer/TwoSquares/smtlib.711545.smt2` — 302 of 512 distinct, e.g. `(* -1 (f11 f12 (f6 f7 @purify_25)))`, `(* -1 (f8 f35 (+ 1 (* 4 f15))))`, `(* -1 (f8 f35 (+ 1 (f11 (f13 f14 f26) (f6 f7 2)))))`, `(* -1 f25)`
- `UFNIA/vcc-havoc/baby.1.20.handle_illegal.smt2` — 176 of 262 distinct, e.g. `(+ (* 204 (conv_u4_to_i8 (ld_u4 mem (ptr g_cg_1 0)))) (offset (ptr g_PCB_1 0)))`, `(+ (* 204 (conv_u4_to_i8 (ld_u4 mem_3 (ptr g_cg_1 0)))) (offset (ptr g_PCB_1 0)))`, `(+ (* 204 (conv_u4_to_i8 (ld_u4 mem_4 (ptr g_cg_1 0)))) (offset (ptr g_PCB_1 0)))`, `(+ (* 204 (conv_u4_to_i8 (ld_u4 mem_6 (ptr g_cg_1 0)))) (offset (ptr g_PCB_1 0)))`
- `UFLIA/simplify/javafe.tc.FlowInsensitiveChecks.679.smt2` — 169 of 347 distinct, e.g. `(+ -1 (typeof map_pre_5_301_35))`, `(+ -10 (typeof map_pre_5_301_35))`, `(+ -100 (typeof map_pre_5_301_35))`, `(+ -101 (typeof map_pre_5_301_35))`
- `UFNIA/vcc-havoc/verisoft-sim.c.2.25.untranslated_write_sim.smt2` — 134 of 245 distinct, e.g. `(+ (* 204 (conv_u4_to_i8 n)) (offset pcb))`, `(+ (* 4 (conv_u4_to_i8 (+ (shr a 10) (shl (x (ld_u4 mem (add_ptr (add_ptr proc 128 1) 9 4)) 1048576) 10)))) (offset (conv_u8_to_ptr (ld_u8 mem (ptr g_mm_4_1 0)))))`, `(+ (* 4 (conv_u4_to_i8 (+ (shr a 10) (shl (x (ld_u4 mem_1 (add_ptr (add_ptr proc 128 1) 9 4)) 1048576) 10)))) (offset (conv_u8_to_ptr (ld_u8 mem_1 (ptr g_mm_4_1 0)))))`, `(+ (* 4 (conv_u4_to_i8 (shl (+ 33 n) 10))) (offset (conv_u8_to_ptr (ld_u8 mem_1 (ptr g_mm_4_1 0)))))`
- `UFLIA/simplify2/small_suite/getRootInterface.smt2` — 128 of 459 distinct, e.g. `(+ 51 (arrayLength otherStrings_pre_50.193.30) (arrayLength punctuationStrings_pre_50.134.22))`, `(array (typeof S_978.5))`, `(arrayLength (select1 elements_32.61.37 (select1 (asField raises_25.32.35 T_javafe.ast.TypeNameVec) m_941.1_0_945.5)))`, `(arrayLength (select1 elements_5.72.21 (select1 (asField constructorSeq_171.38 T_javafe.util.StackVector) inst_25.52)))`
- `UFLIA/simplify/javafe.ast.UnaryExpr.424.smt2` — 122 of 267 distinct, e.g. `(+ -4 T__TYPE)`, `(+ -8 T__TYPE)`, `(+ -9 T__TYPE)`, `(+ 1 T__TYPE)`
- `UFNIA/sledgehammer/Fundamental_Theorem_Algebra/z3.844134.smt2` — 113 of 391 distinct, e.g. `(* 2 (f60 f78 1))`, `(+ (* 2 (f60 f78 0)) (* 2 (f60 f78 1)))`, `(+ (f60 f78 0) (f60 f78 1))`, `(+ 1 (f43 f44 (f41 f42 0)))`
- `UFLIA/simplify/javafe.ast.NewInstanceExpr.271.smt2` — 111 of 250 distinct, e.g. `(+ -1 (typeof S_131_41))`, `(+ -10 (typeof S_131_41))`, `(+ -11 (typeof S_131_41))`, `(+ -12 (typeof S_131_41))`
- `UFLIA/simplify/javafe.ast.CatchClauseVec.66.smt2` — 76 of 137 distinct, e.g. `(+ -4 T__TYPE)`, `(+ -9 T__TYPE)`, `(+ 1 T__TYPE)`, `(+ 10 T__TYPE)`
- `UFNIA/vcc-havoc/baby.59.handle_reset.smt2` — 64 of 106 distinct, e.g. `(+ (offset global_ghost) (conv_base_to_i8 (base global_ghost)))`, `(+ 135168 (offset (conv_u8_to_ptr (ld_u8 mem (ptr g_mm_4_1 0)))))`, `(+ 135168 (offset (conv_u8_to_ptr (ld_u8 mem_0 (ptr g_mm_4_1 0)))))`, `(+ 167936 (offset (conv_u8_to_ptr (ld_u8 mem (ptr g_mm_4_1 0)))))`
- `UFNIA/spec_sharp/specsharp-BoundedStack.3.BoundedStack..ctor_System.Int32.smt2` — 61 of 169 distinct, e.g. `(BaseClass (select2 Heap_8 (select2 Heap stringLiteral11 ownerRef) ownerFrame))`, `(DeclType ownerRef)`, `(select2 Heap stringLiteral10 ownerRef)`, `(select2 Heap stringLiteral11 ownerRef)`

### The brief's small-numeral hypothesis

| shape | distinct terms | share |
|---|---:|---:|
| integer numeral | 1219 | 12.7% |
| cvc5 Skolem | 1741 | 18.1% |
| other ground term | 6649 | 69.2% |

### Explicit `:pattern` -- does the 2019-Preiner shape generalise?

| family | files | quantifiers instantiated | of those, carrying `:pattern` |
|---|---:|---:|---:|
| `UFLIA/simplify2` | 29 | 481 | 183 |
| `UFNIA/2019-Preiner` | 16 | 16 | 0 |
| `UFLIA/sledgehammer` | 13 | 1094 | 0 |
| `UFLIA/boogie` | 11 | 260 | 139 |
| `UFNIA/vcc-havoc` | 10 | 375 | 279 |
| `UFLIA/simplify` | 9 | 212 | 0 |
| `UFNIA/2019-Zohar-ic` | 8 | 22 | 0 |
| `UFNIA/sledgehammer` | 7 | 571 | 0 |
| `UFNIA/spec_sharp` | 5 | 224 | 199 |
| `UFLIA/grasshopper` | 3 | 140 | 0 |
| `UFNIA/lahiri-cav09-storm-queries` | 3 | 4 | 3 |
| `UFLIA/tokeneer` | 1 | 3 | 2 |
| **all** | **115** | **3402** | **805** |
