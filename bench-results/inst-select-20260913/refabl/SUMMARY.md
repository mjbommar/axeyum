## M1 -- reference ablation (cvc5 1.3.4, 24 s, 8 GiB, pinned core)

Arms are NOT a partition: a file may refute in several.  `NONE` is a
run with no verdict-shaped line (crash / OOM / watchdog) and is kept
separate from `unknown` -- it is not a solver opinion.

| division | rows | arm | unsat | sat | unknown | NONE |
|---|---:|---|---:|---:|---:|---:|
| UFNIA | 61 | `default` | 49 | 0 | 6 | 6 |
| UFNIA | 61 | `ematch` | 45 | 0 | 10 | 6 |
| UFNIA | 61 | `noematch` | 29 | 0 | 30 | 2 |
| UFNIA | 61 | `neither` | 25 | 0 | 35 | 1 |
| UFLIA | 68 | `default` | 66 | 0 | 1 | 1 |
| UFLIA | 68 | `ematch` | 66 | 0 | 1 | 1 |
| UFLIA | 68 | `noematch` | 18 | 0 | 50 | 0 |
| UFLIA | 68 | `neither` | 18 | 0 | 50 | 0 |

### The load-bearing number: of the files cvc5 DECIDES, how many does
each ablation still decide the same way?

| division | cvc5 decides | `ematch` agrees | share | Wilson 95% | `noematch` agrees | `neither` agrees |
|---|---:|---:|---:|---|---:|---:|
| UFNIA | 49 | 45 | **92%** | [81%, 97%] | 29 | 25 |
| UFLIA | 66 | 66 | **100%** | [94%, 100%] | 18 | 18 |
| **both** | **115** | **111** | **97%** | [91%, 99%] | 47 | 43 |

### Files cvc5 decides that the `ematch` arm does NOT

These are the only candidates for "out of e-matching's reach", and even
for them the evidence is one-sided.

- `UFNIA/2019-Zohar-ic/partial/int_check_bvsle_bvudiv1_ltr_no_inv.smt2` — default `unsat` (207 ms), ematch `unknown`, noematch `unsat`, neither `unknown`
- `UFNIA/2019-Zohar-ic/partial/int_check_bvugt_bvudiv0_ltr_no_inv.smt2` — default `unsat` (108 ms), ematch `unknown`, noematch `unsat`, neither `unknown`
- `UFNIA/2019-Zohar-ic/qf/int_check_bvsge_bvneg_ltr_no_inv.smt2` — default `unsat` (208 ms), ematch `unknown`, noematch `unsat`, neither `unknown`
- `UFNIA/2019-Zohar-ic/full/int_check_bvslt_bvurem1_ltr_no_inv.smt2` — default `unsat` (108 ms), ematch `NONE`, noematch `unsat`, neither `unknown`

### Rows with NO verdict from cvc5 at all

- **UFNIA: 6 of 61**
  - `UFNIA/spec_sharp/test14-Xml.ssc.17.Microsoft.Boogie.XmlSink.WriteFileFragment_System.String_notnull.smt2` (declared `:status unsat`)
  - `UFNIA/vcc-havoc/verisoft-sim.c.1.13.untranslated_write_sim.smt2` (declared `:status unsat`)
  - `UFNIA/2019-Zohar-ic/partial/int_check_bvsgt_bvlshr0_ltr_no_inv.smt2` (declared `:status unknown`)
  - `UFNIA/sledgehammer/Fundamental_Theorem_Algebra/z3.1031223.smt2` (declared `:status unsat`)
  - `UFNIA/spec_sharp/textbook-Factorial.dll.1.Factorial.F_System.Int32.smt2` (declared `:status unsat`)
  - `UFNIA/lahiri-cav09-storm-queries/mqueue_example_cegar_2_3_10.smt2` (declared `:status unsat`)
- **UFLIA: 1 of 68**
  - `UFLIA/simplify/javafe.tc.TypeSig.730.smt2` (declared `:status unsat`)
