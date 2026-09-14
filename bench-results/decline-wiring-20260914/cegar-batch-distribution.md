# The lazy function-consistency lemma batch, measured before any cap existed

Source: the committed ADR-2015 census (`bench-results/round-head-20260914/census/`),
re-read by `cegar-batch-distribution.py`. **Observational — no run.**

**Method note, bought with a wrong answer here.** The separator inside the stats
parenthetical is `,_`, and `\w` in the key regex eats the leading `_`, so every
key but the first is mis-named and a `lemmas_added` filter silently drops every
row. The first version of this script printed **0 observations**, and that zero
looked exactly like a finding. An empty result from a tool that never pointed at
its subject is indistinguishable from a strong negative.

**The headline, visible in every row:** `lemmas_added == equal_arg_pairs` on all
31 observations. The batch is not "uncapped" in the sense of occasionally
growing large — it is *the entire equal-argument pair set*, emitted the moment
any single pair is violated. `solve_rounds` is 1, 2 or 3, and on the 15 rows
that emit anything, `lemmas_added == last_new_lemmas`: the whole batch goes in
during **one** round and the loop never gets another. The amplification from the
pairs the model actually violates reaches **1,555x**.

CEGAR stat observations: 31 raw, 31 distinct over 31 files
  of which the file's shipped verdict is unknown: 31

               field    n      min      p25       med       p75       p90       max
        applications   31       13      464       636       948      1028      1047
     function_groups   31        1       13        14        21        23        50
     potential_pairs   31       78    27423     53077    196143    198014    278420
        solve_rounds   31        1        1         2         2         2         3
          elapsed_ms   31       33       37      1231      2459      2635      5221
      sat_candidates   31        0        0         1         1         1         2
         pair_checks   31        0        0      9860     48695    113347    351724
     equal_arg_pairs   31        0        0       191      3246     12440     17750
      violated_pairs   31        0        0         8        47       229      3120
    preseeded_lemmas   31        0        0         0         0         0         0
      sibling_lemmas   31        0        0         0         0         0         1
        lemmas_added   31        0        0       192      3246     12440     17750
     last_new_lemmas   31        0        0         4      3246     12440     17750

=== per-observation, sorted by lemmas_added ===
  viol   eqarg   lemadd  lastnew  rounds   apps  potpairs      ms  file
   448   17750    17750    17750       2    928    115229    3930  spec_sharp/textbook-Factorial.dll.1.Factorial.F_System.Int32
    22   15635    15635    15635       2    876    113347    2635  boogie/DefaultLoopInv0_A.M-modifiesOnLoop-noinfer.smt2
  3120   13698    13698    13698       2    499     23313    3860  vcc-havoc/havoc-bench_dlist_insert_head.12.ua_wcscpy.smt2
     8   12440    12440    12440       2    798     59445    5221  simplify/javafe.ast.StandardPrettyPrint.322.smt2
  2770    5829     5829     5829       2    451      9860    2370  sledgehammer/Hoare/z3.850818.smt2
    91    3805     3805     3805       2    710    105365     253  simplify2/front_end_suite/javafe.ast.ImportDeclVec.015.smt2
    23    3288     3288     3288       2    537     34087     622  boogie/AssignToRepField_AssignToRepField.N.smt2
    20    3246     3246     3246       2    528     27423    1231  simplify/javafe.ast.NewInstanceExpr.271.smt2
    25    3157     3157     3157       2    521     27381    1326  simplify/javafe.ast.UnaryExpr.424.smt2
    32    2020     2020     2020       2    594     48908    2397  boogie/Interval_Cell.Shift_System.Int32.smt2
   229    2019     2019     2019       2    607     48695     300  spec_sharp/textbook-Sum.dll.6.C.TransformQuant_System.Int32.
    18    1531     1531     1531       2    463     31576    1588  boogie/Cast_Cast.R_System.Object_System.Int32.smt2
   136    1300     1300     1300       2    447     38593    1667  simplify/javafe.ast.LexicalPragmaVec.219.smt2
     8    1240     1240     1240       2    339     10035    1232  simplify2/front_end_suite/javafe.parser.Parse.005.smt2
   141     766      766      766       2    948    278420    2297  simplify2/front_end_suite/javafe.tc.TypeSigVec.005.smt2
    47     191      192        4       3    725    175956    2459  simplify2/front_end_suite/javafe.test.SuperlinksTest.004.smt
     0       0        0        0       1     13        78    2487  2019-Zohar-ic/combined/int_check_bvsle_bvashr0_rtl.smt2
     0       0        0        0       1   1026    198014      40  simplify2/front_end_suite/javafe.ast.AmbiguousVariableAccess
     0       0        0        0       1    929    153258      34  simplify2/front_end_suite/javafe.ast.ForStmt.009.smt2
     0       0        0        0       1   1047    199544      35  simplify2/front_end_suite/javafe.ast.ParenExpr.006.smt2
     0       0        0        0       1     13        78    2493  2019-Zohar-ic/combined/int_check_bvugt_bvashr0_ltr_inv_g.smt
     0       0        0        0       1    636     53077      37  simplify2/front_end_suite/javafe.ast.CompilationUnit.001.smt
     0       0        0        0       1   1031    197919      35  simplify2/front_end_suite/javafe.ast.VariableAccess.001.smt2
     0       0        0        0       1     14        91    2491  2019-Preiner/combined/f2_rw343.smt2
     0       0        0        0       1    464     28859      33  simplify2/front_end_suite/javafe.ast.ConstructorDecl.007.smt
     0       0        0        0       1   1028    197181      35  simplify2/front_end_suite/javafe.ast.LabelStmt.011.smt2
     0       0        0        0       1   1044    201583      36  simplify2/front_end_suite/javafe.ast.SuperObjectDesignator.0
     0       0        0        0       1   1022    196143      37  simplify2/front_end_suite/javafe.parser.test.TestLex.030.smt
     0       0        0        0       1    757    109058      39  simplify2/front_end_suite/javafe.ast.DefaultVisitor.028.smt2
     0       0        0        0       1    477     28725      37  simplify2/front_end_suite/javafe.ast.MethodDecl.005.smt2
     0       0        0        0       1   1026    198014      41  simplify2/front_end_suite/javafe.ast.ThrowStmt.004.smt2

=== how many observations would a per-round cap of N have bound? ===
(bound == last_new_lemmas > N on the largest round we can see)
  cap=    1: binds 16/31
  cap=    8: binds 15/31
  cap=   16: binds 15/31
  cap=   32: binds 15/31
  cap=   64: binds 15/31
  cap=  128: binds 15/31
  cap=  256: binds 15/31
  cap=  512: binds 15/31
  cap= 1024: binds 14/31
  cap= 4096: binds 5/31
