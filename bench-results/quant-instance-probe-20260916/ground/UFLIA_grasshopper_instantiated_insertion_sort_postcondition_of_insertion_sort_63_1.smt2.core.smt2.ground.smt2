(set-info :smt-lib-version 2.6)
(set-logic QF_UFLIA)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/sls/sls_insertion_sort.spl:63:1-2:A postcondition of procedure insertion_sort might not hold at this return point
  tests/spl/sls/sls_insertion_sort.spl:32:10-26:Related location: This is the postcondition that might not hold
  |)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort Loc 0)
(declare-sort SetLoc 0)
(declare-sort SetInt 0)
(declare-sort FldBool 0)
(declare-sort FldLoc 0)
(declare-sort FldInt 0)
(declare-fun null$0 () Loc)
(declare-fun read$0 (FldInt Loc) Int)
(declare-fun read$1 (FldLoc Loc) Loc)
(declare-fun ep$0 (FldLoc SetLoc Loc) Loc)
(declare-fun emptyset$0 () SetLoc)
(declare-fun setenum$0 (Loc) SetLoc)
(declare-fun union$0 (SetLoc SetLoc) SetLoc)
(declare-fun intersection$0 (SetLoc SetLoc) SetLoc)
(declare-fun setminus$0 (SetLoc SetLoc) SetLoc)
(declare-fun Btwn$0 (FldLoc Loc Loc Loc) Bool)
(declare-fun Frame$0 (SetLoc SetLoc FldInt FldInt) Bool)
(declare-fun Frame$1 (SetLoc SetLoc FldLoc FldLoc) Bool)
(declare-fun in$0 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun Axiom_3$0 () Bool)
(declare-fun Axiom_4$0 () Bool)
(declare-fun Axiom_5$0 () Bool)
(declare-fun Axiom_6$0 () Bool)
(declare-fun Axiom_7$0 () Bool)
(declare-fun Axiom_8$0 () Bool)
(declare-fun Axiom_9$0 () Bool)
(declare-fun Axiom_10$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_1$0 () SetLoc)
(declare-fun FP_2$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_1$0 () SetLoc)
(declare-fun FP_Caller_final_1$0 () SetLoc)
(declare-fun data$0 () FldInt)
(declare-fun data_1$0 () FldInt)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun lslseg_domain$0 (FldInt FldLoc Loc Loc Int) SetLoc)
(declare-fun lslseg_struct$0 (SetLoc FldInt FldLoc Loc Loc Int) Bool)
(declare-fun lst$0 () Loc)
(declare-fun lst_1$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun prv_2$0 () Loc)
(declare-fun prv_3$0 () Loc)
(declare-fun sk_?X_10$0 () SetLoc)
(declare-fun sk_?X_11$0 () SetLoc)
(declare-fun sk_?X_12$0 () SetLoc)
(declare-fun sk_?X_13$0 () SetLoc)
(declare-fun sk_?X_14$0 () SetLoc)
(declare-fun sk_?X_15$0 () SetLoc)
(declare-fun sk_?X_16$0 () SetLoc)
(declare-fun sk_?X_17$0 () SetLoc)
(declare-fun sk_?X_18$0 () SetLoc)
(declare-fun sk_?X_19$0 () SetLoc)
(declare-fun sk_?X_20$0 () SetLoc)
(declare-fun sk_?X_21$0 () SetLoc)
(declare-fun sk_?X_22$0 () SetLoc)
(declare-fun sk_?X_23$0 () SetLoc)
(declare-fun sk_?X_24$0 () SetLoc)
(declare-fun sk_?X_25$0 () SetLoc)
(declare-fun sk_?X_26$0 () SetLoc)
(declare-fun sk_?X_27$0 () SetLoc)
(declare-fun sk_?X_28$0 () SetLoc)
(declare-fun sk_?X_29$0 () SetLoc)
(declare-fun sk_l1_1$0 () Loc)
(declare-fun sk_l2_1$0 () Loc)
(declare-fun slseg_domain$0 (FldInt FldLoc Loc Loc) SetLoc)
(declare-fun slseg_struct$0 (SetLoc FldInt FldLoc Loc Loc) Bool)
(declare-fun srt_2$0 () Loc)
(declare-fun srt_3$0 () Loc)
(declare-fun ulseg_domain$0 (FldInt FldLoc Loc Loc Int) SetLoc)
(declare-fun ulseg_struct$0 (SetLoc FldInt FldLoc Loc Loc Int) Bool)













(assert (= (read$1 next$0 null$0) null$0))
(assert (= prv_2$0 null$0))
(assert (= srt_3$0 null$0))
(assert (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)))
(assert (= sk_?X_13$0
  (lslseg_domain$0 data_1$0 next$0 lst_1$0 prv_3$0 (read$0 data_1$0 prv_3$0))))
(assert (= sk_?X_15$0 sk_?X_14$0))
(assert (= sk_?X_17$0
  (ulseg_domain$0 data_1$0 next$0 srt_3$0 null$0 (read$0 data_1$0 prv_3$0))))
(assert (or
    (and (= (read$1 next$0 prv_3$0) srt_3$0) (= emptyset$0 emptyset$0)
         (= emptyset$0 (intersection$0 sk_?X_13$0 sk_?X_15$0))
         (= emptyset$0 (intersection$0 sk_?X_16$0 sk_?X_17$0))
         (= sk_?X_18$0
           (union$0 (intersection$0 Alloc$0 FP_1$0)
             (setminus$0 Alloc$0 Alloc$0)))
         (lslseg_struct$0 sk_?X_13$0 data_1$0 next$0 lst_1$0 prv_3$0
           (read$0 data_1$0 prv_3$0))
         (ulseg_struct$0 sk_?X_17$0 data_1$0 next$0 srt_3$0 null$0
           (read$0 data_1$0 prv_3$0)))
    (and (= emptyset$0 emptyset$0)
         (= emptyset$0 (intersection$0 sk_?X_10$0 sk_?X_11$0))
         (= prv_3$0 null$0)
         (= sk_?X_12$0
           (union$0 (intersection$0 Alloc$0 FP_1$0)
             (setminus$0 Alloc$0 Alloc$0)))
         (= srt_3$0 lst_1$0)
         (lseg_struct$0 sk_?X_11$0 next$0 lst_1$0 null$0))))
(assert (= sk_?X_26$0 (lseg_domain$0 next$0 lst$0 null$0)))
(assert (= sk_?X_28$0 FP$0))
(assert (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)))
(assert (= sk_?X_29$0
  (union$0 (intersection$0 Alloc$0 FP$0) (setminus$0 Alloc$0 Alloc$0))))



(assert (or (Btwn$0 next$0 lst$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_28$0 next$0 lst$0 null$0))))
(assert (or (and (Btwn$0 next$0 lst_1$0 prv_3$0 prv_3$0) Axiom_7$0 Axiom_6$0)
    (not
         (lslseg_struct$0 sk_?X_13$0 data_1$0 next$0 lst_1$0 prv_3$0
           (read$0 data_1$0 prv_3$0)))))
(assert (= lst_1$0 lst$0))
(assert (= srt_2$0 lst$0))
(assert (= sk_?X_10$0 emptyset$0))
(assert (= sk_?X_14$0 (setenum$0 prv_3$0)))
(assert (= sk_?X_16$0 (union$0 sk_?X_13$0 sk_?X_15$0)))
(assert (= sk_?X_18$0 (union$0 sk_?X_16$0 sk_?X_17$0)))
(assert (= sk_?X_25$0 (union$0 sk_?X_27$0 sk_?X_26$0)))
(assert (= sk_?X_27$0 emptyset$0))
(assert (or
    (and (= (read$1 next$0 prv_2$0) srt_2$0) (= emptyset$0 emptyset$0)
         (= emptyset$0 (intersection$0 sk_?X_21$0 sk_?X_20$0))
         (= emptyset$0 (intersection$0 sk_?X_24$0 sk_?X_22$0))
         (= sk_?X_19$0 FP_1$0)
         (lslseg_struct$0 sk_?X_24$0 data$0 next$0 lst$0 prv_2$0
           (read$0 data$0 prv_2$0))
         (ulseg_struct$0 sk_?X_20$0 data$0 next$0 srt_2$0 null$0
           (read$0 data$0 prv_2$0)))
    (and (= emptyset$0 emptyset$0)
         (= emptyset$0 (intersection$0 sk_?X_27$0 sk_?X_26$0))
         (= prv_2$0 null$0) (= sk_?X_25$0 FP_1$0) (= srt_2$0 lst$0)
         (lseg_struct$0 sk_?X_26$0 next$0 lst$0 null$0))))
(assert (= sk_?X_28$0 (lseg_domain$0 next$0 lst$0 null$0)))
(assert (lseg_struct$0 sk_?X_28$0 next$0 lst$0 null$0))
(assert (or
    (and (in$0 sk_l2_1$0 sk_?X_29$0)
         (not (in$0 sk_l2_1$0 (slseg_domain$0 data_1$0 next$0 lst$0 null$0))))
    (and (in$0 sk_l2_1$0 (slseg_domain$0 data_1$0 next$0 lst$0 null$0))
         (not (in$0 sk_l2_1$0 sk_?X_29$0)))
    (not (Btwn$0 next$0 lst$0 null$0 null$0))
    (and (Btwn$0 next$0 sk_l1_1$0 sk_l2_1$0 null$0)
         (in$0 sk_l1_1$0 sk_?X_29$0) (in$0 sk_l2_1$0 sk_?X_29$0)
         (not (<= (read$0 data_1$0 sk_l1_1$0) (read$0 data_1$0 sk_l2_1$0))))))




(assert (or (not (Btwn$0 next$0 sk_l2_1$0 prv_3$0 sk_l2_1$0)) (= sk_l2_1$0 prv_3$0)))
(assert (or (not (Btwn$0 next$0 lst$0 prv_3$0 sk_l2_1$0)) (not (Btwn$0 next$0 lst$0 sk_l2_1$0 prv_3$0)) (not (or (not (Btwn$0 next$0 lst$0 sk_l2_1$0 sk_l2_1$0)) (not (Btwn$0 next$0 sk_l2_1$0 prv_3$0 sk_l2_1$0))))))
(assert (or (not (in$0 sk_l2_1$0 sk_?X_13$0)) (not Axiom_6$0) (not (Btwn$0 next$0 sk_l1_1$0 sk_l2_1$0 prv_3$0)) (not (in$0 sk_l1_1$0 sk_?X_13$0)) (>= (+ (read$0 data_1$0 sk_l2_1$0) (* (- 1) (read$0 data_1$0 sk_l1_1$0))) 0)))
(assert (or (not (Btwn$0 next$0 lst$0 sk_l2_1$0 prv_3$0)) (not (Btwn$0 next$0 lst$0 sk_l1_1$0 sk_l2_1$0)) (not (or (not (Btwn$0 next$0 lst$0 sk_l1_1$0 prv_3$0)) (not (Btwn$0 next$0 sk_l1_1$0 sk_l2_1$0 prv_3$0))))))
(assert (or (not (Btwn$0 next$0 lst$0 sk_l1_1$0 null$0)) (not (Btwn$0 next$0 sk_l1_1$0 sk_l2_1$0 null$0)) (not (or (not (Btwn$0 next$0 lst$0 sk_l1_1$0 sk_l2_1$0)) (not (Btwn$0 next$0 lst$0 sk_l2_1$0 null$0))))))
(assert (or (not (or (not (Btwn$0 next$0 lst$0 sk_l1_1$0 null$0)) (not (in$0 sk_l1_1$0 (lseg_domain$0 next$0 lst$0 null$0))) (= sk_l1_1$0 null$0))) (not (or (not (or (= sk_l1_1$0 null$0) (not (Btwn$0 next$0 lst$0 sk_l1_1$0 null$0)))) (in$0 sk_l1_1$0 (lseg_domain$0 next$0 lst$0 null$0))))))
(assert (or (not (or (not (Btwn$0 next$0 lst_1$0 sk_l2_1$0 prv_3$0)) (not (in$0 sk_l2_1$0 (lslseg_domain$0 data_1$0 next$0 lst_1$0 prv_3$0 (read$0 data_1$0 prv_3$0)))) (= sk_l2_1$0 prv_3$0))) (not (or (not (or (= sk_l2_1$0 prv_3$0) (not (Btwn$0 next$0 lst_1$0 sk_l2_1$0 prv_3$0)))) (in$0 sk_l2_1$0 (lslseg_domain$0 data_1$0 next$0 lst_1$0 prv_3$0 (read$0 data_1$0 prv_3$0)))))))
(assert (or (not (or (not (in$0 sk_l2_1$0 (union$0 sk_?X_13$0 sk_?X_14$0))) (not (or (in$0 sk_l2_1$0 sk_?X_13$0) (in$0 sk_l2_1$0 sk_?X_14$0))))) (not (or (in$0 sk_l2_1$0 sk_?X_13$0) (in$0 sk_l2_1$0 sk_?X_14$0) (in$0 sk_l2_1$0 (union$0 sk_?X_13$0 sk_?X_14$0))))))
(assert (or (not (or (not (Btwn$0 next$0 srt_3$0 sk_l2_1$0 null$0)) (not (in$0 sk_l2_1$0 (ulseg_domain$0 data_1$0 next$0 srt_3$0 null$0 (read$0 data_1$0 prv_3$0)))) (= sk_l2_1$0 null$0))) (not (or (not (or (= sk_l2_1$0 null$0) (not (Btwn$0 next$0 srt_3$0 sk_l2_1$0 null$0)))) (in$0 sk_l2_1$0 (ulseg_domain$0 data_1$0 next$0 srt_3$0 null$0 (read$0 data_1$0 prv_3$0)))))))
(assert (or (not (or (not (in$0 sk_l2_1$0 (union$0 sk_?X_16$0 sk_?X_17$0))) (not (or (in$0 sk_l2_1$0 sk_?X_16$0) (in$0 sk_l2_1$0 sk_?X_17$0))))) (not (or (in$0 sk_l2_1$0 sk_?X_16$0) (in$0 sk_l2_1$0 sk_?X_17$0) (in$0 sk_l2_1$0 (union$0 sk_?X_16$0 sk_?X_17$0))))))
(assert (or (not (or (not (in$0 sk_l2_1$0 (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0)))) (not (or (in$0 sk_l2_1$0 (intersection$0 Alloc$0 FP_1$0)) (in$0 sk_l2_1$0 (setminus$0 Alloc$0 Alloc$0)))))) (not (or (in$0 sk_l2_1$0 (intersection$0 Alloc$0 FP_1$0)) (in$0 sk_l2_1$0 (setminus$0 Alloc$0 Alloc$0)) (in$0 sk_l2_1$0 (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0)))))))
(assert (or (not (or (not (in$0 sk_l2_1$0 Alloc$0)) (not (in$0 sk_l2_1$0 FP_1$0)) (not (in$0 sk_l2_1$0 (intersection$0 Alloc$0 FP_1$0))))) (not (or (not (or (not (in$0 sk_l2_1$0 Alloc$0)) (not (in$0 sk_l2_1$0 FP_1$0)))) (in$0 sk_l2_1$0 (intersection$0 Alloc$0 FP_1$0))))))
(assert (or (not (or (not (in$0 sk_l2_1$0 (union$0 sk_?X_10$0 sk_?X_26$0))) (not (or (in$0 sk_l2_1$0 sk_?X_10$0) (in$0 sk_l2_1$0 sk_?X_26$0))))) (not (or (in$0 sk_l2_1$0 sk_?X_10$0) (in$0 sk_l2_1$0 sk_?X_26$0) (in$0 sk_l2_1$0 (union$0 sk_?X_10$0 sk_?X_26$0))))))
(assert (or (not (or (not (= sk_l2_1$0 prv_3$0)) (not (in$0 sk_l2_1$0 (setenum$0 prv_3$0))))) (not (or (= sk_l2_1$0 prv_3$0) (in$0 sk_l2_1$0 (setenum$0 prv_3$0))))))
(assert (or (not (or (not (= sk_l1_1$0 prv_3$0)) (not (in$0 sk_l1_1$0 (setenum$0 prv_3$0))))) (not (or (= sk_l1_1$0 prv_3$0) (in$0 sk_l1_1$0 (setenum$0 prv_3$0))))))
(assert (or (not Axiom_7$0) (not (in$0 sk_l1_1$0 sk_?X_13$0)) (<= (+ (read$0 data_1$0 sk_l1_1$0) (* (- 1) (read$0 data_1$0 prv_3$0))) 0)))
(assert (or (not (or (not (in$0 sk_l1_1$0 (union$0 sk_?X_13$0 sk_?X_14$0))) (not (or (in$0 sk_l1_1$0 sk_?X_13$0) (in$0 sk_l1_1$0 sk_?X_14$0))))) (not (or (in$0 sk_l1_1$0 sk_?X_13$0) (in$0 sk_l1_1$0 sk_?X_14$0) (in$0 sk_l1_1$0 (union$0 sk_?X_13$0 sk_?X_14$0))))))
(assert (or (not (or (not (in$0 sk_l1_1$0 (union$0 sk_?X_16$0 sk_?X_17$0))) (not (or (in$0 sk_l1_1$0 sk_?X_16$0) (in$0 sk_l1_1$0 sk_?X_17$0))))) (not (or (in$0 sk_l1_1$0 sk_?X_16$0) (in$0 sk_l1_1$0 sk_?X_17$0) (in$0 sk_l1_1$0 (union$0 sk_?X_16$0 sk_?X_17$0))))))
(assert (or (not (or (not (in$0 sk_l1_1$0 (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0)))) (not (or (in$0 sk_l1_1$0 (intersection$0 Alloc$0 FP_1$0)) (in$0 sk_l1_1$0 (setminus$0 Alloc$0 Alloc$0)))))) (not (or (in$0 sk_l1_1$0 (intersection$0 Alloc$0 FP_1$0)) (in$0 sk_l1_1$0 (setminus$0 Alloc$0 Alloc$0)) (in$0 sk_l1_1$0 (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0)))))))
(assert (or (not (or (not (in$0 sk_l1_1$0 Alloc$0)) (not (in$0 sk_l1_1$0 FP_1$0)) (not (in$0 sk_l1_1$0 (intersection$0 Alloc$0 FP_1$0))))) (not (or (not (or (not (in$0 sk_l1_1$0 Alloc$0)) (not (in$0 sk_l1_1$0 FP_1$0)))) (in$0 sk_l1_1$0 (intersection$0 Alloc$0 FP_1$0))))))
(assert (or (not (or (not (in$0 sk_l1_1$0 (union$0 sk_?X_10$0 sk_?X_26$0))) (not (or (in$0 sk_l1_1$0 sk_?X_10$0) (in$0 sk_l1_1$0 sk_?X_26$0))))) (not (or (in$0 sk_l1_1$0 sk_?X_10$0) (in$0 sk_l1_1$0 sk_?X_26$0) (in$0 sk_l1_1$0 (union$0 sk_?X_10$0 sk_?X_26$0))))))
(assert (or (not (or (not (in$0 sk_l1_1$0 Alloc$0)) (not (in$0 sk_l1_1$0 sk_?X_26$0)) (not (in$0 sk_l1_1$0 (intersection$0 Alloc$0 sk_?X_26$0))))) (not (or (not (or (not (in$0 sk_l1_1$0 Alloc$0)) (not (in$0 sk_l1_1$0 sk_?X_26$0)))) (in$0 sk_l1_1$0 (intersection$0 Alloc$0 sk_?X_26$0))))))
(assert (or (not (or (not (in$0 sk_l1_1$0 (union$0 (intersection$0 Alloc$0 FP$0) (setminus$0 Alloc$0 Alloc$0)))) (not (or (in$0 sk_l1_1$0 (intersection$0 Alloc$0 FP$0)) (in$0 sk_l1_1$0 (setminus$0 Alloc$0 Alloc$0)))))) (not (or (in$0 sk_l1_1$0 (intersection$0 Alloc$0 FP$0)) (in$0 sk_l1_1$0 (setminus$0 Alloc$0 Alloc$0)) (in$0 sk_l1_1$0 (union$0 (intersection$0 Alloc$0 FP$0) (setminus$0 Alloc$0 Alloc$0)))))))
(assert (or (not (or (not (Btwn$0 next$0 srt_3$0 sk_l1_1$0 null$0)) (not (in$0 sk_l1_1$0 (ulseg_domain$0 data_1$0 next$0 srt_3$0 null$0 (read$0 data_1$0 prv_3$0)))) (= sk_l1_1$0 null$0))) (not (or (not (or (= sk_l1_1$0 null$0) (not (Btwn$0 next$0 srt_3$0 sk_l1_1$0 null$0)))) (in$0 sk_l1_1$0 (ulseg_domain$0 data_1$0 next$0 srt_3$0 null$0 (read$0 data_1$0 prv_3$0)))))))
(assert (or (not (Btwn$0 next$0 null$0 sk_l1_1$0 null$0)) (not (Btwn$0 next$0 sk_l1_1$0 sk_l2_1$0 null$0)) (not (or (not (Btwn$0 next$0 null$0 sk_l1_1$0 sk_l2_1$0)) (not (Btwn$0 next$0 null$0 sk_l2_1$0 null$0))))))
(assert (or (not (or (not (in$0 sk_l2_1$0 (union$0 FP_Caller$0 Alloc$0))) (not (or (in$0 sk_l2_1$0 FP_Caller$0) (in$0 sk_l2_1$0 Alloc$0))))) (not (or (in$0 sk_l2_1$0 (union$0 FP_Caller$0 Alloc$0)) (in$0 sk_l2_1$0 FP_Caller$0) (in$0 sk_l2_1$0 Alloc$0)))))
(assert (or (not (or (not (in$0 sk_l2_1$0 (union$0 sk_?X_26$0 FP_Caller$0))) (not (or (in$0 sk_l2_1$0 FP_Caller$0) (in$0 sk_l2_1$0 sk_?X_26$0))))) (not (or (in$0 sk_l2_1$0 FP_Caller$0) (in$0 sk_l2_1$0 (union$0 sk_?X_26$0 FP_Caller$0)) (in$0 sk_l2_1$0 sk_?X_26$0)))))
(assert (or (not (Btwn$0 next$0 null$0 sk_l2_1$0 null$0)) (= null$0 sk_l2_1$0)))
(assert (or (not (or (not (in$0 sk_l2_1$0 (union$0 (intersection$0 Alloc$0 FP$0) (setminus$0 Alloc$0 Alloc$0)))) (not (or (in$0 sk_l2_1$0 (intersection$0 Alloc$0 FP$0)) (in$0 sk_l2_1$0 (setminus$0 Alloc$0 Alloc$0)))))) (not (or (in$0 sk_l2_1$0 (intersection$0 Alloc$0 FP$0)) (in$0 sk_l2_1$0 (setminus$0 Alloc$0 Alloc$0)) (in$0 sk_l2_1$0 (union$0 (intersection$0 Alloc$0 FP$0) (setminus$0 Alloc$0 Alloc$0)))))))
(assert (or (not (or (not (in$0 sk_l2_1$0 Alloc$0)) (not (in$0 sk_l2_1$0 sk_?X_26$0)) (not (in$0 sk_l2_1$0 (intersection$0 Alloc$0 sk_?X_26$0))))) (not (or (not (or (not (in$0 sk_l2_1$0 Alloc$0)) (not (in$0 sk_l2_1$0 sk_?X_26$0)))) (in$0 sk_l2_1$0 (intersection$0 Alloc$0 sk_?X_26$0))))))
(assert (or (not (or (not (Btwn$0 next$0 lst$0 sk_l2_1$0 null$0)) (not (in$0 sk_l2_1$0 (lseg_domain$0 next$0 lst$0 null$0))) (= sk_l2_1$0 null$0))) (not (or (not (or (= sk_l2_1$0 null$0) (not (Btwn$0 next$0 lst$0 sk_l2_1$0 null$0)))) (in$0 sk_l2_1$0 (lseg_domain$0 next$0 lst$0 null$0))))))
(assert (or (not (or (not (Btwn$0 next$0 lst$0 sk_l2_1$0 null$0)) (not (in$0 sk_l2_1$0 (slseg_domain$0 data_1$0 next$0 lst$0 null$0))) (= sk_l2_1$0 null$0))) (not (or (not (or (= sk_l2_1$0 null$0) (not (Btwn$0 next$0 lst$0 sk_l2_1$0 null$0)))) (in$0 sk_l2_1$0 (slseg_domain$0 data_1$0 next$0 lst$0 null$0))))))
(check-sat)
