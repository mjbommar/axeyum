(set-info :smt-lib-version 2.6)
(set-logic QF_UFLIA)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/sls/sls_strand_sort.spl:60:6-18:Possible heap access through null or dangling reference
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
(declare-fun write$0 (FldLoc Loc Loc) FldLoc)
(declare-fun ep$0 (FldLoc SetLoc Loc) Loc)
(declare-fun emptyset$0 () SetLoc)
(declare-fun setenum$0 (Loc) SetLoc)
(declare-fun union$0 (SetLoc SetLoc) SetLoc)
(declare-fun intersection$0 (SetLoc SetLoc) SetLoc)
(declare-fun setminus$0 (SetLoc SetLoc) SetLoc)
(declare-fun Btwn$0 (FldLoc Loc Loc Loc) Bool)
(declare-fun in$0 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun Axiom_54$0 () Bool)
(declare-fun Axiom_55$0 () Bool)
(declare-fun Axiom_56$0 () Bool)
(declare-fun Axiom_57$0 () Bool)
(declare-fun Axiom_58$0 () Bool)
(declare-fun Axiom_59$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_2$0 () SetLoc)
(declare-fun a_3$0 () Loc)
(declare-fun a_init$0 () Loc)
(declare-fun b_3$0 () Loc)
(declare-fun b_init$0 () Loc)
(declare-fun data$0 () FldInt)
(declare-fun last_4$0 () Loc)
(declare-fun last_5$0 () Loc)
(declare-fun last_init$0 () Loc)
(declare-fun lslseg_domain$0 (FldInt FldLoc Loc Loc Int) SetLoc)
(declare-fun lslseg_struct$0 (SetLoc FldInt FldLoc Loc Loc Int) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun next_2$0 () FldLoc)
(declare-fun res_9$0 () Loc)
(declare-fun res_init$0 () Loc)
(declare-fun sk_?X_113$0 () SetLoc)
(declare-fun sk_?X_114$0 () SetLoc)
(declare-fun sk_?X_115$0 () SetLoc)
(declare-fun sk_?X_116$0 () SetLoc)
(declare-fun sk_?X_117$0 () SetLoc)
(declare-fun sk_?X_118$0 () SetLoc)
(declare-fun sk_?X_119$0 () SetLoc)
(declare-fun sk_?X_120$0 () SetLoc)
(declare-fun sk_?X_121$0 () SetLoc)
(declare-fun sk_?X_122$0 () SetLoc)
(declare-fun sk_?X_123$0 () SetLoc)
(declare-fun t_19$0 () Loc)
(declare-fun t_20$0 () Loc)
(declare-fun t_21$0 () Loc)
(declare-fun uslseg_domain$0 (FldInt FldLoc Loc Loc Int) SetLoc)
(declare-fun uslseg_struct$0 (SetLoc FldInt FldLoc Loc Loc Int) Bool)


(assert (or (and (Btwn$0 next$0 a_init$0 null$0 null$0) Axiom_55$0 Axiom_54$0)
    (not
         (uslseg_struct$0 sk_?X_118$0 data$0 next$0 a_init$0 null$0
           (read$0 data$0 last_init$0)))))
(assert (= sk_?X_113$0 (union$0 sk_?X_122$0 sk_?X_115$0)))
(assert (= sk_?X_115$0 (union$0 sk_?X_117$0 sk_?X_116$0)))
(assert (= sk_?X_117$0 (union$0 sk_?X_119$0 sk_?X_118$0)))
(assert (or
    (and (= (read$1 next$0 last_init$0) a_init$0) (= emptyset$0 emptyset$0)
         (= emptyset$0 (intersection$0 sk_?X_117$0 sk_?X_116$0))
         (= emptyset$0 (intersection$0 sk_?X_119$0 sk_?X_118$0))
         (= emptyset$0 (intersection$0 sk_?X_122$0 sk_?X_115$0))
         (= sk_?X_113$0 FP$0)
         (lslseg_struct$0 sk_?X_119$0 data$0 next$0 res_init$0 last_init$0
           (read$0 data$0 last_init$0))
         (uslseg_struct$0 sk_?X_116$0 data$0 next$0 b_init$0 null$0
           (read$0 data$0 last_init$0))
         (uslseg_struct$0 sk_?X_118$0 data$0 next$0 a_init$0 null$0
           (read$0 data$0 last_init$0)))
    (and (= (read$1 next$0 last_init$0) b_init$0) (= emptyset$0 emptyset$0)
         (= emptyset$0 (intersection$0 sk_?X_117$0 sk_?X_116$0))
         (= emptyset$0 (intersection$0 sk_?X_119$0 sk_?X_118$0))
         (= emptyset$0 (intersection$0 sk_?X_120$0 sk_?X_115$0))
         (= sk_?X_114$0 FP$0)
         (lslseg_struct$0 sk_?X_119$0 data$0 next$0 res_init$0 last_init$0
           (read$0 data$0 last_init$0))
         (uslseg_struct$0 sk_?X_116$0 data$0 next$0 b_init$0 null$0
           (read$0 data$0 last_init$0))
         (uslseg_struct$0 sk_?X_118$0 data$0 next$0 a_init$0 null$0
           (read$0 data$0 last_init$0)))))

(assert (= a_3$0 a_init$0))
(assert (= sk_?X_114$0 (union$0 sk_?X_120$0 sk_?X_115$0)))
(assert (= sk_?X_118$0
  (uslseg_domain$0 data$0 next$0 a_init$0 null$0 (read$0 data$0 last_init$0))))
(assert (not (= a_3$0 null$0)))
(assert (not (in$0 a_3$0 FP$0)))





(assert (or (not (Btwn$0 next$0 last_init$0 a_init$0 a_init$0)) (not (Btwn$0 next$0 last_init$0 a_init$0 a_init$0)) (not (or (not (Btwn$0 next$0 last_init$0 a_init$0 a_init$0)) (not (Btwn$0 next$0 a_init$0 a_init$0 a_init$0))))))
(assert (Btwn$0 next$0 last_init$0 (read$1 next$0 last_init$0) (read$1 next$0 last_init$0)))
(assert (or (not (or (not (in$0 a_init$0 (union$0 sk_?X_122$0 (union$0 sk_?X_117$0 sk_?X_116$0)))) (not (or (in$0 a_init$0 sk_?X_122$0) (in$0 a_init$0 (union$0 sk_?X_117$0 sk_?X_116$0)))))) (not (or (in$0 a_init$0 (union$0 sk_?X_122$0 (union$0 sk_?X_117$0 sk_?X_116$0))) (in$0 a_init$0 sk_?X_122$0) (in$0 a_init$0 (union$0 sk_?X_117$0 sk_?X_116$0))))))
(assert (or (not (Btwn$0 next$0 last_4$0 a_init$0 a_init$0)) (not (Btwn$0 next$0 last_4$0 a_init$0 a_init$0)) (not (or (not (Btwn$0 next$0 last_4$0 a_init$0 a_init$0)) (not (Btwn$0 next$0 a_init$0 a_init$0 a_init$0))))))
(assert (or (not (Btwn$0 next$0 last_4$0 a_init$0 last_4$0)) (= last_4$0 a_init$0)))
(assert (or (not (Btwn$0 (write$0 next$0 last_4$0 a_3$0) last_4$0 a_init$0 a_init$0)) (not (Btwn$0 (write$0 next$0 last_4$0 a_3$0) last_4$0 a_init$0 a_init$0)) (not (or (not (Btwn$0 (write$0 next$0 last_4$0 a_3$0) last_4$0 a_init$0 a_init$0)) (not (Btwn$0 (write$0 next$0 last_4$0 a_3$0) a_init$0 a_init$0 a_init$0))))))
(assert (Btwn$0 (write$0 next$0 last_4$0 a_3$0) last_4$0 (read$1 (write$0 next$0 last_4$0 a_3$0) last_4$0) (read$1 (write$0 next$0 last_4$0 a_3$0) last_4$0)))
(assert (= (read$1 (write$0 next$0 last_4$0 a_init$0) last_4$0) a_init$0))
(assert (or (Btwn$0 next$0 a_init$0 null$0 a_init$0) (not (Btwn$0 next$0 a_init$0 null$0 null$0)) (Btwn$0 next$0 a_init$0 a_init$0 null$0) (not (Btwn$0 next$0 a_init$0 a_init$0 a_init$0))))
(assert (or (not (Btwn$0 (write$0 next$0 last_4$0 a_3$0) a_init$0 null$0 a_init$0)) (= a_init$0 null$0)))
(assert (or (not (or (not (Btwn$0 next$0 a_init$0 a_init$0 null$0)) (not (in$0 a_init$0 (uslseg_domain$0 data$0 next$0 a_init$0 null$0 (read$0 data$0 last_init$0)))) (= a_init$0 null$0))) (not (or (not (or (not (Btwn$0 next$0 a_init$0 a_init$0 null$0)) (= a_init$0 null$0))) (in$0 a_init$0 (uslseg_domain$0 data$0 next$0 a_init$0 null$0 (read$0 data$0 last_init$0)))))))
(assert (or (not (or (not (in$0 a_init$0 (union$0 sk_?X_119$0 (uslseg_domain$0 data$0 next$0 a_init$0 null$0 (read$0 data$0 last_init$0))))) (not (or (in$0 a_init$0 sk_?X_119$0) (in$0 a_init$0 (uslseg_domain$0 data$0 next$0 a_init$0 null$0 (read$0 data$0 last_init$0))))))) (not (or (in$0 a_init$0 (union$0 sk_?X_119$0 (uslseg_domain$0 data$0 next$0 a_init$0 null$0 (read$0 data$0 last_init$0)))) (in$0 a_init$0 sk_?X_119$0) (in$0 a_init$0 (uslseg_domain$0 data$0 next$0 a_init$0 null$0 (read$0 data$0 last_init$0)))))))
(assert (or (not (or (not (in$0 a_init$0 (union$0 (union$0 sk_?X_119$0 sk_?X_118$0) sk_?X_116$0))) (not (or (in$0 a_init$0 (union$0 sk_?X_119$0 sk_?X_118$0)) (in$0 a_init$0 sk_?X_116$0))))) (not (or (in$0 a_init$0 (union$0 (union$0 sk_?X_119$0 sk_?X_118$0) sk_?X_116$0)) (in$0 a_init$0 (union$0 sk_?X_119$0 sk_?X_118$0)) (in$0 a_init$0 sk_?X_116$0)))))
(assert (or (not (or (not (in$0 a_init$0 (union$0 sk_?X_120$0 (union$0 sk_?X_117$0 sk_?X_116$0)))) (not (or (in$0 a_init$0 sk_?X_120$0) (in$0 a_init$0 (union$0 sk_?X_117$0 sk_?X_116$0)))))) (not (or (in$0 a_init$0 (union$0 sk_?X_120$0 (union$0 sk_?X_117$0 sk_?X_116$0))) (in$0 a_init$0 sk_?X_120$0) (in$0 a_init$0 (union$0 sk_?X_117$0 sk_?X_116$0))))))
(check-sat)
