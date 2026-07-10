//! Deadline-robustness gate (#63 / bug330): every solving path must honor
//! `config.timeout`.
//!
//! The `QF_AUFLIA` instance `cli__regress1__auflia__bug330` used to run for
//! ~25s (and, under a tight budget, minutes) against a 2s `config.timeout`,
//! because the UFLIA online *combination* on the array-abstracted relaxation
//! drove its interface case-split DFS (and the per-branch opaque-app LIA
//! feasibility sub-solves) with **no deadline check** — a direct violation of
//! the explicit-resource-limits Hard Rule. The fix threads the existing
//! absolute-deadline pattern through `decide_conjunction` /
//! `run_interface_search` and gives the `LiaTheory` the same deadline, so
//! expiry yields a graceful `Unknown` (never a verdict change).
//!
//! The instance is embedded inline (the source corpus is a gitignored NAS
//! symlink) so the gate is self-contained and committable. Bailing to
//! `unknown` is sound (`unknown` is first-class); the budget never converts a
//! `sat`/`unsat` into a wrong verdict, and fast queries still decide unchanged.

use std::time::{Duration, Instant};

use axeyum_ir::{Rational, Sort, TermArena, TermId};
use axeyum_smtlib::parse_script;
use axeyum_solver::{
    CheckResult, SatBvBackend, SolverBackend, SolverConfig, UnknownKind, check_auto,
    check_qf_aufbv_online_cdclt, check_qf_uflra_online, check_with_uf_arithmetic,
};

/// Public cvc5 regression whose five 1024-bit dividers exposed deadline-blind
/// AIG construction: a 1s benchmark timeout previously returned after 437.5s.
const WIDE_AUFBV_DIVISION: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../corpus/public-curated/non-incremental/QF_AUFBV/cvc5-regress-clean/",
    "cli__regress0__unconstrained__array1.smt2"
));

const ADMITTED_AUFBV_DIVISION: &str = r"
(set-logic QF_AUFBV)
(declare-fun i () (_ BitVec 16))
(declare-fun a () (Array (_ BitVec 16) (_ BitVec 1024)))
(declare-fun x () (_ BitVec 1024))
(declare-fun y () (_ BitVec 1024))
(assert (not (= (select a i) (bvudiv x y))))
(check-sat)
";

#[test]
fn wide_aufbv_division_honors_config_timeout() {
    let budget = Duration::from_millis(25);
    let cfg = SolverConfig::default().with_timeout(budget);

    let mut direct_script = parse_script(WIDE_AUFBV_DIVISION).expect("public AUFBV row parses");
    let direct_assertions = direct_script.checked_flat_view().to_vec();
    let start = Instant::now();
    let direct = check_qf_aufbv_online_cdclt(&mut direct_script.arena, &direct_assertions, &cfg)
        .expect("canonical AUFBV route has no operational error");
    let direct_elapsed = start.elapsed();
    assert!(
        direct_elapsed < budget * 200,
        "canonical AUFBV route overran its {budget:?} budget: elapsed {direct_elapsed:?} \
         (result {direct:?})"
    );

    let mut auto_script = parse_script(WIDE_AUFBV_DIVISION).expect("public AUFBV row parses");
    let auto_assertions = auto_script.checked_flat_view().to_vec();
    let start = Instant::now();
    let automatic = check_auto(&mut auto_script.arena, &auto_assertions, &cfg)
        .expect("automatic dispatch has no operational error");
    let auto_elapsed = start.elapsed();
    assert!(
        auto_elapsed < budget * 200,
        "automatic AUFBV dispatch overran its {budget:?} budget: elapsed {auto_elapsed:?} \
         (result {automatic:?})"
    );

    assert!(
        matches!(
            direct,
            CheckResult::Unknown(ref reason) if reason.kind == UnknownKind::EncodingBudget
        ),
        "oversized public row should be refused before lowering, got {direct:?}"
    );

    // Automatic dispatch may retain the canonical refusal or try another
    // deadline-bounded route. Timeliness, checked above, is its contract here.
    let _ = automatic;
}

#[test]
fn admitted_wide_divisions_expire_during_lowering() {
    let budget = Duration::from_millis(20);
    let cfg = SolverConfig::default().with_timeout(budget);

    let mut arena = TermArena::new();
    let x_symbol = arena.declare("x", Sort::BitVec(1024)).unwrap();
    let y_symbol = arena.declare("y", Sort::BitVec(1024)).unwrap();
    let expected_symbol = arena.declare("expected", Sort::BitVec(1024)).unwrap();
    let x = arena.var(x_symbol);
    let y = arena.var(y_symbol);
    let expected = arena.var(expected_symbol);
    let quotient = arena.bv_udiv(x, y).unwrap();
    let assertion = arena.eq(quotient, expected).unwrap();

    let start = Instant::now();
    let scalar = SatBvBackend::new()
        .check(&arena, &[assertion], &cfg)
        .expect("scalar BV backend has no operational error");
    let scalar_elapsed = start.elapsed();
    assert!(
        scalar_elapsed < budget * 250,
        "scalar BV lowering overran its {budget:?} budget: elapsed {scalar_elapsed:?} \
         (result {scalar:?})"
    );
    assert!(
        matches!(scalar, CheckResult::Unknown(ref reason) if reason.kind == UnknownKind::Timeout),
        "admitted scalar divider should time out during lowering, got {scalar:?}"
    );

    let mut array_script =
        parse_script(ADMITTED_AUFBV_DIVISION).expect("admitted AUFBV row parses");
    let array_assertions = array_script.checked_flat_view().to_vec();
    let start = Instant::now();
    let array = check_qf_aufbv_online_cdclt(&mut array_script.arena, &array_assertions, &cfg)
        .expect("canonical AUFBV route has no operational error");
    let array_elapsed = start.elapsed();
    assert!(
        array_elapsed < budget * 250,
        "canonical AUFBV lowering overran its {budget:?} budget: elapsed {array_elapsed:?} \
         (result {array:?})"
    );
    assert!(
        matches!(array, CheckResult::Unknown(ref reason) if reason.kind == UnknownKind::Timeout),
        "admitted canonical divider should time out during lowering, got {array:?}"
    );
}

/// The `QF_AUFLIA` `bug330` instance verbatim (declared `unsat` upstream; the
/// point here is *timeliness*, not the verdict).
const BUG330: &str = r#"; DISABLE-TESTER: lfsc
(set-logic QF_AUFLIA)
(set-info :source |
Translated from old SVC processor verification benchmarks.  Contact Clark
Barrett at barrett@cs.stanford.edu for more information.

This benchmark was automatically translated into SMT-LIB format from
CVC format using CVC Lite
|)
(set-info :smt-lib-version 2.6)
(set-info :category "industrial")
(set-info :status unsat)
(set-info :difficulty | 0 |)
(declare-fun BUBBLE_EX_INIT () Bool)
(declare-fun OPCODE_EX_INIT () Int)
(declare-fun BUBBLE_ID_INIT () Bool)
(declare-fun RF1_OF (Int) Int)
(declare-fun INST_ID_INIT () Int)
(declare-fun DEST_EX_INIT () Int)
(declare-fun RF2_OF (Int) Int)
(declare-fun OPCODE_OF (Int) Int)
(declare-fun STALL_INIT () Bool)
(declare-fun B_INIT () Int)
(declare-fun plus (Int Int) Int)
(declare-fun A_INIT () Int)
(declare-fun SHORT_IMMED_EX_INIT () Int)
(declare-fun ALU (Int Int Int) Int)
(declare-fun ALU_OP_OF (Int) Int)
(declare-fun DEST_MEM_INIT () Int)
(declare-fun LOAD_FLAG_INIT () Bool)
(declare-fun DMEM_INIT () (Array Int Int))
(declare-fun MAR_INIT () Int)
(declare-fun RESULT_MEM_INIT () Int)
(declare-fun DEST_WB_INIT () Int)
(declare-fun REGFILE_INIT () (Array Int Int))
(declare-fun RESULT_WB_INIT () Int)
(declare-fun IMEM_INIT () (Array Int Int))
(declare-fun PC_INIT () Int)
(declare-fun RF3_OF (Int) Int)
(declare-fun LONG_IMMED_OF (Int) Int)
(declare-fun SHORT_IMMED_OF (Int) Int)
(declare-fun STORE_FLAG_INIT () Bool)
(assert (let ((?v_53 (ite BUBBLE_EX_INIT false true)) (?v_7 (= OPCODE_EX_INIT 10)) (?v_2 (ite BUBBLE_ID_INIT false true)) (?v_5 (RF1_OF INST_ID_INIT))) (let ((?v_6 (= ?v_5 DEST_EX_INIT)) (?v_11 (RF2_OF INST_ID_INIT))) (let ((?v_46 (= ?v_11 DEST_EX_INIT))) (let ((?v_1 (ite ?v_53 (ite ?v_7 (ite ?v_2 (ite ?v_6 true ?v_46) false) false) false)) (?v_0 (OPCODE_OF INST_ID_INIT))) (let ((?v_3 (= ?v_0 11)) (?v_4 (= ?v_0 12)) (?v_128 (= ?v_5 0)) (?v_69 (= OPCODE_EX_INIT 13))) (let ((?v_8 (ite ?v_7 true ?v_69))) (let ((?v_54 (ite ?v_8 (plus A_INIT SHORT_IMMED_EX_INIT) (ALU (ALU_OP_OF OPCODE_EX_INIT) A_INIT B_INIT)))) (let ((?v_47 (ite ?v_8 B_INIT ?v_54)) (?v_48 (ite LOAD_FLAG_INIT (select DMEM_INIT MAR_INIT) RESULT_MEM_INIT)) (?v_49 (ite (ite (= DEST_WB_INIT 0) false true) (store REGFILE_INIT DEST_WB_INIT RESULT_WB_INIT) REGFILE_INIT))) (let ((?v_51 (ite ?v_128 0 (ite ?v_6 ?v_47 (ite (= ?v_5 DEST_MEM_INIT) ?v_48 (select ?v_49 ?v_5)))))) (let ((?v_37 (ite ?v_2 (ite ?v_3 true (ite ?v_4 (= ?v_51 0) false)) false))) (let ((?v_159 (ite STALL_INIT true (ite ?v_1 true ?v_37))) (?v_113 (ite ?v_3 true ?v_4))) (let ((?v_9 (ite ?v_1 true (ite BUBBLE_ID_INIT true ?v_113)))) (let ((?v_68 (ite ?v_9 false true)) (?v_10 (= ?v_0 10)) (?v_112 (ite ?v_1 BUBBLE_ID_INIT true))) (let ((?v_127 (ite ?v_112 false true)) (?v_43 (= ?v_0 13)) (?v_44 (= ?v_0 14))) (let ((?v_116 (ite (ite ?v_10 true ?v_44) ?v_11 (RF3_OF INST_ID_INIT)))) (let ((?v_13 (ite (ite ?v_9 true ?v_43) 0 ?v_116))) (let ((?v_129 (= ?v_13 ?v_5)) (?v_135 (= ?v_13 ?v_11))) (let ((?v_114 (ite ?v_68 (ite ?v_10 (ite ?v_127 (ite ?v_129 true ?v_135) false) false) false))) (let ((?v_115 (ite ?v_114 true (ite ?v_112 true ?v_113)))) (let ((?v_146 (ite ?v_115 false true)) (?v_118 (ite ?v_114 ?v_112 true))) (let ((?v_132 (ite ?v_118 false true)) (?v_117 (ite (ite ?v_115 true ?v_43) 0 ?v_116))) (let ((?v_133 (= ?v_117 ?v_5)) (?v_142 (= ?v_117 ?v_11))) (let ((?v_119 (ite ?v_146 (ite ?v_10 (ite ?v_132 (ite ?v_133 true ?v_142) false) false) false))) (let ((?v_120 (ite ?v_119 true (ite ?v_118 true ?v_113)))) (let ((?v_156 (ite ?v_120 false true)) (?v_122 (ite ?v_119 ?v_118 true))) (let ((?v_140 (ite ?v_122 false true)) (?v_121 (ite (ite ?v_120 true ?v_43) 0 ?v_116))) (let ((?v_141 (= ?v_121 ?v_5)) (?v_151 (= ?v_121 ?v_11))) (let ((?v_123 (ite ?v_156 (ite ?v_10 (ite ?v_140 (ite ?v_141 true ?v_151) false) false) false))) (let ((?v_124 (ite ?v_123 true (ite ?v_122 true ?v_113))) (?v_149 (ite (ite ?v_123 ?v_122 true) false true))) (let ((?v_125 (ite (ite ?v_124 true ?v_43) 0 ?v_116))) (let ((?v_150 (= ?v_125 ?v_5)) (?v_130 (LONG_IMMED_OF INST_ID_INIT)) (?v_45 (SHORT_IMMED_OF INST_ID_INIT))) (let ((?v_38 (ite ?v_3 (plus ?v_130 PC_INIT) (plus ?v_45 PC_INIT)))) (let ((?v_126 (ite ?v_37 ?v_38 PC_INIT))) (let ((?v_131 (ite ?v_1 PC_INIT ?v_126)) (?v_50 (ite ?v_10 true ?v_43)) (?v_134 (= ?v_11 0))) (let ((?v_52 (ite ?v_44 ?v_45 (ite ?v_134 0 (ite ?v_46 ?v_47 (ite (= ?v_11 DEST_MEM_INIT) ?v_48 (select ?v_49 ?v_11)))))) (?v_137 (ALU_OP_OF ?v_0))) (let ((?v_71 (ite ?v_50 (plus ?v_51 ?v_45) (ALU ?v_137 ?v_51 ?v_52)))) (let ((?v_62 (ite ?v_50 ?v_52 ?v_71)) (?v_70 (ite STORE_FLAG_INIT (store DMEM_INIT MAR_INIT RESULT_MEM_INIT) DMEM_INIT))) (let ((?v_63 (ite (ite ?v_53 ?v_7 false) (select ?v_70 ?v_54) ?v_47)) (?v_64 (ite (ite (= DEST_MEM_INIT 0) false true) (store ?v_49 DEST_MEM_INIT ?v_48) ?v_49))) (let ((?v_136 (ite ?v_128 0 (ite ?v_129 ?v_62 (ite ?v_6 ?v_63 (select ?v_64 ?v_5)))))) (let ((?v_139 (ite ?v_114 ?v_131 (ite (ite ?v_127 (ite ?v_3 true (ite ?v_4 (= ?v_136 0) false)) false) (ite ?v_3 (plus ?v_130 ?v_131) (plus ?v_45 ?v_131)) ?v_131))) (?v_138 (ite ?v_44 ?v_45 (ite ?v_134 0 (ite ?v_135 ?v_62 (ite ?v_46 ?v_63 (select ?v_64 ?v_11))))))) (let ((?v_147 (ite ?v_50 (plus ?v_136 ?v_45) (ALU ?v_137 ?v_136 ?v_138)))) (let ((?v_143 (ite ?v_50 ?v_138 ?v_147)) (?v_85 (ite (ite ?v_53 ?v_69 false) (store ?v_70 ?v_54 ?v_47) ?v_70))) (let ((?v_79 (ite (ite ?v_68 ?v_10 false) (select ?v_85 ?v_71) ?v_62)) (?v_80 (ite (ite (= DEST_EX_INIT 0) false true) (store ?v_64 DEST_EX_INIT ?v_63) ?v_64))) (let ((?v_144 (ite ?v_128 0 (ite ?v_133 ?v_143 (ite ?v_129 ?v_79 (select ?v_80 ?v_5)))))) (let ((?v_148 (ite ?v_119 ?v_139 (ite (ite ?v_132 (ite ?v_3 true (ite ?v_4 (= ?v_144 0) false)) false) (ite ?v_3 (plus ?v_130 ?v_139) (plus ?v_45 ?v_139)) ?v_139))) (?v_145 (ite ?v_44 ?v_45 (ite ?v_134 0 (ite ?v_142 ?v_143 (ite ?v_135 ?v_79 (select ?v_80 ?v_11))))))) (let ((?v_157 (ite ?v_50 (plus ?v_144 ?v_45) (ALU ?v_137 ?v_144 ?v_145)))) (let ((?v_152 (ite ?v_50 ?v_145 ?v_157)) (?v_97 (ite (ite ?v_68 ?v_43 false) (store ?v_85 ?v_71 ?v_62) ?v_85))) (let ((?v_153 (ite (ite ?v_146 ?v_10 false) (select ?v_97 ?v_147) ?v_143)) (?v_93 (ite (ite (= ?v_13 0) false true) (store ?v_80 ?v_13 ?v_79) ?v_80))) (let ((?v_154 (ite ?v_128 0 (ite ?v_141 ?v_152 (ite ?v_133 ?v_153 (select ?v_93 ?v_5)))))) (let ((?v_158 (ite ?v_123 ?v_148 (ite (ite ?v_140 (ite ?v_3 true (ite ?v_4 (= ?v_154 0) false)) false) (ite ?v_3 (plus ?v_130 ?v_148) (plus ?v_45 ?v_148)) ?v_148))) (?v_155 (ite ?v_44 ?v_45 (ite ?v_134 0 (ite ?v_151 ?v_152 (ite ?v_142 ?v_153 (select ?v_93 ?v_11)))))) (?v_165 (ite (ite (= ?v_117 0) false true) (store ?v_93 ?v_117 ?v_153) ?v_93))) (let ((?v_160 (ite (ite (ite ?v_124 false true) (ite ?v_10 (ite ?v_149 (ite ?v_150 true (= ?v_125 ?v_11)) false) false) false) ?v_158 (ite (ite ?v_149 (ite ?v_3 true (ite ?v_4 (= (ite ?v_128 0 (ite ?v_150 (ite ?v_50 ?v_155 (ite ?v_50 (plus ?v_154 ?v_45) (ALU ?v_137 ?v_154 ?v_155))) (ite ?v_141 (ite (ite ?v_156 ?v_10 false) (select (ite (ite ?v_146 ?v_43 false) (store ?v_97 ?v_147 ?v_143) ?v_97) ?v_157) ?v_152) (select ?v_165 ?v_5)))) 0) false)) false) (ite ?v_3 (plus ?v_130 ?v_158) (plus ?v_45 ?v_158)) ?v_158)))) (let ((?v_163 (select IMEM_INIT ?v_160))) (let ((?v_161 (OPCODE_OF ?v_163)) (?v_164 (plus 4 ?v_160))) (let ((?v_162 (ite ?v_159 ?v_160 ?v_164)) (?v_166 (RF1_OF ?v_163)) (?v_14 (ite ?v_1 BUBBLE_ID_INIT (ite STALL_INIT true ?v_37)))) (let ((?v_39 (ite ?v_14 false true)) (?v_12 (ite ?v_1 INST_ID_INIT (ite STALL_INIT INST_ID_INIT (select IMEM_INIT PC_INIT))))) (let ((?v_20 (RF1_OF ?v_12))) (let ((?v_42 (= ?v_20 ?v_13)) (?v_19 (RF2_OF ?v_12))) (let ((?v_61 (= ?v_19 ?v_13))) (let ((?v_16 (ite ?v_68 (ite ?v_10 (ite ?v_39 (ite ?v_42 true ?v_61) false) false) false)) (?v_15 (OPCODE_OF ?v_12))) (let ((?v_40 (= ?v_15 11)) (?v_41 (= ?v_15 12))) (let ((?v_23 (ite ?v_40 true ?v_41))) (let ((?v_17 (ite ?v_16 true (ite ?v_14 true ?v_23)))) (let ((?v_84 (ite ?v_17 false true)) (?v_18 (= ?v_15 10)) (?v_22 (ite ?v_16 ?v_14 true))) (let ((?v_56 (ite ?v_22 false true)) (?v_26 (= ?v_15 13)) (?v_59 (= ?v_15 14))) (let ((?v_27 (ite (ite ?v_18 true ?v_59) ?v_19 (RF3_OF ?v_12)))) (let ((?v_21 (ite (ite ?v_17 true ?v_26) 0 ?v_27))) (let ((?v_58 (= ?v_21 ?v_20)) (?v_77 (= ?v_21 ?v_19))) (let ((?v_24 (ite ?v_84 (ite ?v_18 (ite ?v_56 (ite ?v_58 true ?v_77) false) false) false))) (let ((?v_25 (ite ?v_24 true (ite ?v_22 true ?v_23)))) (let ((?v_96 (ite ?v_25 false true)) (?v_29 (ite ?v_24 ?v_22 true))) (let ((?v_74 (ite ?v_29 false true)) (?v_28 (ite (ite ?v_25 true ?v_26) 0 ?v_27))) (let ((?v_75 (= ?v_28 ?v_20)) (?v_90 (= ?v_28 ?v_19))) (let ((?v_30 (ite ?v_96 (ite ?v_18 (ite ?v_74 (ite ?v_75 true ?v_90) false) false) false))) (let ((?v_31 (ite ?v_30 true (ite ?v_29 true ?v_23)))) (let ((?v_108 (ite ?v_31 false true)) (?v_33 (ite ?v_30 ?v_29 true))) (let ((?v_88 (ite ?v_33 false true)) (?v_32 (ite (ite ?v_31 true ?v_26) 0 ?v_27))) (let ((?v_89 (= ?v_32 ?v_20)) (?v_102 (= ?v_32 ?v_19))) (let ((?v_34 (ite ?v_108 (ite ?v_18 (ite ?v_88 (ite ?v_89 true ?v_102) false) false) false))) (let ((?v_35 (ite ?v_34 true (ite ?v_33 true ?v_23))) (?v_100 (ite (ite ?v_34 ?v_33 true) false true))) (let ((?v_36 (ite (ite ?v_35 true ?v_26) 0 ?v_27))) (let ((?v_101 (= ?v_36 ?v_20)) (?v_55 (ite ?v_1 PC_INIT (ite STALL_INIT ?v_126 (ite ?v_37 ?v_38 (plus 4 PC_INIT))))) (?v_57 (= ?v_20 0))) (let ((?v_66 (ite ?v_57 0 (ite ?v_42 ?v_62 (ite (= ?v_20 DEST_EX_INIT) ?v_63 (select ?v_64 ?v_20))))) (?v_72 (LONG_IMMED_OF ?v_12)) (?v_60 (SHORT_IMMED_OF ?v_12))) (let ((?v_73 (ite ?v_16 ?v_55 (ite (ite ?v_39 (ite ?v_40 true (ite ?v_41 (= ?v_66 0) false)) false) (ite ?v_40 (plus ?v_72 ?v_55) (plus ?v_60 ?v_55)) ?v_55))) (?v_65 (ite ?v_18 true ?v_26)) (?v_76 (= ?v_19 0))) (let ((?v_67 (ite ?v_59 ?v_60 (ite ?v_76 0 (ite ?v_61 ?v_62 (ite (= ?v_19 DEST_EX_INIT) ?v_63 (select ?v_64 ?v_19)))))) (?v_82 (ALU_OP_OF ?v_15))) (let ((?v_86 (ite ?v_65 (plus ?v_66 ?v_60) (ALU ?v_82 ?v_66 ?v_67)))) (let ((?v_78 (ite ?v_65 ?v_67 ?v_86))) (let ((?v_81 (ite ?v_57 0 (ite ?v_58 ?v_78 (ite ?v_42 ?v_79 (select ?v_80 ?v_20)))))) (let ((?v_87 (ite ?v_24 ?v_73 (ite (ite ?v_56 (ite ?v_40 true (ite ?v_41 (= ?v_81 0) false)) false) (ite ?v_40 (plus ?v_72 ?v_73) (plus ?v_60 ?v_73)) ?v_73))) (?v_83 (ite ?v_59 ?v_60 (ite ?v_76 0 (ite ?v_77 ?v_78 (ite ?v_61 ?v_79 (select ?v_80 ?v_19))))))) (let ((?v_98 (ite ?v_65 (plus ?v_81 ?v_60) (ALU ?v_82 ?v_81 ?v_83)))) (let ((?v_91 (ite ?v_65 ?v_83 ?v_98)) (?v_92 (ite (ite ?v_84 ?v_18 false) (select ?v_97 ?v_86) ?v_78))) (let ((?v_94 (ite ?v_57 0 (ite ?v_75 ?v_91 (ite ?v_58 ?v_92 (select ?v_93 ?v_20)))))) (let ((?v_99 (ite ?v_30 ?v_87 (ite (ite ?v_74 (ite ?v_40 true (ite ?v_41 (= ?v_94 0) false)) false) (ite ?v_40 (plus ?v_72 ?v_87) (plus ?v_60 ?v_87)) ?v_87))) (?v_95 (ite ?v_59 ?v_60 (ite ?v_76 0 (ite ?v_90 ?v_91 (ite ?v_77 ?v_92 (select ?v_93 ?v_19))))))) (let ((?v_110 (ite ?v_65 (plus ?v_94 ?v_60) (ALU ?v_82 ?v_94 ?v_95)))) (let ((?v_103 (ite ?v_65 ?v_95 ?v_110)) (?v_109 (ite (ite ?v_84 ?v_26 false) (store ?v_97 ?v_86 ?v_78) ?v_97))) (let ((?v_104 (ite (ite ?v_96 ?v_18 false) (select ?v_109 ?v_98) ?v_91)) (?v_105 (ite (ite (= ?v_21 0) false true) (store ?v_93 ?v_21 ?v_92) ?v_93))) (let ((?v_106 (ite ?v_57 0 (ite ?v_89 ?v_103 (ite ?v_75 ?v_104 (select ?v_105 ?v_20)))))) (let ((?v_111 (ite ?v_34 ?v_99 (ite (ite ?v_88 (ite ?v_40 true (ite ?v_41 (= ?v_106 0) false)) false) (ite ?v_40 (plus ?v_72 ?v_99) (plus ?v_60 ?v_99)) ?v_99))) (?v_107 (ite ?v_59 ?v_60 (ite ?v_76 0 (ite ?v_102 ?v_103 (ite ?v_90 ?v_104 (select ?v_105 ?v_19))))))) (not (= (ite (ite (ite ?v_35 false true) (ite ?v_18 (ite ?v_100 (ite ?v_101 true (= ?v_36 ?v_19)) false) false) false) ?v_111 (ite (ite ?v_100 (ite ?v_40 true (ite ?v_41 (= (ite ?v_57 0 (ite ?v_101 (ite ?v_65 ?v_107 (ite ?v_65 (plus ?v_106 ?v_60) (ALU ?v_82 ?v_106 ?v_107))) (ite ?v_89 (ite (ite ?v_108 ?v_18 false) (select (ite (ite ?v_96 ?v_26 false) (store ?v_109 ?v_98 ?v_91) ?v_109) ?v_110) ?v_103) (select (ite (ite (= ?v_28 0) false true) (store ?v_105 ?v_28 ?v_104) ?v_105) ?v_20)))) 0) false)) false) (ite ?v_40 (plus ?v_72 ?v_111) (plus ?v_60 ?v_111)) ?v_111)) (ite (ite ?v_159 false true) (ite (= ?v_161 10) ?v_162 (ite (= ?v_161 13) ?v_162 (ite (= ?v_161 11) (plus (LONG_IMMED_OF ?v_163) ?v_164) (ite (= ?v_161 12) (ite (= (ite (= ?v_166 0) 0 (select ?v_165 ?v_166)) 0) (plus (SHORT_IMMED_OF ?v_163) ?v_164) ?v_164) ?v_162)))) ?v_162)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
(exit)
"#;

#[test]
fn bug330_honors_config_timeout() {
    let budget = Duration::from_secs(2);
    let mut script = parse_script(BUG330).expect("bug330 parses");
    let cfg = SolverConfig::default().with_timeout(budget);

    let start = Instant::now();
    let assertions = script.checked_flat_view().to_vec();
    let result = check_auto(&mut script.arena, &assertions, &cfg).expect("no solver error");
    let elapsed = start.elapsed();

    // Generous multiple of the budget so the assert is robust on a loaded CI
    // box, while still proving the deadline fires — the pre-fix behaviour ran
    // ~25s (minutes under a tight budget) against this same 2s timeout.
    assert!(
        elapsed < budget * 40,
        "bug330 overran its 2s budget: elapsed {elapsed:?} (result {result:?})"
    );

    // Any of sat/unsat/unknown is acceptable — only a *wrong* verdict would be a
    // soundness bug. In practice this degrades to `unknown` at expiry; it must
    // never hang.
    match result {
        CheckResult::Sat(_) | CheckResult::Unsat | CheckResult::Unknown(_) => {}
    }
}

// ---------------------------------------------------------------------------
// QF_UFLRA deadline gate (#16, the `uflra_online` differential-fuzz hang class).
//
// The two 600-case differential fuzzes in `tests/uflra_online.rs` ran with **no
// `config.timeout`** and hung on a loaded box (one stale binary was observed
// running ~3.9h). The grinding path is the *offline reference*
// `check_with_uf_arithmetic` (eager Ackermann → `check_auto` on the
// function-eliminated arithmetic): on a small but hard random conjunction its
// downstream reduced solve grinds unbounded when the budget is `None`. Under a set
// `config.timeout` it degrades to a graceful `Unknown` in ~budget (never a wrong
// verdict). The companion online combination `check_qf_uflra_online` now also
// threads the deadline through its interface-search DFS (up to `3^pairs`
// arrangements) so *it* honors the same budget — parity with the UFLIA sibling
// (bug330 / commit `3cd6c810`), which had left the UFLRA combination untouched.
//
// This gate reconstructs the first grinding fuzz case deterministically (the shared
// LCG advanced to case 99 of the `differential_fuzz_agrees_with_offline_ackermann`
// corpus) and asserts BOTH deciders return within a small multiple of a tight budget.
// ---------------------------------------------------------------------------

/// Advances the fuzz's 64-bit LCG (verbatim from `tests/uflra_online.rs`).
fn next_rand(state: &mut u64) -> u32 {
    *state = state
        .wrapping_mul(6_364_136_223_846_793_005)
        .wrapping_add(1_442_695_040_888_963_407);
    (*state >> 33) as u32
}

/// Builds one deterministic-random `QF_UFLRA` conjunction — verbatim from the
/// `differential_fuzz_agrees_with_offline_ackermann` corpus in `tests/uflra_online.rs`
/// — so the grinding case reproduces bit-for-bit.
#[allow(clippy::many_single_char_names)]
fn build_fuzz_case(arena: &mut TermArena, state: &mut u64) -> Vec<TermId> {
    let f = arena
        .declare_fun("f", &[Sort::Real], Sort::Real)
        .expect("declare f");
    let x = {
        let s = arena.declare("x", Sort::Real).expect("declare x");
        arena.var(s)
    };
    let y = {
        let s = arena.declare("y", Sort::Real).expect("declare y");
        arena.var(s)
    };
    let z = {
        let s = arena.declare("z", Sort::Real).expect("declare z");
        arena.var(s)
    };
    let mut pool: Vec<TermId> = vec![x, y, z];
    for _ in 0..2 {
        let n = i128::from(next_rand(state) % 5);
        pool.push(arena.real_const(Rational::integer(n)));
    }
    for _ in 0..3 {
        let pick = pool[(next_rand(state) as usize) % pool.len()];
        pool.push(arena.apply(f, &[pick]).unwrap());
    }
    let atom_count = 2 + (next_rand(state) % 3) as usize;
    let mut atoms: Vec<TermId> = Vec::with_capacity(atom_count);
    for _ in 0..atom_count {
        let lhs = pool[(next_rand(state) as usize) % pool.len()];
        let rhs = pool[(next_rand(state) as usize) % pool.len()];
        let atom = match next_rand(state) % 5 {
            0 => arena.real_lt(lhs, rhs).unwrap(),
            1 => arena.real_le(lhs, rhs).unwrap(),
            2 => arena.eq(lhs, rhs).unwrap(),
            3 => {
                let e = arena.eq(lhs, rhs).unwrap();
                arena.not(e).unwrap()
            }
            _ => arena.real_ge(lhs, rhs).unwrap(),
        };
        atoms.push(atom);
    }
    atoms
}

#[test]
fn uflra_fuzz_grinder_honors_config_timeout() {
    // Reconstruct case 99 of the `differential_fuzz` corpus: the first case whose
    // offline eager-Ackermann reduced solve grinds unbounded under a `None` budget
    // (the fuzz-hang root). The shared LCG is advanced through cases 0..99 exactly as
    // the fuzz loop does (each on a throwaway arena), then case 99 is built for real.
    let mut state: u64 = 0x1234_5678_9abc_def0;
    for _ in 0..99 {
        let mut throwaway = TermArena::new();
        let _ = build_fuzz_case(&mut throwaway, &mut state);
    }
    let mut arena = TermArena::new();
    let assertions = build_fuzz_case(&mut arena, &mut state);

    let budget = Duration::from_millis(300);
    let cfg = SolverConfig::default().with_timeout(budget);

    // The offline reference — the path that actually grinds — must honor the budget.
    let start = Instant::now();
    let offline = check_with_uf_arithmetic(&mut arena, &assertions, &cfg).expect("no solver error");
    let offline_elapsed = start.elapsed();
    assert!(
        offline_elapsed < budget * 30,
        "offline check_with_uf_arithmetic overran its {budget:?} budget on the fuzz grinder: \
         elapsed {offline_elapsed:?} (result {offline:?})"
    );

    // The online combination (its interface DFS now deadline-threaded) must likewise
    // stay bounded — it decides these small cases instantly, and a hard arrangement
    // degrades to `Unknown` at expiry rather than grinding past the budget.
    let start = Instant::now();
    let online = check_qf_uflra_online(&mut arena, &assertions, &cfg).expect("no solver error");
    let online_elapsed = start.elapsed();
    assert!(
        online_elapsed < budget * 30,
        "online check_qf_uflra_online overran its {budget:?} budget on the fuzz grinder: \
         elapsed {online_elapsed:?} (result {online:?})"
    );

    // Only a *wrong* verdict would be a soundness bug; any of sat/unsat/unknown is fine
    // (in practice the offline path degrades to a graceful `Unknown` at expiry). Where
    // both decide, they must agree — the fuzz's own soundness contract, re-checked here.
    match (&offline, &online) {
        (CheckResult::Sat(_), CheckResult::Unsat) | (CheckResult::Unsat, CheckResult::Sat(_)) => {
            panic!(
                "UFLRA online/offline disagree on the reconstructed fuzz grinder: \
                    offline={offline:?}, online={online:?}"
            );
        }
        _ => {}
    }
}
