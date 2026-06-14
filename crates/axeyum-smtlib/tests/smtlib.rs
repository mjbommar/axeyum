//! Reader/writer tests: feature coverage, round trips, and corpus smoke.

use axeyum_ir::{Assignment, SymbolId, TermStats, Value, eval};
use axeyum_smtlib::{SmtError, parse_script, write_script};

#[test]
fn parses_core_benchmark_shape() {
    let text = r"
        (set-info :status sat)
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= (bvadd x y #x01) (_ bv16 8)))
        (assert (bvult x #b00001111))
        (check-sat)
        (exit)
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.logic.as_deref(), Some("QF_BV"));
    assert_eq!(script.status.as_deref(), Some("sat"));
    assert_eq!(script.assertions.len(), 2);
    assert_eq!(script.check_sats, 1);
}

#[test]
fn let_bindings_shadow_and_share() {
    let text = r"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (let ((t (bvadd x x))) (= (bvmul t t) (_ bv0 8))))
    ";
    let script = parse_script(text).unwrap();
    // t is shared: mul's two children are the same TermId.
    let stats = TermStats::compute(&script.arena, &script.assertions);
    assert!(stats.tree_nodes > stats.dag_nodes);
    // Evaluator agrees with hand computation under x = 4: t = 8, t*t = 64 != 0.
    let sym = script.arena.find_symbol("x").unwrap();
    let mut asg = Assignment::new();
    asg.set(sym, Value::Bv { width: 8, value: 4 });
    assert_eq!(
        eval(&script.arena, script.assertions[0], &asg).unwrap(),
        Value::Bool(false)
    );
}

#[test]
fn nary_and_parameterized_operators() {
    let text = r"
        (set-logic QF_BV)
        (declare-const a (_ BitVec 4))
        (declare-const p Bool)
        (declare-const q Bool)
        (assert (and p q (=> p q)))
        (assert (= ((_ extract 3 2) a) ((_ rotate_left 1) ((_ extract 1 0) a))))
        (assert (= ((_ zero_extend 4) a) (_ bv7 8)))
        (assert (= ((_ repeat 2) a) (concat a a)))
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.assertions.len(), 4);
}

#[test]
fn parses_and_round_trips_qf_abv_select_store() {
    let text = r"
        (set-logic QF_ABV)
        (declare-fun mem () (Array (_ BitVec 4) (_ BitVec 8)))
        (declare-const i (_ BitVec 4))
        (declare-const v (_ BitVec 8))
        (assert (= (select (store mem i v) i) v))
        (assert (= (select mem (_ bv3 4)) (_ bv171 8)))
        (check-sat)
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.logic.as_deref(), Some("QF_ABV"));
    assert_eq!(script.assertions.len(), 2);

    let rendered = write_script(&script.arena, &script.assertions);
    assert!(rendered.contains("(Array (_ BitVec 4) (_ BitVec 8))"));
    assert!(rendered.contains("select"));
    assert!(rendered.contains("store"));

    // The written script re-parses to the same number of assertions.
    let reparsed = parse_script(&rendered).unwrap();
    assert_eq!(reparsed.assertions.len(), 2);
}

#[test]
fn parses_and_round_trips_qf_ufbv_applications() {
    let text = r"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-fun g ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= (f x) (f y)))
        (assert (= (g x y) (f x)))
        (check-sat)
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.logic.as_deref(), Some("QF_UFBV"));
    assert_eq!(script.assertions.len(), 2);

    let rendered = write_script(&script.arena, &script.assertions);
    // The writer re-declares the functions and selects the UF logic.
    assert!(rendered.contains("(set-logic QF_UFBV)"));
    assert!(rendered.contains("(declare-fun f ((_ BitVec 8)) (_ BitVec 8))"));
    assert!(rendered.contains("(declare-fun g ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))"));

    // The written script re-parses to the same number of assertions.
    let reparsed = parse_script(&rendered).unwrap();
    assert_eq!(reparsed.assertions.len(), 2);
}

#[test]
fn parses_and_round_trips_qf_lia() {
    let text = r"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= (+ (* 2 x) y) 7))
        (assert (< x y))
        (assert (>= x (- 0 3)))
        (check-sat)
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.logic.as_deref(), Some("QF_LIA"));
    assert_eq!(script.assertions.len(), 3);

    let rendered = write_script(&script.arena, &script.assertions);
    assert!(rendered.contains("(set-logic QF_LIA)"));
    assert!(rendered.contains("(declare-const x Int)"));

    // The written script re-parses to the same number of assertions.
    let reparsed = parse_script(&rendered).unwrap();
    assert_eq!(reparsed.assertions.len(), 3);
}

#[test]
fn integer_literals_and_negation_parse() {
    let text = r"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= x (- 5)))
        (check-sat)
    ";
    let script = parse_script(text).unwrap();
    // `(- 5)` is unary negation; the assertion is `x = -5`.
    let rendered = write_script(&script.arena, &script.assertions);
    let reparsed = parse_script(&rendered).unwrap();
    assert_eq!(reparsed.assertions.len(), 1);
}

#[test]
fn parses_and_round_trips_qf_lra() {
    let text = r"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (< (+ x y) 1.5))
        (assert (>= x (/ 1.0 3.0)))
        (assert (= y (- 2.0)))
        (check-sat)
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.logic.as_deref(), Some("QF_LRA"));
    assert_eq!(script.assertions.len(), 3);

    let rendered = write_script(&script.arena, &script.assertions);
    assert!(rendered.contains("(set-logic QF_LRA)"));
    assert!(rendered.contains("(declare-const x Real)"));

    // The written script re-parses to the same number of assertions.
    let reparsed = parse_script(&rendered).unwrap();
    assert_eq!(reparsed.assertions.len(), 3);
}

#[test]
fn integer_numerals_coerce_to_real_in_real_context() {
    // The bare numeral `1` is coerced to `Real` because `x` is real.
    let text = r"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (< x 1))
        (check-sat)
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.assertions.len(), 1);
    // Re-render and re-parse to confirm the coerced literal survives.
    let rendered = write_script(&script.arena, &script.assertions);
    let reparsed = parse_script(&rendered).unwrap();
    assert_eq!(reparsed.assertions.len(), 1);
}

#[test]
fn parses_and_round_trips_quantifiers() {
    let text = r"
        (set-logic BV)
        (assert (forall ((x (_ BitVec 4))) (= (bvor x x) x)))
        (assert (exists ((y (_ BitVec 4))) (= y (_ bv3 4))))
        (check-sat)
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.assertions.len(), 2);

    let rendered = write_script(&script.arena, &script.assertions);
    assert!(rendered.contains("(forall ("));
    assert!(rendered.contains("(exists ("));

    // The written script re-parses to the same number of assertions.
    let reparsed = parse_script(&rendered).unwrap();
    assert_eq!(reparsed.assertions.len(), 2);
}

#[test]
fn nested_quantifier_binding_does_not_capture() {
    // Two separately-scoped `x` binders must not collide.
    let text = r"
        (set-logic BV)
        (assert (and
            (forall ((x (_ BitVec 2))) (bvule x x))
            (exists ((x (_ BitVec 2))) (= x (_ bv1 2)))))
        (check-sat)
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.assertions.len(), 1);
    let rendered = write_script(&script.arena, &script.assertions);
    assert_eq!(parse_script(&rendered).unwrap().assertions.len(), 1);
}

#[test]
fn builtin_operators_take_priority_over_function_names() {
    // A declared function may not shadow a builtin: `bvadd` stays the builtin.
    let text = r"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 4)) (_ BitVec 4))
        (declare-const x (_ BitVec 4))
        (assert (= (f (bvadd x x)) x))
        (check-sat)
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.assertions.len(), 1);
    // Re-parse the rendered form to confirm the application survives.
    let rendered = write_script(&script.arena, &script.assertions);
    assert!(rendered.contains("bvadd"));
    let reparsed = parse_script(&rendered).unwrap();
    assert_eq!(reparsed.assertions.len(), 1);
}

#[test]
fn nary_distinct_is_pairwise() {
    let text = r"
        (set-logic QF_BV)
        (assert (distinct (_ bv0 4) (_ bv1 4) (_ bv2 4)))
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(
        eval(&script.arena, script.assertions[0], &Assignment::new()).unwrap(),
        Value::Bool(true)
    );

    let text = r"
        (set-logic QF_BV)
        (assert (distinct (_ bv0 4) (_ bv1 4) (_ bv0 4)))
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(
        eval(&script.arena, script.assertions[0], &Assignment::new()).unwrap(),
        Value::Bool(false)
    );
}

#[test]
fn define_fun_aliases_expand() {
    let text = r"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (define-fun twice () (_ BitVec 8) (bvadd x x))
        (assert (bvult twice (_ bv100 8)))
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.assertions.len(), 1);
}

#[test]
fn parameterized_define_fun_macros_expand_hygienically() {
    let text = r"
        (set-logic QF_BV)
        (define-fun add1 ((x (_ BitVec 8))) (_ BitVec 8)
            (bvadd x (_ bv1 8)))
        (assert (= (add1 (_ bv3 8)) (_ bv4 8)))
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.assertions.len(), 1);
    assert!(
        script.arena.find_symbol("x").is_none(),
        "macro parameters must not leak into global symbols"
    );
    assert_eq!(
        eval(&script.arena, script.assertions[0], &Assignment::new()).unwrap(),
        Value::Bool(true)
    );
}

#[test]
fn parameterized_define_fun_checks_arity_and_sorts_at_call_sites() {
    assert!(matches!(
        parse_script(
            r"
            (set-logic QF_BV)
            (define-fun is-zero ((x (_ BitVec 8))) Bool (= x (_ bv0 8)))
            (assert (is-zero (_ bv0 8) (_ bv1 8)))
            "
        ),
        Err(SmtError::Syntax(_))
    ));
    assert!(matches!(
        parse_script(
            r"
            (set-logic QF_BV)
            (define-fun is-zero ((x (_ BitVec 8))) Bool (= x (_ bv0 8)))
            (assert (is-zero true))
            "
        ),
        Err(SmtError::Ir(_))
    ));
}

#[test]
fn unsupported_constructs_are_clear_errors() {
    // `push`/`pop` are now accepted (incremental scoping); they record commands.
    let inc = parse_script("(push 1)").expect("push is accepted");
    assert_eq!(inc.commands.len(), 1);
    // `check-sat-assuming` is still unsupported.
    assert!(matches!(
        parse_script("(check-sat-assuming (a))"),
        Err(SmtError::Unsupported(_))
    ));
    // n-ary functions over scalar sorts are supported (ADR-0013); a function
    // with an array-sorted parameter is not (functions are scalar).
    assert!(parse_script("(declare-fun f ((_ BitVec 8)) (_ BitVec 8))").is_ok());
    assert!(matches!(
        parse_script("(declare-fun f ((Array (_ BitVec 4) (_ BitVec 8))) Bool)"),
        Err(SmtError::Ir(_))
    ));
    assert!(matches!(
        parse_script("(assert (bvadd"),
        Err(SmtError::Syntax(_))
    ));
}

#[test]
fn malformed_commands_are_rejected_instead_of_truncated() {
    assert!(matches!(
        parse_script("(check-sat true)"),
        Err(SmtError::Syntax(_))
    ));
    assert!(matches!(
        parse_script("(assert true false)"),
        Err(SmtError::Syntax(_))
    ));
    assert!(matches!(
        parse_script("(set-logic QF_BV QF_ABV)"),
        Err(SmtError::Syntax(_))
    ));
    assert!(matches!(
        parse_script("(declare-const x (_ BitVec 8) extra)"),
        Err(SmtError::Syntax(_))
    ));
}

#[test]
fn define_fun_declared_sort_must_match_body() {
    let text = r"
        (set-logic QF_BV)
        (define-fun bad () Bool (_ bv0 1))
    ";
    assert!(matches!(parse_script(text), Err(SmtError::Ir(_))));
}

#[test]
fn write_parse_round_trip_preserves_structure() {
    let text = r"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const p Bool)
        (assert (let ((t (bvadd x (_ bv1 8))))
            (ite p (bvule (bvmul t t) (_ bv64 8)) (= t (_ bv5 8)))))
        (assert ((_ sign_extend 0) x (_ bv0 8)))
    ";
    // The second assert is bogus on purpose? No — keep it valid:
    let text = text.replace("(assert ((_ sign_extend 0) x (_ bv0 8)))", "");
    let first = parse_script(&text).unwrap();
    let exported = write_script(&first.arena, &first.assertions);
    let second = parse_script(&exported).unwrap();
    // Semantically identical: evaluate both under the same assignments.
    let sym_of =
        |s: &axeyum_smtlib::Script, n: &str| -> SymbolId { s.arena.find_symbol(n).unwrap() };
    for xv in [0u128, 4, 5, 200, 255] {
        for pv in [false, true] {
            let mut a1 = Assignment::new();
            a1.set(
                sym_of(&first, "x"),
                Value::Bv {
                    width: 8,
                    value: xv,
                },
            );
            a1.set(sym_of(&first, "p"), Value::Bool(pv));
            let mut a2 = Assignment::new();
            a2.set(
                sym_of(&second, "x"),
                Value::Bv {
                    width: 8,
                    value: xv,
                },
            );
            a2.set(sym_of(&second, "p"), Value::Bool(pv));
            assert_eq!(
                eval(&first.arena, first.assertions[0], &a1).unwrap(),
                eval(&second.arena, second.assertions[0], &a2).unwrap(),
                "x={xv} p={pv}"
            );
        }
    }
}

#[test]
fn writer_escapes_symbols_and_avoids_generated_name_collisions() {
    use axeyum_ir::TermArena;

    let mut a = TermArena::new();
    let x = a.bv_var("x y", 8).unwrap();
    let one = a.bv_const(8, 1).unwrap();
    let sum = a.bv_add(x, one).unwrap();
    let collision = a.bv_var("axy.t2", 8).unwrap();
    let shared = a.eq(sum, sum).unwrap();
    let mentions_collision = a.eq(collision, collision).unwrap();

    let exported = write_script(&a, &[shared, mentions_collision]);
    assert!(exported.contains("(declare-const |x y| (_ BitVec 8))"));
    assert!(exported.contains("(declare-const axy.t2 (_ BitVec 8))"));
    assert!(exported.contains("(define-fun axy.t2.1"));

    let reparsed = parse_script(&exported).unwrap();
    assert!(reparsed.arena.find_symbol("x y").is_some());
    assert!(reparsed.arena.find_symbol("axy.t2").is_some());
    assert_eq!(reparsed.assertions.len(), 2);
}

#[test]
fn export_is_linear_in_dag_not_tree() {
    use axeyum_ir::TermArena;
    // The 2^k bomb must export in linear size via define-fun sharing.
    let mut a = TermArena::new();
    let mut t = a.bv_var("x", 64).unwrap();
    for _ in 0..100 {
        t = a.bv_add(t, t).unwrap();
    }
    let zero = a.bv_const(64, 0).unwrap();
    let f = a.eq(t, zero).unwrap();
    let exported = write_script(&a, &[f]);
    assert!(
        exported.len() < 20_000,
        "export must stay linear, got {} bytes",
        exported.len()
    );
    // And it must parse back.
    let back = parse_script(&exported).unwrap();
    assert_eq!(back.assertions.len(), 1);
}

#[test]
fn corpus_smoke_ingests_local_benchmarks_when_present() {
    // Runtime-skipped where the (gitignored) public corpus is absent (CI).
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../corpus/public/non-incremental/QF_ABV");
    if !dir.exists() {
        eprintln!("corpus absent; skipping");
        return;
    }
    let mut tried = 0;
    let mut parsed = 0;
    let mut unsupported = 0;
    for entry in walk(&dir) {
        if tried >= 25 {
            break;
        }
        let Ok(text) = std::fs::read_to_string(&entry) else {
            continue;
        };
        tried += 1;
        match parse_script(&text) {
            Ok(_) => parsed += 1,
            // QF_ABV files contain arrays — Unsupported is the correct,
            // classified outcome until arrays land (Phase 7).
            Err(SmtError::Unsupported(_) | SmtError::Ir(_)) => unsupported += 1,
            Err(SmtError::Syntax(e)) => panic!("syntax error on {entry:?}: {e}"),
        }
    }
    eprintln!("corpus smoke: {parsed} parsed, {unsupported} unsupported of {tried}");
    assert!(tried > 0);
}

fn walk(dir: &std::path::Path) -> Vec<std::path::PathBuf> {
    let mut files = Vec::new();
    let mut dirs = vec![dir.to_path_buf()];
    while let Some(d) = dirs.pop() {
        let Ok(entries) = std::fs::read_dir(&d) else {
            continue;
        };
        for e in entries.flatten() {
            let p = e.path();
            if p.is_dir() {
                dirs.push(p);
            } else if p.extension().is_some_and(|x| x == "smt2") {
                files.push(p);
            }
        }
        if files.len() > 200 {
            break;
        }
    }
    files.sort();
    files
}

#[test]
fn parses_and_round_trips_lia_div_mod_abs() {
    let text = r"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= (mod x 3) 2))
        (assert (= (div x 4) 1))
        (assert (= (abs x) 5))
        (check-sat)
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.assertions.len(), 3);

    let rendered = write_script(&script.arena, &script.assertions);
    assert!(rendered.contains("(mod "), "renders mod: {rendered}");
    assert!(rendered.contains("(div "), "renders div: {rendered}");
    assert!(rendered.contains("(abs "), "renders abs: {rendered}");

    let reparsed = parse_script(&rendered).unwrap();
    assert_eq!(reparsed.assertions.len(), 3);
}

#[test]
fn parses_lia_divisible() {
    let text = r"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert ((_ divisible 3) x))
        (check-sat)
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.assertions.len(), 1);
    // desugars to (= (mod x 3) 0), which re-parses fine.
    let rendered = write_script(&script.arena, &script.assertions);
    let reparsed = parse_script(&rendered).unwrap();
    assert_eq!(reparsed.assertions.len(), 1);
}

#[test]
fn parses_and_round_trips_const_array() {
    let text = r"
        (set-logic QF_ABV)
        (declare-const i (_ BitVec 4))
        (assert (= (select ((as const (Array (_ BitVec 4) (_ BitVec 8))) (_ bv0 8)) i) (_ bv0 8)))
        (check-sat)
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.assertions.len(), 1);
    let rendered = write_script(&script.arena, &script.assertions);
    assert!(rendered.contains("(as const (Array (_ BitVec 4) (_ BitVec 8)))"), "renders as const: {rendered}");
    let reparsed = parse_script(&rendered).unwrap();
    assert_eq!(reparsed.assertions.len(), 1);
}

#[test]
fn parses_and_round_trips_bv_int_coercions() {
    let text = r"
        (set-logic QF_UFBV)
        (declare-const x (_ BitVec 8))
        (declare-const y Int)
        (assert (= (bv2nat x) 200))
        (assert (= ((_ int2bv 8) y) x))
        (check-sat)
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.assertions.len(), 2);
    let rendered = write_script(&script.arena, &script.assertions);
    assert!(rendered.contains("(bv2nat "), "renders bv2nat: {rendered}");
    assert!(rendered.contains("((_ int2bv 8) "), "renders int2bv: {rendered}");
    let reparsed = parse_script(&rendered).unwrap();
    assert_eq!(reparsed.assertions.len(), 2);
}

#[test]
fn parses_bv_overflow_predicates() {
    // bvuaddo(0xff, 0x01) on 8-bit is true (255 + 1 overflows); the formula
    // asserting it must parse and be satisfiable (it is a true ground fact).
    let text = r"
        (set-logic QF_BV)
        (assert (bvuaddo (_ bv255 8) (_ bv1 8)))
        (assert (not (bvuaddo (_ bv1 8) (_ bv1 8))))
        (assert (bvnego (_ bv128 8)))
        (check-sat)
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.assertions.len(), 3);
    // round-trips structurally (desugared to bvadd/extract/eq); re-parses.
    let rendered = write_script(&script.arena, &script.assertions);
    let reparsed = parse_script(&rendered).unwrap();
    assert_eq!(reparsed.assertions.len(), 3);
}

#[test]
fn parses_symbolic_real_division() {
    let text = r"
        (set-logic QF_NRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (= (/ x y) 2.0))
        (check-sat)
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.assertions.len(), 1);
    let rendered = write_script(&script.arena, &script.assertions);
    assert!(rendered.contains("(/ "), "renders /: {rendered}");
    let reparsed = parse_script(&rendered).unwrap();
    assert_eq!(reparsed.assertions.len(), 1);
}

#[test]
fn folds_constant_int_real_coercions() {
    // (to_real 3) = 3.0, (to_int 7/2) = 3, (is_int 4.0) = true, (is_int 3.5) = false.
    let text = r"
        (set-logic QF_LIRA)
        (declare-const x Real)
        (assert (= x (to_real 3)))
        (assert (> (to_int 3.5) 2))
        (assert (is_int 4.0))
        (assert (not (is_int 3.5)))
        (check-sat)
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.assertions.len(), 4);
}

#[test]
fn parses_attributed_terms_with_patterns() {
    // (! body :pattern (...)) and (! ... :named n) denote the inner term; the
    // annotations are dropped. Common in quantified benchmarks.
    let text = r"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (! (> x 0) :named c1))
        (assert (! (< x 10) :pattern ((+ x 1))))
        (check-sat)
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.assertions.len(), 2);
}

#[test]
fn parses_floating_point_predicates_and_literals() {
    // Float32 declarations, fp literals, special constants, comparisons, and
    // classification all parse (lowered to bit-vectors; ADR-0023).
    let text = r"
        (set-logic QF_FP)
        (declare-const x Float32)
        (assert (fp.isNaN (_ NaN 8 24)))
        (assert (not (fp.isNaN x)))
        (assert (fp.lt x (fp #b0 #b10000000 #b00000000000000000000000)))
        (assert (fp.isInfinite (_ +oo 8 24)))
        (assert (= (fp.abs x) (fp.abs (fp.neg x))))
        (check-sat)
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.assertions.len(), 5);
}

#[test]
fn parses_and_evaluates_rounding_mode_fp_arithmetic() {
    // `fp.add RNE 1.0 1.0 == 2.0` over Float32: the rounding-mode FP front-end
    // lowers to the validated axeyum-fp builders, so the ground assertion
    // evaluates to true. (1.0 = 0x3F800000, 2.0 = 0x40000000.)
    let text = r"
        (set-logic QF_FP)
        (assert (fp.eq
                  (fp.add RNE
                    (fp #b0 #b01111111 #b00000000000000000000000)
                    (fp #b0 #b01111111 #b00000000000000000000000))
                  (fp #b0 #b10000000 #b00000000000000000000000)))
        (check-sat)
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.assertions.len(), 1);
    let v = eval(&script.arena, script.assertions[0], &Assignment::default()).unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn parses_symbolic_round_to_integral_and_fp_conversions() {
    use axeyum_ir::Sort;

    // fp.roundToIntegral now uses the symbolic builder, so it parses over a
    // declared (non-constant) Float32 operand.
    let sym = parse_script(
        r"
        (set-logic QF_FP)
        (declare-const x Float32)
        (assert (fp.eq (fp.roundToIntegral RTZ x) x))
        (check-sat)
    ",
    )
    .unwrap();
    assert_eq!(sym.assertions.len(), 1);

    // fp.roundToIntegral RTZ 2.5 == 2.0 evaluates to true (constant operand).
    // 2.5 = (fp 0 10000000 0100…0), 2.0 = (fp 0 10000000 0…0) over Float32.
    let rti = parse_script(
        r"
        (set-logic QF_FP)
        (assert (fp.eq
                  (fp.roundToIntegral RTZ
                    (fp #b0 #b10000000 #b01000000000000000000000))
                  (fp #b0 #b10000000 #b00000000000000000000000)))
        (check-sat)
    ",
    )
    .unwrap();
    let v = eval(&rti.arena, rti.assertions[0], &Assignment::default()).unwrap();
    assert_eq!(v, Value::Bool(true));

    // fp.to_real on a constant 2.0 folds to the rational 2.
    let to_real = parse_script(
        r"
        (set-logic QF_FP)
        (assert (= (fp.to_real (fp #b0 #b10000000 #b00000000000000000000000)) 2.0))
        (check-sat)
    ",
    )
    .unwrap();
    let v = eval(&to_real.arena, to_real.assertions[0], &Assignment::default()).unwrap();
    assert_eq!(v, Value::Bool(true));

    // ((_ to_fp 8 24) bv) bit-reinterprets a BitVec(32) as Float32 (identity);
    // classifying the reinterpreted 2.0 pattern as not-NaN is true.
    let reinterpret = parse_script(
        r"
        (set-logic QF_FP)
        (assert (not (fp.isNaN ((_ to_fp 8 24) #x40000000))))
        (check-sat)
    ",
    )
    .unwrap();
    let v = eval(
        &reinterpret.arena,
        reinterpret.assertions[0],
        &Assignment::default(),
    )
    .unwrap();
    assert_eq!(v, Value::Bool(true));
    assert_eq!(reinterpret.arena.sort_of(reinterpret.assertions[0]), Sort::Bool);
}

#[test]
#[allow(clippy::similar_names)]
fn parses_and_folds_unambiguous_fp_conversions() {
    // real → fp: (_ to_fp 8 24) RNE 2.0 == the Float32 bit pattern for 2.0.
    let r2fp = parse_script(
        r"
        (set-logic QF_FP)
        (assert (fp.eq ((_ to_fp 8 24) RNE 2.0)
                       (fp #b0 #b10000000 #b00000000000000000000000)))
        (check-sat)
    ",
    )
    .unwrap();
    let v = eval(&r2fp.arena, r2fp.assertions[0], &Assignment::default()).unwrap();
    assert_eq!(v, Value::Bool(true));

    // unsigned bv → fp: (_ to_fp_unsigned 8 24) RNE #x00000002 == 2.0.
    let u2fp = parse_script(
        r"
        (set-logic QF_BVFP)
        (assert (fp.eq ((_ to_fp_unsigned 8 24) RNE #x00000002)
                       (fp #b0 #b10000000 #b00000000000000000000000)))
        (check-sat)
    ",
    )
    .unwrap();
    let v = eval(&u2fp.arena, u2fp.assertions[0], &Assignment::default()).unwrap();
    assert_eq!(v, Value::Bool(true));

    // fp → unsigned bv: (_ fp.to_ubv 32) RNE 2.0 == #x00000002.
    let to_ubv_script = parse_script(
        r"
        (set-logic QF_BVFP)
        (assert (= ((_ fp.to_ubv 32) RNE (fp #b0 #b10000000 #b00000000000000000000000))
                   #x00000002))
        (check-sat)
    ",
    )
    .unwrap();
    let v = eval(&to_ubv_script.arena, to_ubv_script.assertions[0], &Assignment::default()).unwrap();
    assert_eq!(v, Value::Bool(true));

    // fp → signed bv: (_ fp.to_sbv 32) RNE -2.0 == the two's-complement of 2.
    let to_sbv_script = parse_script(
        r"
        (set-logic QF_BVFP)
        (assert (= ((_ fp.to_sbv 32) RNE (fp #b1 #b10000000 #b00000000000000000000000))
                   (bvneg #x00000002)))
        (check-sat)
    ",
    )
    .unwrap();
    let v = eval(&to_sbv_script.arena, to_sbv_script.assertions[0], &Assignment::default()).unwrap();
    assert_eq!(v, Value::Bool(true));

    // Non-dyadic real → fp is reported unsupported, never double-rounded.
    let nd = parse_script(
        r"
        (set-logic QF_FP)
        (assert (fp.isNaN ((_ to_fp 8 24) RNE (/ 1.0 3.0))))
        (check-sat)
    ",
    );
    assert!(matches!(nd, Err(SmtError::Unsupported(_))), "got {nd:?}");

    // A symbolic bit-vector-source to_fp is now signed-BV->FP (no longer
    // ambiguous, since FP operands carry Sort::Float): it parses into a circuit.
    let sbv_sym = parse_script(
        r"
        (set-logic QF_BVFP)
        (declare-const b (_ BitVec 32))
        (assert (fp.isNaN ((_ to_fp 8 24) RNE b)))
        (check-sat)
    ",
    );
    assert!(sbv_sym.is_ok(), "symbolic signed-BV->FP should parse: {sbv_sym:?}");
}

#[test]
#[allow(clippy::similar_names)]
fn parses_sort_disambiguated_to_fp_conversions() {
    // ADR-0026 stage 2/3: with a first-class Float sort, (_ to_fp eb sb) is
    // disambiguated by operand sort, so FP->FP reformat and signed-BV->FP both
    // parse and fold (previously rejected as ambiguous).

    // Float64 2.0 -> Float32 2.0. F64 2.0 = (fp 0 10000000000 0…0[52]);
    // F32 2.0 = 0x40000000.
    let fp_to_fp = parse_script(
        r"
        (set-logic QF_FP)
        (assert (fp.eq
                  ((_ to_fp 8 24) RNE
                    (fp #b0 #b10000000000
                        #b0000000000000000000000000000000000000000000000000000))
                  (fp #b0 #b10000000 #b00000000000000000000000)))
        (check-sat)
    ",
    )
    .unwrap();
    let v = eval(&fp_to_fp.arena, fp_to_fp.assertions[0], &Assignment::default()).unwrap();
    assert_eq!(v, Value::Bool(true));

    // Signed bit-vector -2 (two's complement 0xFFFFFFFE) -> Float32 -2.0.
    let sbv_to_fp = parse_script(
        r"
        (set-logic QF_BVFP)
        (assert (fp.eq ((_ to_fp 8 24) RNE #xFFFFFFFE)
                       (fp #b1 #b10000000 #b00000000000000000000000)))
        (check-sat)
    ",
    )
    .unwrap();
    let v = eval(&sbv_to_fp.arena, sbv_to_fp.assertions[0], &Assignment::default()).unwrap();
    assert_eq!(v, Value::Bool(true));

    // A declared Float32 variable now carries the Float sort, and round-trips
    // through to_fp identity (Float32 -> Float32) symbolically (sat).
    let decl = parse_script(
        r"
        (set-logic QF_FP)
        (declare-const x Float32)
        (assert (fp.eq ((_ to_fp 8 24) RNE x) x))
        (check-sat)
    ",
    )
    .unwrap();
    let sym = decl.arena.find_symbol("x").unwrap();
    assert_eq!(
        decl.arena.symbol(sym).1,
        axeyum_ir::Sort::Float { exp: 8, sig: 24 }
    );
}

#[test]
fn folds_constant_float64_fma() {
    // F64 fp.fma's symbolic circuit exceeds MAX_BV_WIDTH, but constant operands
    // under RNE fold via native mul_add: fma(2.0, 3.0, 1.0) == 7.0 (Float64).
    // Constants built by bit reinterpret of their IEEE hex patterns.
    let script = parse_script(
        r"
        (set-logic QF_FP)
        (assert (fp.eq
                  (fp.fma RNE
                    ((_ to_fp 11 53) #x4000000000000000)
                    ((_ to_fp 11 53) #x4008000000000000)
                    ((_ to_fp 11 53) #x3FF0000000000000))
                  ((_ to_fp 11 53) #x401C000000000000)))
        (check-sat)
    ",
    )
    .unwrap();
    let v = eval(&script.arena, script.assertions[0], &Assignment::default()).unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn float128_nonarithmetic_ops_decide() {
    // F128 (15,113) is exactly 128 bits, so the whole non-arithmetic surface —
    // classification, comparison, sign, min/max, eq — decides with no wider
    // intermediate. Each assertion below is a tautology over F128 constants.
    let tautologies = [
        "(fp.isInfinite (_ +oo 15 113))",
        "(not (fp.isNaN (_ +oo 15 113)))",
        "(fp.isNaN (_ NaN 15 113))",
        "(fp.isZero (_ +zero 15 113))",
        "(fp.isZero (_ -zero 15 113))",
        "(fp.eq (_ +zero 15 113) (_ -zero 15 113))",      // +0 == -0
        "(not (fp.eq (_ NaN 15 113) (_ NaN 15 113)))",    // NaN != NaN
        "(fp.lt (_ -oo 15 113) (_ +oo 15 113))",
        "(fp.leq (_ +zero 15 113) (_ +zero 15 113))",
        "(fp.isNegative (_ -oo 15 113))",
        "(fp.isPositive (_ +oo 15 113))",
        "(fp.eq (fp.abs (_ -oo 15 113)) (_ +oo 15 113))",  // abs(-inf) = +inf
        "(fp.eq (fp.neg (_ +oo 15 113)) (_ -oo 15 113))",  // neg(+inf) = -inf
        "(fp.eq (fp.min (_ -oo 15 113) (_ +oo 15 113)) (_ -oo 15 113))",
        "(fp.eq (fp.max (_ -oo 15 113) (_ +oo 15 113)) (_ +oo 15 113))",
    ];
    for t in tautologies {
        let text = format!("(set-logic QF_FP)\n(assert {t})\n(check-sat)\n");
        let script = parse_script(&text).unwrap_or_else(|e| panic!("parse {t}: {e:?}"));
        let v = eval(&script.arena, script.assertions[0], &Assignment::default())
            .unwrap_or_else(|e| panic!("eval {t}: {e:?}"));
        assert_eq!(v, Value::Bool(true), "F128 tautology failed: {t}");
    }

    // F128 *arithmetic* still exceeds MAX_BV_WIDTH (2*113+5 = 231 > 128) and is
    // reported cleanly (sound), not silently wrong.
    let arith = parse_script(
        "(set-logic QF_FP)\n\
         (assert (fp.eq (fp.add RNE (_ +zero 15 113) (_ +zero 15 113)) (_ +zero 15 113)))\n\
         (check-sat)\n",
    );
    assert!(
        matches!(arith, Err(SmtError::Ir(_) | SmtError::Unsupported(_))),
        "F128 arithmetic should error cleanly, got {arith:?}"
    );
}
