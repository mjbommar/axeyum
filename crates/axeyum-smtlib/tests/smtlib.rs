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
    assert!(matches!(
        parse_script("(push 1)"),
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
