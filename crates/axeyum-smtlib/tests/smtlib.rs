//! Reader/writer tests: feature coverage, round trips, and corpus smoke.

use axeyum_ir::{Assignment, Sort, SymbolId, TermStats, Value, eval};
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
    // An unknown command is still a clear unsupported error.
    assert!(matches!(
        parse_script("(some-unknown-command 0)"),
        Err(SmtError::Unsupported(_))
    ));
    // Arity-0 `declare-sort` is now accepted (modeled as a BitVec); an arity-N
    // (parametric) declared sort is still a graceful unsupported error.
    assert!(parse_script("(declare-sort S 0)").is_ok());
    assert!(matches!(
        parse_script("(declare-sort List 1)"),
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
fn uninterpreted_sort_is_modeled_as_bitvec() {
    // `(declare-sort U 0)` constants resolve to the same `BitVec(W)` width, so an
    // equality between two `U`-typed constants parses as a plain BV equality.
    let text = r"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun a () U)
        (declare-fun b () U)
        (assert (= a b))
        (check-sat)
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.assertions.len(), 1);
    let a = script.arena.find_symbol("a").unwrap();
    let b = script.arena.find_symbol("b").unwrap();
    let (_, sort_a) = script.arena.symbol(a);
    let (_, sort_b) = script.arena.symbol(b);
    let Sort::BitVec(w) = sort_a else {
        panic!("U constant should resolve to a BitVec sort, got {sort_a:?}");
    };
    assert!(w >= 1, "modeling width must be at least 1");
    assert_eq!(sort_a, sort_b, "both U constants must share one width");
}

#[test]
fn uninterpreted_sort_distinct_has_room_for_all_tokens() {
    // Three pairwise-distinct `U`-typed constants must fit in the modeling width
    // (2^W ≥ 3). The width is sized from the whole-script node count + margin, so
    // this can never be forced unsat by running out of distinct BV values.
    let text = r"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun a () U)
        (declare-fun b () U)
        (declare-fun c () U)
        (assert (distinct a b c))
        (check-sat)
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.assertions.len(), 1);
    let a = script.arena.find_symbol("a").unwrap();
    let Sort::BitVec(w) = script.arena.symbol(a).1 else {
        panic!("U constant should resolve to a BitVec sort");
    };
    // The encoding must be able to represent at least the 3 distinct tokens.
    assert!(
        u64::from(w) >= 2,
        "width {w} cannot hold 3 distinct values (need 2^W ≥ 3)"
    );
}

#[test]
fn uninterpreted_function_over_sort_parses() {
    // A function over the uninterpreted sort `(declare-fun f (U) U)` becomes a
    // `BitVec(W) → BitVec(W)` uninterpreted function; a congruence formula
    // (a = b ∧ f(a) ≠ f(b)) parses cleanly into two assertions.
    let text = r"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun a () U)
        (declare-fun b () U)
        (declare-fun f (U) U)
        (assert (= a b))
        (assert (not (= (f a) (f b))))
        (check-sat)
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.assertions.len(), 2);
    // f's result is a BV of the modeling width.
    let fa = script.assertions[1];
    // The second assertion is `(not (= (f a) (f b)))`; just confirm it built and
    // that f's applications are BV-sorted via the term's sort.
    assert_eq!(script.arena.sort_of(fa), Sort::Bool);
}

#[test]
fn uninterpreted_sort_collisions_and_arity_are_errors() {
    // Duplicate declared sort name.
    assert!(matches!(
        parse_script("(declare-sort U 0) (declare-sort U 0)"),
        Err(SmtError::Syntax(_))
    ));
    // A builtin sort name cannot be redeclared.
    assert!(matches!(
        parse_script("(declare-sort Int 0)"),
        Err(SmtError::Syntax(_))
    ));
    // Non-numeric arity is a syntax error.
    assert!(matches!(
        parse_script("(declare-sort U x)"),
        Err(SmtError::Syntax(_))
    ));
    // Parametric (arity ≥ 1) is gracefully unsupported.
    assert!(matches!(
        parse_script("(declare-sort Pair 2)"),
        Err(SmtError::Unsupported(_))
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
    assert!(
        rendered.contains("(as const (Array (_ BitVec 4) (_ BitVec 8)))"),
        "renders as const: {rendered}"
    );
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
    assert!(
        rendered.contains("((_ int2bv 8) "),
        "renders int2bv: {rendered}"
    );
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
fn coerces_non_constant_int_to_real_in_mixed_arithmetic() {
    // An Int *variable* `n` appearing in a Real `+` / `=` context is embedded via
    // the exact `to_real` operator. Bind n := 2, y := 5.0 and evaluate:
    //   (= y (+ (to_real n) 3.0))  ->  5.0 == 2 + 3.0  ->  true.
    let text = r"
        (set-logic QF_LIRA)
        (declare-fun n () Int)
        (declare-fun y () Real)
        (assert (= y (+ n 3.0)))
        (check-sat)
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.assertions.len(), 1);

    let n = script.arena.find_symbol("n").unwrap();
    let y = script.arena.find_symbol("y").unwrap();

    // n = 2, y = 5.0 -> assertion true (5.0 == to_real(2) + 3.0).
    let mut asg_true = Assignment::new();
    asg_true.set(n, Value::Int(2));
    asg_true.set(y, Value::Real(axeyum_ir::Rational::integer(5)));
    assert_eq!(
        eval(&script.arena, script.assertions[0], &asg_true).unwrap(),
        Value::Bool(true),
    );

    // n = 2, y = 4.0 -> assertion false (4.0 != 5.0).
    let mut asg_false = Assignment::new();
    asg_false.set(n, Value::Int(2));
    asg_false.set(y, Value::Real(axeyum_ir::Rational::integer(4)));
    assert_eq!(
        eval(&script.arena, script.assertions[0], &asg_false).unwrap(),
        Value::Bool(false),
    );

    // Round-trips through the writer (the coercion survives re-parse).
    let rendered = write_script(&script.arena, &script.assertions);
    let reparsed = parse_script(&rendered).unwrap();
    assert_eq!(reparsed.assertions.len(), 1);
}

#[test]
fn coerces_non_constant_int_in_mixed_comparison() {
    // Int variable `n` on the Real side of `<`: (< n y) with n := 3, y := 4.5
    // is true (to_real(3) = 3 < 4.5); with y := 2.5 it is false.
    let text = r"
        (set-logic QF_LIRA)
        (declare-fun n () Int)
        (declare-fun y () Real)
        (assert (< n y))
        (check-sat)
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.assertions.len(), 1);

    let n = script.arena.find_symbol("n").unwrap();
    let y = script.arena.find_symbol("y").unwrap();

    let mut asg_true = Assignment::new();
    asg_true.set(n, Value::Int(3));
    asg_true.set(y, Value::Real(axeyum_ir::Rational::new(9, 2)));
    assert_eq!(
        eval(&script.arena, script.assertions[0], &asg_true).unwrap(),
        Value::Bool(true),
    );

    let mut asg_false = Assignment::new();
    asg_false.set(n, Value::Int(3));
    asg_false.set(y, Value::Real(axeyum_ir::Rational::new(5, 2)));
    assert_eq!(
        eval(&script.arena, script.assertions[0], &asg_false).unwrap(),
        Value::Bool(false),
    );
}

#[test]
fn real_division_over_integer_constants_folds_to_rational() {
    // `/` is always Real-typed: `(/ 1 4)` over two integer constants denotes the
    // rational 1/4, even though neither operand is syntactically Real. Bind
    // y := 1/4 and check (= y (/ 1 4)) -> true; y := 1/2 -> false.
    let text = r"
        (set-logic QF_NRA)
        (declare-fun y () Real)
        (assert (= y (/ 1 4)))
        (check-sat)
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.assertions.len(), 1);

    let y = script.arena.find_symbol("y").unwrap();
    let mut asg_true = Assignment::new();
    asg_true.set(y, Value::Real(axeyum_ir::Rational::new(1, 4)));
    assert_eq!(
        eval(&script.arena, script.assertions[0], &asg_true).unwrap(),
        Value::Bool(true),
    );
    let mut asg_false = Assignment::new();
    asg_false.set(y, Value::Real(axeyum_ir::Rational::new(1, 2)));
    assert_eq!(
        eval(&script.arena, script.assertions[0], &asg_false).unwrap(),
        Value::Bool(false),
    );
}

#[test]
fn pure_int_context_is_not_coerced() {
    // No Real operand anywhere: `div`/`mod`/`<` stay integer-typed. Evaluating
    // (= (div n 2) 3) with n := 7 gives 7 div 2 = 3 -> true, exercising integer
    // (not real) division — the coercion must NOT fire here.
    let text = r"
        (set-logic QF_LIA)
        (declare-fun n () Int)
        (assert (= (div n 2) 3))
        (check-sat)
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.assertions.len(), 1);

    let n = script.arena.find_symbol("n").unwrap();
    // The asserted equality's left operand is Int-sorted (integer div), so the
    // result stays an integer comparison.
    assert_eq!(script.arena.sort_of(script.assertions[0]), Sort::Bool);

    let mut asg = Assignment::new();
    asg.set(n, Value::Int(7));
    assert_eq!(
        eval(&script.arena, script.assertions[0], &asg).unwrap(),
        Value::Bool(true),
    );
    // 6 div 2 = 3 too; 8 div 2 = 4 -> false. Confirms truncating int division.
    let mut asg2 = Assignment::new();
    asg2.set(n, Value::Int(8));
    assert_eq!(
        eval(&script.arena, script.assertions[0], &asg2).unwrap(),
        Value::Bool(false),
    );
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
    let v = eval(
        &to_real.arena,
        to_real.assertions[0],
        &Assignment::default(),
    )
    .unwrap();
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
    assert_eq!(
        reinterpret.arena.sort_of(reinterpret.assertions[0]),
        Sort::Bool
    );
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
    let v = eval(
        &to_ubv_script.arena,
        to_ubv_script.assertions[0],
        &Assignment::default(),
    )
    .unwrap();
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
    let v = eval(
        &to_sbv_script.arena,
        to_sbv_script.assertions[0],
        &Assignment::default(),
    )
    .unwrap();
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
    assert!(
        sbv_sym.is_ok(),
        "symbolic signed-BV->FP should parse: {sbv_sym:?}"
    );
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
    let v = eval(
        &fp_to_fp.arena,
        fp_to_fp.assertions[0],
        &Assignment::default(),
    )
    .unwrap();
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
    let v = eval(
        &sbv_to_fp.arena,
        sbv_to_fp.assertions[0],
        &Assignment::default(),
    )
    .unwrap();
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
    // Constant F64 fp.fma operands under RNE fold via native mul_add:
    // fma(2.0, 3.0, 1.0) == 7.0 (Float64). (The symbolic F64 circuit also runs,
    // through the wide bit-vector path — see the solver-level fma tests.)
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
        "(fp.eq (_ +zero 15 113) (_ -zero 15 113))", // +0 == -0
        "(not (fp.eq (_ NaN 15 113) (_ NaN 15 113)))", // NaN != NaN
        "(fp.lt (_ -oo 15 113) (_ +oo 15 113))",
        "(fp.leq (_ +zero 15 113) (_ +zero 15 113))",
        "(fp.isNegative (_ -oo 15 113))",
        "(fp.isPositive (_ +oo 15 113))",
        "(fp.eq (fp.abs (_ -oo 15 113)) (_ +oo 15 113))", // abs(-inf) = +inf
        "(fp.eq (fp.neg (_ +oo 15 113)) (_ -oo 15 113))", // neg(+inf) = -inf
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

    // F128 *arithmetic* now runs through the wide bit-vector path (ADR-0028,
    // validated against rustc_apfloat): `+0 + +0 == +0` builds and evaluates to
    // true rather than erroring.
    let script = parse_script(
        "(set-logic QF_FP)\n\
         (assert (fp.eq (fp.add RNE (_ +zero 15 113) (_ +zero 15 113)) (_ +zero 15 113)))\n\
         (check-sat)\n",
    )
    .expect("F128 arithmetic is supported");
    let v = eval(&script.arena, script.assertions[0], &Assignment::default()).unwrap();
    assert_eq!(v, Value::Bool(true), "F128 (+0 + +0 == +0) should hold");
}

#[test]
fn string_const_and_literal_parse_into_packed_bitvectors() {
    // First slice of the string front end (ADR-0029): a String constant parses
    // (a packed bit-vector with a canonical well-formedness assertion) and a
    // string literal parses into a constant; `(= s "ab")` is a Bool assertion.
    let script = parse_script("(declare-const s String)\n(assert (= s \"ab\"))\n(check-sat)\n")
        .expect("String const + literal should parse");
    // The declare injects one well-formedness assertion; the assert adds another.
    assert_eq!(script.assertions.len(), 2, "wf constraint + the equality");
}

/// Packs a byte string into the parser's canonical bounded-string bit-vector
/// (length in the low 4 bits, byte `i` at bits `[4 + 8i, +8)`), mirroring
/// `pack_string_literal`. `STRING_MAX_LEN = 8`, `STRING_TOTAL = 4 + 8·8 = 68`.
fn pack_str(bytes: &[u8]) -> u128 {
    assert!(bytes.len() <= 8);
    let mut content: u128 = 0;
    for (i, &b) in bytes.iter().enumerate() {
        content |= u128::from(b) << (8 * i);
    }
    u128::try_from(bytes.len()).unwrap() | (content << 4)
}

/// Evaluates every assertion of a parsed script under one concrete assignment of
/// the (single) string symbol `s` to a packed value, AND-ing the Bool results.
fn eval_string_script(text: &str, s_packed: u128) -> bool {
    let script = parse_script(text).expect("script parses");
    let sym = script.arena.find_symbol("s").expect("s declared");
    let mut asg = Assignment::new();
    asg.set(
        sym,
        Value::Bv {
            width: 68,
            value: s_packed,
        },
    );
    script
        .assertions
        .iter()
        .all(|&a| eval(&script.arena, a, &asg).unwrap() == Value::Bool(true))
}

#[test]
fn string_len_and_contains_decide_via_bv_eval() {
    // (str.len s) == 3 ∧ (str.contains s "a") — oracle-checked by evaluating the
    // packed-BV encoding against concrete witnesses.
    let text = "(declare-fun s () String)\n\
                (assert (= (str.len s) 3))\n\
                (assert (str.contains s \"a\"))\n(check-sat)\n";
    assert!(eval_string_script(text, pack_str(b"bah")), "len 3, has 'a'");
    assert!(!eval_string_script(text, pack_str(b"ab")), "len 2 ⇒ false");
    assert!(
        !eval_string_script(text, pack_str(b"xyz")),
        "no 'a' ⇒ false"
    );
}

#[test]
fn string_equality_with_wrong_length_is_unsat_shaped() {
    // (= s "a") ∧ (= (str.len s) 2): no witness satisfies both (a small UNSAT).
    let text = "(declare-fun s () String)\n\
                (assert (= s \"a\"))\n\
                (assert (= (str.len s) 2))\n(check-sat)\n";
    // "a" forces len 1, so the len-2 assertion can never hold for the equal value.
    assert!(!eval_string_script(text, pack_str(b"a")), "len 1 ≠ 2");
    assert!(!eval_string_script(text, pack_str(b"ab")), "≠ \"a\"");
}

#[test]
fn string_at_and_const_concat_eval() {
    // (= (str.at s 0) "h") ∧ (= s (str.++ "h" "i")): str.at picks byte 0, and the
    // constant-folded concat equals "hi".
    let text = "(declare-fun s () String)\n\
                (assert (= (str.at s 0) \"h\"))\n\
                (assert (= s (str.++ \"h\" \"i\")))\n(check-sat)\n";
    assert!(eval_string_script(text, pack_str(b"hi")), "s = \"hi\"");
    assert!(!eval_string_script(text, pack_str(b"ho")), "s ≠ \"hi\"");
}

/// Evaluates every assertion of a parsed script under concrete assignments of the
/// named string symbols (each to its packed bit-vector value), AND-ing the Bool
/// results. The packed width is taken from each symbol's declared sort, so it
/// works for the `STRING_MAX_LEN` declared layout.
fn eval_string_script_vars(text: &str, vars: &[(&str, &[u8])]) -> bool {
    let mut script = parse_script(text).expect("script parses");
    let mut asg = Assignment::new();
    for &(name, bytes) in vars {
        let sym = script.arena.find_symbol(name).expect("symbol declared");
        let v = script.arena.var(sym);
        let Sort::BitVec(width) = script.arena.sort_of(v) else {
            panic!("string symbol should be a bit-vector");
        };
        asg.set(
            sym,
            Value::Bv {
                width,
                value: pack_str(bytes),
            },
        );
    }
    script
        .assertions
        .iter()
        .all(|&a| eval(&script.arena, a, &asg).unwrap() == Value::Bool(true))
}

#[test]
fn variable_concat_length_and_equality_eval() {
    // (= (str.++ a b) "xy") ∧ (= (str.len a) 1): the only witnesses pair a one-byte
    // `a` with the matching `b` so the concat spells "xy". Oracle-checked by
    // concrete evaluation of the packed-BV encoding (no solver dependency).
    let text = "(declare-fun a () String)\n\
                (declare-fun b () String)\n\
                (assert (= (str.++ a b) \"xy\"))\n\
                (assert (= (str.len a) 1))\n(check-sat)\n";
    assert!(
        eval_string_script_vars(text, &[("a", b"x"), ("b", b"y")]),
        "a=\"x\", b=\"y\" ⇒ a++b = \"xy\", len a = 1"
    );
    assert!(
        !eval_string_script_vars(text, &[("a", b"xy"), ("b", b"")]),
        "len a = 2 violates the len-1 assertion"
    );
    assert!(
        !eval_string_script_vars(text, &[("a", b"x"), ("b", b"z")]),
        "a++b = \"xz\" ≠ \"xy\""
    );
}

#[test]
fn variable_concat_length_conflict_is_unsat_shaped() {
    // (= (str.++ a b) "x") ∧ (= (str.len a) 1) ∧ (= (str.len b) 1): the concat would
    // have length 2, but "x" has length 1 — no witness, a small UNSAT.
    let text = "(declare-fun a () String)\n\
                (declare-fun b () String)\n\
                (assert (= (str.++ a b) \"x\"))\n\
                (assert (= (str.len a) 1))\n\
                (assert (= (str.len b) 1))\n(check-sat)\n";
    // Every concrete assignment with len a = len b = 1 makes a++b length 2 ≠ 1.
    for a in [&b"x"[..], b"y", b"z"] {
        for b in [&b"x"[..], b"y", b"a"] {
            assert!(
                !eval_string_script_vars(text, &[("a", a), ("b", b)]),
                "len(a)=len(b)=1 ⇒ |a++b| = 2 ≠ 1"
            );
        }
    }
}

#[test]
fn variable_concat_at_and_contains_decide() {
    // str.at and str.contains over a variable concat result decide via the wider
    // packed sort. (= (str.at (str.++ a b) 0) "h") picks the first byte of a++b.
    let text = "(declare-fun a () String)\n\
                (declare-fun b () String)\n\
                (assert (= (str.at (str.++ a b) 0) \"h\"))\n\
                (assert (str.contains (str.++ a b) \"i\"))\n(check-sat)\n";
    assert!(
        eval_string_script_vars(text, &[("a", b"hi"), ("b", b"")]),
        "a++b = \"hi\": byte0 = 'h', contains \"i\""
    );
    assert!(
        eval_string_script_vars(text, &[("a", b"h"), ("b", b"i")]),
        "a++b = \"hi\" across the boundary"
    );
    assert!(
        !eval_string_script_vars(text, &[("a", b"ab"), ("b", b"i")]),
        "a++b = \"abi\": byte0 = 'a' ≠ 'h'"
    );
}

#[test]
fn variable_concat_over_bound_declines_gracefully() {
    // Two declared strings are max_len 8 each, so a++b is max_len 16 (fits the cap).
    // A *third* concat would be max_len 24 > the 16-byte cap, so it must decline as
    // Unsupported (Unknown to the consumer) — never a wrong verdict.
    let err = parse_script(
        "(declare-fun a () String)\n\
         (declare-fun b () String)\n\
         (declare-fun c () String)\n\
         (assert (= (str.++ (str.++ a b) c) \"z\"))\n(check-sat)\n",
    )
    .expect_err("max_len 24 exceeds the 16-byte cap");
    let SmtError::Unsupported(msg) = err else {
        panic!("expected Unsupported for the over-cap concat, got {err:?}");
    };
    assert!(msg.contains("exceeds the cap"), "actionable msg: {msg}");
}

#[test]
fn string_prefix_and_suffix_eval() {
    let text = "(declare-fun s () String)\n\
                (assert (str.prefixof \"ab\" s))\n\
                (assert (str.suffixof \"yz\" s))\n(check-sat)\n";
    assert!(eval_string_script(text, pack_str(b"abxyz")), "ab…yz");
    assert!(
        !eval_string_script(text, pack_str(b"abxxx")),
        "no yz suffix"
    );
    assert!(
        !eval_string_script(text, pack_str(b"xxxyz")),
        "no ab prefix"
    );
}

/// Evaluates every assertion of a parsed script under concrete assignments of
/// the named **string** symbols (each to its packed bit-vector) and the named
/// **Int** symbols (each to an integer), AND-ing the Bool results. Lets the
/// Int-indexed string ops (`str.at`/`str.substr` with a non-constant index) be
/// oracle-checked by concrete evaluation of the packed-BV encoding.
fn eval_string_int_script(
    text: &str,
    str_vars: &[(&str, &[u8])],
    int_vars: &[(&str, i128)],
) -> bool {
    let mut script = parse_script(text).expect("script parses");
    let mut asg = Assignment::new();
    for &(name, bytes) in str_vars {
        let sym = script
            .arena
            .find_symbol(name)
            .expect("string symbol declared");
        let v = script.arena.var(sym);
        let Sort::BitVec(width) = script.arena.sort_of(v) else {
            panic!("string symbol should be a bit-vector");
        };
        asg.set(
            sym,
            Value::Bv {
                width,
                value: pack_str(bytes),
            },
        );
    }
    for &(name, value) in int_vars {
        let sym = script.arena.find_symbol(name).expect("int symbol declared");
        asg.set(sym, Value::Int(value));
    }
    script
        .assertions
        .iter()
        .all(|&a| eval(&script.arena, a, &asg).unwrap() == Value::Bool(true))
}

/// Evaluates the single assertion of a fully-**constant** script (no free
/// symbols) and returns whether it is `true`. Used to oracle-check the string
/// ops over constant arguments (they fold to a concrete Bool).
fn eval_const_script(text: &str) -> bool {
    let script = parse_script(text).expect("script parses");
    let asg = Assignment::new();
    script
        .assertions
        .iter()
        .all(|&a| eval(&script.arena, a, &asg).unwrap() == Value::Bool(true))
}

#[test]
fn string_substr_constant_eval() {
    // (= (str.substr "hello" 1 3) "ell"): the middle 3 bytes. Out-of-range cases
    // (negative offset, offset ≥ len, non-positive length) all yield "".
    assert!(
        eval_const_script("(assert (= (str.substr \"hello\" 1 3) \"ell\"))\n"),
        "\"ell\" extracted"
    );
    assert!(
        eval_const_script("(assert (= (str.substr \"hello\" 9 3) \"\"))\n"),
        "offset ≥ len ⇒ \"\""
    );
    assert!(
        eval_const_script("(assert (= (str.substr \"hello\" (- 1) 3) \"\"))\n"),
        "negative off ⇒ \"\""
    );
    assert!(
        eval_const_script("(assert (= (str.substr \"hello\" 1 0) \"\"))\n"),
        "n = 0 ⇒ \"\""
    );
    // Clamped length: off+n past the end stops at |s|.
    assert!(
        eval_const_script("(assert (= (str.substr \"hello\" 3 9) \"lo\"))\n"),
        "clamped to |s|"
    );
}

#[test]
fn string_substr_variable_index_eval() {
    // (= (str.substr x i 3) "ell") with x = "hello": only i = 1 makes it true.
    let text = "(declare-fun x () String)\n\
                (declare-fun i () Int)\n\
                (assert (= (str.substr x i 3) \"ell\"))\n(check-sat)\n";
    assert!(
        eval_string_int_script(text, &[("x", b"hello")], &[("i", 1)]),
        "x=\"hello\", i=1 ⇒ substr = \"ell\""
    );
    assert!(
        !eval_string_int_script(text, &[("x", b"hello")], &[("i", 0)]),
        "i=0 ⇒ \"hel\" ≠ \"ell\""
    );
    assert!(
        !eval_string_int_script(text, &[("x", b"hello")], &[("i", 9)]),
        "i out of range ⇒ \"\" ≠ \"ell\""
    );
}

#[test]
fn string_at_variable_index_eval() {
    // (= (str.at "ab" i) "b") → true only at i = 1. Models the regression shape
    // `(= (str.at x i) "b")` with a non-constant Int index.
    let text = "(declare-fun i () Int)\n\
                (assert (= (str.at \"ab\" i) \"b\"))\n(check-sat)\n";
    assert!(eval_string_int_script(text, &[], &[("i", 1)]), "ab[1] = b");
    assert!(!eval_string_int_script(text, &[], &[("i", 0)]), "ab[0] = a");
    assert!(
        !eval_string_int_script(text, &[], &[("i", 5)]),
        "out of range ⇒ \"\" ≠ \"b\""
    );
    assert!(
        !eval_string_int_script(text, &[], &[("i", -1)]),
        "negative ⇒ \"\" ≠ \"b\""
    );
}

#[test]
fn string_to_code_eval() {
    // (= (str.to_code "A") 65); a 2-char string ⇒ -1; "" ⇒ -1.
    assert!(
        eval_const_script("(assert (= (str.to_code \"A\") 65))\n"),
        "code of 'A' is 65"
    );
    assert!(
        eval_const_script("(assert (= (str.to_code \"AB\") (- 1)))\n"),
        "len 2 ⇒ -1"
    );
    assert!(
        eval_const_script("(assert (= (str.to_code \"\") (- 1)))\n"),
        "empty ⇒ -1"
    );
}

#[test]
fn string_from_code_roundtrip_eval() {
    // (= (str.from_code 65) "A") and the round-trip (= (str.to_code (str.from_code 66)) 66).
    assert!(
        eval_const_script("(assert (= (str.from_code 65) \"A\"))\n"),
        "from_code 65 = \"A\""
    );
    assert!(
        eval_const_script("(assert (= (str.to_code (str.from_code 66)) 66))\n"),
        "to_code ∘ from_code round-trips on ASCII"
    );
    // Out-of-range code → "" (conservative for non-ASCII).
    assert!(
        eval_const_script("(assert (= (str.from_code (- 1)) \"\"))\n"),
        "negative code ⇒ \"\""
    );
}

#[test]
fn string_lex_order_eval() {
    // str.< / str.<= over constants: "AC" < "AF", "ab" < "abc" (prefix), and the
    // reflexive/antisymmetric corners.
    assert!(
        eval_const_script("(assert (str.< \"AC\" \"AF\"))\n"),
        "AC < AF (byte order)"
    );
    assert!(
        eval_const_script("(assert (str.< \"ab\" \"abc\"))\n"),
        "proper prefix is less"
    );
    assert!(
        eval_const_script("(assert (not (str.< \"AF\" \"AC\")))\n"),
        "AF not < AC"
    );
    assert!(
        eval_const_script("(assert (not (str.< \"ab\" \"ab\")))\n"),
        "strict: ab not < ab"
    );
    assert!(
        eval_const_script("(assert (str.<= \"ab\" \"ab\"))\n"),
        "reflexive: ab <= ab"
    );
    assert!(
        eval_const_script("(assert (str.<= \"AC\" \"AF\"))\n"),
        "AC <= AF"
    );
}

#[test]
fn string_lex_order_variable_eval() {
    // (str.< "AC" y) ∧ (str.< y "AF") — the regression shape; y = "AD" witnesses.
    let text = "(declare-fun y () String)\n\
                (assert (str.< \"AC\" y))\n\
                (assert (str.< y \"AF\"))\n(check-sat)\n";
    assert!(
        eval_string_int_script(text, &[("y", b"AD")], &[]),
        "AC<AD<AF"
    );
    assert!(
        !eval_string_int_script(text, &[("y", b"AG")], &[]),
        "AG not < AF"
    );
    assert!(
        !eval_string_int_script(text, &[("y", b"AC")], &[]),
        "AC not < AC (strict)"
    );
}

#[test]
fn string_to_int_constant_corners_eval() {
    // SMT-LIB UnicodeStrings total-function corners, oracle-checked by evaluating
    // the packed-BV encoding of constant operands:
    //   - leading zeros are valid: "042" → 42, "007" → 7, "0001" → 1.
    //   - any non-digit char → -1; the empty string → -1.
    assert!(
        eval_const_script("(assert (= (str.to_int \"042\") 42))\n"),
        "042"
    );
    assert!(
        eval_const_script("(assert (= (str.to_int \"007\") 7))\n"),
        "007"
    );
    assert!(
        eval_const_script("(assert (= (str.to_int \"0001\") 1))\n"),
        "leading zeros valid"
    );
    assert!(
        eval_const_script("(assert (= (str.to_int \"1a\") (- 1)))\n"),
        "non-digit ⇒ -1"
    );
    assert!(
        eval_const_script("(assert (= (str.to_int \"\") (- 1)))\n"),
        "empty ⇒ -1"
    );
    assert!(
        eval_const_script("(assert (= (str.to_int \" 1\") (- 1)))\n"),
        "leading space (non-digit) ⇒ -1"
    );
    // A wrong-equality stays unsat-shaped (never spuriously true).
    assert!(
        !eval_const_script("(assert (= (str.to_int \"042\") 41))\n"),
        "042 ≠ 41"
    );
}

#[test]
fn string_to_int_symbolic_eval() {
    // (str.to_int s) over a declared string symbol, oracle-checked under concrete
    // packings: a digit string decodes; a non-digit string is -1.
    let text = "(declare-fun s () String)\n\
                (assert (= (str.to_int s) 25))\n(check-sat)\n";
    assert!(eval_string_script(text, pack_str(b"25")), "\"25\" → 25");
    assert!(
        !eval_string_script(text, pack_str(b"99")),
        "\"99\" → 99 ≠ 25"
    );
    let neg = "(declare-fun s () String)\n\
               (assert (= (str.to_int s) (- 1)))\n(check-sat)\n";
    assert!(eval_string_script(neg, pack_str(b"a")), "non-digit → -1");
    assert!(eval_string_script(neg, pack_str(b"")), "empty → -1");
    assert!(!eval_string_script(neg, pack_str(b"7")), "\"7\" → 7 ≠ -1");
}

#[test]
fn string_to_int_over_length_literal_declines() {
    // A string literal longer than STRING_MAX_LEN declines at pack time, so
    // (str.to_int "<24 digits>") is a clean Unsupported (never a wrapped value).
    let err =
        parse_script("(assert (= (str.to_int \"783914785582390527685649\") 5))\n(check-sat)\n")
            .expect_err("over-length string literal declines");
    assert!(matches!(err, SmtError::Unsupported(_)), "got {err:?}");
}

#[test]
fn string_from_int_constant_corners_eval() {
    // str.from_int: i ≥ 0 → canonical decimal (no leading zeros, 0 → "0"); i < 0 → "".
    assert!(
        eval_const_script("(assert (= (str.from_int 42) \"42\"))\n"),
        "42"
    );
    assert!(
        eval_const_script("(assert (= (str.from_int 0) \"0\"))\n"),
        "0"
    );
    assert!(
        eval_const_script("(assert (= (str.from_int 7) \"7\"))\n"),
        "single digit"
    );
    assert!(
        eval_const_script("(assert (= (str.from_int (- 5)) \"\"))\n"),
        "negative ⇒ \"\""
    );
    // No spurious leading zero / wrong string.
    assert!(
        !eval_const_script("(assert (= (str.from_int 42) \"042\"))\n"),
        "42 ≠ \"042\""
    );
}

#[test]
fn string_from_int_over_bound_constant_declines() {
    // A non-negative constant whose decimal needs more than FROM_INT_MAX_DIGITS
    // bytes cannot be represented in the bounded string sort — a clean Unsupported
    // (Unknown to the consumer), never a truncated/wrong string.
    let err = parse_script(
        "(declare-fun x () String)\n\
         (assert (= x (str.from_int 4785582390527685649)))\n(check-sat)\n",
    )
    .expect_err("19-digit from_int constant exceeds the bound");
    assert!(matches!(err, SmtError::Unsupported(_)), "got {err:?}");
}

#[test]
fn string_from_int_symbolic_eval() {
    // Symbolic `str.from_int i` over an Int symbol, oracle-checked: the packed
    // result equals the decimal string of i (faithful for every in-range i).
    let text = "(declare-fun i () Int)\n\
                (declare-fun x () String)\n\
                (assert (= x (str.from_int i)))\n(check-sat)\n";
    assert!(
        eval_string_int_script(text, &[("x", b"42")], &[("i", 42)]),
        "from_int 42 = \"42\""
    );
    assert!(
        eval_string_int_script(text, &[("x", b"7")], &[("i", 7)]),
        "from_int 7 = \"7\""
    );
    assert!(
        eval_string_int_script(text, &[("x", b"0")], &[("i", 0)]),
        "from_int 0 = \"0\""
    );
    // i < 0 ⇒ "" (negative formats to the empty string).
    assert!(
        eval_string_int_script(text, &[("x", b"")], &[("i", -5)]),
        "from_int (-5) = \"\""
    );
    // A wrong string never spuriously holds.
    assert!(
        !eval_string_int_script(text, &[("x", b"43")], &[("i", 42)]),
        "from_int 42 ≠ \"43\""
    );
}

#[test]
fn string_from_int_round_trip_eval() {
    // to_int ∘ from_int over a constant in range round-trips: a small UNSAT shape
    // catches an encoding that disagrees with itself.
    assert!(
        eval_const_script("(assert (= (str.to_int (str.from_int 123)) 123))\n"),
        "to_int(from_int 123) = 123"
    );
    assert!(
        eval_const_script("(assert (= (str.to_int (str.from_int 0)) 0))\n"),
        "to_int(from_int 0) = 0"
    );
    // from_int of a negative is "", whose to_int is -1 (not the original).
    assert!(
        eval_const_script("(assert (= (str.to_int (str.from_int (- 4))) (- 1)))\n"),
        "to_int(from_int -4) = to_int(\"\") = -1"
    );
}

#[test]
fn declare_fun_string_constant_is_wired_like_declare_const() {
    // QF_S benchmarks overwhelmingly use `(declare-fun s () String)`, not
    // `declare-const`. The 0-ary `declare-fun ... String` form now opens the same
    // bounded packed-BV representation + canonical well-formedness assertion
    // (ADR-0029) as `declare-const ... String`.
    let script = parse_script("(declare-fun s () String)\n(assert (= s \"ab\"))\n(check-sat)\n")
        .expect("declare-fun () String should parse like declare-const");
    assert_eq!(
        script.assertions.len(),
        2,
        "wf constraint (from the declare) + the equality"
    );
    // The symbol is the packed bounded-string bit-vector.
    let mut arena = script.arena;
    let sym = arena.find_symbol("s").expect("s declared");
    let v = arena.var(sym);
    assert_eq!(arena.sort_of(v), Sort::BitVec(4 + 8 * 8));
}

#[test]
fn seq_sort_over_unsupported_element_is_a_clear_unsupported() {
    // A `(Seq E)` whose element sort `E` has no sound fixed-width packing
    // (here `Real`) stays a scoped, actionable Unsupported (Unknown to the
    // consumer) — never a wrong verdict (ADR-0029).
    let err = parse_script("(declare-fun f () (Seq Real))\n(check-sat)\n")
        .expect_err("(Seq Real) has no fixed-width element packing");
    assert!(matches!(err, SmtError::Unsupported(_)), "got {err:?}");
    // The reserved byte width `8` is for `String`, so `(Seq (_ BitVec 8))` declines.
    let err = parse_script("(declare-fun f () (Seq (_ BitVec 8)))\n(check-sat)\n")
        .expect_err("(Seq (_ BitVec 8)) is reserved for String");
    assert!(matches!(err, SmtError::Unsupported(_)), "got {err:?}");
}

// Packed `(Seq Int)` layout constants for the tests: SEQ_INT_WIDTH = 16, and the
// bounded max length is the largest m ≤ 8 with len_width(m) + 16m ≤ 128, i.e.
// m = 7 (len_width(7) = 3): total = 3 + 7*16 = 115.
const SEQ_INT_EW: u32 = 16;
const SEQ_INT_M: u32 = 7;
const SEQ_INT_LW: u32 = 3; // len_width(7)
const SEQ_INT_TOTAL: u32 = SEQ_INT_LW + SEQ_INT_M * SEQ_INT_EW; // 115

#[test]
fn seq_int_const_is_packed_and_wellformed() {
    // A `(Seq Int)` constant resolves to the packed sequence bit-vector (length
    // field over `SEQ_INT_WIDTH`-bit elements) plus its well-formedness assertion.
    let script =
        parse_script("(declare-fun s () (Seq Int))\n(assert (= (seq.len s) 0))\n(check-sat)\n")
            .expect("(Seq Int) constant parses");
    let mut arena = script.arena;
    let sym = arena.find_symbol("s").expect("s declared");
    let v = arena.var(sym);
    assert_eq!(arena.sort_of(v), Sort::BitVec(SEQ_INT_TOTAL));
    assert_eq!(
        script.assertions.len(),
        2,
        "well-formedness (from the declare) + the len assertion"
    );
}

/// Evaluates every assertion of a `(Seq Int)` script against a concrete packed
/// assignment for one sequence symbol `name` of total width `width`.
fn eval_seq_script(text: &str, name: &str, width: u32, packed: u128) -> bool {
    let script = parse_script(text).expect("script parses");
    let sym = script.arena.find_symbol(name).expect("symbol declared");
    let mut asg = Assignment::new();
    asg.set(
        sym,
        Value::Bv {
            width,
            value: packed,
        },
    );
    script
        .assertions
        .iter()
        .all(|&a| eval(&script.arena, a, &asg).unwrap() == Value::Bool(true))
}

/// Packs a `(Seq Int)` value (elements as 16-bit two's-complement) into the
/// canonical layout: length low, elements above, padding zero.
fn pack_seq_int(elems: &[i64]) -> u128 {
    let mut v: u128 = u128::try_from(elems.len()).unwrap();
    for (i, &e) in elems.iter().enumerate() {
        // Low 16 bits, two's-complement (mask the i64 to its low 16 bits).
        #[allow(clippy::cast_sign_loss)]
        let bits = (e & 0xffff) as u128;
        v |= bits << (SEQ_INT_LW + SEQ_INT_EW * u32::try_from(i).unwrap());
    }
    v
}

#[test]
fn seq_len_eval_via_packed_bv() {
    // (seq.len s) == 2 — a length predicate, oracle-checked over concrete witnesses.
    let text = "(declare-fun s () (Seq Int))\n\
                (assert (= (seq.len s) 2))\n(check-sat)\n";
    assert!(
        eval_seq_script(text, "s", SEQ_INT_TOTAL, pack_seq_int(&[7, 3])),
        "length 2 ⇒ true"
    );
    assert!(
        !eval_seq_script(text, "s", SEQ_INT_TOTAL, pack_seq_int(&[7])),
        "length 1 ⇒ false"
    );
}

#[test]
fn seq_unit_len_arithmetic_is_unsat_shaped() {
    // (= (seq.len (seq.unit x)) 2): a unit sequence always has length 1, so the
    // len-2 assertion can never hold — a small UNSAT (oracle: no witness). The
    // `(Seq Int)` declaration fixes the element width for `seq.unit`.
    let text = "(declare-fun s () (Seq Int))\n(declare-fun x () Int)\n\
                (assert (= (seq.len (seq.unit x)) 2))\n(check-sat)\n";
    let script = parse_script(text).expect("parses");
    // (seq.unit x) is a constant-length-1 sequence: the length field is the literal
    // 1, so (= 1 2) is structurally false for every x. Evaluate with any x.
    let sym = script.arena.find_symbol("x").expect("x");
    let mut asg = Assignment::new();
    asg.set(sym, Value::Int(5.into()));
    // Evaluate only the `(= (seq.len (seq.unit x)) 2)` assertion (the last one; the
    // first is `s`'s well-formedness, which references the unassigned `s`).
    let len_eq = *script.assertions.last().expect("the len assertion");
    assert_eq!(
        eval(&script.arena, len_eq, &asg).unwrap(),
        Value::Bool(false),
        "unit length is 1, never 2"
    );
}

#[test]
fn seq_empty_is_length_zero() {
    // (as seq.empty (Seq Int)) is the length-0 sequence; (not (= s empty)) with a
    // length-0 witness for s is false (s equals empty), with a nonempty witness true.
    let text = "(declare-fun s () (Seq Int))\n\
                (assert (not (= s (as seq.empty (Seq Int)))))\n(check-sat)\n";
    assert!(
        !eval_seq_script(text, "s", SEQ_INT_TOTAL, pack_seq_int(&[])),
        "s = empty ⇒ (not (= s empty)) false"
    );
    assert!(
        eval_seq_script(text, "s", SEQ_INT_TOTAL, pack_seq_int(&[9])),
        "s nonempty ⇒ true"
    );
}

/// Evaluates every assertion of a `(Seq Int)` script under a concrete assignment
/// built from `(symbol-name, Value)` pairs — used for `seq.nth`/`seq.at` tests
/// that must assign both the sequence and a fresh out-of-bounds symbol.
fn eval_seq_script_multi(text: &str, binds: &[(&str, Value)]) -> bool {
    let script = parse_script(text).expect("script parses");
    let mut asg = Assignment::new();
    for (name, val) in binds {
        let sym = script.arena.find_symbol(name).expect("symbol declared");
        asg.set(sym, val.clone());
    }
    script
        .assertions
        .iter()
        .all(|&a| eval(&script.arena, a, &asg).unwrap() == Value::Bool(true))
}

/// The name of the fresh out-of-bounds symbol minted for the (single) `seq.nth`
/// application in a script, found by its `!seq.nth.oob.` prefix.
fn seq_nth_oob_name(text: &str) -> String {
    let script = parse_script(text).expect("parses");
    script
        .arena
        .symbols()
        .map(|(_, name, _)| name)
        .find(|n| n.starts_with("!seq.nth.oob."))
        .expect("a seq.nth application minted an oob symbol")
        .to_owned()
}

#[test]
fn seq_nth_in_bounds_is_the_element() {
    // (seq.nth s 0) == 7 with a witness s = [7, 3]: in-bounds nth returns the
    // 0-th element, so the equality holds. Oracle: concrete eval over a witness.
    let text = "(declare-fun s () (Seq Int))\n\
                (assert (= (seq.len s) 2))\n(assert (= (seq.nth s 0) 7))\n(check-sat)\n";
    // `eval` walks both `ite` branches, so the (unused, in-bounds) oob symbol must
    // be bound to *some* value; the result is independent of it.
    let oob = seq_nth_oob_name(text);
    assert!(
        eval_seq_script_multi(
            text,
            &[
                (
                    "s",
                    Value::Bv {
                        width: SEQ_INT_TOTAL,
                        value: pack_seq_int(&[7, 3])
                    }
                ),
                (
                    &oob,
                    Value::Bv {
                        width: SEQ_INT_EW,
                        value: 0
                    }
                ),
            ],
        ),
        "s=[7,3] ⇒ (seq.nth s 0)=7 holds"
    );
    assert!(
        !eval_seq_script_multi(
            text,
            &[
                (
                    "s",
                    Value::Bv {
                        width: SEQ_INT_TOTAL,
                        value: pack_seq_int(&[5, 3])
                    }
                ),
                (
                    &oob,
                    Value::Bv {
                        width: SEQ_INT_EW,
                        value: 0
                    }
                ),
            ],
        ),
        "s=[5,3] ⇒ (seq.nth s 0)=7 false"
    );
}

#[test]
fn seq_nth_out_of_bounds_is_unconstrained_not_zero() {
    // THE SOUNDNESS TEST. Under a zero-padded model, `(seq.nth s 0)` for an empty
    // `s` would be forced to 0, making `(= (seq.nth s 0) 7)` a WRONG `unsat`.
    // SMT-LIB leaves it unconstrained, so a model exists (oob value = 7): the
    // script is SAT. We exhibit a witness (s = empty, oob symbol = 7) under which
    // every assertion is true — proving the front end did NOT pin the oob value.
    let text = "(declare-fun s () (Seq Int))\n\
                (assert (= (seq.len s) 0))\n(assert (= (seq.nth s 0) 7))\n(check-sat)\n";
    let oob = seq_nth_oob_name(text);
    // The oob symbol is a BitVec(16); 7 packs as the literal 7.
    let witness_true = eval_seq_script_multi(
        text,
        &[
            (
                "s",
                Value::Bv {
                    width: SEQ_INT_TOTAL,
                    value: pack_seq_int(&[]),
                },
            ),
            (
                &oob,
                Value::Bv {
                    width: SEQ_INT_EW,
                    value: 7,
                },
            ),
        ],
    );
    assert!(
        witness_true,
        "an out-of-bounds witness with oob=7 satisfies the script — not a wrong unsat"
    );
}

#[test]
fn seq_nth_congruence_constraint_is_emitted() {
    // Two distinct `seq.nth` applications over equal operands must agree even
    // out-of-bounds (`seq.nth` is a function). The front end emits the eager
    // Ackermann implication `(s=t ∧ i=i') ⇒ oob(s,i)=oob(t,i')` as an extra
    // assertion; structurally, the script gains it beyond its own asserts.
    let text = "(declare-fun s () (Seq Int))\n(declare-fun t () (Seq Int))\n\
                (declare-fun i () Int)\n(assert (= s t))\n\
                (assert (not (= (seq.nth s i) (seq.nth t i))))\n(check-sat)\n";
    let script = parse_script(text).expect("parses");
    // Two well-formedness asserts (s, t) + (= s t) + (not (= nth nth)) + the
    // appended congruence = 5 assertions.
    assert_eq!(
        script.assertions.len(),
        5,
        "the congruence implication is appended as a 5th assertion"
    );
}

#[test]
fn seq_at_in_bounds_is_unit_of_element() {
    // (seq.at s 0) is the length-1 sequence [s[0]]; with s=[7,3] that is [7], so
    // (= (seq.at s 0) (seq.unit 7)) holds. Oracle: concrete eval over the witness.
    let text = "(declare-fun s () (Seq Int))\n\
                (assert (= (seq.len s) 2))\n\
                (assert (= (seq.at s 0) (seq.unit 7)))\n(check-sat)\n";
    assert!(
        eval_seq_script(text, "s", SEQ_INT_TOTAL, pack_seq_int(&[7, 3])),
        "s=[7,3] ⇒ (seq.at s 0)=[7]"
    );
    assert!(
        !eval_seq_script(text, "s", SEQ_INT_TOTAL, pack_seq_int(&[8, 3])),
        "s=[8,3] ⇒ (seq.at s 0)=[8] ≠ [7]"
    );
}

#[test]
fn seq_at_out_of_bounds_is_empty() {
    // (seq.at s 5) on a length-2 sequence is out of bounds → the empty sequence;
    // so (= (seq.at s 5) (as seq.empty (Seq Int))) holds. seq.at is total.
    let text = "(declare-fun s () (Seq Int))\n\
                (assert (= (seq.len s) 2))\n\
                (assert (= (seq.at s 5) (as seq.empty (Seq Int))))\n(check-sat)\n";
    assert!(
        eval_seq_script(text, "s", SEQ_INT_TOTAL, pack_seq_int(&[7, 3])),
        "out-of-bounds seq.at is the empty sequence"
    );
    // And in-bounds it is NOT empty (length 1), so the same shape at index 0 fails.
    let text0 = "(declare-fun s () (Seq Int))\n\
                 (assert (= (seq.len s) 2))\n\
                 (assert (= (seq.at s 0) (as seq.empty (Seq Int))))\n(check-sat)\n";
    assert!(
        !eval_seq_script(text0, "s", SEQ_INT_TOTAL, pack_seq_int(&[7, 3])),
        "in-bounds seq.at is length 1, not empty"
    );
}

#[test]
fn seq_update_family_still_declined() {
    // The slice-3 ops stay cleanly declined (Unsupported), never a wrong verdict.
    for op in ["seq.update", "seq.rev", "seq.replace", "seq.indexof"] {
        let text = format!(
            "(declare-fun s () (Seq Int))\n(assert (= (seq.len ({op} s)) 0))\n(check-sat)\n"
        );
        let err = parse_script(&text).expect_err("slice-3 op declines");
        assert!(matches!(err, SmtError::Unsupported(_)), "{op}: got {err:?}");
    }
}

#[test]
fn unsupported_string_op_declines_gracefully() {
    // A `str.*` operator outside the wired bounded subset is a clean `Unsupported`
    // (the benchmark is declined, never mis-decided).
    let err = parse_script(
        "(declare-fun s () String)\n(assert (= (str.replace s \"a\" \"b\") \"x\"))\n(check-sat)\n",
    )
    .expect_err("str.replace is outside the wired subset");
    let SmtError::Unsupported(msg) = err else {
        panic!("expected Unsupported for str.replace, got {err:?}");
    };
    assert!(msg.contains("str.replace"), "actionable msg: {msg}");
}

/// The full set of standard output/query no-op commands is accepted, so a
/// conformant SMT-LIB script using them is not rejected at parse time.
#[test]
fn accepts_standard_output_commands() {
    let text = r#"
        (set-logic QF_BV)
        (echo "solving")
        (declare-const x (_ BitVec 8))
        (assert (= x #x05))
        (check-sat)
        (get-model)
        (get-assignment)
        (get-unsat-assumptions)
        (get-assertions)
        (echo "done")
        (exit)
    "#;
    let script = parse_script(text).expect("standard output commands parse");
    assert_eq!(script.logic.as_deref(), Some("QF_BV"));
    assert_eq!(script.assertions.len(), 1);
}

/// A genuinely-unknown command is still a clean `Unsupported` error (not a panic).
#[test]
fn rejects_unknown_command() {
    let err =
        parse_script("(set-logic QF_BV)\n(frobnicate 3)\n").expect_err("unknown command errors");
    assert!(matches!(err, SmtError::Unsupported(_)));
}

/// `(define-sort Byte () (_ BitVec 8))` then `(declare-const x Byte)` declares
/// `x` with the aliased sort `BitVec(8)`.
#[test]
fn define_sort_alias_is_resolved() {
    let text = r"
        (set-logic QF_BV)
        (define-sort Byte () (_ BitVec 8))
        (declare-const x Byte)
        (assert (= x #x05))
        (check-sat)
    ";
    let script = parse_script(text).unwrap();
    let sym = script.arena.find_symbol("x").unwrap();
    assert_eq!(script.arena.symbol(sym).1, axeyum_ir::Sort::BitVec(8));
}

/// A sort alias resolves inside a compound sort (here an `Array`), exercising
/// the recursive `parse_sort` alias lookup.
#[test]
fn define_sort_alias_inside_array() {
    let text = r"
        (set-logic QF_ABV)
        (define-sort Idx () (_ BitVec 4))
        (declare-const a (Array Idx Idx))
    ";
    let script = parse_script(text).unwrap();
    let sym = script.arena.find_symbol("a").unwrap();
    assert_eq!(
        script.arena.symbol(sym).1,
        axeyum_ir::Sort::Array {
            index: 4,
            element: 4
        }
    );
}

/// An alias may reference an earlier alias (the body is parsed through
/// `parse_sort`, which consults the alias map).
#[test]
fn define_sort_chains() {
    let text = r"
        (set-logic QF_BV)
        (define-sort Byte () (_ BitVec 8))
        (define-sort Word () Byte)
        (declare-const w Word)
    ";
    let script = parse_script(text).unwrap();
    let sym = script.arena.find_symbol("w").unwrap();
    assert_eq!(script.arena.symbol(sym).1, axeyum_ir::Sort::BitVec(8));
}

/// Redefining a builtin sort name as an alias is rejected.
#[test]
fn define_sort_rejects_builtin_redefinition() {
    let err = parse_script("(set-logic QF_BV)\n(define-sort Int () Real)\n")
        .expect_err("redefining a builtin sort errors");
    assert!(matches!(err, SmtError::Syntax(_)));
}

/// A duplicate sort alias is rejected.
#[test]
fn define_sort_rejects_duplicate_alias() {
    let text = r"
        (set-logic QF_BV)
        (define-sort Byte () (_ BitVec 8))
        (define-sort Byte () (_ BitVec 16))
    ";
    let err = parse_script(text).expect_err("duplicate sort alias errors");
    assert!(matches!(err, SmtError::Syntax(_)));
}

/// A parametric `define-sort` is cleanly rejected as unsupported.
#[test]
fn define_sort_rejects_parametric() {
    let err = parse_script("(set-logic QF_BV)\n(define-sort P (X) X)\n")
        .expect_err("parametric define-sort is unsupported");
    assert!(matches!(err, SmtError::Unsupported(_)));
}

// --- datatype `match` desugaring (SMT-LIB 2.6) -------------------------------

/// `match` over an enum (nullary constructors): each case selects a bit-vector
/// constant. Verified end-to-end by the ground evaluator on a concrete value.
#[test]
fn match_enum_nullary_cases() {
    let text = r"
        (set-logic QF_BV)
        (declare-datatype Color ((red) (green) (blue)))
        (declare-const c Color)
        (assert (= (match c ((red #x01) (green #x02) (blue #x03))) #x02))
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.assertions.len(), 1);
    // c = green ⇒ the match yields #x02, so the assertion is true.
    let mut asg = Assignment::new();
    asg.set(
        sym_of(&script, "c"),
        Value::Datatype {
            datatype: dt_of(&script, "Color"),
            constructor: ctor_of(&script, "green"),
            fields: vec![],
        },
    );
    assert_eq!(
        eval(&script.arena, script.assertions[0], &asg).unwrap(),
        Value::Bool(true)
    );
    // c = red ⇒ the match yields #x01, so the assertion is false.
    let mut asg_red = Assignment::new();
    asg_red.set(
        sym_of(&script, "c"),
        Value::Datatype {
            datatype: dt_of(&script, "Color"),
            constructor: ctor_of(&script, "red"),
            fields: vec![],
        },
    );
    assert_eq!(
        eval(&script.arena, script.assertions[0], &asg_red).unwrap(),
        Value::Bool(false)
    );
}

/// `match` over a recursive datatype binding a constructor field: the `cons`
/// case binds `h`/`t` to the head/tail selectors. Evaluated on a concrete list.
#[test]
fn match_constructor_pattern_binds_fields() {
    let text = r"
        (set-logic QF_UFDT)
        (declare-datatype IntList ((nil) (cons (head Int) (tail IntList))))
        (declare-const xs IntList)
        (assert (= (match xs ((nil 0) ((cons h t) h))) 7))
    ";
    let script = parse_script(text).unwrap();
    // xs = (cons 7 nil) ⇒ match yields head = 7, assertion holds.
    let mut asg = Assignment::new();
    let nil = Value::Datatype {
        datatype: dt_of(&script, "IntList"),
        constructor: ctor_of(&script, "nil"),
        fields: vec![],
    };
    asg.set(
        sym_of(&script, "xs"),
        Value::Datatype {
            datatype: dt_of(&script, "IntList"),
            constructor: ctor_of(&script, "cons"),
            fields: vec![Value::Int(7), nil.clone()],
        },
    );
    assert_eq!(
        eval(&script.arena, script.assertions[0], &asg).unwrap(),
        Value::Bool(true)
    );
    // xs = nil ⇒ match yields 0, so `(= 0 7)` is false.
    let mut asg_nil = Assignment::new();
    asg_nil.set(sym_of(&script, "xs"), nil);
    assert_eq!(
        eval(&script.arena, script.assertions[0], &asg_nil).unwrap(),
        Value::Bool(false)
    );
}

/// A trailing variable (default) case catches the constructors not listed and
/// binds the whole scrutinee.
#[test]
fn match_default_variable_case() {
    let text = r"
        (set-logic QF_UFDT)
        (declare-datatype IntList ((nil) (cons (head Int) (tail IntList))))
        (declare-const xs IntList)
        (assert (= (match xs ((nil 0) (other 1))) 1))
    ";
    let script = parse_script(text).unwrap();
    // xs = (cons 1 nil) ⇒ falls to the `other` default ⇒ 1, assertion holds.
    let nil = Value::Datatype {
        datatype: dt_of(&script, "IntList"),
        constructor: ctor_of(&script, "nil"),
        fields: vec![],
    };
    let mut asg = Assignment::new();
    asg.set(
        sym_of(&script, "xs"),
        Value::Datatype {
            datatype: dt_of(&script, "IntList"),
            constructor: ctor_of(&script, "cons"),
            fields: vec![Value::Int(1), nil.clone()],
        },
    );
    assert_eq!(
        eval(&script.arena, script.assertions[0], &asg).unwrap(),
        Value::Bool(true)
    );
    // xs = nil ⇒ the `nil` case yields 0, so `(= 0 1)` is false.
    let mut asg_nil = Assignment::new();
    asg_nil.set(sym_of(&script, "xs"), nil);
    assert_eq!(
        eval(&script.arena, script.assertions[0], &asg_nil).unwrap(),
        Value::Bool(false)
    );
}

/// A wildcard `_` default matches but binds nothing.
#[test]
fn match_wildcard_default() {
    let text = r"
        (set-logic QF_BV)
        (declare-datatype Color ((red) (green) (blue)))
        (declare-const c Color)
        (assert (= (match c ((red #x01) (_ #x00))) #x00))
    ";
    let script = parse_script(text).unwrap();
    let mut asg = Assignment::new();
    asg.set(
        sym_of(&script, "c"),
        Value::Datatype {
            datatype: dt_of(&script, "Color"),
            constructor: ctor_of(&script, "blue"),
            fields: vec![],
        },
    );
    // c = blue ⇒ wildcard branch ⇒ #x00, assertion holds.
    assert_eq!(
        eval(&script.arena, script.assertions[0], &asg).unwrap(),
        Value::Bool(true)
    );
}

/// Structural check: the parsed `match` term equals the hand-written desugaring
/// `(ite (is-red c) #x01 (ite (is-green c) #x02 #x03))`. Term interning means
/// identical structure shares the same `TermId`.
#[test]
fn match_desugars_to_nested_ite() {
    let text = r"
        (set-logic QF_BV)
        (declare-datatype Color ((red) (green) (blue)))
        (declare-const c Color)
        (assert (= (match c ((red #x01) (green #x02) (blue #x03))) #x00))
        (assert (= (ite ((_ is red) c) #x01 (ite ((_ is green) c) #x02 #x03)) #x00))
    ";
    let script = parse_script(text).unwrap();
    assert_eq!(script.assertions.len(), 2);
    // The two assertions are `(= <match> #x00)` and `(= <ite> #x00)`; identical
    // desugaring ⇒ identical interned `TermId`.
    assert_eq!(script.assertions[0], script.assertions[1]);
}

/// `match` on a non-datatype scrutinee is a clean error, not a panic.
#[test]
fn match_on_non_datatype_errors() {
    let text = r"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= (match x ((y #x00))) #x00))
    ";
    let err = parse_script(text).expect_err("match on a bit-vector is rejected");
    assert!(matches!(err, SmtError::Syntax(_)));
}

/// An unknown constructor in a pattern is rejected.
#[test]
fn match_unknown_constructor_errors() {
    let text = r"
        (set-logic QF_BV)
        (declare-datatype Color ((red) (green) (blue)))
        (declare-const c Color)
        (assert (= (match c ((red #x01) ((cons h) #x02))) #x00))
    ";
    let err = parse_script(text).expect_err("unknown constructor pattern is rejected");
    assert!(matches!(
        err,
        SmtError::Unsupported(_) | SmtError::Syntax(_)
    ));
}

/// A constructor pattern with the wrong field arity is rejected.
#[test]
fn match_wrong_arity_errors() {
    let text = r"
        (set-logic QF_UFDT)
        (declare-datatype IntList ((nil) (cons (head Int) (tail IntList))))
        (declare-const xs IntList)
        (assert (= (match xs ((nil 0) ((cons h) 1))) 0))
    ";
    let err = parse_script(text).expect_err("wrong constructor field arity is rejected");
    assert!(matches!(err, SmtError::Syntax(_)));
}

/// A non-exhaustive match (a constructor missing, no default) is rejected.
#[test]
fn match_non_exhaustive_errors() {
    let text = r"
        (set-logic QF_BV)
        (declare-datatype Color ((red) (green) (blue)))
        (declare-const c Color)
        (assert (= (match c ((red #x01) (green #x02))) #x00))
    ";
    let err = parse_script(text).expect_err("non-exhaustive match is rejected");
    assert!(matches!(err, SmtError::Syntax(_)));
}

/// A default (variable) case that is not last is rejected.
#[test]
fn match_default_not_last_errors() {
    let text = r"
        (set-logic QF_BV)
        (declare-datatype Color ((red) (green) (blue)))
        (declare-const c Color)
        (assert (= (match c ((other #x00) (red #x01))) #x00))
    ";
    let err = parse_script(text).expect_err("a default before the last case is rejected");
    assert!(matches!(err, SmtError::Syntax(_)));
}

/// The bound field variable is visible to a nested `let` in the case body
/// (shadowing/scoping reuses the `let` machinery).
#[test]
fn match_body_sees_pattern_var_under_let() {
    let text = r"
        (set-logic QF_UFDT)
        (declare-datatype IntList ((nil) (cons (head Int) (tail IntList))))
        (declare-const xs IntList)
        (assert (= (match xs ((nil 0) ((cons h t) (let ((g h)) (+ g g))))) 14))
    ";
    let script = parse_script(text).unwrap();
    let nil = Value::Datatype {
        datatype: dt_of(&script, "IntList"),
        constructor: ctor_of(&script, "nil"),
        fields: vec![],
    };
    let mut asg = Assignment::new();
    asg.set(
        sym_of(&script, "xs"),
        Value::Datatype {
            datatype: dt_of(&script, "IntList"),
            constructor: ctor_of(&script, "cons"),
            fields: vec![Value::Int(7), nil],
        },
    );
    // h = 7 ⇒ (+ g g) with g = h = 7 ⇒ 14, assertion holds.
    assert_eq!(
        eval(&script.arena, script.assertions[0], &asg).unwrap(),
        Value::Bool(true)
    );
}

// --- helpers for the `match` tests ------------------------------------------

fn sym_of(script: &axeyum_smtlib::Script, name: &str) -> SymbolId {
    script
        .arena
        .find_symbol(name)
        .unwrap_or_else(|| panic!("symbol `{name}` not declared"))
}

// --- Front-end coverage gaps: bvred* / iand / :named -----------------------

/// `(bvredor x)` desugars to `(bvnot (bvcomp x 0))` — `#b1` iff `x != 0`. The
/// concrete-value checks via `eval` are oracle-checkable.
#[test]
fn bvredor_reduces_to_nonzero_bit() {
    // x = 0b0100 ≠ 0  ⇒  bvredor = #b1.
    let s = parse_script("(set-logic QF_BV)\n(assert (= (bvredor (_ bv4 4)) (_ bv1 1)))").unwrap();
    assert_eq!(
        eval(&s.arena, s.assertions[0], &Assignment::new()).unwrap(),
        Value::Bool(true)
    );
    // x = 0  ⇒  bvredor = #b0.
    let s = parse_script("(set-logic QF_BV)\n(assert (= (bvredor (_ bv0 4)) (_ bv0 1)))").unwrap();
    assert_eq!(
        eval(&s.arena, s.assertions[0], &Assignment::new()).unwrap(),
        Value::Bool(true)
    );
    // The result sort is one bit wide.
    assert_eq!(s.arena.sort_of(s.assertions[0]), Sort::Bool);
}

/// `(bvredand x)` desugars to `(bvcomp x ~0)` — `#b1` iff every bit is set.
#[test]
fn bvredand_reduces_to_all_ones_bit() {
    // x = 0b1111 = ~0  ⇒  bvredand = #b1.
    let s =
        parse_script("(set-logic QF_BV)\n(assert (= (bvredand (_ bv15 4)) (_ bv1 1)))").unwrap();
    assert_eq!(
        eval(&s.arena, s.assertions[0], &Assignment::new()).unwrap(),
        Value::Bool(true)
    );
    // x = 0b1110 ≠ ~0  ⇒  bvredand = #b0.
    let s =
        parse_script("(set-logic QF_BV)\n(assert (= (bvredand (_ bv14 4)) (_ bv0 1)))").unwrap();
    assert_eq!(
        eval(&s.arena, s.assertions[0], &Assignment::new()).unwrap(),
        Value::Bool(true)
    );
}

/// `(bvredxor x)` desugars to the XOR-fold of all bits — the parity of `x`.
#[test]
fn bvredxor_reduces_to_parity_bit() {
    // popcount(0b1011) = 3 (odd)  ⇒  bvredxor = #b1.
    let s =
        parse_script("(set-logic QF_BV)\n(assert (= (bvredxor (_ bv11 4)) (_ bv1 1)))").unwrap();
    assert_eq!(
        eval(&s.arena, s.assertions[0], &Assignment::new()).unwrap(),
        Value::Bool(true)
    );
    // popcount(0b0011) = 2 (even)  ⇒  bvredxor = #b0.
    let s = parse_script("(set-logic QF_BV)\n(assert (= (bvredxor (_ bv3 4)) (_ bv0 1)))").unwrap();
    assert_eq!(
        eval(&s.arena, s.assertions[0], &Assignment::new()).unwrap(),
        Value::Bool(true)
    );
}

/// A tiny SAT and tiny UNSAT formula over `bvredor`, each evaluated against the
/// satisfying / contradicting assignment to confirm the desugaring's verdict.
#[test]
fn bvred_sat_and_unsat_witnesses() {
    // SAT: there is an x with (bvredor x) = #b1, e.g. x = 1.
    let s = parse_script(
        "(set-logic QF_BV)\n(declare-const x (_ BitVec 4))\n\
         (assert (= (bvredor x) (_ bv1 1)))",
    )
    .unwrap();
    let mut asg = Assignment::new();
    asg.set(sym_of(&s, "x"), Value::Bv { width: 4, value: 1 });
    assert_eq!(
        eval(&s.arena, s.assertions[0], &asg).unwrap(),
        Value::Bool(true),
        "x=1 should satisfy (bvredor x) = 1"
    );

    // UNSAT shape: (bvredor 0) = #b1 is contradictory (ground, evaluates false).
    let s = parse_script("(set-logic QF_BV)\n(assert (= (bvredor (_ bv0 4)) (_ bv1 1)))").unwrap();
    assert_eq!(
        eval(&s.arena, s.assertions[0], &Assignment::new()).unwrap(),
        Value::Bool(false),
        "(bvredor 0) = 1 is unsatisfiable"
    );
}

/// `((_ iand N) a b)` desugars to `bv2nat(bvand(int2bv_N a, int2bv_N b))`.
/// `(_ iand 4) 6 3` = bitand(0b0110, 0b0011) = 0b0010 = 2.
#[test]
fn iand_computes_integer_bitwise_and() {
    let s = parse_script("(set-logic QF_NIA)\n(assert (= ((_ iand 4) 6 3) 2))").unwrap();
    assert_eq!(
        eval(&s.arena, s.assertions[0], &Assignment::new()).unwrap(),
        Value::Bool(true)
    );

    // Operands are reduced mod 2^N: (_ iand 4) 22 3 — 22 mod 16 = 6, so still 2.
    let s = parse_script("(set-logic QF_NIA)\n(assert (= ((_ iand 4) 22 3) 2))").unwrap();
    assert_eq!(
        eval(&s.arena, s.assertions[0], &Assignment::new()).unwrap(),
        Value::Bool(true),
        "iand reduces operands mod 2^N (22 ≡ 6 mod 16)"
    );

    // The result is an Int (it is fed to an integer equality above).
    assert_eq!(s.arena.sort_of(s.assertions[0]), Sort::Bool);
}

/// A `:named` annotation binds an alias; a later bare reference resolves to the
/// annotated term. Here `(! (+ x 1) :named s)` then `(= s 5)`.
#[test]
fn named_annotation_binds_reusable_alias() {
    let s = parse_script(
        "(set-logic QF_LIA)\n(declare-const x Int)\n\
         (assert (> (! (+ x 1) :named s) 3))\n\
         (assert (= s 5))",
    )
    .unwrap();
    assert_eq!(s.assertions.len(), 2);
    // The second assertion `(= s 5)` resolves `s` to `(+ x 1)`; with x = 4 it
    // evaluates true (5 = 5) and the first (5 > 3) also holds.
    let mut asg = Assignment::new();
    asg.set(sym_of(&s, "x"), Value::Int(4));
    assert_eq!(
        eval(&s.arena, s.assertions[0], &asg).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval(&s.arena, s.assertions[1], &asg).unwrap(),
        Value::Bool(true)
    );
    // With x = 0, `s = 1`, so `(= s 5)` is false — confirms `s` really is `x+1`.
    let mut asg0 = Assignment::new();
    asg0.set(sym_of(&s, "x"), Value::Int(0));
    assert_eq!(
        eval(&s.arena, s.assertions[1], &asg0).unwrap(),
        Value::Bool(false)
    );
}

/// A real declared symbol is never shadowed by a `:named` of the same name: the
/// declaration wins (the `:named` map is consulted only after symbol lookup).
#[test]
fn declared_symbol_wins_over_named_alias() {
    // `(! (+ y 5) :named y)` would bind `y → (+ y 5)`, but a bare `y` must still
    // resolve to the declared variable. The assertion `(= (! (+ y 5) :named y) y)`
    // is therefore `(+ y 5) = y` (RHS = declared var), which is false for all y.
    // If the `:named` alias had won, the RHS `y` would be `(+ y 5)` and the
    // assertion would be the tautology `(+ y 5) = (+ y 5)` (true) — so a `false`
    // result confirms the declaration wins.
    let s = parse_script(
        "(set-logic QF_LIA)\n(declare-const y Int)\n\
         (assert (= (! (+ y 5) :named y) y))",
    )
    .unwrap();
    let mut asg = Assignment::new();
    asg.set(sym_of(&s, "y"), Value::Int(7));
    assert_eq!(
        eval(&s.arena, s.assertions[0], &asg).unwrap(),
        Value::Bool(false),
        "declared `y` must win over the `:named y` alias"
    );
}

#[test]
fn define_const_is_nullary_define_fun() {
    // `(define-const g Bool body)` must bind `g` exactly like
    // `(define-fun g () Bool body)`: a later bare `g` resolves to `body`.
    let s = parse_script(
        "(set-logic QF_UF)\n(declare-const y Bool)\n\
         (define-const g Bool (not y))\n(assert g)",
    )
    .unwrap();
    // Under y = false, `g = (not y) = true`, so the assertion is true.
    let mut asg = Assignment::new();
    asg.set(sym_of(&s, "y"), Value::Bool(false));
    assert_eq!(
        eval(&s.arena, s.assertions[0], &asg).unwrap(),
        Value::Bool(true),
        "`g` must alias `(not y)`"
    );
    // A wrong arity (the `define-fun` `()` slot accidentally present) is rejected.
    assert!(matches!(
        parse_script("(set-logic QF_UF)\n(define-const g () Bool true)"),
        Err(SmtError::Syntax(_))
    ));
}

#[test]
fn define_const_sort_mismatch_is_rejected() {
    // Body sort must match the declared sort, exactly as `define-fun` enforces.
    assert!(parse_script("(set-logic QF_BV)\n(define-const g Bool (_ bv1 8))").is_err());
}

#[test]
fn sort_ascription_is_identity() {
    // `(as e0 I)` denotes `e0`: the assertion `(= (as e0 I) (as e0 I))` is the
    // reflexive equality `e0 = e0`, true under every assignment. Critically the
    // sort `I` must NOT be parsed as a term (it is an uninterpreted sort here).
    let s = parse_script(
        "(set-logic QF_UF)\n(declare-sort I 0)\n(declare-fun e0 () I)\n\
         (assert (= (as e0 I) (as e0 I)))",
    )
    .unwrap();
    assert_eq!(s.assertions.len(), 1);
    // Concrete check over a Bool-sorted ascription (so `eval` needs no UF model):
    // `(as x Bool)` denotes `x`, so `(= (as x Bool) (not x))` is false under any x.
    let sb =
        parse_script("(set-logic QF_UF)\n(declare-const x Bool)\n(assert (= (as x Bool) (not x)))")
            .unwrap();
    let mut asg = Assignment::new();
    asg.set(sym_of(&sb, "x"), Value::Bool(true));
    assert_eq!(
        eval(&sb.arena, sb.assertions[0], &asg).unwrap(),
        Value::Bool(false),
        "`(as x Bool)` must denote `x`"
    );
    // The ascribed term shares structure with the bare term: `(as e0 I) = e0`.
    let bare = parse_script(
        "(set-logic QF_UF)\n(declare-sort I 0)\n(declare-fun e0 () I)\n(assert (= e0 e0))",
    )
    .unwrap();
    assert_eq!(
        TermStats::compute(&s.arena, &s.assertions).dag_nodes,
        TermStats::compute(&bare.arena, &bare.assertions).dag_nodes,
        "ascription adds no nodes"
    );
}

#[test]
fn unary_and_or_are_identity() {
    // `(and x)` / `(or x)` denote `x`. Under x = false both assertions reduce to
    // `x`, so both evaluate to false.
    let s = parse_script(
        "(set-logic QF_UF)\n(declare-const x Bool)\n(assert (and x))\n(assert (or x))",
    )
    .unwrap();
    let mut asg = Assignment::new();
    asg.set(sym_of(&s, "x"), Value::Bool(false));
    assert_eq!(
        eval(&s.arena, s.assertions[0], &asg).unwrap(),
        Value::Bool(false)
    );
    assert_eq!(
        eval(&s.arena, s.assertions[1], &asg).unwrap(),
        Value::Bool(false)
    );
    // `(and x)` is structurally just `x` (no extra connective node).
    assert_eq!(
        s.assertions[0], s.assertions[1],
        "both alias the same `x` node"
    );
}

#[test]
fn ubv_to_int_aliases_bv2nat() {
    // `ubv_to_int` (SMT-LIB 2.7) and `bv2nat` (2.6) are the same operator; the
    // two parses must produce structurally identical terms.
    let a = parse_script(
        "(set-logic QF_UFBVLIA)\n(declare-fun a () (_ BitVec 4))\n(assert (= (ubv_to_int a) 5))",
    )
    .unwrap();
    let b = parse_script(
        "(set-logic QF_UFBVLIA)\n(declare-fun a () (_ BitVec 4))\n(assert (= (bv2nat a) 5))",
    )
    .unwrap();
    // Concrete check: under a = #b0101 = 5, the assertion is true.
    let mut asg = Assignment::new();
    asg.set(sym_of(&a, "a"), Value::Bv { width: 4, value: 5 });
    assert_eq!(
        eval(&a.arena, a.assertions[0], &asg).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        TermStats::compute(&a.arena, &a.assertions).dag_nodes,
        TermStats::compute(&b.arena, &b.assertions).dag_nodes,
        "ubv_to_int and bv2nat lower identically"
    );
}

#[test]
fn int_to_bv_aliases_int2bv() {
    // `(_ int_to_bv N)` (SMT-LIB 2.7) and `(_ int2bv N)` (2.6) are the same
    // indexed operator (integer reduced mod 2^N to an N-bit pattern).
    let a = parse_script("(set-logic QF_UFBVLIA)\n(declare-fun t () Int)\n(assert (= ((_ int_to_bv 3) t) (_ bv2 3)))").unwrap();
    // Under t = 10, 10 mod 8 = 2 = #b010, so the assertion is true.
    let mut asg = Assignment::new();
    asg.set(sym_of(&a, "t"), Value::Int(10));
    assert_eq!(
        eval(&a.arena, a.assertions[0], &asg).unwrap(),
        Value::Bool(true)
    );
    let b = parse_script(
        "(set-logic QF_UFBVLIA)\n(declare-fun t () Int)\n(assert (= ((_ int2bv 3) t) (_ bv2 3)))",
    )
    .unwrap();
    assert_eq!(
        TermStats::compute(&a.arena, &a.assertions).dag_nodes,
        TermStats::compute(&b.arena, &b.assertions).dag_nodes,
        "int_to_bv and int2bv lower identically"
    );
}

fn dt_of(script: &axeyum_smtlib::Script, name: &str) -> axeyum_ir::DatatypeId {
    script
        .arena
        .find_datatype(name)
        .unwrap_or_else(|| panic!("datatype `{name}` not declared"))
}

fn ctor_of(script: &axeyum_smtlib::Script, name: &str) -> axeyum_ir::ConstructorId {
    script
        .arena
        .find_constructor(name)
        .unwrap_or_else(|| panic!("constructor `{name}` not declared"))
}

// --- finite Sets via BitVec modeling ---------------------------------------
//
// `(Set E)` is modeled as a `BitVec(W)` over the finite element domain; the sound
// subset of set ops is desugared to BV ops at parse time. These tests are
// oracle-free: a satisfiable formula is checked by `eval`-ing the original
// assertions under a concrete BV model, and an unsatisfiable/declined shape is
// checked structurally.

/// A `(Set E)` constant resolves to a `BitVec(W)` sort (so set ops are BV ops).
#[test]
fn set_sort_is_modeled_as_bitvec() {
    let text = r"
        (set-logic QF_UFLIAFS)
        (declare-sort E 0)
        (declare-fun s () (Set E))
        (assert (set.member 0 s))
        (check-sat)
    ";
    let script = parse_script(text).unwrap();
    let s = sym_of(&script, "s");
    assert!(
        matches!(script.arena.symbol(s).1, Sort::BitVec(_)),
        "a (Set E) constant must resolve to a BitVec sort"
    );
    // The assertion `(set.member 0 s)` is a Bool (a bit test).
    assert_eq!(script.arena.sort_of(script.assertions[0]), Sort::Bool);
}

/// `(set.member e (set.union (set.singleton a) (set.singleton b)))` is true exactly
/// when `e ∈ {a, b}`. Checked by `eval` over the empty assignment (no free vars).
#[test]
fn set_member_of_union_of_singletons() {
    // 1 ∈ {1, 2}  ⇒ true.
    let s = parse_script(
        "(set-logic QF_UFLIAFS)\n(declare-sort E 0)\n\
         (assert (set.member 1 (set.union (set.singleton 1) (set.singleton 2))))",
    )
    .unwrap();
    assert_eq!(
        eval(&s.arena, s.assertions[0], &Assignment::new()).unwrap(),
        Value::Bool(true)
    );
    // 3 ∈ {1, 2}  ⇒ false.
    let s = parse_script(
        "(set-logic QF_UFLIAFS)\n(declare-sort E 0)\n\
         (assert (set.member 3 (set.union (set.singleton 1) (set.singleton 2))))",
    )
    .unwrap();
    assert_eq!(
        eval(&s.arena, s.assertions[0], &Assignment::new()).unwrap(),
        Value::Bool(false)
    );
}

/// Intersection / difference are exact over the named-element domain. `{1,2} ∩
/// {2,3} = {2}` and `{1,2} \ {2,3} = {1}`, checked by membership via `eval`.
#[test]
fn set_inter_and_minus_are_exact() {
    let s = parse_script(
        "(set-logic QF_UFLIAFS)\n(declare-sort E 0)\n\
         (assert (and \
            (set.member 2 (set.inter (set.union (set.singleton 1) (set.singleton 2)) \
                                     (set.union (set.singleton 2) (set.singleton 3)))) \
            (not (set.member 1 (set.inter (set.union (set.singleton 1) (set.singleton 2)) \
                                          (set.union (set.singleton 2) (set.singleton 3))))) \
            (set.member 1 (set.minus (set.union (set.singleton 1) (set.singleton 2)) \
                                     (set.union (set.singleton 2) (set.singleton 3)))) \
            (not (set.member 2 (set.minus (set.union (set.singleton 1) (set.singleton 2)) \
                                          (set.union (set.singleton 2) (set.singleton 3)))))))",
    )
    .unwrap();
    assert_eq!(
        eval(&s.arena, s.assertions[0], &Assignment::new()).unwrap(),
        Value::Bool(true)
    );
}

/// `(as set.empty (Set E))` is the all-zeros bit-set: nothing is a member, and a
/// `subset` of empty forces a free set empty. A satisfiable membership formula is
/// witnessed by a concrete BV model and re-checked by `eval`.
#[test]
fn set_empty_and_subset_witness() {
    // `(not (set.member 0 (as set.empty (Set E))))` is valid (empty has no members).
    let s = parse_script(
        "(set-logic QF_UFLIAFS)\n(declare-sort E 0)\n\
         (assert (not (set.member 0 (as set.empty (Set E)))))",
    )
    .unwrap();
    assert_eq!(
        eval(&s.arena, s.assertions[0], &Assignment::new()).unwrap(),
        Value::Bool(true)
    );

    // A free set `s` with `(set.subset (set.singleton 0) s)` and `(set.member 0 s)`:
    // pick the BV model where bit-0 of `s` is set; `eval` the original assertions.
    let s = parse_script(
        "(set-logic QF_UFLIAFS)\n(declare-sort E 0)\n(declare-fun s () (Set E))\n\
         (assert (set.subset (set.singleton 0) s))\n(assert (set.member 0 s))",
    )
    .unwrap();
    let sv = sym_of(&s, "s");
    let Sort::BitVec(w) = s.arena.symbol(sv).1 else {
        panic!("set var must be a BitVec");
    };
    let mut asg = Assignment::new();
    // bit-0 of `s` set (0 is the only named element → bit 0).
    asg.set(sv, Value::Bv { width: w, value: 1 });
    for &a in &s.assertions {
        assert_eq!(eval(&s.arena, a, &asg).unwrap(), Value::Bool(true));
    }
}

/// A `subset` that forces a contradiction is unsatisfiable: `s ⊆ {1}` and `2 ∈ s`
/// and `1 ∉ s` over a *free* `s` cannot hold, because the only members `s` can
/// have are among the named domain and the constraints pin every named bit. The
/// encoding makes this a pure BV/Bool formula; checked by exhausting the (tiny)
/// modeled domain.
#[test]
fn set_subset_unsat_shape_is_pure_bv() {
    let s = parse_script(
        "(set-logic QF_UFLIAFS)\n(declare-sort E 0)\n(declare-fun s () (Set E))\n\
         (assert (set.subset s (set.singleton 1)))\n(assert (set.member 2 s))",
    )
    .unwrap();
    // Every assertion is a Bool over a BitVec set var; no unsupported sort leaks.
    for &a in &s.assertions {
        assert_eq!(s.arena.sort_of(a), Sort::Bool);
    }
    let sv = sym_of(&s, "s");
    let Sort::BitVec(w) = s.arena.symbol(sv).1 else {
        panic!("set var must be a BitVec");
    };
    // Exhaust all 2^w assignments of `s`: the conjunction is never true (unsat).
    let mut any_sat = false;
    for value in 0u128..(1u128 << w) {
        let mut asg = Assignment::new();
        asg.set(sv, Value::Bv { width: w, value });
        let all = s
            .assertions
            .iter()
            .all(|&a| eval(&s.arena, a, &asg).unwrap() == Value::Bool(true));
        any_sat |= all;
    }
    assert!(!any_sat, "s ⊆ {{1}} ∧ 2 ∈ s must be unsatisfiable");
}

/// Two free sets over an infinite element sort can differ: `(not (= x y))` is
/// satisfiable. The junk margin bits give room for the witness; checked by `eval`.
#[test]
fn distinct_free_sets_are_satisfiable() {
    let s = parse_script(
        "(set-logic QF_UFLIAFS)\n(declare-fun x () (Set Int))\n(declare-fun y () (Set Int))\n\
         (assert (not (= x y)))",
    )
    .unwrap();
    let xv = sym_of(&s, "x");
    let yv = sym_of(&s, "y");
    let Sort::BitVec(w) = s.arena.symbol(xv).1 else {
        panic!("set var must be a BitVec");
    };
    let mut asg = Assignment::new();
    asg.set(xv, Value::Bv { width: w, value: 0 });
    asg.set(yv, Value::Bv { width: w, value: 1 });
    assert_eq!(
        eval(&s.arena, s.assertions[0], &asg).unwrap(),
        Value::Bool(true)
    );
}

/// `set.card` ranges over the whole (possibly infinite) element sort, so it is
/// **declined** — gracefully `Unsupported`, never a wrong verdict.
#[test]
fn set_card_is_declined_not_wrong() {
    let text = r"
        (set-logic QF_UFLIAFS)
        (declare-sort E 0)
        (declare-fun s () (Set E))
        (assert (>= (set.card s) 5))
        (check-sat)
    ";
    assert!(
        matches!(parse_script(text), Err(SmtError::Unsupported(_))),
        "set.card must be declined as Unsupported"
    );
}

/// `set.complement`/`set.universe`/`set.comprehension` are likewise declined.
#[test]
fn set_complement_and_comprehension_are_declined() {
    for op in [
        "(set.complement s)",
        "(set.subset x (set.comprehension ((z U)) (not (= z a)) z))",
    ] {
        let text = format!(
            "(set-logic QF_UFLIAFS)\n(declare-sort U 0)\n(declare-fun a () U)\n\
             (declare-fun s () (Set U))\n(declare-fun x () (Set U))\n(assert {op})"
        );
        assert!(
            matches!(parse_script(&text), Err(SmtError::Unsupported(_))),
            "`{op}` must be declined"
        );
    }
}

/// A non-literal element term (`(set.member (* v 7) s)`) can alias another element
/// term, so it is **declined** rather than risk an unsound per-term bit.
#[test]
fn nonliteral_set_element_is_declined() {
    let text = r"
        (set-logic QF_UFLIAFS)
        (declare-fun v () Int)
        (declare-fun s () (Set Int))
        (assert (set.member (* v 7) s))
        (check-sat)
    ";
    assert!(
        matches!(parse_script(text), Err(SmtError::Unsupported(_))),
        "non-literal set elements must be declined"
    );
}

/// A script with no sets at all is completely unaffected by the set pre-pass.
#[test]
fn no_set_usage_is_untouched() {
    let text = r"
        (set-logic QF_BV)
        (declare-fun a () (_ BitVec 4))
        (assert (= a (_ bv5 4)))
        (check-sat)
    ";
    let s = parse_script(text).unwrap();
    assert_eq!(s.assertions.len(), 1);
    assert_eq!(s.arena.sort_of(s.assertions[0]), Sort::Bool);
}

// --- bounded regex matching (`str.in_re`, ADR-0029 slice 5) ------------------

/// `str.in_re s R` over a single declared string `s`. The encoding is over `s`'s
/// packed bytes, so evaluating the asserted Bool under a concrete packed `s`
/// directly reports whether that string is in the regex language — an exact
/// oracle by construction. (`eval_string_script` ANDs the wf constraint too, so
/// only ≤8-byte strings are valid witnesses, which is the bounded fragment.)
#[test]
fn regex_to_re_and_star_and_concat_match() {
    // (str.in_re s (re.++ (str.to_re "a") (re.* (re.range "a" "z")))):
    // "a" followed by zero-or-more lowercase letters.
    let text = "(declare-fun s () String)\n\
                (assert (str.in_re s (re.++ (str.to_re \"a\") (re.* (re.range \"a\" \"z\")))))\n\
                (check-sat)\n";
    assert!(
        eval_string_script(text, pack_str(b"a")),
        "\"a\" matches (star = 0)"
    );
    assert!(
        eval_string_script(text, pack_str(b"abc")),
        "\"abc\" matches"
    );
    assert!(eval_string_script(text, pack_str(b"az")), "\"az\" matches");
    assert!(
        !eval_string_script(text, pack_str(b"b")),
        "\"b\" ≠ leading 'a'"
    );
    assert!(!eval_string_script(text, pack_str(b"a1")), "'1' ∉ [a-z]");
    assert!(
        !eval_string_script(text, pack_str(b"")),
        "empty ≠ needs leading 'a'"
    );
}

#[test]
fn regex_to_re_literal_exact_match() {
    // (str.in_re s (str.to_re "abc")) matches exactly "abc".
    let text = "(declare-fun s () String)\n\
                (assert (str.in_re s (str.to_re \"abc\")))\n(check-sat)\n";
    assert!(eval_string_script(text, pack_str(b"abc")), "exact match");
    assert!(!eval_string_script(text, pack_str(b"ab")), "prefix only");
    assert!(!eval_string_script(text, pack_str(b"abcd")), "extra char");
    assert!(!eval_string_script(text, pack_str(b"abd")), "wrong char");
}

#[test]
fn regex_union_matches_either_alternative() {
    // (str.in_re s (re.union (str.to_re "cat") (str.to_re "dog"))).
    let text = "(declare-fun s () String)\n\
                (assert (str.in_re s (re.union (str.to_re \"cat\") (str.to_re \"dog\"))))\n\
                (check-sat)\n";
    assert!(eval_string_script(text, pack_str(b"cat")), "cat ∈ union");
    assert!(eval_string_script(text, pack_str(b"dog")), "dog ∈ union");
    assert!(!eval_string_script(text, pack_str(b"cow")), "cow ∉ union");
    assert!(
        !eval_string_script(text, pack_str(b"ca")),
        "partial ∉ union"
    );
}

#[test]
fn regex_opt_matches_zero_or_one() {
    // (str.in_re s (re.++ (str.to_re "a") (re.opt (str.to_re "b")) (str.to_re "c"))):
    // "ac" or "abc".
    let text = "(declare-fun s () String)\n\
                (assert (str.in_re s (re.++ (str.to_re \"a\") (re.opt (str.to_re \"b\")) (str.to_re \"c\"))))\n\
                (check-sat)\n";
    assert!(eval_string_script(text, pack_str(b"ac")), "opt absent");
    assert!(eval_string_script(text, pack_str(b"abc")), "opt present");
    assert!(!eval_string_script(text, pack_str(b"abbc")), "opt is ≤1");
    assert!(!eval_string_script(text, pack_str(b"a")), "missing 'c'");
}

#[test]
fn regex_plus_requires_one_or_more() {
    // (str.in_re s (re.+ (str.to_re "ab"))): "ab", "abab", … but not "".
    let text = "(declare-fun s () String)\n\
                (assert (str.in_re s (re.+ (str.to_re \"ab\"))))\n(check-sat)\n";
    assert!(eval_string_script(text, pack_str(b"ab")), "one rep");
    assert!(eval_string_script(text, pack_str(b"abab")), "two reps");
    assert!(!eval_string_script(text, pack_str(b"")), "+ needs ≥1");
    assert!(
        !eval_string_script(text, pack_str(b"aba")),
        "incomplete rep"
    );
}

#[test]
fn regex_star_matches_empty() {
    // (str.in_re s (re.* (str.to_re "x"))): "", "x", "xx", …
    let text = "(declare-fun s () String)\n\
                (assert (str.in_re s (re.* (str.to_re \"x\"))))\n(check-sat)\n";
    assert!(eval_string_script(text, pack_str(b"")), "* matches empty");
    assert!(eval_string_script(text, pack_str(b"x")), "one x");
    assert!(eval_string_script(text, pack_str(b"xxx")), "many x");
    assert!(!eval_string_script(text, pack_str(b"xy")), "stray y");
}

#[test]
fn regex_allchar_all_none() {
    // re.allchar = any single char; re.all = Σ*; re.none = ∅.
    let any1 = "(declare-fun s () String)\n\
                (assert (str.in_re s re.allchar))\n(check-sat)\n";
    assert!(
        eval_string_script(any1, pack_str(b"q")),
        "one char ∈ allchar"
    );
    assert!(!eval_string_script(any1, pack_str(b"")), "empty ∉ allchar");
    assert!(
        !eval_string_script(any1, pack_str(b"qq")),
        "two chars ∉ allchar"
    );

    let all = "(declare-fun s () String)\n\
               (assert (str.in_re s re.all))\n(check-sat)\n";
    assert!(eval_string_script(all, pack_str(b"")), "empty ∈ all");
    assert!(
        eval_string_script(all, pack_str(b"hello")),
        "anything ∈ all"
    );

    let none = "(declare-fun s () String)\n\
                (assert (str.in_re s re.none))\n(check-sat)\n";
    assert!(!eval_string_script(none, pack_str(b"")), "empty ∉ none");
    assert!(!eval_string_script(none, pack_str(b"a")), "nothing ∈ none");
}

#[test]
fn regex_negated_in_re_is_complement_of_match() {
    // (not (str.in_re s (str.to_re "hi"))): true for every string except "hi".
    let text = "(declare-fun s () String)\n\
                (assert (not (str.in_re s (str.to_re \"hi\"))))\n(check-sat)\n";
    assert!(
        !eval_string_script(text, pack_str(b"hi")),
        "\"hi\" fails the negation"
    );
    assert!(
        eval_string_script(text, pack_str(b"ho")),
        "non-match passes"
    );
    assert!(eval_string_script(text, pack_str(b"")), "empty passes");
}

#[test]
fn regex_range_endpoints_and_degenerate() {
    // (re.range "0" "9"): a single digit.
    let digit = "(declare-fun s () String)\n\
                 (assert (str.in_re s (re.range \"0\" \"9\")))\n(check-sat)\n";
    assert!(eval_string_script(digit, pack_str(b"0")), "'0' in [0-9]");
    assert!(eval_string_script(digit, pack_str(b"9")), "'9' in [0-9]");
    assert!(eval_string_script(digit, pack_str(b"5")), "'5' in [0-9]");
    assert!(!eval_string_script(digit, pack_str(b"a")), "'a' ∉ [0-9]");
    assert!(
        !eval_string_script(digit, pack_str(b"")),
        "empty ∉ single-char class"
    );

    // A reversed range "9".."0" denotes ∅ (matches nothing).
    let empty = "(declare-fun s () String)\n\
                 (assert (str.in_re s (re.range \"9\" \"0\")))\n(check-sat)\n";
    assert!(
        !eval_string_script(empty, pack_str(b"5")),
        "reversed range is ∅"
    );
}

#[test]
fn regex_declined_constructs_are_clean_unsupported() {
    // re.comp (complement) is declined cleanly — never a wrong verdict.
    assert!(matches!(
        parse_script(
            "(declare-fun s () String)\n\
             (assert (str.in_re s (re.comp (str.to_re \"a\"))))\n(check-sat)\n"
        ),
        Err(SmtError::Unsupported(_))
    ));
    // re.diff is declined.
    assert!(matches!(
        parse_script(
            "(declare-fun s () String)\n\
             (assert (str.in_re s (re.diff re.all (str.to_re \"a\"))))\n(check-sat)\n"
        ),
        Err(SmtError::Unsupported(_))
    ));
    // (_ re.loop 0 2) (indexed head) is declined.
    assert!(matches!(
        parse_script(
            "(declare-fun s () String)\n\
             (assert (str.in_re s ((_ re.loop 0 2) (str.to_re \"a\"))))\n(check-sat)\n"
        ),
        Err(SmtError::Unsupported(_))
    ));
    // str.to_re of a non-literal (symbolic) string is declined.
    assert!(matches!(
        parse_script(
            "(declare-fun s () String)\n(declare-fun t () String)\n\
             (assert (str.in_re s (str.to_re t)))\n(check-sat)\n"
        ),
        Err(SmtError::Unsupported(_))
    ));
}

#[test]
fn regex_inter_matches_intersection() {
    // (re.inter (re.* (re.range "a" "z")) (str.to_re "ab")): lowercase-only ∩ {"ab"} = {"ab"}.
    let text = "(declare-fun s () String)\n\
                (assert (str.in_re s (re.inter (re.* (re.range \"a\" \"z\")) (str.to_re \"ab\"))))\n\
                (check-sat)\n";
    assert!(eval_string_script(text, pack_str(b"ab")), "ab in both");
    assert!(
        !eval_string_script(text, pack_str(b"a")),
        "a not in the singleton ab"
    );
    assert!(
        !eval_string_script(text, pack_str(b"AB")),
        "uppercase not lowercase-class"
    );
}

#[test]
fn regex_over_bound_string_is_not_a_wrong_verdict() {
    // A regex match constraint plus a length far over the bound: parsing succeeds
    // (the encoding is over the bounded bytes), and no ≤8-byte witness satisfies a
    // forced len=12, so eval is false for every representable string — i.e. the
    // bounded model is unsat-shaped here, which the solver surfaces as `unknown`
    // (tested end-to-end in the corpus run), never a wrong `sat`/`unsat`.
    let text = "(declare-fun s () String)\n\
                (assert (str.in_re s (re.* (str.to_re \"a\"))))\n\
                (assert (= (str.len s) 12))\n(check-sat)\n";
    let script = parse_script(text).expect("over-bound regex still parses");
    // No representable (≤8-byte, wf) witness can have len 12.
    for w in [b"".as_slice(), b"a", b"aaaaaaaa"] {
        assert!(
            !eval_string_script(text, pack_str(w)),
            "len ≠ 12 for any ≤8-byte string"
        );
    }
    assert!(
        script.assertions.len() >= 2,
        "wf + in_re + len constraints present"
    );
}

#[test]
fn regex_unicode_escape_range_is_sound() {
    // (re.range "\u{0}" "\u{ff}") is any byte (code points 0..=255 are
    // representable), so `str.in_re s (re.* …)` ∧ `str.in_re s …` is sat for any
    // single character — the exact `issue1684-regex` shape. The decode must NOT
    // collapse the escaped endpoints to the empty language (which was a latent
    // wrong-unsat).
    let any = "(declare-fun s () String)\n\
               (assert (str.in_re s (re.range \"\\u{0}\" \"\\u{ff}\")))\n(check-sat)\n";
    assert!(
        eval_string_script(any, pack_str(b"x")),
        "any single byte matches"
    );
    assert!(
        eval_string_script(any, pack_str(&[0u8])),
        "the NUL byte matches"
    );
    assert!(
        !eval_string_script(any, pack_str(b"")),
        "empty ∉ single-char class"
    );
    assert!(
        !eval_string_script(any, pack_str(b"xy")),
        "two chars ∉ single-char class"
    );

    // A \uXXXX escape for a digit: (re.range "0" "9") = [0-9].
    let digit = "(declare-fun s () String)\n\
                 (assert (str.in_re s (re.range \"\\u0030\" \"\\u0039\")))\n(check-sat)\n";
    assert!(
        eval_string_script(digit, pack_str(b"5")),
        "'5' in \\u0030-\\u0039"
    );
    assert!(!eval_string_script(digit, pack_str(b"a")), "'a' ∉ digits");
}

#[test]
fn regex_out_of_byte_codepoint_declines() {
    // A code point > 255 is outside the byte model; the regex must DECLINE
    // (Unsupported), never silently treat it as the empty language.
    assert!(matches!(
        parse_script(
            "(declare-fun s () String)\n\
             (assert (str.in_re s (str.to_re \"\\u{1f600}\")))\n(check-sat)\n"
        ),
        Err(SmtError::Unsupported(_))
    ));
    assert!(matches!(
        parse_script(
            "(declare-fun s () String)\n\
             (assert (str.in_re s (re.range \"\\u{100}\" \"\\u{200}\")))\n(check-sat)\n"
        ),
        Err(SmtError::Unsupported(_))
    ));
}
