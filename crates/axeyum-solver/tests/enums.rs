//! Finite enumeration datatypes lowered to bit-vectors, solved end-to-end.
#![cfg(feature = "full")]

use axeyum_ir::TermArena;
use axeyum_solver::{CheckResult, EnumSort, SolverConfig, solve};

#[test]
fn enum_width_and_domain_are_minimal() {
    // 3 constructors -> 2 bits, with a domain constraint (3 < 4).
    let three = EnumSort::new("Color", ["red", "green", "blue"]).unwrap();
    assert_eq!(three.width(), 2);
    assert_eq!(three.count(), 3);
    let mut arena = TermArena::new();
    let v = three.var(&mut arena, "c").unwrap();
    assert!(v.domain.is_some(), "3 of 4 patterns valid -> needs domain");

    // 4 constructors -> 2 bits, no domain constraint (every pattern valid).
    let four = EnumSort::new("Dir", ["n", "e", "s", "w"]).unwrap();
    assert_eq!(four.width(), 2);
    let mut arena2 = TermArena::new();
    let v4 = four.var(&mut arena2, "d").unwrap();
    assert!(v4.domain.is_none(), "all 4 patterns valid -> no domain");
}

#[test]
fn tester_selects_a_constructor_and_model_reads_back() {
    let color = EnumSort::new("Color", ["red", "green", "blue"]).unwrap();
    let mut arena = TermArena::new();
    let c = color.var(&mut arena, "c").unwrap();
    let is_green = color.tester(&mut arena, c.term, "green").unwrap();

    let mut assertions = vec![is_green];
    assertions.extend(c.domain);

    match solve(&mut arena, &assertions, &SolverConfig::default()).unwrap() {
        CheckResult::Sat(model) => {
            let sym = arena
                .symbols()
                .find(|(_, n, _)| *n == "c")
                .map(|(id, _, _)| id)
                .unwrap();
            let value = model.get(sym).unwrap();
            assert_eq!(color.value_name(&value), Some("green"));
        }
        other => panic!("expected sat, got {other:?}"),
    }
}

#[test]
fn two_distinct_constructors_are_unsat() {
    // is-red(c) AND is-green(c) cannot both hold.
    let color = EnumSort::new("Color", ["red", "green", "blue"]).unwrap();
    let mut arena = TermArena::new();
    let c = color.var(&mut arena, "c").unwrap();
    let is_red = color.tester(&mut arena, c.term, "red").unwrap();
    let is_green = color.tester(&mut arena, c.term, "green").unwrap();

    assert!(matches!(
        solve(&mut arena, &[is_red, is_green], &SolverConfig::default()),
        Ok(CheckResult::Unsat)
    ));
}

#[test]
fn domain_excludes_invalid_patterns() {
    // With 3 constructors over 2 bits, value 3 is not a constructor. Asserting
    // c != red, c != green, c != blue is unsat *given the domain* (only 0,1,2
    // are valid), but satisfiable without it (c = 3). This shows the domain
    // constraint is what makes the enum total over its constructors.
    let color = EnumSort::new("Color", ["red", "green", "blue"]).unwrap();
    let mut arena = TermArena::new();
    let c = color.var(&mut arena, "c").unwrap();
    let domain = c.domain.expect("3-of-4 needs a domain");
    let is_red = color.tester(&mut arena, c.term, "red").unwrap();
    let is_green = color.tester(&mut arena, c.term, "green").unwrap();
    let is_blue = color.tester(&mut arena, c.term, "blue").unwrap();
    let not_red = arena.not(is_red).unwrap();
    let not_green = arena.not(is_green).unwrap();
    let not_blue = arena.not(is_blue).unwrap();

    // Without the domain: c can be the spurious pattern 3 -> sat.
    assert!(matches!(
        solve(
            &mut arena,
            &[not_red, not_green, not_blue],
            &SolverConfig::default()
        ),
        Ok(CheckResult::Sat(_))
    ));
    // With the domain: every valid constructor is excluded -> unsat.
    assert!(matches!(
        solve(
            &mut arena,
            &[domain, not_red, not_green, not_blue],
            &SolverConfig::default()
        ),
        Ok(CheckResult::Unsat)
    ));
}
