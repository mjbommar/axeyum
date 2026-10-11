//! Promoted rational constants retain exact SMT-LIB source identities.
use axeyum_ir::{Rational, Sort, TermArena};
use axeyum_smtlib::write_script;

#[test]
fn promoted_real_constants_serialize_without_narrowing() {
    let twice_max = Rational::integer(i128::MAX)
        .wide_mul(Rational::integer(2))
        .unwrap();
    let tiny = Rational::new(1, i128::MAX)
        .wide_mul(Rational::new(1, 2))
        .unwrap();
    for (value, expected) in [
        (twice_max, "340282366920938463463374607431768211454.0"),
        (
            twice_max.wide_neg().unwrap(),
            "(- 340282366920938463463374607431768211454.0)",
        ),
        (tiny, "(/ 1.0 340282366920938463463374607431768211454.0)"),
        (
            tiny.wide_neg().unwrap(),
            "(- (/ 1.0 340282366920938463463374607431768211454.0))",
        ),
    ] {
        let mut arena = TermArena::new();
        let symbol = arena.declare("x", Sort::Real).unwrap();
        let x = arena.var(symbol);
        let constant = arena.real_const(value);
        let assertion = arena.eq(x, constant).unwrap();
        let source = write_script(&arena, &[assertion]);
        assert!(source.contains(expected), "{source}");
        assert!(source.contains("(assert (= x "));
    }
}
