//! Flat append-only formula-arena gates (ADR-0285).

use axeyum_cnf::{CnfClause, CnfError, CnfFormula, CnfLit, CnfVar, parse_dimacs};

fn p(index: usize) -> CnfLit {
    CnfLit::positive(CnfVar::new(index).unwrap())
}

fn eval_clause(clause: &[CnfLit], assignment: &[bool]) -> bool {
    clause.iter().copied().any(|lit| {
        let value = assignment[lit.var().index()];
        value != lit.is_negated()
    })
}

fn eval_oracle(clauses: &[Vec<CnfLit>], assignment: &[bool]) -> bool {
    clauses.iter().all(|clause| eval_clause(clause, assignment))
}

#[test]
fn flat_formula_preserves_order_index_clone_evaluation_and_dimacs() {
    let expected = vec![
        vec![],
        vec![p(0)],
        vec![p(1).negated(), p(2)],
        vec![p(0), p(2).negated(), p(3)],
        vec![p(3), p(2), p(1), p(0).negated()],
    ];
    let mut formula = CnfFormula::new(4);
    for clause in &expected {
        formula.add_clause(CnfClause::new(clause.clone())).unwrap();
    }

    assert_eq!(formula.clause_count(), expected.len());
    assert_eq!(formula.literal_count(), 10);
    assert_eq!(formula.clause(0), Some(&[][..]));
    assert_eq!(formula.clause(2), Some(expected[2].as_slice()));
    assert_eq!(formula.clause(expected.len()), None);
    assert_eq!(
        formula
            .clauses()
            .map(<[CnfLit]>::to_vec)
            .collect::<Vec<_>>(),
        expected
    );
    assert_eq!(formula.clone(), formula);

    for bits in 0_u8..16 {
        let assignment = (0..4)
            .map(|index| bits & (1 << index) != 0)
            .collect::<Vec<_>>();
        assert_eq!(
            formula.evaluate(&assignment).unwrap(),
            eval_oracle(&expected, &assignment)
        );
    }

    let dimacs = formula.to_dimacs();
    let reparsed = parse_dimacs(&dimacs).unwrap();
    assert_eq!(reparsed, formula);
    assert_eq!(reparsed.to_dimacs(), dimacs);
}

#[test]
fn structured_formula_matches_vec_oracle_and_reports_storage_exactly() {
    const CLAUSES: usize = 10_000;
    const VARIABLES: usize = 32;
    let mut expected = Vec::with_capacity(CLAUSES);
    let mut formula = CnfFormula::new(VARIABLES);
    let mut state = 0xd1b5_4a32_d192_ed03_u64;

    for index in 0..CLAUSES {
        let selector = index % 100;
        let len = match selector {
            0 => 0,
            1..=8 => 1,
            9..=70 => 2,
            71..=98 => 3,
            _ => 7,
        };
        let mut clause = Vec::with_capacity(len);
        for _ in 0..len {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let var = usize::from(state.to_le_bytes()[0]) % VARIABLES;
            let lit = if state >> 63 == 0 {
                p(var)
            } else {
                p(var).negated()
            };
            clause.push(lit);
        }
        formula.add_clause(CnfClause::new(clause.clone())).unwrap();
        expected.push(clause);
    }

    assert_eq!(
        formula
            .clauses()
            .map(<[CnfLit]>::to_vec)
            .collect::<Vec<_>>(),
        expected
    );
    for sample in 0_u64..256 {
        let assignment = (0..VARIABLES)
            .map(|index| sample.rotate_left(u32::try_from(index).unwrap()) & 1 != 0)
            .collect::<Vec<_>>();
        assert_eq!(
            formula.evaluate(&assignment).unwrap(),
            eval_oracle(&expected, &assignment)
        );
    }

    let profile = formula.storage_profile();
    assert!(profile.invariants_hold());
    assert!(profile.clause_ends_monotone);
    assert!(profile.clause_ends_in_bounds);
    assert!(profile.terminal_end_matches_literals);
    assert_eq!(profile.clauses, CLAUSES);
    assert_eq!(
        profile.literals,
        expected.iter().map(Vec::len).sum::<usize>()
    );
    assert_eq!(profile.clause_end_logical_bytes, CLAUSES * size_of::<u32>());
    assert_eq!(
        profile.literal_logical_bytes,
        profile.literals * size_of::<CnfLit>()
    );
    assert_eq!(
        profile.arena_logical_bytes,
        profile.clause_end_logical_bytes + profile.literal_logical_bytes
    );
    assert!(
        profile.arena_logical_bytes * 5 <= profile.legacy_logical_lower_bound_bytes * 4,
        "flat logical storage must use at most 80% of the conservative legacy lower bound: {profile:?}"
    );
}

#[test]
fn invalid_clause_does_not_mutate_flat_formula() {
    let mut formula = CnfFormula::new(2);
    formula.add_clause(CnfClause::new(vec![p(0)])).unwrap();
    let before = formula.clone();

    assert_eq!(
        formula.add_clause(CnfClause::new(vec![p(1), p(2)])),
        Err(CnfError::InvalidVariable {
            variable: 3,
            variable_count: 2,
        })
    );
    assert_eq!(formula, before);
}
