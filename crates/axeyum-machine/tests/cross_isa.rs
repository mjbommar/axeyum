//! Direct checks for typed cross-machine relations.

use axeyum_machine::{
    cross_isa::{
        AbsoluteValuePoint, AbsoluteValuePrograms, RelationClause, RelationError,
        simulate_absolute_value, simulate_absolute_value_with_programs,
    },
    x64,
};

#[test]
fn absolute_value_relates_both_paths_and_boundaries() {
    for input in [
        0,
        1,
        7,
        i64::MAX as u64,
        u64::MAX,
        (-7_i64).cast_unsigned(),
        i64::MIN.cast_unsigned(),
    ] {
        let simulation = simulate_absolute_value(input).unwrap();
        assert!(
            simulation
                .relations
                .iter()
                .all(axeyum_machine::cross_isa::RelationResult::holds)
        );
        assert_eq!(simulation.update.is_some(), input.cast_signed() < 0);
        let expected = if input.cast_signed() >= 0 {
            input
        } else {
            0_u64.wrapping_sub(input)
        };
        assert_eq!(simulation.exit.a0.registers[0].unsigned(), expected);
        assert_eq!(simulation.exit.rv64.register(10), expected);
        assert_eq!(simulation.exit.x64.register(0), expected);
    }
}

#[test]
fn changed_x86_predicate_is_rejected_at_its_first_bad_point() {
    let canonical = AbsoluteValuePrograms::book().unwrap();
    let mutated = AbsoluteValuePrograms {
        a0: canonical.a0,
        rv64: canonical.rv64,
        x64: x64::Program::new(
            0,
            vec![
                0x48, 0x89, 0xf8, 0x48, 0x85, 0xc0, 0x74, 0x03, 0x48, 0xf7, 0xd8,
            ],
        ),
    };
    assert_eq!(
        simulate_absolute_value_with_programs(7, &mutated),
        Err(RelationError::FailedClause {
            point: AbsoluteValuePoint::Exit,
            clause: RelationClause::ControlPoint,
        })
    );
}

#[test]
fn relation_reports_stable_named_points_and_clauses() {
    let simulation = simulate_absolute_value((-3_i64).cast_unsigned()).unwrap();
    assert_eq!(
        simulation
            .relations
            .iter()
            .map(|relation| relation.point)
            .collect::<Vec<_>>(),
        [
            AbsoluteValuePoint::Entry,
            AbsoluteValuePoint::Decision,
            AbsoluteValuePoint::Update,
            AbsoluteValuePoint::Exit,
        ]
    );
    assert!(simulation.relations.iter().all(|relation| {
        relation.first_failure().is_none()
            && relation
                .clauses
                .iter()
                .any(|result| result.clause == RelationClause::MemoryFrame)
    }));
}
