//! Typed cross-machine relations for the book's scalar teaching routines.
//!
//! This module relates states produced by the concrete A0, RV64I, and x86-64
//! semantics. It does not replace any instruction semantics with a second
//! implementation. The first route binds the exact absolute-value programs
//! printed in Chapter 12 and names every synchronization point and clause.

use crate::{a0, rv64, x64};

/// A named synchronization point in the three-machine absolute-value proof.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AbsoluteValuePoint {
    /// Before any instruction executes.
    Entry,
    /// Immediately before the architecture-specific signed branch.
    Decision,
    /// Immediately before modular negation on the negative path.
    Update,
    /// Immediately after the routine on either path.
    Exit,
}

/// One independently reported clause of the cross-machine relation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelationClause {
    /// The three program counters name the same logical control point.
    ControlPoint,
    /// All three machines remain in their running outcome.
    RunningOutcomes,
    /// A0 and RV64 carry the same logical word.
    A0ToRv64Value,
    /// A0 and x86-64 carry the same logical word.
    A0ToX64Value,
    /// A0's harness-provided zero register remains zero.
    A0ZeroRegister,
    /// All three architecture-specific predicates answer the same question.
    SignedPredicate,
    /// All three data memories equal the entry memory.
    MemoryFrame,
}

/// Result of one relation clause at one synchronization point.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClauseResult {
    /// Clause that was evaluated.
    pub clause: RelationClause,
    /// Whether the clause holds.
    pub holds: bool,
}

/// Complete relation result with deterministic first-failure reporting.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelationResult {
    /// Synchronization point checked.
    pub point: AbsoluteValuePoint,
    /// Clauses in stable diagnostic order.
    pub clauses: Vec<ClauseResult>,
}

impl RelationResult {
    /// Whether every declared clause holds.
    #[must_use]
    pub fn holds(&self) -> bool {
        self.clauses.iter().all(|result| result.holds)
    }

    /// First failed clause in stable diagnostic order.
    #[must_use]
    pub fn first_failure(&self) -> Option<RelationClause> {
        self.clauses
            .iter()
            .find_map(|result| (!result.holds).then_some(result.clause))
    }
}

/// Concrete states compared at one logical synchronization point.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbsoluteValueStates {
    /// A0 state.
    pub a0: a0::State,
    /// RV64I state.
    pub rv64: rv64::State,
    /// x86-64 state.
    pub x64: x64::State,
}

/// Complete replay of both the concrete programs and their typed relations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbsoluteValueSimulation {
    /// Common input word.
    pub input: u64,
    /// Entry states and relation.
    pub entry: AbsoluteValueStates,
    /// Architecture-specific decision states and relation.
    pub decision: AbsoluteValueStates,
    /// Negative-path update states and relation, absent on the keep path.
    pub update: Option<AbsoluteValueStates>,
    /// Exit states and relation.
    pub exit: AbsoluteValueStates,
    /// Relation checks in execution order.
    pub relations: Vec<RelationResult>,
}

/// Failure to construct or reach a declared relation point.
#[allow(missing_docs)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RelationError {
    A0(a0::A0Error),
    DidNotReach {
        machine: &'static str,
        expected: u64,
        actual: u64,
    },
    FailedClause {
        point: AbsoluteValuePoint,
        clause: RelationClause,
    },
}

impl From<a0::A0Error> for RelationError {
    fn from(error: a0::A0Error) -> Self {
        Self::A0(error)
    }
}

/// Exact code images printed in the Chapter 12 byte table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbsoluteValuePrograms {
    /// Exact A0 code image.
    pub a0: a0::Program,
    /// Exact RV64I code image.
    pub rv64: rv64::Program,
    /// Exact x86-64 code image.
    pub x64: x64::Program,
}

impl AbsoluteValuePrograms {
    /// Constructs the three canonical code images at base address zero.
    ///
    /// # Errors
    ///
    /// Returns an A0 construction error if the fixed 64-bit code base cannot
    /// be represented, which would indicate a semantic-package defect.
    pub fn book() -> Result<Self, RelationError> {
        Ok(Self {
            a0: a0::Program::new(
                64,
                a0::Word::new(64, 0)?,
                vec![
                    0x11, 0x02, 0x01, 0x00, 0x30, 0x00, 0x18, 0x01, 0x11, 0x08, 0x00, 0x00,
                ],
            )?,
            rv64: rv64::Program::new(0, vec![0x63, 0x54, 0x05, 0x00, 0x33, 0x05, 0xa0, 0x40]),
            x64: x64::Program::new(
                0,
                vec![
                    0x48, 0x89, 0xf8, 0x48, 0x85, 0xc0, 0x79, 0x03, 0x48, 0xf7, 0xd8,
                ],
            ),
        })
    }
}

/// Replays the exact three-machine absolute-value routine and checks every
/// named relation point.
///
/// This establishes modular absolute value for the supplied concrete input.
/// Interpreting the result as positive mathematical absolute value additionally
/// excludes `0x8000_0000_0000_0000`, as the chapter states.
///
/// # Errors
///
/// Returns the first unreachable control point or failed relation clause.
pub fn simulate_absolute_value(input: u64) -> Result<AbsoluteValueSimulation, RelationError> {
    simulate_absolute_value_with_programs(input, &AbsoluteValuePrograms::book()?)
}

/// Replays absolute value with explicitly supplied code images.
///
/// This entry point exists so evidence controls can mutate one program while
/// retaining the same relation checker.
///
/// # Errors
///
/// Returns the first unreachable control point or failed relation clause.
pub fn simulate_absolute_value_with_programs(
    input: u64,
    programs: &AbsoluteValuePrograms,
) -> Result<AbsoluteValueSimulation, RelationError> {
    let memory = a0::Memory::zeroed(0);
    let zero = a0::Word::new(64, 0)?;
    let mut a0_entry = a0::State::new(64, memory.clone(), zero)?;
    a0_entry.registers[0] = a0::Word::new(64, input)?;
    let mut rv64_entry = rv64::State::new(memory.clone(), 0);
    rv64_entry.registers[10] = input;
    let mut x64_entry = x64::State::new(memory, 0);
    x64_entry.registers[7] = input;
    let entry = AbsoluteValueStates {
        a0: a0_entry,
        rv64: rv64_entry,
        x64: x64_entry,
    };

    let decision = AbsoluteValueStates {
        a0: a0::step(&programs.a0, &entry.a0),
        rv64: entry.rv64.clone(),
        x64: x64::step(&programs.x64, &x64::step(&programs.x64, &entry.x64)),
    };
    let nonnegative = signed_nonnegative(input);
    let (update, exit) = if nonnegative {
        (
            None,
            AbsoluteValueStates {
                a0: a0::step(&programs.a0, &decision.a0),
                rv64: rv64::step(&programs.rv64, &decision.rv64),
                x64: x64::step(&programs.x64, &decision.x64),
            },
        )
    } else {
        let update = AbsoluteValueStates {
            a0: a0::step(&programs.a0, &decision.a0),
            rv64: rv64::step(&programs.rv64, &decision.rv64),
            x64: x64::step(&programs.x64, &decision.x64),
        };
        let exit = AbsoluteValueStates {
            a0: a0::step(&programs.a0, &update.a0),
            rv64: rv64::step(&programs.rv64, &update.rv64),
            x64: x64::step(&programs.x64, &update.x64),
        };
        (Some(update), exit)
    };
    let mut relations = vec![check_absolute_value_relation(
        AbsoluteValuePoint::Entry,
        input,
        &entry,
        &entry,
    )];
    relations.push(check_absolute_value_relation(
        AbsoluteValuePoint::Decision,
        input,
        &entry,
        &decision,
    ));
    if let Some(states) = &update {
        relations.push(check_absolute_value_relation(
            AbsoluteValuePoint::Update,
            input,
            &entry,
            states,
        ));
    }
    relations.push(check_absolute_value_relation(
        AbsoluteValuePoint::Exit,
        input,
        &entry,
        &exit,
    ));
    if let Some((failed, clause)) = relations
        .iter()
        .find_map(|result| result.first_failure().map(|clause| (result, clause)))
    {
        return Err(RelationError::FailedClause {
            point: failed.point,
            clause,
        });
    }
    Ok(AbsoluteValueSimulation {
        input,
        entry,
        decision,
        update,
        exit,
        relations,
    })
}

/// Evaluates the typed relation at one declared synchronization point.
#[must_use]
pub fn check_absolute_value_relation(
    point: AbsoluteValuePoint,
    input: u64,
    entry: &AbsoluteValueStates,
    states: &AbsoluteValueStates,
) -> RelationResult {
    let (a0_pc, rv64_pc, x64_pc) = point_pcs(point);
    let a0_value = match point {
        AbsoluteValuePoint::Entry | AbsoluteValuePoint::Decision | AbsoluteValuePoint::Update => {
            states.a0.registers[0].unsigned()
        }
        AbsoluteValuePoint::Exit => states.a0.registers[0].unsigned(),
    };
    let rv64_value = states.rv64.register(10);
    let x64_value = match point {
        AbsoluteValuePoint::Entry => states.x64.register(7),
        AbsoluteValuePoint::Decision | AbsoluteValuePoint::Update | AbsoluteValuePoint::Exit => {
            states.x64.register(0)
        }
    };
    let expected = if point == AbsoluteValuePoint::Exit {
        modular_absolute_value(input)
    } else {
        input
    };
    let mut clauses = vec![
        ClauseResult {
            clause: RelationClause::ControlPoint,
            holds: states.a0.pc.unsigned() == a0_pc
                && states.rv64.pc == rv64_pc
                && states.x64.rip == x64_pc,
        },
        ClauseResult {
            clause: RelationClause::RunningOutcomes,
            holds: states.a0.outcome == a0::Outcome::Running
                && states.rv64.outcome == rv64::Outcome::Running
                && states.x64.outcome == x64::Outcome::Running,
        },
        ClauseResult {
            clause: RelationClause::A0ToRv64Value,
            holds: a0_value == expected && rv64_value == a0_value,
        },
        ClauseResult {
            clause: RelationClause::A0ToX64Value,
            holds: a0_value == expected && x64_value == a0_value,
        },
        ClauseResult {
            clause: RelationClause::A0ZeroRegister,
            holds: states.a0.registers[1].unsigned() == 0,
        },
    ];
    if point == AbsoluteValuePoint::Decision {
        clauses.push(ClauseResult {
            clause: RelationClause::SignedPredicate,
            holds: (states.a0.conditions.negative == states.a0.conditions.overflow)
                == signed_nonnegative(input)
                && (states.rv64.register(10).cast_signed() >= 0) == signed_nonnegative(input)
                && (states.x64.flags.sign == x64::FlagValue::Clear) == signed_nonnegative(input),
        });
    }
    clauses.push(ClauseResult {
        clause: RelationClause::MemoryFrame,
        holds: states.a0.memory == entry.a0.memory
            && states.rv64.memory == entry.rv64.memory
            && states.x64.memory == entry.x64.memory,
    });
    RelationResult { point, clauses }
}

const fn point_pcs(point: AbsoluteValuePoint) -> (u64, u64, u64) {
    match point {
        AbsoluteValuePoint::Entry => (0, 0, 0),
        AbsoluteValuePoint::Decision => (4, 0, 6),
        AbsoluteValuePoint::Update => (8, 4, 8),
        AbsoluteValuePoint::Exit => (12, 8, 11),
    }
}

const fn signed_nonnegative(value: u64) -> bool {
    value & (1_u64 << 63) == 0
}

const fn modular_absolute_value(value: u64) -> u64 {
    if signed_nonnegative(value) {
        value
    } else {
        0_u64.wrapping_sub(value)
    }
}
