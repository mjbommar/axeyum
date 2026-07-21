//! Typed source-contract bridges into checked reflection summaries.
//!
//! ADR-0317 deliberately starts with one tiny total scalar fragment. The
//! source contract is proved through the ordinary source verifier first, then
//! translated into the already checked
//! [`ScalarCallContract`](crate::reflect::llvm::loops::ScalarCallContract)
//! language. A MIR
//! resolver must still verify that declaration independently against an exact
//! compiler body before any caller may consume it.

use std::error::Error;
use std::fmt;

use axeyum_solver::SolverConfig;

use crate::ast::{BinOp, ContractProgram, Expr, Ty};
use crate::reflect::llvm::loops::{ScalarCallContract, ScalarContractExpr};
use crate::{Verdict, verify_contract_program};

/// Stable failure class for the first source-contract summary bridge.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SourceContractBridgeErrorKind {
    /// The source verifier found a concrete contract/body counterexample.
    SourceCounterexample,
    /// Source verification was invalid, unsupported, or undecided.
    SourceUnknown,
    /// Source verification did not produce independently rechecked evidence.
    SourceUncertified,
    /// The contract lies outside ADR-0317's exact total `u8` fragment.
    UnsupportedShape,
    /// Existing scalar-contract construction rejected the translated form.
    ContractConstruction,
    /// The source-verification solver raised a hard error.
    Solver,
}

/// Fail-closed error from [`scalar_contract_from_source`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceContractBridgeError {
    kind: SourceContractBridgeErrorKind,
    detail: String,
}

impl SourceContractBridgeError {
    fn new(kind: SourceContractBridgeErrorKind, detail: impl Into<String>) -> Self {
        Self {
            kind,
            detail: detail.into(),
        }
    }

    /// Stable failure class.
    #[must_use]
    pub fn kind(&self) -> SourceContractBridgeErrorKind {
        self.kind
    }

    /// Deterministic human-readable detail.
    #[must_use]
    pub fn detail(&self) -> &str {
        &self.detail
    }
}

impl fmt::Display for SourceContractBridgeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}", self.detail)
    }
}

impl Error for SourceContractBridgeError {}

/// Proves and translates ADR-0317's total annotated scalar contract.
///
/// The admitted version-one shape is deliberately exact: one unsigned `u8`
/// parameter, no prefix statements or arrays, literal-true `requires`, a
/// retained `wrapping_add` result, and an equality postcondition over the
/// retained result. The output is the existing relational
/// [`ScalarCallContract`]; compiler-body verification remains the independent
/// responsibility of a checked MIR resolver.
///
/// # Errors
///
/// Returns a stable [`SourceContractBridgeError`] when source verification is
/// refuted/undecided/uncertified, the AST leaves the frozen fragment, existing
/// contract construction rejects the translation, or the solver hard-errors.
pub fn scalar_contract_from_source(
    contract: &ContractProgram,
    config: &SolverConfig,
) -> Result<ScalarCallContract, SourceContractBridgeError> {
    match verify_contract_program(contract, config) {
        Ok(Verdict::Verified {
            certified: true, ..
        }) => {}
        Ok(Verdict::Verified {
            certified: false, ..
        }) => {
            return Err(SourceContractBridgeError::new(
                SourceContractBridgeErrorKind::SourceUncertified,
                "source contract verified without independently rechecked evidence",
            ));
        }
        Ok(Verdict::Counterexample { class, .. }) => {
            return Err(SourceContractBridgeError::new(
                SourceContractBridgeErrorKind::SourceCounterexample,
                format!("source contract has a replayable `{class}` counterexample"),
            ));
        }
        Ok(Verdict::Unknown { reason }) => {
            return Err(SourceContractBridgeError::new(
                SourceContractBridgeErrorKind::SourceUnknown,
                format!("source contract is not verified: {reason}"),
            ));
        }
        Err(error) => {
            return Err(SourceContractBridgeError::new(
                SourceContractBridgeErrorKind::Solver,
                format!("source contract verification failed: {error}"),
            ));
        }
    }

    let program = &contract.program;
    let [parameter] = program.params.as_slice() else {
        return Err(unsupported("expected exactly one scalar parameter"));
    };
    let byte_ty = Ty::Int {
        width: 8,
        signed: false,
    };
    if parameter.ty != byte_ty {
        return Err(unsupported("the sole parameter must be unsigned `u8`"));
    }
    if !program.arrays.is_empty() {
        return Err(unsupported("arrays are outside the first source bridge"));
    }
    if !program.body.is_empty() {
        return Err(unsupported(
            "prefix statements are outside the first source bridge",
        ));
    }
    if !matches!(contract.requires, Expr::BoolLit(true)) {
        return Err(unsupported(
            "the first checked-MIR bridge requires literal-true `requires`",
        ));
    }
    if contract.result_name == parameter.name {
        return Err(unsupported(
            "the retained result binding must not collide with the parameter",
        ));
    }

    let context = TranslationContext {
        parameter: &parameter.name,
        result: &contract.result_name,
        byte_ty,
    };
    let translated_result = translate_expr(&contract.result, &context, false)?;
    let translated_ensures = translate_expr(&contract.ensures, &context, true)?;
    let expected_result = ScalarContractExpr::BvAdd(
        Box::new(ScalarContractExpr::Argument(0)),
        Box::new(ScalarContractExpr::BitVec { width: 8, value: 1 }),
    );
    if translated_result != expected_result {
        return Err(unsupported(
            "the retained result must be exactly `parameter.wrapping_add(1)`",
        ));
    }
    let expected_ensures = ScalarContractExpr::Eq(
        Box::new(ScalarContractExpr::Result),
        Box::new(expected_result),
    );
    if translated_ensures != expected_ensures {
        return Err(unsupported(
            "the postcondition must equate the result with `parameter.wrapping_add(1)`",
        ));
    }

    ScalarCallContract::new_relational(
        &program.name,
        vec![8],
        8,
        ScalarContractExpr::Bool(true),
        ScalarContractExpr::Bool(true),
        translated_ensures,
        ScalarContractExpr::Bool(true),
    )
    .map_err(|error| {
        SourceContractBridgeError::new(
            SourceContractBridgeErrorKind::ContractConstruction,
            format!("translated scalar contract was rejected: {error}"),
        )
    })
}

struct TranslationContext<'a> {
    parameter: &'a str,
    result: &'a str,
    byte_ty: Ty,
}

fn translate_expr(
    expression: &Expr,
    context: &TranslationContext<'_>,
    allow_result: bool,
) -> Result<ScalarContractExpr, SourceContractBridgeError> {
    match expression {
        Expr::BoolLit(true) => Ok(ScalarContractExpr::Bool(true)),
        Expr::IntLit { value, ty } if *ty == context.byte_ty && *value <= u8::MAX.into() => {
            Ok(ScalarContractExpr::BitVec {
                width: 8,
                value: *value,
            })
        }
        Expr::Var(name) if name == context.parameter => Ok(ScalarContractExpr::Argument(0)),
        Expr::Var(name) if allow_result && name == context.result => Ok(ScalarContractExpr::Result),
        Expr::Binary {
            op: BinOp::Eq,
            lhs,
            rhs,
        } => Ok(ScalarContractExpr::Eq(
            Box::new(translate_expr(lhs, context, allow_result)?),
            Box::new(translate_expr(rhs, context, allow_result)?),
        )),
        Expr::Binary {
            op: BinOp::WrappingAdd,
            lhs,
            rhs,
        } => Ok(ScalarContractExpr::BvAdd(
            Box::new(translate_expr(lhs, context, allow_result)?),
            Box::new(translate_expr(rhs, context, allow_result)?),
        )),
        Expr::Var(name) if name == context.result => Err(unsupported(
            "the retained result binding is not allowed in this contract component",
        )),
        Expr::Var(name) => Err(unsupported(&format!(
            "unknown source-contract variable `{name}`"
        ))),
        _ => Err(unsupported(
            "source expression is outside the first wrapping-add bridge",
        )),
    }
}

fn unsupported(detail: &str) -> SourceContractBridgeError {
    SourceContractBridgeError::new(SourceContractBridgeErrorKind::UnsupportedShape, detail)
}
