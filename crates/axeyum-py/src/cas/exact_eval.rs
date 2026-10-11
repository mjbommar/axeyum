//! Bounded exact evaluation for Python's promoted rational expression surface.
use std::collections::BTreeMap;

use axeyum_arith::big::{BigInt, BigRational, One, Zero};
use axeyum_cas::CasExpr;
use axeyum_ir::Rational;
use pyo3::prelude::*;

use crate::error::BudgetExceeded;

const MAX_BITS: u64 = 16_384;
const MAX_NODES: usize = 4_096;

pub(crate) fn eval(expr: &CasExpr, env: &BTreeMap<String, Rational>) -> PyResult<Option<Rational>> {
    let mut remaining = MAX_NODES;
    match visit(expr, env, &mut remaining, 0) {
        Ok(value) => Rational::from_big_rational(&value)
            .map(Some)
            .ok_or_else(|| BudgetExceeded::new_err("exact rational interning limit exceeded")),
        Err(Decline::Unsupported) => Ok(None),
        Err(Decline::Resource) => Err(BudgetExceeded::new_err(
            "exact rational evaluation exceeds 16384 bits, 4096 nodes or depth 128",
        )),
    }
}

#[derive(Clone, Copy)]
enum Decline {
    Unsupported,
    Resource,
}

fn bounded(value: BigRational) -> Result<BigRational, Decline> {
    if value.numer().bits() > MAX_BITS || value.denom().bits() > MAX_BITS {
        Err(Decline::Resource)
    } else {
        Ok(value)
    }
}

fn visit(
    expr: &CasExpr,
    env: &BTreeMap<String, Rational>,
    remaining: &mut usize,
    depth: usize,
) -> Result<BigRational, Decline> {
    *remaining = remaining.checked_sub(1).ok_or(Decline::Resource)?;
    if depth > 128 {
        return Err(Decline::Resource);
    }
    match expr {
        CasExpr::Const(value) => bounded(value.to_big_rational()),
        CasExpr::Var(name) => bounded(env.get(name).ok_or(Decline::Unsupported)?.to_big_rational()),
        CasExpr::Add(terms) => terms.iter().try_fold(BigRational::zero(), |sum, term| {
            bounded(sum + visit(term, env, remaining, depth + 1)?)
        }),
        CasExpr::Mul(terms) => terms.iter().try_fold(BigRational::one(), |product, term| {
            bounded(product * visit(term, env, remaining, depth + 1)?)
        }),
        CasExpr::Neg(inner) => Ok(-visit(inner, env, remaining, depth + 1)?),
        CasExpr::Div(numerator, denominator) => {
            let denominator = visit(denominator, env, remaining, depth + 1)?;
            if denominator.is_zero() {
                return Err(Decline::Unsupported);
            }
            bounded(visit(numerator, env, remaining, depth + 1)? / denominator)
        }
        CasExpr::Pow(base, exponent) => {
            let mut base = visit(base, env, remaining, depth + 1)?;
            let mut exponent = *exponent;
            let mut value = BigRational::from_integer(BigInt::from(1));
            while exponent != 0 {
                if exponent & 1 == 1 {
                    value = bounded(value * &base)?;
                }
                exponent >>= 1;
                if exponent != 0 {
                    base = bounded(&base * &base)?;
                }
            }
            Ok(value)
        }
        CasExpr::Pi | CasExpr::Unary(_, _) => Err(Decline::Unsupported),
    }
}
