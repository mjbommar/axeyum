//! Versioned, bounded expression transport (ADR-6100); carries no proof claim.
use crate::{CasExpr, UnaryFunc};
use axeyum_ir::Rational;
use num_bigint::BigInt;
use num_rational::BigRational;
use serde::{Deserialize, Serialize};

const MAX_BYTES: usize = 1_048_576;
const MAX_NODES: usize = 4096;
const MAX_DEPTH: usize = 32;
const MAX_BITS: u64 = 16384;
const MAX_NAME: usize = 1024;

/// Transport failures distinguish invalid syntax from explicit resource limits.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WireError {
    /// Invalid or unsupported version-1 encoding.
    Invalid(String),
    /// A hard transport cap was exceeded.
    ResourceLimit(String),
}
impl std::fmt::Display for WireError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Invalid(s) => write!(f, "invalid expression encoding: {s}"),
            Self::ResourceLimit(s) => write!(f, "expression encoding resource limit: {s}"),
        }
    }
}
impl std::error::Error for WireError {}
fn invalid(s: &str) -> WireError {
    WireError::Invalid(s.into())
}
fn resource(s: &str) -> WireError {
    WireError::ResourceLimit(s.into())
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Envelope {
    version: u32,
    expression: Node,
}
#[derive(Serialize, Deserialize)]
#[serde(
    tag = "kind",
    content = "args",
    rename_all = "snake_case",
    deny_unknown_fields
)]
enum Node {
    Const {
        numerator: String,
        denominator: String,
    },
    Pi,
    Var(String),
    Add(Vec<Node>),
    Mul(Vec<Node>),
    Neg(Box<Node>),
    Div {
        numerator: Box<Node>,
        denominator: Box<Node>,
    },
    Pow {
        base: Box<Node>,
        exponent: u32,
    },
    Unary {
        head: UnaryFunc,
        argument: Box<Node>,
    },
}

fn rational(n: &str, d: &str) -> Result<Rational, WireError> {
    // Bound decimal parsing before allocating bignum arithmetic intermediates.
    if n.len() > 5000 || d.len() > 5000 {
        return Err(resource("rational digits"));
    }
    let n: BigInt = n.parse().map_err(|_| invalid("numerator"))?;
    let d: BigInt = d.parse().map_err(|_| invalid("denominator"))?;
    if n.bits() > MAX_BITS || d.bits() > MAX_BITS {
        return Err(resource("rational bits"));
    }
    if d <= BigInt::from(0) {
        return Err(invalid("denominator must be positive"));
    }
    Rational::from_big_rational(&BigRational::new(n, d)).ok_or_else(|| resource("rational carrier"))
}

fn inspect(expr: &CasExpr) -> Result<(), WireError> {
    let mut pending = vec![(expr, 1)];
    let mut nodes = 0;
    let mut size = 0usize;
    while let Some((node, depth)) = pending.pop() {
        nodes += 1;
        if nodes > MAX_NODES || depth > MAX_DEPTH {
            return Err(resource("nodes or depth"));
        }
        size += 128; // Conservative JSON syntax overhead for every node.
        match node {
            CasExpr::Const(r) => {
                let n = r.numerator_big();
                let d = r.denominator_big();
                if n.bits() > MAX_BITS || d.bits() > MAX_BITS {
                    return Err(resource("rational bits"));
                }
                size += n.to_string().len() + d.to_string().len();
            }
            CasExpr::Var(s) => {
                if s.len() > MAX_NAME {
                    return Err(resource("variable name"));
                }
                size += s.len() * 6; // Worst-case JSON escaping.
            }
            CasExpr::Pi => (),
            CasExpr::Add(v) | CasExpr::Mul(v) => {
                if v.len() > MAX_NODES {
                    return Err(resource("children"));
                }
                pending.extend(v.iter().map(|e| (e, depth + 1)));
            }
            CasExpr::Neg(e) | CasExpr::Pow(e, _) | CasExpr::Unary(_, e) => {
                pending.push((e, depth + 1));
            }
            CasExpr::Div(a, b) => {
                pending.push((a, depth + 1));
                pending.push((b, depth + 1));
            }
        }
        if size > MAX_BYTES {
            return Err(resource("encoded size"));
        }
    }
    Ok(())
}
fn encode(e: &CasExpr) -> Node {
    match e {
        CasExpr::Const(r) => Node::Const {
            numerator: r.numerator_big().to_string(),
            denominator: r.denominator_big().to_string(),
        },
        CasExpr::Pi => Node::Pi,
        CasExpr::Var(s) => Node::Var(s.clone()),
        CasExpr::Add(v) => Node::Add(v.iter().map(encode).collect()),
        CasExpr::Mul(v) => Node::Mul(v.iter().map(encode).collect()),
        CasExpr::Neg(e) => Node::Neg(Box::new(encode(e))),
        CasExpr::Div(a, b) => Node::Div {
            numerator: Box::new(encode(a)),
            denominator: Box::new(encode(b)),
        },
        CasExpr::Pow(e, exponent) => Node::Pow {
            base: Box::new(encode(e)),
            exponent: *exponent,
        },
        CasExpr::Unary(head, e) => Node::Unary {
            head: *head,
            argument: Box::new(encode(e)),
        },
    }
}
fn decode(e: Node, depth: usize, nodes: &mut usize) -> Result<CasExpr, WireError> {
    *nodes += 1;
    if *nodes > MAX_NODES || depth > MAX_DEPTH {
        return Err(resource("nodes or depth"));
    }
    let mut child = |e| decode(e, depth + 1, nodes);
    Ok(match e {
        Node::Const {
            numerator,
            denominator,
        } => {
            let r = rational(&numerator, &denominator)?;
            if r.numerator_big().to_string() != numerator
                || r.denominator_big().to_string() != denominator
            {
                return Err(invalid(
                    "rational must use reduced canonical decimal components",
                ));
            }
            CasExpr::Const(r)
        }
        Node::Pi => CasExpr::Pi,
        Node::Var(s) => {
            if s.len() > MAX_NAME {
                return Err(resource("variable name"));
            }
            CasExpr::Var(s)
        }
        Node::Add(v) => CasExpr::Add(v.into_iter().map(&mut child).collect::<Result<_, _>>()?),
        Node::Mul(v) => CasExpr::Mul(v.into_iter().map(&mut child).collect::<Result<_, _>>()?),
        Node::Neg(e) => CasExpr::Neg(Box::new(child(*e)?)),
        Node::Div {
            numerator,
            denominator,
        } => CasExpr::Div(Box::new(child(*numerator)?), Box::new(child(*denominator)?)),
        Node::Pow { base, exponent } => CasExpr::Pow(Box::new(child(*base)?), exponent),
        Node::Unary { head, argument } => CasExpr::Unary(head, Box::new(child(*argument)?)),
    })
}
/// Serialize exact source syntax, including constant identity and wide rationals.
///
/// # Errors
/// Returns a resource limit when the source exceeds hard transport caps.
pub fn to_json(expr: &CasExpr) -> Result<String, WireError> {
    inspect(expr)?;
    let s = serde_json::to_string(&Envelope {
        version: 1,
        expression: encode(expr),
    })
    .map_err(|e| invalid(&e.to_string()))?;
    if s.len() > MAX_BYTES {
        return Err(resource("bytes"));
    }
    Ok(s)
}
/// Decode version-1 source syntax without simplifying or certifying it.
///
/// # Errors
/// Rejects malformed/noncanonical components and reports hard transport limits.
pub fn from_json(s: &str) -> Result<CasExpr, WireError> {
    if s.len() > MAX_BYTES {
        return Err(resource("bytes"));
    }
    let envelope: Envelope = serde_json::from_str(s).map_err(|e| invalid(&e.to_string()))?;
    if envelope.version != 1 {
        return Err(invalid("unsupported version"));
    }
    let expr = decode(envelope.expression, 1, &mut 0)?;
    inspect(&expr)?;
    Ok(expr)
}
