//! Original-source certificate data. Deserialization alone grants no acceptance.
use super::{OptimizationMode, OptimizationReport};
use crate::SolverError;
use axeyum_ir::{Rational, Value};
use serde::{Deserialize, Serialize};

const BYTE_CAP: usize = 262_144;
const SOURCE_CAP: usize = 65_536;

/// Source-bearing evidence envelope; check against the original subject before use.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct OptimizationCertificate {
    version: u32,
    source: String,
    mode: String,
    selected: usize,
    rows: Vec<Row>,
}
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Row {
    index: usize,
    maximize: bool,
    value: String,
    model: Vec<Binding>,
    columns: Vec<String>,
    atoms: Vec<Atom>,
    origins: Vec<usize>,
    multipliers: Vec<Exact>,
}
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Binding {
    name: String,
    value: Scalar,
}
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(
    tag = "kind",
    content = "value",
    rename_all = "snake_case",
    deny_unknown_fields
)]
enum Scalar {
    Int(String),
    Bool(bool),
    Real(Exact),
}
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Exact {
    numerator: String,
    denominator: String,
}
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Atom {
    coefficients: Vec<(usize, Exact)>,
    constant: Exact,
    strict: bool,
}
fn unsupported(message: &str) -> SolverError {
    SolverError::Unsupported(message.into())
}
fn exact(value: Rational) -> Result<Exact, SolverError> {
    Ok(Exact {
        numerator: value
            .checked_numerator()
            .ok_or_else(|| unsupported("wide certificate numerator"))?
            .to_string(),
        denominator: value
            .checked_denominator()
            .ok_or_else(|| unsupported("wide certificate denominator"))?
            .to_string(),
    })
}
impl OptimizationCertificate {
    /// Serialize bounded evidence data. This does not replace byte replay.
    ///
    /// # Errors
    /// Declines oversized envelopes or serialization failures.
    pub fn to_json(&self) -> Result<String, SolverError> {
        let bytes = serde_json::to_string(self).map_err(|e| SolverError::Backend(e.to_string()))?;
        if bytes.len() > BYTE_CAP {
            return Err(unsupported("optimization certificate byte limit"));
        }
        Ok(bytes)
    }
    /// Parse strict bounded evidence data without accepting its claims.
    ///
    /// # Errors
    /// Rejects malformed, unknown-version or oversized evidence.
    pub fn from_json(bytes: &str) -> Result<Self, SolverError> {
        if bytes.len() > BYTE_CAP {
            return Err(unsupported("optimization certificate byte limit"));
        }
        let result: Self =
            serde_json::from_str(bytes).map_err(|e| SolverError::Parse(e.to_string()))?;
        if result.version != 1
            || result.source.len() > SOURCE_CAP
            || result.rows.is_empty()
            || result.rows.len() > 128
            || !matches!(result.mode.as_str(), "lex" | "box")
        {
            return Err(unsupported("optimization certificate envelope"));
        }
        Ok(result)
    }
}
impl OptimizationReport {
    /// Export the selected gold result and all required lexicographic witnesses.
    ///
    /// # Errors
    /// Declines missing refutations, unsupported model carriers or oversized data.
    pub fn certificate(&self, selected: usize) -> Result<OptimizationCertificate, SolverError> {
        if self.source.len() > SOURCE_CAP || !self.gold_eligible(selected)? {
            return Err(unsupported("no bounded checked optimization certificate"));
        }
        let start = if self.mode == OptimizationMode::Lexicographic {
            0
        } else {
            selected
        };
        if selected - start >= 128 {
            return Err(unsupported("optimization certificate row limit"));
        }
        let mut rows = Vec::new();
        for index in start..=selected {
            let row = &self.objectives[index];
            let Some(Value::Int(value)) = &row.value else {
                return Err(unsupported("certificate objective carrier"));
            };
            let proof = row
                .no_better
                .as_ref()
                .ok_or_else(|| unsupported("missing refutation"))?;
            let model = row
                .model
                .as_ref()
                .ok_or_else(|| unsupported("missing model"))?;
            let bindings = self
                .script
                .model_symbols
                .iter()
                .filter_map(|&symbol| model.get(symbol).map(|value| (symbol, value)))
                .map(|(symbol, value)| {
                    Ok(Binding {
                        name: self.script.arena.symbol(symbol).0.to_owned(),
                        value: match value {
                            Value::Int(v) => Scalar::Int(v.to_string()),
                            Value::Bool(v) => Scalar::Bool(v),
                            Value::Real(v) => Scalar::Real(exact(v)?),
                            _ => return Err(unsupported("certificate model carrier")),
                        },
                    })
                })
                .collect::<Result<Vec<_>, SolverError>>()?;
            let atoms = proof
                .atoms
                .iter()
                .map(|atom| {
                    Ok(Atom {
                        coefficients: atom
                            .coeffs
                            .iter()
                            .map(|&(i, v)| Ok((i, exact(v)?)))
                            .collect::<Result<Vec<_>, SolverError>>()?,
                        constant: exact(atom.constant)?,
                        strict: atom.strict,
                    })
                })
                .collect::<Result<Vec<_>, SolverError>>()?;
            rows.push(Row {
                index,
                maximize: row.maximize,
                value: value.to_string(),
                model: bindings,
                columns: row.no_better_names.clone(),
                atoms,
                origins: proof.origins.clone(),
                multipliers: proof
                    .multipliers
                    .iter()
                    .map(|&v| exact(v))
                    .collect::<Result<Vec<_>, SolverError>>()?,
            });
        }
        let certificate = OptimizationCertificate {
            version: 1,
            source: self.source.clone(),
            mode: self.mode.name().into(),
            selected,
            rows,
        };
        certificate.to_json()?;
        Ok(certificate)
    }
}
