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
    columns: Vec<(String, bool)>,
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

/// Counted replay outcome; acceptance requires actual model/refutation checks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertificateCheckReport {
    /// True only after every required row checks against the original subject.
    pub accepted: bool,
    /// True when replay exhausted its caller deadline without a verdict.
    pub resource_limited: bool,
    /// Number of model/refutation obligations attempted.
    pub examined: usize,
    /// Number of obligations successfully checked.
    pub discharged: usize,
    /// Concrete rejection reason, absent only on acceptance.
    pub reason: Option<String>,
}
fn rejected(examined: usize, discharged: usize, reason: &str) -> CertificateCheckReport {
    CertificateCheckReport {
        accepted: false,
        resource_limited: false,
        examined,
        discharged,
        reason: Some(reason.into()),
    }
}
fn limited(examined: usize, discharged: usize) -> CertificateCheckReport {
    CertificateCheckReport {
        accepted: false,
        resource_limited: true,
        examined,
        discharged,
        reason: Some("optimization certificate replay deadline exhausted".into()),
    }
}
fn expired(deadline: Option<std::time::Instant>) -> bool {
    deadline.is_some_and(|at| std::time::Instant::now() >= at)
}
fn integer(text: &str) -> Result<i128, SolverError> {
    let value = text
        .parse::<i128>()
        .map_err(|_| unsupported("certificate integer carrier"))?;
    if value.to_string() != text {
        return Err(unsupported("noncanonical certificate integer"));
    }
    Ok(value)
}
impl Exact {
    fn rational(&self) -> Result<Rational, SolverError> {
        let n = integer(&self.numerator)?;
        let d = integer(&self.denominator)?;
        if d <= 0 {
            return Err(unsupported("certificate denominator"));
        }
        let r =
            Rational::wide_new(n, d).ok_or_else(|| unsupported("certificate rational carrier"))?;
        if r.checked_numerator() != Some(n) || r.checked_denominator() != Some(d) {
            return Err(unsupported("noncanonical certificate rational"));
        }
        Ok(r)
    }
}
fn source_limits(source: &str, deadline: Option<std::time::Instant>) -> Result<(), SolverError> {
    if source.len() > SOURCE_CAP {
        return Err(unsupported("certificate source byte limit"));
    }
    let commands = axeyum_smtlib::read_all_within(source, deadline)
        .map_err(|e| SolverError::Parse(e.to_string()))?;
    let mut count = 0;
    let mut stack: Vec<_> = commands.iter().map(|node| (node, 0)).collect();
    while let Some((node, depth)) = stack.pop() {
        count += 1;
        if count > 4096 || depth > 32 {
            return Err(unsupported("certificate source syntax limit"));
        }
        if let Some(children) = node.list() {
            stack.extend(children.iter().map(|child| (child, depth + 1)));
        }
    }
    // Macro expansion and recursive definitions need their own preemptible
    // ingestion contract before they enter the portable checker.
    for command in &commands {
        let row = command
            .list()
            .ok_or_else(|| unsupported("certificate source command"))?;
        let name = row
            .first()
            .and_then(axeyum_smtlib::SExpr::atom)
            .unwrap_or("");
        if !matches!(
            name,
            "set-logic"
                | "set-option"
                | "declare-const"
                | "declare-fun"
                | "assert"
                | "maximize"
                | "minimize"
                | "check-sat"
                | "check-sat-assuming"
                | "get-model"
                | "get-value"
                | "push"
                | "pop"
                | "reset-assertions"
                | "exit"
        ) {
            return Err(unsupported(
                "certificate source command outside bounded transport",
            ));
        }
        if name == "set-option"
            && !matches!(
                row.get(1).and_then(axeyum_smtlib::SExpr::atom),
                Some(":opt.priority" | ":produce-models" | ":produce-proofs")
            )
        {
            return Err(unsupported("certificate source option"));
        }
        if matches!(name, "push" | "pop")
            && row
                .get(1)
                .and_then(axeyum_smtlib::SExpr::atom)
                .and_then(|s| s.parse::<usize>().ok())
                .is_none_or(|n| n > 128)
        {
            return Err(unsupported("certificate scope limit"));
        }
    }
    Ok(())
}
impl OptimizationCertificate {
    /// Check original-source models and refutations without optimization search.
    ///
    /// # Errors
    /// Returns malformed/unsupported evidence or bounded source parsing errors.
    // Keep the ordered model/refutation discharge loop together for auditing.
    #[allow(clippy::too_many_lines)]
    pub fn check(&self, subject: &str) -> Result<CertificateCheckReport, SolverError> {
        self.check_within(subject, None)
    }

    /// Replay with one deadline shared by intake, models and Farkas checks.
    /// Resource exhaustion never accepts or rejects the mathematical claim.
    ///
    /// # Errors
    /// As [`Self::check`], for malformed or unsupported evidence.
    #[allow(clippy::too_many_lines)]
    pub fn check_within(
        &self,
        subject: &str,
        deadline: Option<std::time::Instant>,
    ) -> Result<CertificateCheckReport, SolverError> {
        use crate::lra::{FarkasAtom, FarkasCertificate};
        use crate::{Model, check_model};
        use axeyum_ir::{Sort, eval};
        if expired(deadline) {
            return Ok(limited(0, 0));
        }
        if self.source != subject {
            return Ok(rejected(0, 0, "original source mismatch"));
        }
        self.to_json()?;
        let limits = source_limits(subject, deadline);
        if expired(deadline) {
            return Ok(limited(0, 0));
        }
        limits?;
        let mut script = match axeyum_smtlib::parse_script_within(subject, deadline) {
            Ok(script) => script,
            Err(
                axeyum_smtlib::SmtError::DeadlineExceeded(_)
                | axeyum_smtlib::SmtError::ResourceLimit(_),
            ) => return Ok(limited(0, 0)),
            Err(error) => return Err(SolverError::Parse(error.to_string())),
        };
        let commands = match axeyum_smtlib::read_all_within(subject, deadline) {
            Ok(commands) => commands,
            Err(
                axeyum_smtlib::SmtError::DeadlineExceeded(_)
                | axeyum_smtlib::SmtError::ResourceLimit(_),
            ) => return Ok(limited(0, 0)),
            Err(error) => return Err(SolverError::Parse(error.to_string())),
        };
        let objectives = super::active_objectives_from_commands(&commands, &script)?;
        let mut context = super::smtlib_single_optimization_query(&script)?.assertions;
        if self.selected >= objectives.len() || self.rows.is_empty() || self.rows.len() > 128 {
            return Ok(rejected(0, 0, "objective selection mismatch"));
        }
        let start = match self.mode.as_str() {
            "lex" => 0,
            "box" => self.selected,
            _ => return Ok(rejected(0, 0, "objective mode")),
        };
        if self.version != 1 || self.rows.len() != self.selected - start + 1 {
            return Ok(rejected(0, 0, "missing objective prefix"));
        }
        if super::active_priority_from_commands(&commands)
            .is_some_and(|priority| priority != self.mode)
        {
            return Ok(rejected(0, 0, "source objective mode mismatch"));
        }
        let mut examined = 0;
        let mut discharged = 0;
        for (offset, row) in self.rows.iter().enumerate() {
            if expired(deadline) {
                return Ok(limited(examined, discharged));
            }
            let index = start + offset;
            let (objective, maximize) = objectives[index];
            if row.index != index
                || row.maximize != maximize
                || script.arena.sort_of(objective) != Sort::Int
            {
                return Ok(rejected(
                    examined,
                    discharged,
                    "objective direction/order/sort",
                ));
            }
            if row.model.len() > 4096
                || row.atoms.len() > 4096
                || row.columns.len() > 4096
                || row.origins.len() != row.atoms.len()
                || row.multipliers.len() != row.atoms.len()
                || row
                    .atoms
                    .iter()
                    .map(|a| a.coefficients.len())
                    .sum::<usize>()
                    > 32768
            {
                return Err(unsupported("certificate obligation limits"));
            }
            let value = integer(&row.value)?;
            let bound = script.arena.int_const(value);
            let pin = script.arena.eq(objective, bound)?;
            let mut model = Model::new();
            let mut names = std::collections::BTreeSet::new();
            for binding in &row.model {
                let Some(symbol) = script.arena.find_symbol(&binding.name) else {
                    return Ok(rejected(examined, discharged, "unknown model symbol"));
                };
                if !names.insert(&binding.name) || !script.model_symbols.contains(&symbol) {
                    return Ok(rejected(
                        examined,
                        discharged,
                        "duplicate/non-source model symbol",
                    ));
                }
                let scalar = match &binding.value {
                    Scalar::Int(v) => Value::Int(integer(v)?),
                    Scalar::Bool(v) => Value::Bool(*v),
                    Scalar::Real(v) => Value::Real(v.rational()?),
                };
                let sort = script.arena.symbol(symbol).1;
                if !matches!(
                    (&scalar, sort),
                    (Value::Int(_), Sort::Int)
                        | (Value::Bool(_), Sort::Bool)
                        | (Value::Real(_), Sort::Real)
                ) {
                    return Ok(rejected(examined, discharged, "model sort mismatch"));
                }
                model.set(symbol, scalar);
            }
            let mut feasible = context.clone();
            feasible.push(pin);
            examined += 1;
            if !check_model(&script.arena, &feasible, &model)?
                || eval(&script.arena, objective, &model.to_assignment()).ok()
                    != Some(Value::Int(value))
            {
                return Ok(rejected(
                    examined,
                    discharged,
                    "original feasible model/value",
                ));
            }
            discharged += 1;
            let better = if maximize {
                script.arena.int_gt(objective, bound)?
            } else {
                script.arena.int_lt(objective, bound)?
            };
            let mut query = context.clone();
            query.push(better);
            let Some((relaxed, assertions)) =
                crate::int_real_relax::relax_int_assertions_to_real(&script.arena, &query)?
            else {
                return Ok(rejected(
                    examined,
                    discharged,
                    "source relaxation unavailable",
                ));
            };
            let columns = row
                .columns
                .iter()
                .map(|(name, internal)| {
                    let symbol = if *internal {
                        relaxed.find_internal_symbol(name)
                    } else {
                        relaxed.find_symbol(name)
                    };
                    symbol.ok_or_else(|| unsupported("unknown certificate column"))
                })
                .collect::<Result<Vec<_>, SolverError>>()?;
            let atoms = row
                .atoms
                .iter()
                .map(|atom| {
                    Ok(FarkasAtom {
                        coeffs: atom
                            .coefficients
                            .iter()
                            .map(|(i, c)| Ok((*i, c.rational()?)))
                            .collect::<Result<Vec<_>, SolverError>>()?,
                        constant: atom.constant.rational()?,
                        strict: atom.strict,
                    })
                })
                .collect::<Result<Vec<_>, SolverError>>()?;
            let certificate = FarkasCertificate {
                atoms,
                vars: columns,
                origins: row.origins.clone(),
                multipliers: row
                    .multipliers
                    .iter()
                    .map(Exact::rational)
                    .collect::<Result<Vec<_>, SolverError>>()?,
            };
            examined += 1;
            let checked = certificate.verify_against_within(&relaxed, &assertions, deadline)?;
            if expired(deadline) {
                return Ok(limited(examined, discharged));
            }
            if !checked {
                return Ok(rejected(
                    examined,
                    discharged,
                    "original strict-better refutation",
                ));
            }
            discharged += 1;
            if self.mode == "lex" {
                context.push(pin);
            }
        }
        if expired(deadline) {
            return Ok(limited(examined, discharged));
        }
        Ok(CertificateCheckReport {
            accepted: true,
            resource_limited: false,
            examined,
            discharged,
            reason: None,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const SOURCE: &str = "(declare-const x Int)(declare-const y Int)(assert (and (>= x 0) (<= x 10) (>= y 0) (<= y 3) (<= (+ x y) 10)))(maximize x)(maximize y)(check-sat)";
    fn certificate(mode: OptimizationMode, selected: usize) -> OptimizationCertificate {
        super::super::optimize_with_models(SOURCE, mode, &crate::SolverConfig::new())
            .unwrap()
            .certificate(selected)
            .unwrap()
    }
    #[test]
    fn serialized_modes_replay_actual_nonzero_obligations() {
        for (mode, count) in [
            (OptimizationMode::Box, 2),
            (OptimizationMode::Lexicographic, 4),
        ] {
            let cert = certificate(mode, 1);
            let bytes = cert.to_json().unwrap();
            let report = OptimizationCertificate::from_json(&bytes)
                .unwrap()
                .check(SOURCE)
                .unwrap();
            assert!(report.accepted);
            assert_eq!(report.examined, count);
            assert_eq!(report.discharged, count);
            assert_eq!(report.reason, None);
        }
    }
    #[test]
    fn original_subject_and_retargeted_constraints_are_checked() {
        let mut cert = certificate(OptimizationMode::Box, 0);
        assert!(!cert.check(&format!("{SOURCE} ")).unwrap().accepted);
        let changed = SOURCE.replace("(<= x 10)", "(<= x 11)");
        cert.source = changed.clone();
        assert!(!cert.check(&changed).unwrap().accepted);
    }
    #[test]
    fn model_value_and_direction_corruptions_fail() {
        let original = certificate(OptimizationMode::Box, 0);
        let mut cert = original.clone();
        cert.rows[0].value = "9".into();
        assert!(!cert.check(SOURCE).unwrap().accepted);
        let mut cert = original.clone();
        cert.rows[0].model[0].value = Scalar::Int("9".into());
        assert!(!cert.check(SOURCE).unwrap().accepted);
        let mut cert = original;
        cert.rows[0].maximize = false;
        assert!(!cert.check(SOURCE).unwrap().accepted);
    }
    #[test]
    fn prefix_and_refutation_corruptions_fail() {
        let original = certificate(OptimizationMode::Lexicographic, 1);
        let mut cert = original.clone();
        cert.rows.remove(0);
        assert!(!cert.check(SOURCE).unwrap().accepted);
        let mut cert = original.clone();
        cert.rows[0].origins[0] = 1000;
        assert!(!cert.check(SOURCE).unwrap().accepted);
        let mut cert = original;
        for multiplier in &mut cert.rows[0].multipliers {
            multiplier.numerator = "0".into();
            multiplier.denominator = "1".into();
        }
        assert!(!cert.check(SOURCE).unwrap().accepted);
    }
    #[test]
    fn column_namespace_is_part_of_source_binding() {
        let mut cert = certificate(OptimizationMode::Box, 0);
        assert!(cert.rows[0].columns.iter().any(|(_, internal)| *internal));
        for (_, internal) in &mut cert.rows[0].columns {
            *internal = false;
        }
        assert!(cert.check(SOURCE).is_err());
    }
    #[test]
    fn explicit_priority_replays_and_cannot_be_retargeted() {
        let source = format!("(set-option :opt.priority lex){SOURCE}");
        let mut cert = super::super::optimize_with_models(
            &source,
            OptimizationMode::Lexicographic,
            &crate::SolverConfig::new(),
        )
        .unwrap()
        .certificate(1)
        .unwrap();
        let report = cert.check(&source).unwrap();
        assert!(report.accepted);
        assert_eq!(report.discharged, 4);
        let changed = source.replace(":opt.priority lex", ":opt.priority box");
        cert.source = changed.clone();
        assert!(!cert.check(&changed).unwrap().accepted);
    }
    #[test]
    fn strict_envelope_rejects_unknown_duplicate_and_oversized_data() {
        let bytes = certificate(OptimizationMode::Box, 0).to_json().unwrap();
        let duplicate = bytes.replacen("\"version\":1", "\"version\":1,\"version\":1", 1);
        assert!(OptimizationCertificate::from_json(&duplicate).is_err());
        let unknown = bytes.replacen('{', "{\"accepted\":true,", 1);
        assert!(OptimizationCertificate::from_json(&unknown).is_err());
        assert!(OptimizationCertificate::from_json(&" ".repeat(BYTE_CAP + 1)).is_err());
    }
}
