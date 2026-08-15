//! The certificate artifact format: exact rationals as integer pairs, no floats.
//!
//! A decimal literal anywhere in the document is a hard parse error, for the
//! reason the geometry format gives and this domain makes sharper: a numerical
//! artifact is exactly where a float would look natural, and a float in a proof
//! artifact is a way to change a proof without changing what it looks like. The
//! whole claim of this module is that its arithmetic is exact; admitting `0.5`
//! would quietly retract it.
//!
//! The reader and writer here are deliberately private to this module rather
//! than shared with `geometry_json`. That module's helpers are private, and
//! reaching into another lane's file to widen them is the shared-file failure
//! mode `CLAUDE.md` documents. The duplication is about a hundred lines of
//! tokenizer and is the cheaper of the two costs.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use axeyum_ir::Rational;

use crate::mvpoly::{Monomial, MvPoly};
use crate::sos::{
    BarrierCertificate, BarrierProblem, LyapunovCertificate, LyapunovProblem, PsdNotSosCertificate,
    PsdNotSosProblem, SosArtifact, SosSum, VectorField,
};

const FORMAT: &str = "axeyum-sos-certificate";
const VERSION: i128 = 1;

// ---------------------------------------------------------------------------
// Writing
// ---------------------------------------------------------------------------

/// Render an artifact as a certificate document.
#[must_use]
#[allow(clippy::too_many_lines)]
pub fn to_json(artifact: &SosArtifact) -> String {
    let mut out = String::new();
    out.push_str("{\n");
    let _ = writeln!(out, "  \"format\": {},", quote(FORMAT));
    let _ = writeln!(out, "  \"version\": {VERSION},");
    let _ = writeln!(out, "  \"kind\": {},", quote(artifact.kind()));
    match artifact {
        SosArtifact::Lyapunov(problem, certificate) => {
            let _ = writeln!(out, "  \"id\": {},", quote(&problem.id));
            let _ = writeln!(out, "  \"description\": {},", quote(&problem.description));
            write_system(&mut out, &problem.system);
            let _ = writeln!(out, "  \"v\": {},", write_poly(&problem.v));
            let _ = writeln!(out, "  \"lower\": {},", write_rational(problem.lower));
            let _ = writeln!(out, "  \"upper\": {},", write_rational(problem.upper));
            let _ = writeln!(out, "  \"decay\": {},", write_rational(problem.decay));
            let _ = writeln!(
                out,
                "  \"naive_failure\": {},",
                write_assignment(&problem.naive_failure)
            );
            out.push_str("  \"certificate\": {\n");
            let _ = writeln!(
                out,
                "    \"lower_gap\": {},",
                write_sos(&certificate.lower_gap)
            );
            let _ = writeln!(
                out,
                "    \"upper_gap\": {},",
                write_sos(&certificate.upper_gap)
            );
            let _ = writeln!(
                out,
                "    \"decrease\": {}",
                write_sos(&certificate.decrease)
            );
            out.push_str("  }\n");
        }
        SosArtifact::Barrier(problem, certificate) => {
            let _ = writeln!(out, "  \"id\": {},", quote(&problem.id));
            let _ = writeln!(out, "  \"description\": {},", quote(&problem.description));
            write_system(&mut out, &problem.system);
            let _ = writeln!(out, "  \"initial\": {},", write_polys(&problem.initial));
            let _ = writeln!(
                out,
                "  \"unsafe\": {},",
                write_polys(&problem.unsafe_region)
            );
            let _ = writeln!(out, "  \"barrier\": {},", write_poly(&problem.barrier));
            let _ = writeln!(
                out,
                "  \"initial_witness\": {},",
                write_assignment(&problem.initial_witness)
            );
            let _ = writeln!(
                out,
                "  \"unsafe_witness\": {},",
                write_assignment(&problem.unsafe_witness)
            );
            out.push_str("  \"certificate\": {\n");
            let _ = writeln!(
                out,
                "    \"initial_multipliers\": {},",
                write_sos_list(&certificate.initial_multipliers)
            );
            let _ = writeln!(
                out,
                "    \"initial_margin\": {},",
                write_rational(certificate.initial_margin)
            );
            let _ = writeln!(
                out,
                "    \"initial_gap\": {},",
                write_sos(&certificate.initial_gap)
            );
            let _ = writeln!(
                out,
                "    \"unsafe_multipliers\": {},",
                write_sos_list(&certificate.unsafe_multipliers)
            );
            let _ = writeln!(
                out,
                "    \"unsafe_margin\": {},",
                write_rational(certificate.unsafe_margin)
            );
            let _ = writeln!(
                out,
                "    \"unsafe_gap\": {},",
                write_sos(&certificate.unsafe_gap)
            );
            let _ = writeln!(
                out,
                "    \"decrease\": {}",
                write_sos(&certificate.decrease)
            );
            out.push_str("  }\n");
        }
        SosArtifact::PsdNotSos(problem, certificate) => {
            let _ = writeln!(out, "  \"id\": {},", quote(&problem.id));
            let _ = writeln!(out, "  \"description\": {},", quote(&problem.description));
            let _ = writeln!(
                out,
                "  \"variables\": [{}],",
                problem
                    .variables
                    .iter()
                    .map(|name| quote(name))
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            let _ = writeln!(out, "  \"form\": {},", write_poly(&problem.form));
            let _ = writeln!(
                out,
                "  \"multiplier\": {},",
                write_poly(&problem.multiplier)
            );
            let _ = writeln!(out, "  \"half_degree\": {},", problem.half_degree);
            out.push_str("  \"certificate\": {\n");
            let _ = writeln!(
                out,
                "    \"multiplied\": {},",
                write_sos(&certificate.multiplied)
            );
            let _ = writeln!(out, "    \"dual\": {}", write_dual(&certificate.dual));
            out.push_str("  }\n");
        }
    }
    out.push_str("}\n");
    out
}

fn write_system(out: &mut String, system: &VectorField) {
    let _ = writeln!(
        out,
        "  \"variables\": [{}],",
        system
            .variables
            .iter()
            .map(|name| quote(name))
            .collect::<Vec<_>>()
            .join(", ")
    );
    let _ = writeln!(out, "  \"field\": {},", write_polys(&system.field));
}

fn quote(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + 2);
    out.push('"');
    for character in text.chars() {
        match character {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            other => out.push(other),
        }
    }
    out.push('"');
    out
}

fn write_rational(value: Rational) -> String {
    format!("[{}, {}]", value.numerator(), value.denominator())
}

fn write_monomial(monomial: &Monomial) -> String {
    let mut out = String::from("[");
    for (index, (name, exponent)) in monomial.powers().enumerate() {
        if index > 0 {
            out.push_str(", ");
        }
        let _ = write!(out, "[{}, {exponent}]", quote(name));
    }
    out.push(']');
    out
}

fn write_poly(poly: &MvPoly) -> String {
    let mut out = String::from("{\"terms\": [");
    for (index, (monomial, coefficient)) in poly.terms().enumerate() {
        if index > 0 {
            out.push_str(", ");
        }
        let _ = write!(
            out,
            "{{\"monomial\": {}, \"coefficient\": {}}}",
            write_monomial(monomial),
            write_rational(*coefficient)
        );
    }
    out.push_str("]}");
    out
}

fn write_polys(polys: &[MvPoly]) -> String {
    format!(
        "[{}]",
        polys.iter().map(write_poly).collect::<Vec<_>>().join(", ")
    )
}

fn write_sos(sum: &SosSum) -> String {
    let mut out = String::from("{\"squares\": [");
    for (index, (weight, square)) in sum.squares().iter().enumerate() {
        if index > 0 {
            out.push_str(", ");
        }
        let _ = write!(
            out,
            "{{\"weight\": {}, \"square\": {}}}",
            write_rational(*weight),
            write_poly(square)
        );
    }
    out.push_str("]}");
    out
}

fn write_sos_list(sums: &[SosSum]) -> String {
    format!(
        "[{}]",
        sums.iter().map(write_sos).collect::<Vec<_>>().join(", ")
    )
}

fn write_assignment(assignment: &BTreeMap<String, Rational>) -> String {
    let mut out = String::from("[");
    for (index, (name, value)) in assignment.iter().enumerate() {
        if index > 0 {
            out.push_str(", ");
        }
        let _ = write!(out, "[{}, {}]", quote(name), write_rational(*value));
    }
    out.push(']');
    out
}

fn write_dual(dual: &BTreeMap<Monomial, Rational>) -> String {
    let mut out = String::from("[");
    for (index, (monomial, value)) in dual.iter().enumerate() {
        if index > 0 {
            out.push_str(", ");
        }
        let _ = write!(
            out,
            "[{}, {}]",
            write_monomial(monomial),
            write_rational(*value)
        );
    }
    out.push(']');
    out
}

// ---------------------------------------------------------------------------
// Reading
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
enum Json {
    Text(String),
    Integer(i128),
    Array(Vec<Json>),
    Object(Vec<(String, Json)>),
}

impl Json {
    fn field(&self, name: &str) -> Result<&Json, String> {
        match self {
            Json::Object(fields) => fields
                .iter()
                .find(|(key, _)| key == name)
                .map(|(_, value)| value)
                .ok_or_else(|| format!("missing field `{name}`")),
            _ => Err(format!("expected an object to read `{name}` from")),
        }
    }

    fn array(&self) -> Result<&[Json], String> {
        match self {
            Json::Array(items) => Ok(items),
            _ => Err("expected an array".into()),
        }
    }

    fn text(&self) -> Result<&str, String> {
        match self {
            Json::Text(value) => Ok(value),
            _ => Err("expected a string".into()),
        }
    }

    fn integer(&self) -> Result<i128, String> {
        match self {
            Json::Integer(value) => Ok(*value),
            _ => Err("expected an integer".into()),
        }
    }
}

/// Parse a certificate document.
///
/// # Errors
///
/// Returns a message describing the first structural problem: a foreign format
/// tag or version, an unknown kind, a missing or mistyped field, a decimal where
/// an exact rational belongs, a zero denominator, a negative sum-of-squares
/// weight, or a coefficient outside the exact rational range.
pub fn from_json(text: &str) -> Result<SosArtifact, String> {
    let root = parse(text)?;
    if root.field("format")?.text()? != FORMAT {
        return Err(format!("not a {FORMAT} document"));
    }
    if root.field("version")?.integer()? != VERSION {
        return Err("unsupported certificate version".into());
    }
    let id = root.field("id")?.text()?.to_string();
    let description = root.field("description")?.text()?.to_string();
    let variables = read_names(root.field("variables")?)?;
    let certificate = root.field("certificate")?;
    match root.field("kind")?.text()? {
        "lyapunov" => {
            let problem = LyapunovProblem {
                id,
                description,
                system: VectorField {
                    variables,
                    field: read_polys(root.field("field")?)?,
                },
                v: read_poly(root.field("v")?)?,
                lower: read_rational(root.field("lower")?)?,
                upper: read_rational(root.field("upper")?)?,
                decay: read_rational(root.field("decay")?)?,
                naive_failure: read_assignment(root.field("naive_failure")?)?,
            };
            let certificate = LyapunovCertificate {
                lower_gap: read_sos(certificate.field("lower_gap")?)?,
                upper_gap: read_sos(certificate.field("upper_gap")?)?,
                decrease: read_sos(certificate.field("decrease")?)?,
            };
            Ok(SosArtifact::Lyapunov(problem, certificate))
        }
        "barrier" => {
            let problem = BarrierProblem {
                id,
                description,
                system: VectorField {
                    variables,
                    field: read_polys(root.field("field")?)?,
                },
                initial: read_polys(root.field("initial")?)?,
                unsafe_region: read_polys(root.field("unsafe")?)?,
                barrier: read_poly(root.field("barrier")?)?,
                initial_witness: read_assignment(root.field("initial_witness")?)?,
                unsafe_witness: read_assignment(root.field("unsafe_witness")?)?,
            };
            let certificate = BarrierCertificate {
                initial_multipliers: read_sos_list(certificate.field("initial_multipliers")?)?,
                initial_margin: read_rational(certificate.field("initial_margin")?)?,
                initial_gap: read_sos(certificate.field("initial_gap")?)?,
                unsafe_multipliers: read_sos_list(certificate.field("unsafe_multipliers")?)?,
                unsafe_margin: read_rational(certificate.field("unsafe_margin")?)?,
                unsafe_gap: read_sos(certificate.field("unsafe_gap")?)?,
                decrease: read_sos(certificate.field("decrease")?)?,
            };
            Ok(SosArtifact::Barrier(problem, certificate))
        }
        "psd-not-sos" => {
            let half_degree = root.field("half_degree")?.integer()?;
            let half_degree = u32::try_from(half_degree)
                .map_err(|_| "half_degree is out of range".to_string())?;
            let problem = PsdNotSosProblem {
                id,
                description,
                variables,
                form: read_poly(root.field("form")?)?,
                multiplier: read_poly(root.field("multiplier")?)?,
                half_degree,
            };
            let certificate = PsdNotSosCertificate {
                multiplied: read_sos(certificate.field("multiplied")?)?,
                dual: read_dual(certificate.field("dual")?)?,
            };
            Ok(SosArtifact::PsdNotSos(problem, certificate))
        }
        other => Err(format!("unknown certificate kind `{other}`")),
    }
}

fn read_names(value: &Json) -> Result<Vec<String>, String> {
    value
        .array()?
        .iter()
        .map(|item| Ok(item.text()?.to_string()))
        .collect()
}

fn read_rational(value: &Json) -> Result<Rational, String> {
    let pair = value.array()?;
    if pair.len() != 2 {
        return Err("a rational is a [numerator, denominator] pair".into());
    }
    let numerator = pair[0].integer()?;
    let denominator = pair[1].integer()?;
    if denominator == 0 {
        return Err("a rational may not have a zero denominator".into());
    }
    Rational::checked_new(numerator, denominator).ok_or_else(|| "rational out of range".into())
}

fn read_monomial(value: &Json) -> Result<Monomial, String> {
    let mut factors: Vec<(String, u32)> = Vec::new();
    for power in value.array()? {
        let pair = power.array()?;
        if pair.len() != 2 {
            return Err("a monomial factor is a [variable, exponent] pair".into());
        }
        let name = pair[0].text()?.to_string();
        let exponent = pair[1].integer()?;
        if exponent <= 0 {
            return Err("a stored monomial exponent must be positive".into());
        }
        factors.push((
            name,
            u32::try_from(exponent).map_err(|_| "exponent out of range".to_string())?,
        ));
    }
    let borrowed: Vec<(&str, u32)> = factors
        .iter()
        .map(|(name, exponent)| (name.as_str(), *exponent))
        .collect();
    Ok(Monomial::from_powers(&borrowed))
}

fn read_poly(value: &Json) -> Result<MvPoly, String> {
    let mut terms = Vec::new();
    for term in value.field("terms")?.array()? {
        terms.push((
            read_monomial(term.field("monomial")?)?,
            read_rational(term.field("coefficient")?)?,
        ));
    }
    MvPoly::from_terms(terms).ok_or_else(|| "polynomial coefficients overflowed".into())
}

fn read_polys(value: &Json) -> Result<Vec<MvPoly>, String> {
    value.array()?.iter().map(read_poly).collect()
}

fn read_sos(value: &Json) -> Result<SosSum, String> {
    let mut squares = Vec::new();
    for item in value.field("squares")?.array()? {
        squares.push((
            read_rational(item.field("weight")?)?,
            read_poly(item.field("square")?)?,
        ));
    }
    SosSum::new(squares)
}

fn read_sos_list(value: &Json) -> Result<Vec<SosSum>, String> {
    value.array()?.iter().map(read_sos).collect()
}

fn read_assignment(value: &Json) -> Result<BTreeMap<String, Rational>, String> {
    let mut assignment = BTreeMap::new();
    for pair in value.array()? {
        let items = pair.array()?;
        if items.len() != 2 {
            return Err("an assignment entry is a [variable, value] pair".into());
        }
        let name = items[0].text()?.to_string();
        if assignment.insert(name, read_rational(&items[1])?).is_some() {
            return Err("an assignment binds a variable twice".into());
        }
    }
    Ok(assignment)
}

fn read_dual(value: &Json) -> Result<BTreeMap<Monomial, Rational>, String> {
    let mut dual = BTreeMap::new();
    for pair in value.array()? {
        let items = pair.array()?;
        if items.len() != 2 {
            return Err("a dual entry is a [monomial, value] pair".into());
        }
        if dual
            .insert(read_monomial(&items[0])?, read_rational(&items[1])?)
            .is_some()
        {
            return Err("the dual functional names a monomial twice".into());
        }
    }
    Ok(dual)
}

// --- the tokenizer ----------------------------------------------------------

fn parse(text: &str) -> Result<Json, String> {
    let characters: Vec<char> = text.chars().collect();
    let mut cursor = 0usize;
    let value = parse_value(&characters, &mut cursor)?;
    skip_space(&characters, &mut cursor);
    if cursor != characters.len() {
        return Err("trailing content after the document".into());
    }
    Ok(value)
}

fn skip_space(characters: &[char], cursor: &mut usize) {
    while *cursor < characters.len() && characters[*cursor].is_ascii_whitespace() {
        *cursor += 1;
    }
}

fn expect(characters: &[char], cursor: &mut usize, wanted: char) -> Result<(), String> {
    skip_space(characters, cursor);
    if *cursor < characters.len() && characters[*cursor] == wanted {
        *cursor += 1;
        Ok(())
    } else {
        Err(format!("expected `{wanted}`"))
    }
}

fn parse_value(characters: &[char], cursor: &mut usize) -> Result<Json, String> {
    skip_space(characters, cursor);
    match characters.get(*cursor) {
        Some('{') => parse_object(characters, cursor),
        Some('[') => parse_array(characters, cursor),
        Some('"') => Ok(Json::Text(parse_string(characters, cursor)?)),
        Some(character) if *character == '-' || character.is_ascii_digit() => {
            parse_integer(characters, cursor)
        }
        _ => Err("unexpected token".into()),
    }
}

fn parse_object(characters: &[char], cursor: &mut usize) -> Result<Json, String> {
    expect(characters, cursor, '{')?;
    let mut fields = Vec::new();
    skip_space(characters, cursor);
    if characters.get(*cursor) == Some(&'}') {
        *cursor += 1;
        return Ok(Json::Object(fields));
    }
    loop {
        skip_space(characters, cursor);
        let key = parse_string(characters, cursor)?;
        expect(characters, cursor, ':')?;
        let value = parse_value(characters, cursor)?;
        fields.push((key, value));
        skip_space(characters, cursor);
        match characters.get(*cursor) {
            Some(',') => *cursor += 1,
            Some('}') => {
                *cursor += 1;
                return Ok(Json::Object(fields));
            }
            _ => return Err("expected `,` or `}`".into()),
        }
    }
}

fn parse_array(characters: &[char], cursor: &mut usize) -> Result<Json, String> {
    expect(characters, cursor, '[')?;
    let mut items = Vec::new();
    skip_space(characters, cursor);
    if characters.get(*cursor) == Some(&']') {
        *cursor += 1;
        return Ok(Json::Array(items));
    }
    loop {
        items.push(parse_value(characters, cursor)?);
        skip_space(characters, cursor);
        match characters.get(*cursor) {
            Some(',') => *cursor += 1,
            Some(']') => {
                *cursor += 1;
                return Ok(Json::Array(items));
            }
            _ => return Err("expected `,` or `]`".into()),
        }
    }
}

fn parse_string(characters: &[char], cursor: &mut usize) -> Result<String, String> {
    expect(characters, cursor, '"')?;
    let mut out = String::new();
    while let Some(character) = characters.get(*cursor) {
        *cursor += 1;
        match character {
            '"' => return Ok(out),
            '\\' => {
                let escaped = characters.get(*cursor).ok_or("truncated escape")?;
                *cursor += 1;
                match escaped {
                    '"' => out.push('"'),
                    '\\' => out.push('\\'),
                    'n' => out.push('\n'),
                    't' => out.push('\t'),
                    'r' => out.push('\r'),
                    '/' => out.push('/'),
                    other => return Err(format!("unsupported escape `\\{other}`")),
                }
            }
            other => out.push(*other),
        }
    }
    Err("unterminated string".into())
}

/// Integers only. A decimal point or an exponent is a hard error.
fn parse_integer(characters: &[char], cursor: &mut usize) -> Result<Json, String> {
    let start = *cursor;
    if characters.get(*cursor) == Some(&'-') {
        *cursor += 1;
    }
    let digits = *cursor;
    while matches!(characters.get(*cursor), Some(character) if character.is_ascii_digit()) {
        *cursor += 1;
    }
    if *cursor == digits {
        return Err("expected a digit".into());
    }
    if matches!(characters.get(*cursor), Some('.' | 'e' | 'E')) {
        return Err("this format carries exact rationals; a decimal is refused".into());
    }
    let literal: String = characters[start..*cursor].iter().collect();
    literal
        .parse::<i128>()
        .map(Json::Integer)
        .map_err(|_| "integer out of range".into())
}

#[cfg(test)]
mod tests {
    use super::{from_json, to_json};
    use crate::sos::corpus;

    #[test]
    fn every_artifact_round_trips() {
        for artifact in corpus::all() {
            let text = to_json(&artifact);
            let parsed = from_json(&text).unwrap_or_else(|message| {
                panic!("{} did not parse back: {message}", artifact.id())
            });
            assert_eq!(parsed, artifact, "{} did not round trip", artifact.id());
        }
    }

    #[test]
    fn a_decimal_is_refused() {
        let text = to_json(&corpus::damped_rotation_lyapunov()).replace("[51, 1]", "[51.0, 1]");
        assert!(from_json(&text).is_err(), "a float must not parse");
    }

    #[test]
    fn a_negative_weight_is_refused_by_the_parser() {
        let text = to_json(&corpus::damped_rotation_lyapunov())
            .replace("\"weight\": [1, 2]", "\"weight\": [-1, 2]");
        let message = from_json(&text).expect_err("a negative weight must not parse");
        assert!(message.contains("negative weight"), "{message}");
    }

    #[test]
    fn a_foreign_format_tag_is_refused() {
        let text = to_json(&corpus::motzkin_psd_not_sos())
            .replace("axeyum-sos-certificate", "axeyum-geometry-certificate");
        assert!(from_json(&text).is_err());
    }
}
