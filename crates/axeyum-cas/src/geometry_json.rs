//! A deterministic, dependency-free codec for geometry cofactor certificates.
//!
//! The serialised form is what makes `artifacts/geometry-certificates/*.json`
//! evidence rather than decoration: the checker reads the file and re-derives the
//! identity without the producer ever running. Two properties are load-bearing.
//!
//! - **No decimals anywhere.** Every rational is an integer pair
//!   `[numerator, denominator]`, and the reader *refuses* a number that is not an
//!   integer literal. A binary floating-point round trip through a certificate
//!   would be a silent way to change a proof.
//! - **Byte-stable output.** Polynomials serialise in [`MvPoly`]'s canonical term
//!   order, so regenerating an unchanged certificate produces an identical file
//!   and a diff means something changed.
//!
//! This reader is written independently of [`crate::telescoping_json`] — it is a
//! second implementation of the same conventions, not a shared one.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use axeyum_ir::Rational;

use crate::geometry_certify::{
    CertifiedConclusion, Condition, Constraint, DegenerateWitness, GenericWitness,
    GeometryCertificate, Saturation,
};
use crate::mvpoly::{Monomial, MvPoly};

/// The format tag every certificate file carries.
pub const FORMAT: &str = "axeyum-geometry-certificate";

/// The format version.
pub const VERSION: i128 = 1;

// ---------------------------------------------------------------------------
// Writing
// ---------------------------------------------------------------------------

/// Render a certificate as canonical JSON.
#[must_use]
pub fn to_json(certificate: &GeometryCertificate) -> String {
    let mut out = String::new();
    out.push_str("{\n");
    let _ = writeln!(out, "  \"format\": {},", quote(FORMAT));
    let _ = writeln!(out, "  \"version\": {VERSION},");
    let _ = writeln!(out, "  \"id\": {},", quote(&certificate.id));
    let _ = writeln!(out, "  \"title\": {},", quote(&certificate.title));
    let _ = writeln!(out, "  \"statement\": {},", quote(&certificate.statement));
    out.push_str("  \"coordinate_gloss\": [");
    for (index, (name, gloss)) in certificate.coordinate_gloss.iter().enumerate() {
        if index > 0 {
            out.push_str(", ");
        }
        let _ = write!(out, "[{}, {}]", quote(name), quote(gloss));
    }
    out.push_str("],\n");
    out.push_str("  \"coordinates\": [");
    for (index, name) in certificate.coordinates.iter().enumerate() {
        if index > 0 {
            out.push_str(", ");
        }
        out.push_str(&quote(name));
    }
    out.push_str("],\n");

    out.push_str("  \"hypotheses\": [\n");
    for (index, hypothesis) in certificate.hypotheses.iter().enumerate() {
        let _ = writeln!(
            out,
            "    {{\"id\": {}, \"description\": {}, \"poly\": {}}}{}",
            quote(&hypothesis.id),
            quote(&hypothesis.description),
            write_poly(&hypothesis.poly),
            comma(index, certificate.hypotheses.len())
        );
    }
    out.push_str("  ],\n");

    out.push_str("  \"saturations\": [\n");
    for (index, saturation) in certificate.saturations.iter().enumerate() {
        let _ = writeln!(
            out,
            "    {{\"condition_id\": {}, \"description\": {}, \"var\": {}, \"condition\": {}}}{}",
            quote(&saturation.condition_id),
            quote(&saturation.description),
            quote(&saturation.var),
            write_poly(&saturation.condition),
            comma(index, certificate.saturations.len())
        );
    }
    out.push_str("  ],\n");

    out.push_str("  \"generators\": [\n");
    for (index, generator) in certificate.generators.iter().enumerate() {
        let _ = writeln!(
            out,
            "    {}{}",
            write_poly(generator),
            comma(index, certificate.generators.len())
        );
    }
    out.push_str("  ],\n");

    out.push_str("  \"conclusions\": [\n");
    for (index, conclusion) in certificate.conclusions.iter().enumerate() {
        let _ = write!(
            out,
            "    {{\"id\": {}, \"description\": {}, \"poly\": {}, \"cofactors\": [",
            quote(&conclusion.id),
            quote(&conclusion.description),
            write_poly(&conclusion.poly)
        );
        for (slot, cofactor) in conclusion.cofactors.iter().enumerate() {
            if slot > 0 {
                out.push_str(", ");
            }
            out.push_str(&write_poly(cofactor));
        }
        let _ = writeln!(out, "]}}{}", comma(index, certificate.conclusions.len()));
    }
    out.push_str("  ],\n");

    out.push_str("  \"degenerate_witnesses\": [\n");
    for (index, witness) in certificate.degenerate_witnesses.iter().enumerate() {
        let _ = writeln!(
            out,
            "    {{\"condition_id\": {}, \"description\": {}, \"assignment\": {}}}{}",
            quote(&witness.condition_id),
            quote(&witness.description),
            write_assignment(&witness.assignment),
            comma(index, certificate.degenerate_witnesses.len())
        );
    }
    out.push_str("  ],\n");

    out.push_str("  \"generic_witnesses\": [\n");
    for (index, witness) in certificate.generic_witnesses.iter().enumerate() {
        let _ = writeln!(
            out,
            "    {{\"description\": {}, \"assignment\": {}}}{}",
            quote(&witness.description),
            write_assignment(&witness.assignment),
            comma(index, certificate.generic_witnesses.len())
        );
    }
    out.push_str("  ]\n}\n");
    out
}

fn comma(index: usize, total: usize) -> &'static str {
    if index + 1 == total { "" } else { "," }
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

fn write_poly(poly: &MvPoly) -> String {
    let mut out = String::from("{\"terms\": [");
    for (index, (monomial, coefficient)) in poly.terms().enumerate() {
        if index > 0 {
            out.push_str(", ");
        }
        out.push_str("{\"monomial\": [");
        for (slot, (var, exponent)) in monomial.powers().enumerate() {
            if slot > 0 {
                out.push_str(", ");
            }
            let _ = write!(out, "[{}, {exponent}]", quote(var));
        }
        let _ = write!(
            out,
            "], \"coefficient\": {}}}",
            write_rational(*coefficient)
        );
    }
    out.push_str("]}");
    out
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

/// Parse a certificate file. Every failure is a message, never a panic.
///
/// # Errors
///
/// Returns a message describing the first structural problem: a missing or
/// mistyped field, a foreign format tag or version, a truncated document, a
/// decimal where an exact integer belongs, a zero denominator, a non-positive
/// stored exponent, or a coefficient outside the exact rational range.
#[allow(clippy::too_many_lines)]
pub fn from_json(text: &str) -> Result<GeometryCertificate, String> {
    let root = parse(text)?;
    if root.field("format")?.text()? != FORMAT {
        return Err(format!("not a {FORMAT} document"));
    }
    if root.field("version")?.integer()? != VERSION {
        return Err("unsupported certificate version".into());
    }
    let coordinate_gloss = root
        .field("coordinate_gloss")?
        .array()?
        .iter()
        .map(|pair| {
            let items = pair.array()?;
            if items.len() != 2 {
                return Err("a coordinate gloss is a [name, gloss] pair".into());
            }
            Ok((items[0].text()?.to_string(), items[1].text()?.to_string()))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let coordinates = root
        .field("coordinates")?
        .array()?
        .iter()
        .map(|item| Ok(item.text()?.to_string()))
        .collect::<Result<Vec<String>, String>>()?;
    let hypotheses = root
        .field("hypotheses")?
        .array()?
        .iter()
        .map(read_constraint)
        .collect::<Result<Vec<_>, String>>()?;
    let saturations = root
        .field("saturations")?
        .array()?
        .iter()
        .map(|item| {
            Ok(Saturation {
                condition_id: item.field("condition_id")?.text()?.to_string(),
                description: item.field("description")?.text()?.to_string(),
                var: item.field("var")?.text()?.to_string(),
                condition: read_poly(item.field("condition")?)?,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let generators = root
        .field("generators")?
        .array()?
        .iter()
        .map(read_poly)
        .collect::<Result<Vec<_>, String>>()?;
    let conclusions = root
        .field("conclusions")?
        .array()?
        .iter()
        .map(|item| {
            Ok(CertifiedConclusion {
                id: item.field("id")?.text()?.to_string(),
                description: item.field("description")?.text()?.to_string(),
                poly: read_poly(item.field("poly")?)?,
                cofactors: item
                    .field("cofactors")?
                    .array()?
                    .iter()
                    .map(read_poly)
                    .collect::<Result<Vec<_>, String>>()?,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let degenerate_witnesses = root
        .field("degenerate_witnesses")?
        .array()?
        .iter()
        .map(|item| {
            Ok(DegenerateWitness {
                condition_id: item.field("condition_id")?.text()?.to_string(),
                description: item.field("description")?.text()?.to_string(),
                assignment: read_assignment(item.field("assignment")?)?,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let generic_witnesses = root
        .field("generic_witnesses")?
        .array()?
        .iter()
        .map(|item| {
            Ok(GenericWitness {
                description: item.field("description")?.text()?.to_string(),
                assignment: read_assignment(item.field("assignment")?)?,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;

    Ok(GeometryCertificate {
        id: root.field("id")?.text()?.to_string(),
        title: root.field("title")?.text()?.to_string(),
        statement: root.field("statement")?.text()?.to_string(),
        coordinate_gloss,
        coordinates,
        hypotheses,
        saturations,
        generators,
        conclusions,
        degenerate_witnesses,
        generic_witnesses,
    })
}

/// The `Condition` form, for callers that want to read a non-degeneracy
/// condition back out of a saturation row.
#[must_use]
pub fn condition_of(saturation: &Saturation) -> Condition {
    Condition {
        id: saturation.condition_id.clone(),
        description: saturation.description.clone(),
        poly: saturation.condition.clone(),
    }
}

fn read_constraint(value: &Json) -> Result<Constraint, String> {
    Ok(Constraint {
        id: value.field("id")?.text()?.to_string(),
        description: value.field("description")?.text()?.to_string(),
        poly: read_poly(value.field("poly")?)?,
    })
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

fn read_poly(value: &Json) -> Result<MvPoly, String> {
    let mut terms = Vec::new();
    for term in value.field("terms")?.array()? {
        let mut factors: Vec<(String, u32)> = Vec::new();
        for power in term.field("monomial")?.array()? {
            let pair = power.array()?;
            if pair.len() != 2 {
                return Err("a monomial factor is a [variable, exponent] pair".into());
            }
            let name = pair[0].text()?.to_string();
            let exponent = pair[1].integer()?;
            if exponent <= 0 {
                return Err("a stored monomial exponent must be positive".into());
            }
            let exponent = u32::try_from(exponent).map_err(|_| "exponent out of range")?;
            factors.push((name, exponent));
        }
        let borrowed: Vec<(&str, u32)> = factors
            .iter()
            .map(|(name, exponent)| (name.as_str(), *exponent))
            .collect();
        terms.push((
            Monomial::from_powers(&borrowed),
            read_rational(term.field("coefficient")?)?,
        ));
    }
    MvPoly::from_terms(terms).ok_or_else(|| "polynomial coefficients overflowed".into())
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

// --- the parser ------------------------------------------------------------

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

/// Integers only. A decimal point or an exponent is a hard error: this format
/// carries exact rationals as integer pairs, and a float in a proof artifact is
/// a way to change a proof without changing what it looks like.
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
