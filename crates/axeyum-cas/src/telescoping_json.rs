//! A deterministic JSON codec for creative-telescoping certificates.
//!
//! A certificate that only ever exists as a Rust value is evidence for nothing:
//! the fact ledger ends up pointing at a *test that rebuilds it*, and the claim
//! rests on running the producer again. Serialising the certificate makes the
//! artifact the proof object — read the file, re-check it, done — and it is what
//! lets one checker command sweep a directory of hundreds.
//!
//! # What is in the file
//!
//! Everything [`crate::telescoping_check::check_certificate`] needs and nothing
//! it does not: the summand as a [`HyperTerm`] *specification* (not an expression
//! tree), which variable is summed and which is shifted, the recurrence
//! coefficients, `R = P/Q`, the sampling grid the claim was checked over, and —
//! optionally — a claimed closed form and the base index it starts from.
//!
//! Rationals are `[numerator, denominator]` integer pairs, never decimals, so a
//! round trip is exact and a diff is readable.
//!
//! # What the codec is and is not trusted for
//!
//! The parser is not a soundness boundary. A malformed file fails to parse; a
//! file that parses to a *different* certificate than it appears to state is
//! rejected by the checker unless it is genuinely valid — in which case it is a
//! valid certificate for whatever term it actually denotes. The one thing the
//! reader does carry is the same assumption the whole route carries, that the
//! `HyperTerm` written down denotes the intended summand
//! (`cas.hyperterm-specification-denotes-the-summand`). Serialising it at least
//! puts that specification in front of a reader instead of inside a test.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use axeyum_ir::Rational;

use crate::mvpoly::{Monomial, MvPoly};
use crate::telescoping::{Factor, HyperTerm, LinearForm, TelescopingCertificate};
use crate::telescoping_check::CheckOptions;

/// The format tag written into every certificate file.
pub const FORMAT: &str = "axeyum-telescoping-certificate";

/// The format version written into every certificate file.
pub const VERSION: i128 = 1;

/// A certificate together with everything needed to re-check it from the file
/// alone.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertificateDocument {
    /// A stable identifier for this certificate, used as the file stem.
    pub id: String,
    /// One line saying which identity this is about, for a human reading a diff.
    pub title: String,
    /// The certificate itself.
    pub certificate: TelescopingCertificate,
    /// The grid and window the certificate is claimed to have been checked over.
    pub options: CheckOptions,
    /// A claimed closed form, the base index it holds from, and whether the base
    /// case is to be settled at symbolic parameters.
    pub closed_form: Option<ClosedFormClaim>,
}

/// A closed form claimed alongside a certificate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClosedFormClaim {
    /// The claimed closed form, as a hypergeometric term.
    pub term: HyperTerm,
    /// The index from which the closed form is claimed.
    pub base: i64,
    /// Whether the base case must be settled with the remaining parameters left
    /// symbolic rather than by evaluation at concrete integers.
    pub symbolic: bool,
}

// ---------------------------------------------------------------------------
// Writing
// ---------------------------------------------------------------------------

/// Render a certificate document as deterministic JSON.
///
/// Key order is fixed, map iteration is `BTreeMap` order, and every number is an
/// integer, so the same document always produces byte-identical output.
#[must_use]
pub fn to_json(document: &CertificateDocument) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "{{");
    let _ = writeln!(out, "  \"format\": {},", quote(FORMAT));
    let _ = writeln!(out, "  \"version\": {VERSION},");
    let _ = writeln!(out, "  \"id\": {},", quote(&document.id));
    let _ = writeln!(out, "  \"title\": {},", quote(&document.title));
    let _ = writeln!(
        out,
        "  \"shift_var\": {},",
        quote(&document.certificate.shift_var)
    );
    let _ = writeln!(
        out,
        "  \"sum_var\": {},",
        quote(&document.certificate.sum_var)
    );
    let _ = writeln!(
        out,
        "  \"term\": {},",
        write_term(&document.certificate.term)
    );
    let recurrence: Vec<String> = document
        .certificate
        .recurrence
        .iter()
        .map(write_poly)
        .collect();
    let _ = writeln!(out, "  \"recurrence\": [{}],", recurrence.join(", "));
    let _ = writeln!(
        out,
        "  \"certificate_numerator\": {},",
        write_poly(&document.certificate.certificate_numerator)
    );
    let _ = writeln!(
        out,
        "  \"certificate_denominator\": {},",
        write_poly(&document.certificate.certificate_denominator)
    );
    let _ = write!(out, "  \"check\": {}", write_options(&document.options));
    if let Some(claim) = &document.closed_form {
        let _ = writeln!(out, ",");
        let _ = write!(
            out,
            "  \"closed_form\": {{\"base\": {}, \"symbolic\": {}, \"term\": {}}}",
            claim.base,
            claim.symbolic,
            write_term(&claim.term)
        );
    }
    let _ = writeln!(out);
    let _ = writeln!(out, "}}");
    out
}

/// A JSON string literal with the characters this codec can emit escaped.
fn quote(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + 2);
    out.push('"');
    for character in text.chars() {
        match character {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            other => out.push(other),
        }
    }
    out.push('"');
    out
}

/// `[numerator, denominator]`.
fn write_rational(value: Rational) -> String {
    format!("[{}, {}]", value.numerator(), value.denominator())
}

/// A polynomial as `{"terms": [{"monomial": [["k", 2]], "coefficient": [3, 1]}]}`.
fn write_poly(poly: &MvPoly) -> String {
    let terms: Vec<String> = poly
        .terms()
        .map(|(mono, coefficient)| {
            let powers: Vec<String> = mono
                .powers()
                .map(|(name, power)| format!("[{}, {power}]", quote(name)))
                .collect();
            format!(
                "{{\"monomial\": [{}], \"coefficient\": {}}}",
                powers.join(", "),
                write_rational(*coefficient)
            )
        })
        .collect();
    format!("{{\"terms\": [{}]}}", terms.join(", "))
}

/// A linear form as `{"vars": [["m", 1]], "constant": 1}`.
fn write_form(form: &LinearForm) -> String {
    let vars: Vec<String> = form
        .variables()
        .iter()
        .map(|name| format!("[{}, {}]", quote(name), form.coefficient(name)))
        .collect();
    format!(
        "{{\"vars\": [{}], \"constant\": {}}}",
        vars.join(", "),
        form.constant()
    )
}

/// A hypergeometric term as its ordered factor list.
fn write_term(term: &HyperTerm) -> String {
    let factors: Vec<String> = term
        .factors()
        .iter()
        .map(|factor| match factor {
            Factor::Gamma { form, exponent } => format!(
                "{{\"kind\": \"gamma\", \"form\": {}, \"exponent\": {exponent}}}",
                write_form(form)
            ),
            Factor::Power { base, form } => format!(
                "{{\"kind\": \"power\", \"base\": {}, \"form\": {}}}",
                write_rational(*base),
                write_form(form)
            ),
            Factor::Poly { poly, exponent } => format!(
                "{{\"kind\": \"poly\", \"poly\": {}, \"exponent\": {exponent}}}",
                write_poly(poly)
            ),
        })
        .collect();
    format!("{{\"factors\": [{}]}}", factors.join(", "))
}

/// The check grid and window.
fn write_options(options: &CheckOptions) -> String {
    let samples: Vec<String> = options
        .samples
        .iter()
        .map(|(name, values)| {
            let rendered: Vec<String> = values.iter().map(i64::to_string).collect();
            format!("{}: [{}]", quote(name), rendered.join(", "))
        })
        .collect();
    format!(
        "{{\"samples\": {{{}}}, \"window\": [{}, {}], \"min_ratio_samples\": {}, \"min_pointwise_samples\": {}}}",
        samples.join(", "),
        options.window.0,
        options.window.1,
        options.min_ratio_samples,
        options.min_pointwise_samples
    )
}

// ---------------------------------------------------------------------------
// Reading
// ---------------------------------------------------------------------------

/// A parsed JSON value, in the fragment this codec emits.
#[derive(Debug, Clone, PartialEq)]
enum Json {
    Null,
    Bool(bool),
    Integer(i128),
    Text(String),
    Array(Vec<Json>),
    Object(BTreeMap<String, Json>),
}

impl Json {
    fn field(&self, name: &str) -> Result<&Json, String> {
        match self {
            Json::Object(map) => map
                .get(name)
                .ok_or_else(|| format!("missing field `{name}`")),
            _ => Err(format!("expected an object to read `{name}` from")),
        }
    }

    fn array(&self) -> Result<&[Json], String> {
        match self {
            Json::Array(items) => Ok(items),
            _ => Err("expected an array".to_owned()),
        }
    }

    fn text(&self) -> Result<&str, String> {
        match self {
            Json::Text(value) => Ok(value),
            _ => Err("expected a string".to_owned()),
        }
    }

    fn integer(&self) -> Result<i128, String> {
        match self {
            Json::Integer(value) => Ok(*value),
            _ => Err("expected an integer".to_owned()),
        }
    }

    fn narrow(&self) -> Result<i64, String> {
        i64::try_from(self.integer()?).map_err(|_| "integer out of range".to_owned())
    }

    fn boolean(&self) -> Result<bool, String> {
        match self {
            Json::Bool(value) => Ok(*value),
            _ => Err("expected a boolean".to_owned()),
        }
    }
}

/// Parse a certificate document from JSON.
///
/// # Errors
///
/// Returns a message naming the first structural problem: malformed JSON, a
/// wrong or missing `format`/`version` tag, a missing field, a value of the
/// wrong shape, or an arithmetic value outside the exact ranges this crate
/// supports.
pub fn from_json(text: &str) -> Result<CertificateDocument, String> {
    let value = parse(text)?;
    let format = value.field("format")?.text()?;
    if format != FORMAT {
        return Err(format!("format is `{format}`, expected `{FORMAT}`"));
    }
    let version = value.field("version")?.integer()?;
    if version != VERSION {
        return Err(format!("version is {version}, expected {VERSION}"));
    }
    let certificate = TelescopingCertificate {
        term: read_term(value.field("term")?)?,
        shift_var: value.field("shift_var")?.text()?.to_owned(),
        sum_var: value.field("sum_var")?.text()?.to_owned(),
        recurrence: value
            .field("recurrence")?
            .array()?
            .iter()
            .map(read_poly)
            .collect::<Result<Vec<MvPoly>, String>>()?,
        certificate_numerator: read_poly(value.field("certificate_numerator")?)?,
        certificate_denominator: read_poly(value.field("certificate_denominator")?)?,
    };
    let closed_form = match value.field("closed_form") {
        Ok(claim) => Some(ClosedFormClaim {
            term: read_term(claim.field("term")?)?,
            base: claim.field("base")?.narrow()?,
            symbolic: claim.field("symbolic")?.boolean()?,
        }),
        Err(_) => None,
    };
    Ok(CertificateDocument {
        id: value.field("id")?.text()?.to_owned(),
        title: value.field("title")?.text()?.to_owned(),
        certificate,
        options: read_options(value.field("check")?)?,
        closed_form,
    })
}

fn read_rational(value: &Json) -> Result<Rational, String> {
    let pair = value.array()?;
    if pair.len() != 2 {
        return Err("a rational must be a [numerator, denominator] pair".to_owned());
    }
    Rational::checked_new(pair[0].integer()?, pair[1].integer()?)
        .ok_or_else(|| "rational out of exact range".to_owned())
}

fn read_poly(value: &Json) -> Result<MvPoly, String> {
    let mut terms: Vec<(Monomial, Rational)> = Vec::new();
    for entry in value.field("terms")?.array()? {
        let mut powers: Vec<(String, u32)> = Vec::new();
        for power in entry.field("monomial")?.array()? {
            let pair = power.array()?;
            if pair.len() != 2 {
                return Err("a monomial factor must be a [name, exponent] pair".to_owned());
            }
            let exponent = u32::try_from(pair[1].integer()?)
                .map_err(|_| "monomial exponent out of range".to_owned())?;
            powers.push((pair[0].text()?.to_owned(), exponent));
        }
        let borrowed: Vec<(&str, u32)> = powers
            .iter()
            .map(|(name, exponent)| (name.as_str(), *exponent))
            .collect();
        terms.push((
            Monomial::from_powers(&borrowed),
            read_rational(entry.field("coefficient")?)?,
        ));
    }
    MvPoly::from_terms(terms).ok_or_else(|| "polynomial coefficients out of exact range".to_owned())
}

fn read_form(value: &Json) -> Result<LinearForm, String> {
    let mut pairs: Vec<(String, i64)> = Vec::new();
    for entry in value.field("vars")?.array()? {
        let pair = entry.array()?;
        if pair.len() != 2 {
            return Err("a linear-form term must be a [name, coefficient] pair".to_owned());
        }
        pairs.push((pair[0].text()?.to_owned(), pair[1].narrow()?));
    }
    let borrowed: Vec<(&str, i64)> = pairs
        .iter()
        .map(|(name, coefficient)| (name.as_str(), *coefficient))
        .collect();
    Ok(LinearForm::new(
        &borrowed,
        value.field("constant")?.narrow()?,
    ))
}

fn read_term(value: &Json) -> Result<HyperTerm, String> {
    let mut factors: Vec<Factor> = Vec::new();
    for entry in value.field("factors")?.array()? {
        let kind = entry.field("kind")?.text()?;
        let factor = match kind {
            "gamma" => Factor::Gamma {
                form: read_form(entry.field("form")?)?,
                exponent: read_exponent(entry.field("exponent")?)?,
            },
            "power" => Factor::Power {
                base: read_rational(entry.field("base")?)?,
                form: read_form(entry.field("form")?)?,
            },
            "poly" => Factor::Poly {
                poly: read_poly(entry.field("poly")?)?,
                exponent: read_exponent(entry.field("exponent")?)?,
            },
            other => return Err(format!("unknown factor kind `{other}`")),
        };
        factors.push(factor);
    }
    Ok(HyperTerm::new(factors))
}

fn read_exponent(value: &Json) -> Result<i32, String> {
    i32::try_from(value.integer()?).map_err(|_| "factor exponent out of range".to_owned())
}

fn read_options(value: &Json) -> Result<CheckOptions, String> {
    let mut samples: BTreeMap<String, Vec<i64>> = BTreeMap::new();
    match value.field("samples")? {
        Json::Object(map) => {
            for (name, values) in map {
                let points: Result<Vec<i64>, String> =
                    values.array()?.iter().map(Json::narrow).collect();
                samples.insert(name.clone(), points?);
            }
        }
        _ => return Err("`check.samples` must be an object".to_owned()),
    }
    let window = value.field("window")?.array()?;
    if window.len() != 2 {
        return Err("`check.window` must be a [low, high] pair".to_owned());
    }
    Ok(CheckOptions {
        samples,
        window: (window[0].narrow()?, window[1].narrow()?),
        min_ratio_samples: usize::try_from(value.field("min_ratio_samples")?.integer()?)
            .map_err(|_| "`check.min_ratio_samples` out of range".to_owned())?,
        // Required, not defaulted. A missing field would silently give every
        // pre-existing artifact whatever floor this codec happened to pick,
        // which is the recorded-distinction defect ADR-1400 is about: the
        // file would not say what coverage it was admitted under.
        min_pointwise_samples: usize::try_from(value.field("min_pointwise_samples")?.integer()?)
            .map_err(|_| "`check.min_pointwise_samples` out of range".to_owned())?,
    })
}

// ---------------------------------------------------------------------------
// A minimal JSON reader
// ---------------------------------------------------------------------------

/// Parse one JSON value from `text`, which must contain nothing else but
/// whitespace afterwards.
fn parse(text: &str) -> Result<Json, String> {
    let bytes: Vec<char> = text.chars().collect();
    let mut cursor = 0usize;
    let value = parse_value(&bytes, &mut cursor)?;
    skip_space(&bytes, &mut cursor);
    if cursor != bytes.len() {
        return Err(format!("trailing input at character {cursor}"));
    }
    Ok(value)
}

fn skip_space(bytes: &[char], cursor: &mut usize) {
    while *cursor < bytes.len() && bytes[*cursor].is_whitespace() {
        *cursor += 1;
    }
}

fn expect(bytes: &[char], cursor: &mut usize, character: char) -> Result<(), String> {
    skip_space(bytes, cursor);
    if bytes.get(*cursor) == Some(&character) {
        *cursor += 1;
        Ok(())
    } else {
        Err(format!("expected `{character}` at character {cursor}"))
    }
}

fn parse_value(bytes: &[char], cursor: &mut usize) -> Result<Json, String> {
    skip_space(bytes, cursor);
    match bytes.get(*cursor) {
        None => Err("unexpected end of input".to_owned()),
        Some('{') => parse_object(bytes, cursor),
        Some('[') => parse_array(bytes, cursor),
        Some('"') => Ok(Json::Text(parse_string(bytes, cursor)?)),
        Some('t' | 'f' | 'n') => parse_word(bytes, cursor),
        Some(_) => parse_integer(bytes, cursor),
    }
}

fn parse_object(bytes: &[char], cursor: &mut usize) -> Result<Json, String> {
    expect(bytes, cursor, '{')?;
    let mut map: BTreeMap<String, Json> = BTreeMap::new();
    skip_space(bytes, cursor);
    if bytes.get(*cursor) == Some(&'}') {
        *cursor += 1;
        return Ok(Json::Object(map));
    }
    loop {
        skip_space(bytes, cursor);
        let key = parse_string(bytes, cursor)?;
        expect(bytes, cursor, ':')?;
        let value = parse_value(bytes, cursor)?;
        if map.insert(key.clone(), value).is_some() {
            return Err(format!("duplicate key `{key}`"));
        }
        skip_space(bytes, cursor);
        match bytes.get(*cursor) {
            Some(',') => *cursor += 1,
            Some('}') => {
                *cursor += 1;
                return Ok(Json::Object(map));
            }
            _ => return Err(format!("expected `,` or `}}` at character {cursor}")),
        }
    }
}

fn parse_array(bytes: &[char], cursor: &mut usize) -> Result<Json, String> {
    expect(bytes, cursor, '[')?;
    let mut items: Vec<Json> = Vec::new();
    skip_space(bytes, cursor);
    if bytes.get(*cursor) == Some(&']') {
        *cursor += 1;
        return Ok(Json::Array(items));
    }
    loop {
        items.push(parse_value(bytes, cursor)?);
        skip_space(bytes, cursor);
        match bytes.get(*cursor) {
            Some(',') => *cursor += 1,
            Some(']') => {
                *cursor += 1;
                return Ok(Json::Array(items));
            }
            _ => return Err(format!("expected `,` or `]` at character {cursor}")),
        }
    }
}

fn parse_string(bytes: &[char], cursor: &mut usize) -> Result<String, String> {
    expect(bytes, cursor, '"')?;
    let mut out = String::new();
    loop {
        match bytes.get(*cursor) {
            None => return Err("unterminated string".to_owned()),
            Some('"') => {
                *cursor += 1;
                return Ok(out);
            }
            Some('\\') => {
                *cursor += 1;
                match bytes.get(*cursor) {
                    Some('"') => out.push('"'),
                    Some('\\') => out.push('\\'),
                    Some('n') => out.push('\n'),
                    _ => return Err(format!("unsupported escape at character {cursor}")),
                }
                *cursor += 1;
            }
            Some(other) => {
                out.push(*other);
                *cursor += 1;
            }
        }
    }
}

fn parse_word(bytes: &[char], cursor: &mut usize) -> Result<Json, String> {
    for (word, value) in [
        ("true", Json::Bool(true)),
        ("false", Json::Bool(false)),
        ("null", Json::Null),
    ] {
        let end = *cursor + word.len();
        if end <= bytes.len() && bytes[*cursor..end].iter().collect::<String>() == word {
            *cursor = end;
            return Ok(value);
        }
    }
    Err(format!("unrecognized literal at character {cursor}"))
}

fn parse_integer(bytes: &[char], cursor: &mut usize) -> Result<Json, String> {
    let start = *cursor;
    if bytes.get(*cursor) == Some(&'-') {
        *cursor += 1;
    }
    let digits = *cursor;
    while bytes.get(*cursor).is_some_and(char::is_ascii_digit) {
        *cursor += 1;
    }
    if *cursor == digits {
        return Err(format!("expected an integer at character {start}"));
    }
    if bytes
        .get(*cursor)
        .is_some_and(|next| *next == '.' || *next == 'e' || *next == 'E')
    {
        return Err(format!(
            "non-integer number at character {start}; this format uses [numerator, denominator] pairs"
        ));
    }
    bytes[start..*cursor]
        .iter()
        .collect::<String>()
        .parse::<i128>()
        .map(Json::Integer)
        .map_err(|_| format!("integer out of exact range at character {start}"))
}

#[cfg(test)]
mod tests {
    use super::{CertificateDocument, ClosedFormClaim, from_json, to_json};
    use crate::telescoping::{
        HyperTerm, Limits, LinearForm, TelescopingOutcome, binomial_factors, zeilberger,
    };
    use crate::telescoping_check::CheckOptions;

    fn document() -> CertificateDocument {
        let term = HyperTerm::new(binomial_factors(
            &LinearForm::new(&[("n", 1)], 0),
            &LinearForm::new(&[("k", 1)], 0),
            1,
        ));
        let TelescopingOutcome::Found(certificate) =
            zeilberger(&term, "n", "k", &Limits::classical())
        else {
            panic!("no certificate for the binomial row sum");
        };
        CertificateDocument {
            id: "binomial-row-sum-two-power".to_owned(),
            title: "sum_k C(n,k) = 2^n".to_owned(),
            certificate: *certificate,
            options: CheckOptions::over("n", &[0, 1, 2, 3], (-2, 10)),
            closed_form: Some(ClosedFormClaim {
                term: HyperTerm::new(vec![crate::telescoping::Factor::Power {
                    base: axeyum_ir::Rational::integer(2),
                    form: LinearForm::new(&[("n", 1)], 0),
                }]),
                base: 0,
                symbolic: false,
            }),
        }
    }

    #[test]
    fn a_document_round_trips_exactly() {
        let original = document();
        let text = to_json(&original);
        let parsed = from_json(&text).expect("the codec must read back its own output");
        assert_eq!(parsed, original);
        // And rendering is deterministic, so a redeploy is a no-op diff.
        assert_eq!(to_json(&parsed), text);
    }

    #[test]
    fn a_truncated_or_mistyped_file_is_refused() {
        let text = to_json(&document());
        assert!(from_json(&text[..text.len() / 2]).is_err());
        assert!(from_json(&text.replace("\"version\": 1", "\"version\": 2")).is_err());
        assert!(
            from_json(&text.replace(FORMAT_MARKER, "some-other-format")).is_err(),
            "a foreign format tag must be refused"
        );
        // Decimals are not a representation this format accepts, because they
        // are not exact.
        assert!(
            from_json(&text.replace("[1, 1]", "[1.0, 1]")).is_err(),
            "a decimal must be refused rather than rounded"
        );
    }

    const FORMAT_MARKER: &str = "axeyum-telescoping-certificate";
}
