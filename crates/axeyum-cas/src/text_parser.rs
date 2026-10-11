//! Bounded exact human expression grammar with UTF-8 byte diagnostics (ADR-6800).
use crate::{CasExpr, Rational, UnaryFunc};
use num_bigint::BigInt;
use num_rational::BigRational;

/// A syntax or resource refusal at a half-open UTF-8 byte span.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    /// Human-readable reason; parsing never establishes a proof claim.
    pub message: String,
    /// Inclusive start byte offset.
    pub start: usize,
    /// Exclusive end byte offset.
    pub end: usize,
}
impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} at [{}:{}]", self.message, self.start, self.end)
    }
}
impl std::error::Error for ParseError {}
#[derive(Clone, Copy)]
struct Token<'a> {
    text: &'a str,
    start: usize,
    end: usize,
}
fn error(message: &str, start: usize, end: usize) -> ParseError {
    ParseError {
        message: message.into(),
        start,
        end,
    }
}
fn tokenize(source: &str) -> Result<Vec<Token<'_>>, ParseError> {
    if source.len() > 8192 {
        return Err(error("source byte limit exceeded", 8192, source.len()));
    }
    let mut tokens = Vec::new();
    let mut offset = 0;
    while offset < source.len() {
        let ch = source[offset..]
            .chars()
            .next()
            .expect("valid nonempty UTF-8 suffix");
        if ch.is_whitespace() {
            offset += ch.len_utf8();
            continue;
        }
        let start = offset;
        let bytes = source.as_bytes();
        if ch.is_ascii_digit() {
            while offset < bytes.len() && bytes[offset].is_ascii_digit() {
                offset += 1;
            }
            if offset + 1 < bytes.len()
                && bytes[offset] == b'.'
                && bytes[offset + 1].is_ascii_digit()
            {
                offset += 1;
                while offset < bytes.len() && bytes[offset].is_ascii_digit() {
                    offset += 1;
                }
            }
            if source[start..offset]
                .bytes()
                .filter(u8::is_ascii_digit)
                .count()
                > 1024
            {
                return Err(error("literal digit limit exceeded", start, offset));
            }
        } else if ch.is_ascii_alphabetic() || ch == '_' {
            offset += 1;
            while offset < bytes.len()
                && (bytes[offset].is_ascii_alphanumeric() || bytes[offset] == b'_')
            {
                offset += 1;
            }
        } else if ch == 'π' {
            offset += ch.len_utf8();
        } else if "()+*/^-".contains(ch) {
            offset += 1;
            if ch == '*' && offset < bytes.len() && bytes[offset] == b'*' {
                offset += 1;
            }
        } else {
            return Err(error("unexpected character", start, start + ch.len_utf8()));
        }
        if tokens.len() == 512 {
            return Err(error("token limit exceeded", start, offset));
        }
        tokens.push(Token {
            text: &source[start..offset],
            start,
            end: offset,
        });
    }
    tokens.push(Token {
        text: "",
        start: source.len(),
        end: source.len(),
    });
    Ok(tokens)
}
struct Parser<'a> {
    tokens: Vec<Token<'a>>,
    index: usize,
    nodes: usize,
}
impl Parser<'_> {
    fn fail(&self, message: &str) -> ParseError {
        let t = self.tokens[self.index];
        error(message, t.start, t.end)
    }
    fn take(&mut self, text: &str) -> bool {
        if self.tokens[self.index].text == text {
            self.index += 1;
            true
        } else {
            false
        }
    }
    fn node(&mut self, expr: CasExpr) -> Result<CasExpr, ParseError> {
        self.nodes += 1;
        if self.nodes > 64 {
            Err(self.fail("expression node limit exceeded"))
        } else {
            Ok(expr)
        }
    }
    fn literal(&self, text: &str) -> Result<CasExpr, ParseError> {
        let (digits, denominator) = if let Some((whole, fractional)) = text.split_once('.') {
            (
                format!("{whole}{fractional}"),
                BigInt::from(10)
                    .pow(u32::try_from(fractional.len()).map_err(|_| self.fail("decimal scale"))?),
            )
        } else {
            (text.into(), BigInt::from(1))
        };
        let numerator = BigInt::parse_bytes(digits.as_bytes(), 10)
            .ok_or_else(|| self.fail("invalid numeral"))?;
        if numerator.bits().max(denominator.bits()) > 16384 {
            return Err(self.fail("coefficient bit limit exceeded"));
        }
        let rational = Rational::from_big_rational(&BigRational::new(numerator, denominator))
            .ok_or_else(|| self.fail("rational transport declined"))?;
        Ok(CasExpr::Const(rational))
    }
    fn atom(&mut self, depth: usize) -> Result<CasExpr, ParseError> {
        let token = self.tokens[self.index];
        if token.text == "+" || token.text == "-" {
            self.index += 1;
            let inner = self.expression(3, depth + 1)?;
            return if token.text == "-" {
                self.node(CasExpr::Neg(Box::new(inner)))
            } else {
                Ok(inner)
            };
        }
        if self.take("(") {
            let inner = self.expression(0, depth + 1)?;
            if !self.take(")") {
                return Err(self.fail("expected closing parenthesis"));
            }
            return Ok(inner);
        }
        if token.text.starts_with(|c: char| c.is_ascii_digit()) {
            self.index += 1;
            let literal = self.literal(token.text)?;
            return self.node(literal);
        }
        if token.text == "pi" || token.text == "π" {
            self.index += 1;
            return self.node(CasExpr::Pi);
        }
        if token
            .text
            .starts_with(|c: char| c.is_ascii_alphabetic() || c == '_')
        {
            self.index += 1;
            if !self.take("(") {
                return self.node(CasExpr::Var(token.text.into()));
            }
            let head = match token.text {
                "sin" => UnaryFunc::Sin,
                "cos" => UnaryFunc::Cos,
                "tan" => UnaryFunc::Tan,
                "atan" => UnaryFunc::Atan,
                "ln" => UnaryFunc::Ln,
                "exp" => UnaryFunc::Exp,
                "sqrt" => UnaryFunc::Sqrt,
                "abs" => UnaryFunc::Abs,
                "sign" => UnaryFunc::Sign,
                "floor" => UnaryFunc::Floor,
                "ceiling" => UnaryFunc::Ceiling,
                "cbrt" => UnaryFunc::NthRoot(3),
                _ => return Err(error("unknown unary function", token.start, token.end)),
            };
            let inner = self.expression(0, depth + 1)?;
            if !self.take(")") {
                return Err(self.fail("expected closing parenthesis"));
            }
            return self.node(CasExpr::Unary(head, Box::new(inner)));
        }
        Err(self.fail("expected expression"))
    }
    fn expression(&mut self, minimum: u8, depth: usize) -> Result<CasExpr, ParseError> {
        if depth > 32 {
            return Err(self.fail("expression depth limit exceeded"));
        }
        let mut left = self.atom(depth)?;
        loop {
            let operator = self.tokens[self.index].text;
            let precedence = match operator {
                "+" | "-" => 1,
                "*" | "/" => 2,
                "^" | "**" => 4,
                _ => return Ok(left),
            };
            if precedence < minimum {
                return Ok(left);
            }
            self.index += 1;
            if precedence == 4 {
                let negative = self.take("-");
                if !negative {
                    self.take("+");
                }
                let token = self.tokens[self.index];
                if token.text.is_empty() || !token.text.bytes().all(|b| b.is_ascii_digit()) {
                    return Err(self.fail("expected signed integer exponent"));
                }
                let magnitude: u32 = token
                    .text
                    .parse()
                    .map_err(|_| self.fail("exponent magnitude exceeds 4294967295"))?;
                self.index += 1;
                let exponent = i64::from(magnitude) * if negative { -1 } else { 1 };
                left = self.node(
                    left.pow_signed(exponent)
                        .ok_or_else(|| self.fail("unsupported exponent"))?,
                )?;
                if matches!(self.tokens[self.index].text, "^" | "**") {
                    return Err(self.fail("chained powers require parentheses"));
                }
            } else {
                let right = self.expression(precedence + 1, depth + 1)?;
                left = self.node(match operator {
                    "+" => CasExpr::Add(vec![left, right]),
                    "-" => CasExpr::Add(vec![left, CasExpr::Neg(Box::new(right))]),
                    "*" => CasExpr::Mul(vec![left, right]),
                    _ => CasExpr::Div(Box::new(left), Box::new(right)),
                })?;
            }
        }
    }
}
/// Parse bounded exact arithmetic syntax; this constructs an expression, not a proof.
///
/// # Errors
/// Malformed input, unsupported calls/exponents, or explicit resource exhaustion.
pub fn parse(source: &str) -> Result<CasExpr, ParseError> {
    let mut parser = Parser {
        tokens: tokenize(source)?,
        index: 0,
        nodes: 0,
    };
    let result = parser.expression(0, 0)?;
    if !parser.tokens[parser.index].text.is_empty() {
        return Err(parser.fail("unexpected trailing token"));
    }
    // Lowering signed powers/subtraction adds nodes beyond the grammar's builders.
    let mut work = vec![(&result, 0)];
    let mut count = 0;
    while let Some((expr, depth)) = work.pop() {
        count += 1;
        if count > 64 || depth > 32 {
            return Err(parser.fail("lowered expression shape limit exceeded"));
        }
        match expr {
            CasExpr::Add(xs) | CasExpr::Mul(xs) => work.extend(xs.iter().map(|x| (x, depth + 1))),
            CasExpr::Neg(x) | CasExpr::Pow(x, _) | CasExpr::Unary(_, x) => {
                work.push((x, depth + 1))
            }
            CasExpr::Div(a, b) => {
                work.push((a, depth + 1));
                work.push((b, depth + 1));
            }
            _ => {}
        }
    }
    Ok(result)
}
