//! Iterative s-expression tokenizer and reader.
//!
//! Both passes are loop-based with explicit stacks, so adversarially deep
//! benchmark files cannot overflow the call stack (hard rule).

use crate::SmtError;

/// A parsed s-expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SExpr {
    /// An atomic token: symbol, keyword, numeral, `#x`/`#b` literal, or
    /// `"string"` (kept verbatim including quotes).
    Atom(String),
    /// A parenthesized list.
    List(Vec<SExpr>),
}

impl SExpr {
    /// The atom's text, or `None` for lists.
    pub fn atom(&self) -> Option<&str> {
        match self {
            SExpr::Atom(s) => Some(s),
            SExpr::List(_) => None,
        }
    }

    /// The list's items, or `None` for atoms.
    pub fn list(&self) -> Option<&[SExpr]> {
        match self {
            SExpr::Atom(_) => None,
            SExpr::List(items) => Some(items),
        }
    }
}

/// Reads every top-level s-expression in `input`.
///
/// # Errors
///
/// Returns [`SmtError::Syntax`] on unbalanced parentheses, unterminated
/// strings/quoted symbols, or stray closing parens.
pub fn read_all(input: &str) -> Result<Vec<SExpr>, SmtError> {
    let mut top = Vec::new();
    // Stack of open lists; pushes/pops instead of recursion.
    let mut stack: Vec<Vec<SExpr>> = Vec::new();
    let bytes = input.as_bytes();
    let mut i = 0usize;
    let n = bytes.len();

    let emit = |stack: &mut Vec<Vec<SExpr>>, top: &mut Vec<SExpr>, e: SExpr| {
        if let Some(open) = stack.last_mut() {
            open.push(e);
        } else {
            top.push(e);
        }
    };

    while i < n {
        let c = bytes[i];
        match c {
            b' ' | b'\t' | b'\r' | b'\n' => i += 1,
            b';' => {
                while i < n && bytes[i] != b'\n' {
                    i += 1;
                }
            }
            b'(' => {
                stack.push(Vec::new());
                i += 1;
            }
            b')' => {
                let done = stack
                    .pop()
                    .ok_or_else(|| SmtError::Syntax(format!("stray ')' at byte {i}")))?;
                emit(&mut stack, &mut top, SExpr::List(done));
                i += 1;
            }
            b'"' => {
                let start = i;
                i += 1;
                loop {
                    if i >= n {
                        return Err(SmtError::Syntax(format!(
                            "unterminated string at byte {start}"
                        )));
                    }
                    if bytes[i] == b'"' {
                        // SMT-LIB escapes a quote by doubling it.
                        if i + 1 < n && bytes[i + 1] == b'"' {
                            i += 2;
                            continue;
                        }
                        i += 1;
                        break;
                    }
                    i += 1;
                }
                emit(
                    &mut stack,
                    &mut top,
                    SExpr::Atom(input[start..i].to_owned()),
                );
            }
            b'|' => {
                let start = i;
                i += 1;
                while i < n && bytes[i] != b'|' {
                    i += 1;
                }
                if i >= n {
                    return Err(SmtError::Syntax(format!(
                        "unterminated quoted symbol at byte {start}"
                    )));
                }
                i += 1;
                // Strip the pipes; the inner text is the symbol name.
                emit(
                    &mut stack,
                    &mut top,
                    SExpr::Atom(input[start + 1..i - 1].to_owned()),
                );
            }
            _ => {
                let start = i;
                while i < n
                    && !matches!(bytes[i], b' ' | b'\t' | b'\r' | b'\n' | b'(' | b')' | b';')
                {
                    i += 1;
                }
                emit(
                    &mut stack,
                    &mut top,
                    SExpr::Atom(input[start..i].to_owned()),
                );
            }
        }
    }
    if !stack.is_empty() {
        return Err(SmtError::Syntax(
            "unbalanced '(' at end of input".to_owned(),
        ));
    }
    Ok(top)
}
