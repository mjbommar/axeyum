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

    /// Every node of this tree in pre-order (`self` first, then each child's
    /// subtree left to right).
    ///
    /// This exists so that "does the script mention X anywhere" scans — of
    /// which the front door runs several on *every* parsed script — can be
    /// written without native recursion. A recursive scan's depth is the
    /// source's nesting depth, which a benchmark file controls directly: a
    /// left-associated `(and (and (and …)))` or `(bvadd (bvadd …))` spine
    /// overflowed the stack and **aborted** the process, so no first-class
    /// `unknown` could be reported and a harness read the exit as a crash
    /// (the failure mode fixed in `fcc8760d`). The reader itself has always
    /// been iterative for exactly this reason; the scans over its output must
    /// be too.
    pub fn descendants(&self) -> Descendants<'_> {
        Descendants { stack: vec![self] }
    }
}

/// Pre-order iterator over an [`SExpr`] tree; see [`SExpr::descendants`].
#[derive(Debug, Clone)]
pub struct Descendants<'a> {
    stack: Vec<&'a SExpr>,
}

impl<'a> Iterator for Descendants<'a> {
    type Item = &'a SExpr;

    fn next(&mut self) -> Option<&'a SExpr> {
        let node = self.stack.pop()?;
        if let SExpr::List(items) = node {
            // Reversed, so the stack yields children left to right.
            self.stack.extend(items.iter().rev());
        }
        Some(node)
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

impl Drop for SExpr {
    /// Dismantles the tree with an explicit worklist.
    ///
    /// The compiler's generated drop glue for `SExpr::List(Vec<SExpr>)` is
    /// *recursive*: its depth is the source's nesting depth, so simply dropping
    /// a parsed script with a left-associated `(and (and (and …)))` or
    /// `(not (not (not …)))` spine overflowed the stack and **aborted** the
    /// process — after the query had already been decided. No amount of care in
    /// the walking code prevents that, because no walking code is involved.
    fn drop(&mut self) {
        let SExpr::List(items) = self else { return };
        if items.is_empty() {
            return;
        }
        let mut work: Vec<SExpr> = std::mem::take(items);
        while let Some(mut node) = work.pop() {
            if let SExpr::List(children) = &mut node {
                // Moves the grandchildren out, so `node` drops at depth 1.
                work.append(children);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{SExpr, read_all};

    /// Builds `(not (not (not … a)))` nested `depth` deep.
    fn nested(depth: usize) -> SExpr {
        let mut e = SExpr::Atom("a".to_owned());
        for _ in 0..depth {
            e = SExpr::List(vec![SExpr::Atom("not".to_owned()), e]);
        }
        e
    }

    /// Dropping a deeply nested tree must not blow the stack.
    ///
    /// The compiler's drop glue for `List(Vec<SExpr>)` is recursive, so before
    /// [`SExpr`]'s manual [`Drop`] a parsed script with a deep spine aborted the
    /// process *after* the query had been decided. The depth is far past what
    /// any recursive frame survives on the harness's thread stack, so a
    /// regression aborts the test binary rather than failing quietly.
    #[test]
    fn dropping_a_deeply_nested_tree_does_not_overflow() {
        const DEPTH: usize = 200_000;
        drop(nested(DEPTH));
    }

    /// The reader is iterative, so the same depth survives parsing — and the
    /// tree it returns is dropped iteratively too.
    #[test]
    fn reading_and_dropping_deeply_nested_source_does_not_overflow() {
        const DEPTH: usize = 200_000;
        let text = format!("{}a{}", "(not ".repeat(DEPTH), ")".repeat(DEPTH));
        let read = read_all(&text).expect("balanced source");
        assert_eq!(read.len(), 1);
        // Compared structurally rather than with `==`: the derived `PartialEq`
        // is itself recursive, so it would overflow on a tree this deep.
        assert_eq!(read[0].descendants().count(), 2 * DEPTH + 1);
    }

    /// `descendants` visits the whole tree, in pre-order, without recursing.
    #[test]
    fn descendants_is_preorder_and_iterative() {
        let flat = SExpr::List(vec![
            SExpr::Atom("f".to_owned()),
            SExpr::List(vec![
                SExpr::Atom("g".to_owned()),
                SExpr::Atom("x".to_owned()),
            ]),
            SExpr::Atom("y".to_owned()),
        ]);
        let atoms: Vec<&str> = flat.descendants().filter_map(SExpr::atom).collect();
        assert_eq!(atoms, vec!["f", "g", "x", "y"]);

        let deep = nested(200_000);
        assert_eq!(deep.descendants().count(), 2 * 200_000 + 1);
    }
}
