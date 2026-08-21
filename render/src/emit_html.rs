//! HTML emitter: one self-contained file per document.
//!
//! Contract, from `docs/render-2026-08/03-architecture.md`: emitters are
//! TOTAL and DUMB. Everything that can be a build error happens in assembly,
//! before this module sees the document. Nothing here inspects evidence to
//! decide a status -- it renders the status it is given.
//!
//! That leaves this module two jobs it must do exactly:
//!
//! 1. **Never invent.** A block shape this emitter does not understand is
//!    rendered as a loud, unmissable `ax-unrenderable` box AND reported in the
//!    diagnostics list, never dropped and never guessed at. The same rule
//!    governs the LaTeX subset: an unrecognised command becomes a visible
//!    `<merror>`, because a formula silently rendered wrong is the exact drift
//!    this strand exists to kill.
//! 2. **Never phone home.** A document emitted here makes zero network
//!    requests. [`lint_self_contained`] is the machine statement of that, and
//!    it is wired into this module's own tests -- including tests that inject
//!    each violation class and require it to be caught.
//!
//! Input is `serde_json::Value` in the Doc-IR shape. Reading JSON rather than
//! the Rust structs is deliberate for round 1: the schema is owned by another
//! lane, so this module treats it as data and accepts both serde enum
//! encodings (externally tagged `{"Prose": {..}}` and internally tagged
//! `{"kind": "prose", ..}`). See `docs/render-2026-08/11-design-diary.md`
//! for the integration items this leaves for round 2.

// Pedantic lints deliberately allowed in this module, with reasons. The
// package sets `clippy::pedantic = warn`; these four fire on shapes that are
// correct here and whose "fix" would make the code worse:
#![allow(
    // Layout arithmetic converts small counts to f64 for geometry. The counts
    // are node indices and layer sizes -- bounded by the ~325-node ledger, so
    // nowhere near f64's 53-bit exact range.
    clippy::cast_precision_loss,
    // Rounding a computed coordinate or a tick value to an integer for display
    // is the intent, not an accident.
    clippy::cast_possible_truncation,
    // Emitting HTML is a long straight-line sequence of writes; splitting it
    // into a dozen private helpers to satisfy a line count would hide the
    // document structure, which is the one thing a reader of an emitter needs.
    clippy::too_many_lines,
    // `write!` into a String cannot fail, and the `format!`-append form reads
    // better than a `let _ = write!` in an expression position.
    clippy::format_push_string
)]

use serde_json::Value;
use std::fmt::Write as _;

use crate::layout::{self, LayoutConfig, NodeSpec};

/// The stylesheet and the page script, inlined at emit time. `include_str!`
/// keeps them editable as real `.css`/`.js` files while guaranteeing the
/// output has no external reference to them.
const STYLE_CSS: &str = include_str!("../assets/style.css");
const APP_JS: &str = include_str!("../assets/app.js");

/// Reading level the document opens at. `Full` is the only safe default: it
/// is what a reader with JavaScript disabled sees, since level gating is
/// CSS driven off a `body` attribute the script never gets to set.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReadingLevel {
    Summary,
    Full,
    Forensic,
}

impl ReadingLevel {
    fn slug(self) -> &'static str {
        match self {
            ReadingLevel::Summary => "summary",
            ReadingLevel::Full => "full",
            ReadingLevel::Forensic => "forensic",
        }
    }
}

/// Emitter options.
#[derive(Clone, Debug)]
pub struct HtmlOptions {
    pub level: ReadingLevel,
    /// Rendered into the footer as the build stamp. Must come from the commit
    /// or `SOURCE_DATE_EPOCH`; this emitter never reads a clock.
    pub epoch: Option<String>,
}

impl Default for HtmlOptions {
    fn default() -> Self {
        HtmlOptions {
            level: ReadingLevel::Full,
            epoch: None,
        }
    }
}

/// Render a Doc-IR document to a single self-contained HTML file.
pub fn emit(doc: &Value, opts: &HtmlOptions) -> String {
    emit_with_diagnostics(doc, opts).0
}

/// Render, and report everything the emitter could not interpret.
///
/// The diagnostics are not decoration: `render/check.sh` should treat a
/// non-empty list as a failure, because every entry means the document on
/// screen is missing something the IR carried.
pub fn emit_with_diagnostics(doc: &Value, opts: &HtmlOptions) -> (String, Vec<String>) {
    let mut d = Vec::new();
    let meta = doc.get("meta").unwrap_or(&Value::Null);
    let title = s(meta, "title").unwrap_or("Untitled document");

    let mut body = String::new();
    let blocks = doc.get("blocks").and_then(|b| b.as_array());
    if let Some(bs) = blocks {
        for (i, b) in bs.iter().enumerate() {
            block(&mut body, b, i, &mut d);
        }
    } else {
        d.push("document has no `blocks` array".to_string());
        let _ = write!(
            body,
            "<div class=\"ax-unrenderable\">document has no `blocks` array</div>"
        );
    }

    let mut out = String::with_capacity(STYLE_CSS.len() + APP_JS.len() + body.len() + 4096);
    out.push_str("<!doctype html>\n<html lang=\"en\">\n<head>\n");
    out.push_str("<meta charset=\"utf-8\">\n");
    out.push_str("<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n");
    let _ = writeln!(out, "<title>{}</title>", esc(title));
    if let Some(sub) = s(meta, "subtitle") {
        let _ = writeln!(
            out,
            "<meta name=\"description\" content=\"{}\">",
            esc_attr(sub)
        );
    }
    out.push_str("<style>\n");
    out.push_str(STYLE_CSS);
    out.push_str("\n</style>\n</head>\n");
    let _ = writeln!(out, "<body data-level=\"{}\">", opts.level.slug());
    out.push_str("<a class=\"ax-skip\" href=\"#ax-main\">Skip to content</a>\n");
    header(&mut out, meta, opts);
    out.push_str("<main id=\"ax-main\" class=\"ax-doc\">\n");
    out.push_str(&body);
    out.push_str("</main>\n");
    footer(&mut out, meta, opts, &d);
    out.push_str("<script>\n");
    out.push_str(APP_JS);
    out.push_str("\n</script>\n</body>\n</html>\n");
    (out, d)
}

// ---------------------------------------------------------------------------
// small JSON accessors -- deliberately total, never panicking on shape
// ---------------------------------------------------------------------------

fn s<'a>(v: &'a Value, key: &str) -> Option<&'a str> {
    v.get(key)
        .and_then(|x| x.as_str())
        .filter(|x| !x.is_empty())
}

fn arr<'a>(v: &'a Value, key: &str) -> &'a [Value] {
    v.get(key)
        .and_then(|x| x.as_array())
        .map_or(&[][..], std::vec::Vec::as_slice)
}

fn text_of(v: &Value) -> String {
    match v {
        Value::String(x) => x.clone(),
        Value::Number(n) => n.to_string(),
        Value::Bool(b) => b.to_string(),
        Value::Null => String::new(),
        other => other.to_string(),
    }
}

// ---------------------------------------------------------------------------
// escaping
// ---------------------------------------------------------------------------

/// HTML text escaping, ASCII-out.
///
/// `<`, `&` and `>` become entities -- `>` too, because a stray one in a
/// comment-like run is a real parse hazard. Every non-ASCII character becomes a
/// numeric character reference, which is what makes the emitted file ASCII
/// (repository-wide rule, and `lib.rs` contract point 8). That matters more
/// here than it looks: the fact ledger is full of `forall`, `Nat` and `Int`
/// glyphs, and a document is not allowed to depend on a byte the pipeline might
/// re-encode.
pub fn esc(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 8);
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            c if c.is_ascii() => out.push(c),
            c => {
                let _ = write!(out, "&#x{:X};", c as u32);
            }
        }
    }
    out
}

/// Attribute-value escaping: everything `esc` does, plus both quote forms.
pub fn esc_attr(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 8);
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#39;"),
            c if c.is_ascii() => out.push(c),
            c => {
                let _ = write!(out, "&#x{:X};", c as u32);
            }
        }
    }
    out
}

/// An id safe to use as an HTML anchor. Deterministic: same input, same id.
pub fn slug(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut prev_dash = false;
    for c in s.chars() {
        if c.is_ascii_alphanumeric() {
            out.push(c.to_ascii_lowercase());
            prev_dash = false;
        } else if !prev_dash && !out.is_empty() {
            out.push('-');
            prev_dash = true;
        }
    }
    while out.ends_with('-') {
        out.pop();
    }
    if out.is_empty() { "x".to_string() } else { out }
}

// ---------------------------------------------------------------------------
// R-b: LaTeX subset -> MathML Core
// ---------------------------------------------------------------------------

/// Convert a small, explicitly enumerated LaTeX subset to MathML Core.
///
/// Returns the markup and whether every token was recognised. **An
/// unrecognised command is rendered as a visible `<merror>` and reported as
/// `false`**, never approximated: the failure mode this whole strand exists to
/// prevent is a document that looks right and says something else.
///
/// Why MathML and not SVG or Unicode (full argument in
/// `docs/render-2026-08/07-r-notes.md`, section R-b): MathML Core is Baseline
/// "widely available" since January 2023 and measured at 94.31% of global
/// usage on caniuse (read 2026-08-21); it inherits `color`, so dark mode is
/// free; and it is the only one of the three with a screen-reader story.
pub fn latex_to_mathml(src: &str) -> (String, bool) {
    let mut p = Tex {
        b: src.as_bytes(),
        i: 0,
        ok: true,
    };
    let inner = p.row(None);
    let ok = p.ok;
    let mut out = String::new();
    let _ = write!(
        out,
        "<math display=\"inline\" alttext=\"{}\"><semantics>{}<annotation encoding=\"application/x-tex\">{}</annotation></semantics></math>",
        esc_attr(src),
        inner,
        esc(src)
    );
    (out, ok)
}

struct Tex<'a> {
    b: &'a [u8],
    i: usize,
    ok: bool,
}

impl Tex<'_> {
    fn peek(&self) -> Option<u8> {
        self.b.get(self.i).copied()
    }

    /// Parse a sequence of atoms into an `<mrow>`, stopping at `stop`.
    fn row(&mut self, stop: Option<u8>) -> String {
        let mut items: Vec<String> = Vec::new();
        loop {
            while self.peek() == Some(b' ') {
                self.i += 1;
            }
            match self.peek() {
                None => break,
                Some(c) if Some(c) == stop => {
                    self.i += 1;
                    break;
                }
                Some(b'}') if stop.is_none() => {
                    // Unbalanced: report rather than swallow.
                    self.ok = false;
                    self.i += 1;
                    items.push("<merror><mtext>}</mtext></merror>".to_string());
                }
                Some(b'^' | b'_') => {
                    let script = self.b[self.i];
                    self.i += 1;
                    let base = items.pop().unwrap_or_else(|| "<mi></mi>".to_string());
                    let arg = self.atom();
                    let tag = if script == b'^' { "msup" } else { "msub" };
                    // x_i^2 : a script on a scripted base becomes msubsup.
                    items.push(format!("<{tag}>{base}{arg}</{tag}>"));
                }
                Some(_) => {
                    let a = self.atom();
                    if !a.is_empty() {
                        items.push(a);
                    }
                }
            }
        }
        format!("<mrow>{}</mrow>", items.concat())
    }

    /// One atom: a group, a command, a number, an identifier run, or an
    /// operator character.
    fn atom(&mut self) -> String {
        while self.peek() == Some(b' ') {
            self.i += 1;
        }
        let Some(c) = self.peek() else {
            return String::new();
        };
        if c == b'{' {
            self.i += 1;
            return self.row(Some(b'}'));
        }
        if c == b'\\' {
            return self.command();
        }
        if c.is_ascii_digit() {
            let start = self.i;
            while self.peek().is_some_and(|d| d.is_ascii_digit() || d == b'.') {
                self.i += 1;
            }
            return format!(
                "<mn>{}</mn>",
                &String::from_utf8_lossy(&self.b[start..self.i])
            );
        }
        if c.is_ascii_alphabetic() {
            self.i += 1;
            return format!("<mi>{}</mi>", c as char);
        }
        self.i += 1;
        match c {
            b'+' | b'-' | b'*' | b'/' | b'=' | b'<' | b'>' | b'|' | b',' | b';' | b'.' | b':'
            | b'!' | b'(' | b')' | b'[' | b']' => {
                let g = match c {
                    b'-' => "\u{2212}".to_string(), // MINUS SIGN, not hyphen
                    b'*' => "\u{2217}".to_string(),
                    _ => (c as char).to_string(),
                };
                let stretch = matches!(c, b'(' | b')' | b'[' | b']');
                format!(
                    "<mo{}>{}</mo>",
                    if stretch { "" } else { " stretchy=\"false\"" },
                    esc(&g)
                )
            }
            _ => {
                self.ok = false;
                format!(
                    "<merror><mtext>{}</mtext></merror>",
                    esc(&(c as char).to_string())
                )
            }
        }
    }

    fn command(&mut self) -> String {
        debug_assert_eq!(self.peek(), Some(b'\\'));
        self.i += 1;
        let start = self.i;
        while self.peek().is_some_and(|d| d.is_ascii_alphabetic()) {
            self.i += 1;
        }
        if start == self.i {
            // A single non-letter escape such as `\{` or `\,`.
            let c = self.peek().unwrap_or(b' ');
            self.i += 1;
            return match c {
                b'{' | b'}' => format!("<mo stretchy=\"false\">{}</mo>", c as char),
                b',' => "<mspace width=\"0.17em\"></mspace>".to_string(),
                b';' => "<mspace width=\"0.28em\"></mspace>".to_string(),
                b' ' => "<mspace width=\"0.25em\"></mspace>".to_string(),
                _ => {
                    self.ok = false;
                    format!(
                        "<merror><mtext>\\{}</mtext></merror>",
                        esc(&(c as char).to_string())
                    )
                }
            };
        }
        let name = String::from_utf8_lossy(&self.b[start..self.i]).to_string();
        match name.as_str() {
            "frac" => {
                let n = self.atom();
                let d = self.atom();
                format!("<mfrac>{n}{d}</mfrac>")
            }
            "binom" => {
                let n = self.atom();
                let k = self.atom();
                format!(
                    "<mrow><mo>(</mo><mfrac linethickness=\"0\">{n}{k}</mfrac><mo>)</mo></mrow>"
                )
            }
            "sqrt" => {
                let a = self.atom();
                format!("<msqrt>{a}</msqrt>")
            }
            "text" | "mathrm" | "operatorname" | "mathit" => {
                let raw = self.raw_group();
                format!("<mtext>{}</mtext>", esc(&raw))
            }
            "mathbb" => {
                let raw = self.raw_group();
                let mapped: String = raw
                    .chars()
                    .map(|ch| match ch {
                        'N' => '\u{2115}',
                        'Z' => '\u{2124}',
                        'Q' => '\u{211A}',
                        'R' => '\u{211D}',
                        'C' => '\u{2102}',
                        'F' => '\u{1D53D}',
                        other => other,
                    })
                    .collect();
                format!("<mi>{}</mi>", esc(&mapped))
            }
            _ => {
                if let Some(g) = greek(&name) {
                    return format!("<mi>{}</mi>", esc(g));
                }
                if let Some((g, kind)) = operator(&name) {
                    return match kind {
                        OpKind::Op => format!("<mo>{}</mo>", esc(g)),
                        OpKind::Fence => format!("<mo stretchy=\"false\">{}</mo>", esc(g)),
                        OpKind::Big => format!("<mo movablelimits=\"true\">{}</mo>", esc(g)),
                        OpKind::Fun => format!("<mi>{}</mi>", esc(g)),
                    };
                }
                self.ok = false;
                format!("<merror><mtext>\\{}</mtext></merror>", esc(&name))
            }
        }
    }

    /// Contents of a `{...}` group as literal text (for `\text` and friends).
    fn raw_group(&mut self) -> String {
        while self.peek() == Some(b' ') {
            self.i += 1;
        }
        if self.peek() != Some(b'{') {
            let a = self.atom();
            // Strip tags: this path is rare (`\text x`) and must not nest.
            return strip_tags(&a);
        }
        self.i += 1;
        let start = self.i;
        let mut depth = 1;
        while let Some(c) = self.peek() {
            if c == b'{' {
                depth += 1;
            } else if c == b'}' {
                depth -= 1;
                if depth == 0 {
                    break;
                }
            }
            self.i += 1;
        }
        let out = String::from_utf8_lossy(&self.b[start..self.i]).to_string();
        if self.peek() == Some(b'}') {
            self.i += 1;
        } else {
            self.ok = false;
        }
        out
    }
}

fn strip_tags(s: &str) -> String {
    let mut out = String::new();
    let mut inside = false;
    for c in s.chars() {
        match c {
            '<' => inside = true,
            '>' => inside = false,
            _ if !inside => out.push(c),
            _ => {}
        }
    }
    out
}

enum OpKind {
    Op,
    Fence,
    Big,
    Fun,
}

fn greek(name: &str) -> Option<&'static str> {
    Some(match name {
        "alpha" => "\u{3b1}",
        "beta" => "\u{3b2}",
        "gamma" => "\u{3b3}",
        "delta" => "\u{3b4}",
        "epsilon" | "varepsilon" => "\u{3b5}",
        "zeta" => "\u{3b6}",
        "eta" => "\u{3b7}",
        "theta" => "\u{3b8}",
        "iota" => "\u{3b9}",
        "kappa" => "\u{3ba}",
        "lambda" => "\u{3bb}",
        "mu" => "\u{3bc}",
        "nu" => "\u{3bd}",
        "xi" => "\u{3be}",
        "pi" => "\u{3c0}",
        "rho" => "\u{3c1}",
        "sigma" => "\u{3c3}",
        "tau" => "\u{3c4}",
        "phi" => "\u{3c6}",
        "varphi" => "\u{3d5}",
        "chi" => "\u{3c7}",
        "psi" => "\u{3c8}",
        "omega" => "\u{3c9}",
        "Gamma" => "\u{393}",
        "Delta" => "\u{394}",
        "Theta" => "\u{398}",
        "Lambda" => "\u{39b}",
        "Xi" => "\u{39e}",
        "Pi" => "\u{3a0}",
        "Sigma" => "\u{3a3}",
        "Phi" => "\u{3a6}",
        "Psi" => "\u{3a8}",
        "Omega" => "\u{3a9}",
        _ => return None,
    })
}

fn operator(name: &str) -> Option<(&'static str, OpKind)> {
    Some(match name {
        // relations
        "le" | "leq" => ("\u{2264}", OpKind::Op),
        "ge" | "geq" => ("\u{2265}", OpKind::Op),
        "ne" | "neq" => ("\u{2260}", OpKind::Op),
        "equiv" => ("\u{2261}", OpKind::Op),
        "approx" => ("\u{2248}", OpKind::Op),
        "sim" => ("\u{223c}", OpKind::Op),
        "ll" => ("\u{226a}", OpKind::Op),
        "gg" => ("\u{226b}", OpKind::Op),
        "mid" => ("\u{2223}", OpKind::Op),
        "nmid" => ("\u{2224}", OpKind::Op),
        "in" => ("\u{2208}", OpKind::Op),
        "notin" => ("\u{2209}", OpKind::Op),
        "subseteq" => ("\u{2286}", OpKind::Op),
        "subset" => ("\u{2282}", OpKind::Op),
        "propto" => ("\u{221d}", OpKind::Op),
        // binary
        "cdot" => ("\u{22c5}", OpKind::Op),
        "times" => ("\u{d7}", OpKind::Op),
        "div" => ("\u{f7}", OpKind::Op),
        "pm" => ("\u{b1}", OpKind::Op),
        "mp" => ("\u{2213}", OpKind::Op),
        "cup" => ("\u{222a}", OpKind::Op),
        "cap" => ("\u{2229}", OpKind::Op),
        "oplus" => ("\u{2295}", OpKind::Op),
        "otimes" => ("\u{2297}", OpKind::Op),
        // arrows and logic
        "to" | "rightarrow" => ("\u{2192}", OpKind::Op),
        "mapsto" => ("\u{21a6}", OpKind::Op),
        "implies" | "Rightarrow" => ("\u{21d2}", OpKind::Op),
        "iff" | "Leftrightarrow" => ("\u{21d4}", OpKind::Op),
        "land" | "wedge" => ("\u{2227}", OpKind::Op),
        "lor" | "vee" => ("\u{2228}", OpKind::Op),
        "neg" | "lnot" => ("\u{ac}", OpKind::Op),
        "forall" => ("\u{2200}", OpKind::Op),
        "exists" => ("\u{2203}", OpKind::Op),
        "vdash" => ("\u{22a2}", OpKind::Op),
        "models" => ("\u{22a8}", OpKind::Op),
        "bot" => ("\u{22a5}", OpKind::Op),
        "top" => ("\u{22a4}", OpKind::Op),
        // fences (deliberately non-stretchy: without a MATH-table font,
        // stretchy operators silently fail to grow -- see 07-r-notes R-b)
        "lfloor" => ("\u{230a}", OpKind::Fence),
        "rfloor" => ("\u{230b}", OpKind::Fence),
        "lceil" => ("\u{2308}", OpKind::Fence),
        "rceil" => ("\u{2309}", OpKind::Fence),
        "langle" => ("\u{27e8}", OpKind::Fence),
        "rangle" => ("\u{27e9}", OpKind::Fence),
        "lvert" | "rvert" | "vert" => ("\u{7c}", OpKind::Fence),
        // large operators
        "sum" => ("\u{2211}", OpKind::Big),
        "prod" => ("\u{220f}", OpKind::Big),
        "int" => ("\u{222b}", OpKind::Big),
        "bigcup" => ("\u{22c3}", OpKind::Big),
        "bigcap" => ("\u{22c2}", OpKind::Big),
        // named functions and misc symbols
        "gcd" => ("gcd", OpKind::Fun),
        "lcm" => ("lcm", OpKind::Fun),
        "min" => ("min", OpKind::Fun),
        "max" => ("max", OpKind::Fun),
        "log" => ("log", OpKind::Fun),
        "deg" => ("deg", OpKind::Fun),
        "bmod" => ("mod", OpKind::Fun),
        "infty" => ("\u{221e}", OpKind::Op),
        "emptyset" => ("\u{2205}", OpKind::Op),
        "partial" => ("\u{2202}", OpKind::Op),
        "ldots" | "dots" => ("\u{2026}", OpKind::Op),
        "cdots" => ("\u{22ef}", OpKind::Op),
        _ => return None,
    })
}

// ---------------------------------------------------------------------------
// inline rich text
// ---------------------------------------------------------------------------

/// The inline markup accepted in `Prose` and in statement text.
///
/// Deliberately tiny and fully enumerated: `` `code` ``, `$math$`, `**strong**`,
/// `*emphasis*`, `[label](#anchor)` and `[label](https://...)`. Everything else
/// is escaped literal text. There is no HTML passthrough -- a producer cannot
/// smuggle markup, and therefore cannot smuggle a network request, through a
/// prose block.
pub fn inline(src: &str) -> String {
    let b = src.as_bytes();
    let mut out = String::with_capacity(src.len() + 16);
    let mut i = 0usize;
    while i < b.len() {
        match b[i] {
            b'`' => {
                if let Some(j) = find(b, i + 1, b'`') {
                    let _ = write!(out, "<code>{}</code>", esc(&src[i + 1..j]));
                    i = j + 1;
                    continue;
                }
            }
            b'$' => {
                if let Some(j) = find(b, i + 1, b'$') {
                    let (m, _ok) = latex_to_mathml(&src[i + 1..j]);
                    out.push_str(&m);
                    i = j + 1;
                    continue;
                }
            }
            // Emphasis, with CommonMark's flanking rule in miniature. Without
            // it, `m*mn + n*nn` -- a real statement from the ledger -- renders
            // as italics and the multiplications VANISH. A renderer that can
            // silently delete an operator from a theorem is the exact failure
            // this strand exists to prevent, so the rule is: an opening `*`
            // must not follow an alphanumeric, and the run must close at a
            // word boundary.
            b'*' if i == 0 || !b[i - 1].is_ascii_alphanumeric() => {
                let strong = b.get(i + 1) == Some(&b'*');
                let (open, close, marker_len) = if strong {
                    ("<strong>", "</strong>", 2)
                } else {
                    ("<em>", "</em>", 1)
                };
                let needle = if strong { "**" } else { "*" };
                if let Some(rel) = src[i + marker_len..]
                    .match_indices(needle)
                    .map(|(k, _)| k)
                    .find(|&k| {
                        let j = i + marker_len + k;
                        j > i + marker_len
                            && !b[j - 1].is_ascii_whitespace()
                            && b.get(j + marker_len)
                                .is_none_or(|c| !c.is_ascii_alphanumeric())
                    })
                {
                    let j = i + marker_len + rel;
                    out.push_str(open);
                    out.push_str(&inline(&src[i + marker_len..j]));
                    out.push_str(close);
                    i = j + marker_len;
                    continue;
                }
            }
            b'-' if b.get(i + 1) == Some(&b'-')
                && b.get(i + 2) != Some(&b'-')
                && (i == 0 || b[i - 1] != b'-') =>
            {
                // The single piece of smart punctuation, and it earns its place
                // because the source files are ASCII by rule: `--` is the only
                // way to write an em dash in them, and rendering it literally
                // puts a line-breaking double hyphen mid-sentence.
                out.push_str("&#x2014;");
                i += 2;
                continue;
            }
            b'[' => {
                if let Some(close) = find(b, i + 1, b']')
                    && b.get(close + 1) == Some(&b'(')
                    && let Some(end) = find(b, close + 2, b')')
                {
                    let label = &src[i + 1..close];
                    let target = &src[close + 2..end];
                    out.push_str(&link(label, target));
                    i = end + 1;
                    continue;
                }
            }
            _ => {}
        }
        // Default: one escaped character. `i` always sits on a char boundary
        // (every branch above advances past a whole ASCII delimiter), so this
        // cannot be empty; the `else` is a total fallback rather than a panic.
        let Some(ch) = src[i..].chars().next() else {
            break;
        };
        out.push_str(&esc(&ch.to_string()));
        i += ch.len_utf8();
    }
    out
}

fn find(b: &[u8], from: usize, needle: u8) -> Option<usize> {
    (from..b.len()).find(|&k| b[k] == needle)
}

/// Render a link. External (`http`/`https`) links carry `data-external="1"`,
/// which is the ONLY construct [`lint_self_contained`] accepts an absolute URL
/// inside -- it marks a link the reader must click, never a resource the page
/// fetches on load.
fn link(label: &str, target: &str) -> String {
    let external = target.starts_with("http://") || target.starts_with("https://");
    if external {
        format!(
            "<a data-external=\"1\" class=\"ext\" rel=\"noopener noreferrer\" href=\"{}\">{}</a>",
            esc_attr(target),
            inline(label)
        )
    } else if target.starts_with('#') || target.starts_with("mailto:") {
        format!("<a href=\"{}\">{}</a>", esc_attr(target), inline(label))
    } else {
        // A repo-relative path is shown as text, not as a link: a file:// or
        // relative href in a single-file document is a dead link by
        // construction, and a dead link that looks live is a small lie.
        format!("{} (<code>{}</code>)", inline(label), esc(target))
    }
}

// ---------------------------------------------------------------------------
// status badges: colour AND shape
// ---------------------------------------------------------------------------

/// Every status the ledger and this strand can carry, mapped to a CSS class
/// and a distinct SHAPE. The shape is not decoration: it is what keeps the
/// badge readable in greyscale print and for a colour-blind reader, which
/// `05-html-interactivity.md` requires.
///
/// Unknown status strings are rendered verbatim with the neutral `unknown`
/// styling -- the emitter never maps an unrecognised status onto a known one,
/// because silently upgrading `sat-unchecked` to `checked` is precisely the
/// class of lie the fail-closed law exists to stop.
fn badge_shape(status: &str) -> (&'static str, &'static str) {
    // (css slug, inline svg path in a 16x16 box)
    match status {
        // a shield: the kernel checked it
        "proved" => (
            "proved",
            "M8 1l6 2.4v4.2c0 3.6-2.5 6.4-6 7.4-3.5-1-6-3.8-6-7.4V3.4L8 1z",
        ),
        // a double tick: independently replayed
        "checked" => (
            "checked",
            "M1 8.5l3 3 5-6 1.6 1.4-6.6 7.6L0 10zM9 8.5l1.4-1.6L11.8 8 15 4l1.2 1.4L11.8 11z",
        ),
        // a filled square grid: finite computation
        "evidence" => ("evidence", "M1 1h6v6H1zM9 9h6v6H9zM9 1h6v6H9zM1 9h6v6H1z"),
        // a triangle: computed here
        "computed" => ("computed", "M8 1l7 13H1z"),
        // a hexagon: measured, not proved
        "empirical" => ("empirical", "M8 1l6 3.5v7L8 15l-6-3.5v-7z"),
        // a tilde bar: non-comparable run
        "advisory" => (
            "advisory",
            "M1 6c2-3 4 3 6 0s4-3 6 0v3c-2 3-4-3-6 0s-4 3-6 0z",
        ),
        // an open diamond: believed, unproved
        "conjectured" => (
            "conjectured",
            "M8 1l7 7-7 7-7-7zm0 2.8L3.8 8 8 12.2 12.2 8z",
        ),
        // a cross: witness against
        "refuted" => (
            "refuted",
            "M2.6 1L8 6.4 13.4 1 15 2.6 9.6 8 15 13.4 13.4 15 8 9.6 2.6 15 1 13.4 6.4 8 1 2.6z",
        ),
        // a hollow ring: nothing established
        "open" => (
            "open",
            "M8 1a7 7 0 100 14A7 7 0 008 1zm0 2.4A4.6 4.6 0 118 12.6 4.6 4.6 0 018 3.4z",
        ),
        // a pinned bar: asserted, not derived
        "axiom" => ("axiom", "M2 2h12v3H2zm4.5 4h3v8h-3z"),
        _ => (
            "unknown",
            "M8 2a6 6 0 016 6 6 6 0 01-6 6 6 6 0 01-6-6 6 6 0 016-6zm-1 3v6h2V5z",
        ),
    }
}

/// A status badge.
///
/// The visible text is the UPPERCASE status token, identical in every emitter:
/// `lib.rs` contract point 5 requires the cross-format test to recover the
/// exact token from the bytes, so a lowercase or prettified rendering here
/// would silently break the property that the three formats say the same thing.
pub fn badge(status: &str, label: Option<&str>) -> String {
    let (slug, path) = badge_shape(status);
    let upper = status.to_ascii_uppercase();
    let text = label.unwrap_or(&upper);
    format!(
        "<span class=\"badge badge-{slug}\"><svg viewBox=\"0 0 16 16\" aria-hidden=\"true\" focusable=\"false\"><path d=\"{path}\"/></svg>{}</span>",
        esc(text)
    )
}

/// The two-axis presentation from `fact.schema.json`: what WE established next
/// to what mathematics knows. Rendering them together is the point -- their
/// disagreement in our favour is a new result, and the emitter marks it.
fn status_axes(epistemic: &str, external: Option<&str>) -> String {
    let mut out = String::from("<span class=\"ax-axes\">");
    out.push_str("<span class=\"ax-axis-label\">here</span>");
    out.push_str(&badge(epistemic, None));
    if let Some(ext) = external {
        out.push_str("<span class=\"ax-axis-label\">literature</span>");
        out.push_str(&badge(ext, None));
        if is_established(epistemic) && !is_established(ext) {
            out.push_str(
                "<span class=\"ax-newresult\" title=\"established here, not in the literature\">new result</span>",
            );
        }
    }
    out.push_str("</span>");
    out
}

fn is_established(status: &str) -> bool {
    matches!(status, "proved" | "computed" | "refuted" | "checked")
}

// ---------------------------------------------------------------------------
// page furniture
// ---------------------------------------------------------------------------

fn header(out: &mut String, meta: &Value, opts: &HtmlOptions) {
    out.push_str("<header class=\"ax-head\"><div class=\"ax-doc\">\n");
    if let Some(k) = s(meta, "kicker") {
        let _ = writeln!(out, "<p class=\"ax-kicker\">{}</p>", esc(k));
    }
    let _ = writeln!(
        out,
        "<h1 class=\"ax-title\">{}</h1>",
        inline(s(meta, "title").unwrap_or("Untitled document"))
    );
    if let Some(sub) = s(meta, "subtitle") {
        let _ = writeln!(out, "<p class=\"ax-subtitle\">{}</p>", inline(sub));
    }
    out.push_str("<ul class=\"ax-meta\">\n");
    for (key, label) in [
        ("doc_id", "document"),
        ("genre", "genre"),
        ("generator", "generated by"),
        ("source", "source"),
    ] {
        if let Some(v) = s(meta, key) {
            let _ = writeln!(out, "<li><b>{}</b> {}</li>", esc(label), inline(v));
        }
    }
    if let Some(e) = opts.epoch.as_deref().or_else(|| s(meta, "epoch")) {
        let _ = writeln!(out, "<li><b>epoch</b> <code>{}</code></li>", esc(e));
    }
    out.push_str("</ul>\n");
    out.push_str(
        "<p style=\"margin-top:var(--sp-4)\"><span class=\"ax-levelnote\">reading level</span> \
<span class=\"ax-levels\" role=\"group\" aria-label=\"reading level\">\
<button type=\"button\" data-level=\"summary\" aria-pressed=\"false\">summary</button>\
<button type=\"button\" data-level=\"full\" aria-pressed=\"true\">full</button>\
<button type=\"button\" data-level=\"forensic\" aria-pressed=\"false\">forensic</button>\
</span></p>\n",
    );
    out.push_str("</div></header>\n");
}

fn footer(out: &mut String, meta: &Value, opts: &HtmlOptions, diags: &[String]) {
    out.push_str("<footer class=\"ax-foot\"><div class=\"ax-doc\">\n");
    if !diags.is_empty() {
        out.push_str("<div class=\"ax-unrenderable\"><b>emitter diagnostics</b><ul>");
        for d in diags {
            let _ = write!(out, "<li>{}</li>", esc(d));
        }
        out.push_str("</ul></div>\n");
    }
    out.push_str(
        "<p>This file is self-contained: it embeds its own stylesheet, script and figures \
and makes no network request when opened. Every status badge above is data carried by the \
document, not a judgement made while rendering it.</p>\n",
    );
    if let Some(e) = opts.epoch.as_deref().or_else(|| s(meta, "epoch")) {
        let _ = writeln!(
            out,
            "<p>Build epoch <code>{}</code>. No wall clock was read.</p>",
            esc(e)
        );
    }
    if let Some(n) = s(meta, "footer_note") {
        let _ = writeln!(out, "<p>{}</p>", inline(n));
    }
    out.push_str("</div></footer>\n");
}

// ---------------------------------------------------------------------------
// block dispatch
// ---------------------------------------------------------------------------

/// Resolve a block's kind, accepting both serde enum encodings.
fn kind_of(block: &Value) -> Option<(String, Value)> {
    match block.get("kind") {
        Some(Value::String(name)) => Some((name.to_ascii_lowercase(), block.clone())),
        Some(Value::Object(map)) if map.len() == 1 => {
            let (k, v) = map.iter().next()?;
            Some((k.to_ascii_lowercase(), v.clone()))
        }
        _ => None,
    }
}

fn tag_class(block: &Value) -> &'static str {
    match block
        .get("tag")
        .and_then(|t| t.as_str())
        .unwrap_or("essential")
        .to_ascii_lowercase()
        .as_str()
    {
        "detail" => "t-detail",
        "archive" => "t-archive",
        _ => "t-essential",
    }
}

fn block(out: &mut String, b: &Value, idx: usize, diags: &mut Vec<String>) {
    let id = s(b, "id").map_or_else(|| format!("b{idx}"), slug);
    let tag = tag_class(b);
    let Some((kind, body)) = kind_of(b) else {
        diags.push(format!("block {idx} ({id}): missing or malformed `kind`"));
        let _ = write!(
            out,
            "<div class=\"ax-unrenderable\">block <code>{}</code>: missing or malformed <code>kind</code></div>",
            esc(&id)
        );
        return;
    };
    match kind.as_str() {
        "prose" => prose(out, &body, &id, tag),
        "claim" => claim(out, &body, &id, tag, diags),
        "statement" => statement(out, &body, &id, tag),
        "steps" => steps(out, &body, &id, tag),
        "table" => table(out, &body, &id, tag),
        "certificate" => certificate(out, &body, &id, tag, diags),
        "figure" => figure(out, &body, &id, tag, diags),
        "include" => include_block(out, &body, &id),
        other => {
            diags.push(format!("block {idx} ({id}): unknown kind `{other}`"));
            let _ = write!(
                out,
                "<div class=\"ax-unrenderable\">block <code>{}</code>: unknown kind <code>{}</code>. \
Nothing was rendered for it; the document is incomplete.</div>",
                esc(&id),
                esc(other)
            );
        }
    }
    if let Some(p) = b.get("provenance").filter(|p| p.is_object()) {
        provenance_line(out, p);
    }
}

fn provenance_line(out: &mut String, p: &Value) {
    let mut bits: Vec<String> = Vec::new();
    if let Some(g) = s(p, "generator") {
        bits.push(format!("generated by <code>{}</code>", esc(g)));
    }
    if let Some(c) = s(p, "command") {
        bits.push(format!("<code>{}</code>", esc(c)));
    }
    if let Some(x) = p.get("exit_status").and_then(serde_json::Value::as_i64) {
        let cls = if x == 0 { "ax-exit-ok" } else { "ax-exit-bad" };
        bits.push(format!("exit <span class=\"{cls}\">{x}</span>"));
    }
    if bits.is_empty() {
        return;
    }
    let _ = writeln!(
        out,
        "<p class=\"ax-source\">{}</p>",
        bits.join(" &middot; ")
    );
}

// ---------------------------------------------------------------------------
// blocks
// ---------------------------------------------------------------------------

fn heading_of(v: &Value, out: &mut String) {
    if let Some(h) = s(v, "heading") {
        let level = v
            .get("level")
            .and_then(serde_json::Value::as_u64)
            .unwrap_or(2)
            .clamp(2, 4);
        let _ = writeln!(
            out,
            "<h{level} id=\"{}\">{}</h{level}>",
            esc_attr(&slug(h)),
            inline(h)
        );
    }
}

fn prose(out: &mut String, v: &Value, id: &str, tag: &str) {
    let text = match v {
        Value::String(t) => t.clone(),
        _ => s(v, "text").unwrap_or_default().to_string(),
    };
    let _ = writeln!(
        out,
        "<section class=\"blk prose {tag}\" id=\"{}\">",
        esc_attr(id)
    );
    heading_of(v, out);
    for para in text.split("\n\n") {
        let para = para.trim();
        if para.is_empty() {
            continue;
        }
        let _ = writeln!(out, "<p>{}</p>", inline(para));
    }
    out.push_str("</section>\n");
}

fn statement(out: &mut String, v: &Value, id: &str, tag: &str) {
    let status = s(v, "status").unwrap_or("open");
    let _ = write!(
        out,
        "<article class=\"card blk {tag} s-{}\" id=\"{}\">\n<div class=\"card-head\">",
        esc_attr(badge_shape(status).0),
        esc_attr(id)
    );
    let _ = write!(
        out,
        "<h3>{}</h3>",
        inline(s(v, "title").unwrap_or("Statement"))
    );
    out.push_str(&status_axes(status, s(v, "external_status")));
    out.push_str("</div>\n");
    if let Some(r) = s(v, "ref") {
        let _ = writeln!(out, "<p class=\"card-id\">{}</p>", esc(r));
    }
    if let Some(st) = s(v, "statement") {
        let _ = writeln!(out, "<p class=\"card-statement\">{}</p>", inline(st));
    }
    formal_block(out, v);
    out.push_str("</article>\n");
}

/// The machine-readable statement. Rendered as `<pre>`, never as math: a Lean
/// core type or an SMT-LIB assertion is the exact text the kernel checked, and
/// prettifying it would put a second, unchecked rendering of the proposition
/// on the page.
fn formal_block(out: &mut String, v: &Value) {
    let f = match v.get("formal") {
        Some(f) if f.is_object() => f,
        _ => return,
    };
    let lang = s(f, "language").unwrap_or("formal");
    let Some(stmt) = s(f, "statement") else {
        return;
    };
    let _ = writeln!(
        out,
        "<div class=\"card-formal\"><p class=\"ax-tinylabel\">formal statement &middot; {}{}</p><pre><code>{}</code></pre></div>",
        esc(lang),
        s(f, "fragment")
            .map(|x| format!(" &middot; {}", esc(x)))
            .unwrap_or_default(),
        esc(stmt)
    );
}

fn claim(out: &mut String, v: &Value, id: &str, tag: &str, diags: &mut Vec<String>) {
    let status = s(v, "status")
        .or_else(|| s(v, "epistemic_status"))
        .unwrap_or("open");
    let evidence = arr(v, "evidence");

    // Defensive audit. Assembly is the authority on the fail-closed law; this
    // is a second, independent statement of the same rule, and it can only
    // ever make the page LOUDER -- it never upgrades anything.
    let mut alarms: Vec<String> = Vec::new();
    if is_established(status) && evidence.is_empty() {
        alarms.push(format!(
            "status `{status}` with no evidence reference: the fail-closed law forbids this"
        ));
    }
    for e in evidence {
        if let Some(x) = e.get("exit_status").and_then(serde_json::Value::as_i64)
            && x != 0
            && is_established(status)
        {
            alarms.push(format!(
                "evidence `{}` exited {x} but the claim renders as `{status}`",
                s(e, "id").unwrap_or("?")
            ));
        }
    }
    for a in &alarms {
        diags.push(format!("claim {id}: {a}"));
    }

    let label = s(v, "label").or(s(v, "title")).unwrap_or("Claim");
    // `data-claim` / `data-status` is the machine-recoverable pairing that
    // `lib.rs` contract point 5 requires, carrying the exact uppercase badge
    // token. The cross-format test reads it out of the BYTES, so a claim this
    // emitter quietly dropped is a failing test rather than a shorter page.
    let _ = write!(
        out,
        "<article class=\"card blk {tag} s-{}\" id=\"{}\" data-claim=\"{}\" data-status=\"{}\">\n<div class=\"card-head\">",
        badge_shape(status).0,
        esc_attr(id),
        esc_attr(label),
        esc_attr(&status.to_ascii_uppercase())
    );
    let _ = write!(out, "<h3>{}</h3>", inline(label));
    out.push_str(&status_axes(status, s(v, "external_status")));
    out.push_str("</div>\n");
    if let Some(r) = s(v, "ref").or(s(v, "fact_id")) {
        let _ = writeln!(out, "<p class=\"card-id\">{}</p>", esc(r));
    }
    if let Some(st) = s(v, "statement") {
        let _ = writeln!(out, "<p class=\"card-statement\">{}</p>", inline(st));
    }
    formal_block(out, v);
    for a in &alarms {
        let _ = writeln!(out, "<p class=\"ax-unrenderable\">{}</p>", esc(a));
    }
    if let Some(route) = s(v, "proof_route") {
        let _ = writeln!(
            out,
            "<p class=\"ax-source\">proof route <code>{}</code>{}</p>",
            esc(route),
            axiom_footprint(v)
        );
    }
    if evidence.is_empty() {
        out.push_str(
            "<p class=\"ax-noevidence\">No evidence is attached. Nothing here has been \
established by this system; the status above says exactly that.</p>\n",
        );
    } else {
        out.push_str("<p class=\"ax-tinylabel\">evidence</p>\n<ul class=\"ax-evidence\">\n");
        for (i, e) in evidence.iter().enumerate() {
            evidence_row(out, e, &format!("{id}-ev{i}"));
        }
        out.push_str("</ul>\n");
    }
    if let Some(n) = s(v, "notes") {
        let _ = writeln!(
            out,
            "<details class=\"ax-fold t-detail\"><summary>note</summary><div class=\"ax-foldbody\">{}</div></details>",
            note_paragraphs(n)
        );
    }
    out.push_str("</article>\n");
}

/// The axiom footprint, rendered so `[]` is unmistakably a claim and not an
/// omission -- the ledger's own distinction, and the metric this project
/// publishes.
fn axiom_footprint(v: &Value) -> String {
    match v.get("axiom_footprint") {
        Some(Value::Array(a)) if a.is_empty() => {
            " &middot; axiom footprint <b>empty</b> (axiom-free)".to_string()
        }
        Some(Value::Array(a)) => {
            let names: Vec<String> = a
                .iter()
                .map(|x| format!("<code>{}</code>", esc(&text_of(x))))
                .collect();
            format!(" &middot; rests on {}", names.join(", "))
        }
        _ => String::new(),
    }
}

fn note_paragraphs(n: &str) -> String {
    let mut out = String::new();
    for para in n.split("\n\n") {
        let para = para.trim();
        if !para.is_empty() {
            let _ = write!(out, "<p>{}</p>", inline(para));
        }
    }
    out
}

fn evidence_row(out: &mut String, e: &Value, id: &str) {
    let check = s(e, "check_status").unwrap_or("open");
    out.push_str("<li>\n<div class=\"ax-ev-head\">");
    out.push_str(&badge(check, None));
    if let Some(k) = s(e, "kind") {
        let _ = write!(out, "<span class=\"ax-ev-kind\">{}</span>", esc(k));
    }
    if let Some(i) = s(e, "id") {
        let _ = write!(out, "<span class=\"ax-ev-kind\">{}</span>", esc(i));
    }
    if let Some(x) = e.get("exit_status").and_then(serde_json::Value::as_i64) {
        let cls = if x == 0 { "ax-exit-ok" } else { "ax-exit-bad" };
        let _ = write!(out, "<span class=\"{cls}\">exit {x}</span>");
    }
    out.push_str("</div>\n");
    if let Some(sup) = s(e, "supports") {
        let _ = writeln!(out, "<p class=\"ax-ev-supports\">{}</p>", inline(sup));
    }
    if let Some(cmd) = s(e, "checker_command") {
        command_box(out, cmd, &format!("{id}-cmd"), "copy");
    }
    let checkers = arr(e, "checkers");
    if !checkers.is_empty() {
        let names: Vec<String> = checkers
            .iter()
            .map(|c| format!("<code>{}</code>", esc(&text_of(c))))
            .collect();
        let _ = writeln!(
            out,
            "<p class=\"ax-source\">checked by {}</p>",
            names.join(", ")
        );
    }
    if let Some(a) = s(e, "artifact") {
        let _ = writeln!(
            out,
            "<p class=\"ax-source\">artifact <code>{}</code></p>",
            esc(a)
        );
    }
    if let Some(n) = s(e, "notes") {
        let _ = writeln!(
            out,
            "<details class=\"ax-fold t-detail\"><summary>why this counts</summary><div class=\"ax-foldbody\">{}</div></details>",
            note_paragraphs(n)
        );
    }
    out.push_str("</li>\n");
}

/// A command with a copy button. The button is progressive enhancement: with
/// JavaScript off the command is still plain selectable text.
fn command_box(out: &mut String, cmd: &str, id: &str, label: &str) {
    let _ = writeln!(
        out,
        "<div class=\"ax-cmd\"><code id=\"{}\">{}</code><button type=\"button\" data-copy-target=\"{}\">{}</button></div>",
        esc_attr(id),
        esc(cmd),
        esc_attr(id),
        esc(label)
    );
}

fn steps(out: &mut String, v: &Value, id: &str, tag: &str) {
    let items = if v.get("steps").is_some() {
        arr(v, "steps")
    } else {
        arr(v, "items")
    };
    let _ = writeln!(out, "<section class=\"blk {tag}\" id=\"{}\">", esc_attr(id));
    heading_of(v, out);
    if let Some(c) = s(v, "caption") {
        let _ = writeln!(out, "<p>{}</p>", inline(c));
    }
    out.push_str(
        "<div class=\"ax-stepbar\"><button type=\"button\" data-step=\"prev\">prev</button>\
<button type=\"button\" data-step=\"next\">next</button>\
<span>or press <kbd>j</kbd> / <kbd>k</kbd> with the list focused</span></div>\n",
    );
    out.push_str("<ol class=\"ax-steps\">\n");
    for st in items {
        out.push_str("<li><div>\n");
        if let Some(op) = s(st, "op") {
            let _ = writeln!(out, "<div class=\"ax-step-op\">{}</div>", esc(op));
        }
        if let Some(i) = s(st, "input") {
            let _ = writeln!(out, "<div class=\"ax-step-io\">{}</div>", esc(i));
        }
        if let Some(o) = s(st, "output") {
            let _ = writeln!(out, "<div class=\"ax-step-io\">&rarr; {}</div>", esc(o));
        }
        if let Some(n) = s(st, "note") {
            let _ = writeln!(out, "<div class=\"ax-step-note\">{}</div>", inline(n));
        }
        out.push_str("</div></li>\n");
    }
    out.push_str("</ol>\n</section>\n");
}

fn table(out: &mut String, v: &Value, id: &str, tag: &str) {
    let cols = arr(v, "columns");
    let rows = arr(v, "rows");
    let _ = writeln!(out, "<section class=\"blk {tag}\" id=\"{}\">", esc_attr(id));
    heading_of(v, out);
    out.push_str("<div class=\"ax-tablewrap\"><table class=\"ax-table\">\n");
    if let Some(c) = s(v, "caption") {
        let _ = writeln!(out, "<caption>{}</caption>", inline(c));
    }
    let aligns: Vec<&str> = cols
        .iter()
        .map(|c| match c {
            Value::String(_) => "",
            _ => match s(c, "align") {
                Some("right" | "num") => "num",
                _ => "",
            },
        })
        .collect();
    if !cols.is_empty() {
        out.push_str("<thead><tr>");
        for (i, c) in cols.iter().enumerate() {
            let label = match c {
                Value::String(x) => x.clone(),
                _ => s(c, "label").unwrap_or("").to_string(),
            };
            let _ = write!(out, "<th class=\"{}\">{}</th>", aligns[i], inline(&label));
        }
        out.push_str("</tr></thead>\n");
    }
    out.push_str("<tbody>\n");
    for r in rows {
        out.push_str("<tr>");
        if let Some(cells) = r.as_array() {
            for (i, cell) in cells.iter().enumerate() {
                let a = aligns.get(i).copied().unwrap_or("");
                let a = if a.is_empty() && cell.is_number() {
                    "num"
                } else {
                    a
                };
                let _ = write!(out, "<td class=\"{a}\">{}</td>", inline(&text_of(cell)));
            }
        }
        out.push_str("</tr>\n");
    }
    out.push_str("</tbody>\n</table></div>\n");
    if let Some(src) = v.get("source").filter(|p| p.is_object()) {
        provenance_line(out, src);
    }
    out.push_str("</section>\n");
}

fn certificate(out: &mut String, v: &Value, id: &str, tag: &str, diags: &mut Vec<String>) {
    let exit = v.get("exit_status").and_then(serde_json::Value::as_i64);
    let verdict = s(v, "verdict").unwrap_or(match exit {
        Some(0) => "checked",
        Some(_) => "refuted",
        None => "open",
    });
    // A certificate CAN legitimately have no exit status -- some are too
    // expensive to re-run per commit, and the honest form of that is a stated
    // reason, not a blank. What is never acceptable is silence: with neither an
    // exit status nor a reason, the box would imply a run that nothing records.
    let no_exit_reason = s(v, "no_exit_reason");
    if exit.is_none() && no_exit_reason.is_none() {
        diags.push(format!(
            "certificate {id}: no `exit_status` and no `no_exit_reason`; a certificate box \
must either carry the status of a run or say why there is none"
        ));
    }
    let _ = write!(
        out,
        "<details class=\"ax-fold card ax-cert blk {tag} s-{}\" id=\"{}\">\n<summary>",
        badge_shape(verdict).0,
        esc_attr(id)
    );
    out.push_str(&badge(verdict, None));
    let _ = write!(
        out,
        "<span>{}</span>",
        inline(s(v, "summary").unwrap_or("certificate"))
    );
    if let Some(x) = exit {
        let cls = if x == 0 { "ax-exit-ok" } else { "ax-exit-bad" };
        let _ = write!(out, "<span class=\"{cls}\">exit {x}</span>");
    } else if let Some(r) = no_exit_reason {
        let _ = write!(
            out,
            "<span class=\"ax-exit-none\">not re-run: {}</span>",
            esc(r)
        );
    } else {
        out.push_str("<span class=\"ax-exit-bad\">exit status missing</span>");
    }
    out.push_str("</summary>\n<div class=\"ax-foldbody\">\n");
    out.push_str("<dl class=\"ax-cert-grid\">\n");
    for (key, label) in [
        ("kind", "kind"),
        ("generator", "generator"),
        ("backend", "backend"),
        ("host", "host"),
    ] {
        if let Some(x) = s(v, key) {
            let _ = writeln!(
                out,
                "<dt>{}</dt><dd><code>{}</code></dd>",
                esc(label),
                esc(x)
            );
        }
    }
    out.push_str("</dl>\n");
    let inputs = arr(v, "inputs");
    if !inputs.is_empty() {
        out.push_str(
            "<p class=\"ax-tinylabel\">inputs, by content hash</p>\n<div class=\"ax-tablewrap\">\
<table class=\"ax-table\"><thead><tr><th>path</th><th>sha256</th></tr></thead><tbody>\n",
        );
        for i in inputs {
            let _ = writeln!(
                out,
                "<tr><td><code>{}</code></td><td class=\"ax-hash\">{}</td></tr>",
                esc(s(i, "path").unwrap_or("?")),
                esc(s(i, "sha256").unwrap_or("?"))
            );
        }
        out.push_str("</tbody></table></div>\n");
    }
    if let Some(cmd) = s(v, "replay").or(s(v, "command")) {
        out.push_str("<p class=\"ax-tinylabel\">replay this yourself</p>\n");
        command_box(out, cmd, &format!("{id}-replay"), "copy");
    }
    if let Some(raw) = v.get("raw").filter(|r| !r.is_null()) {
        let pretty = serde_json::to_string_pretty(raw).unwrap_or_else(|_| raw.to_string());
        let _ = writeln!(
            out,
            "<details class=\"ax-fold t-archive\"><summary>raw run record</summary>\
<div class=\"ax-foldbody\"><pre><code>{}</code></pre></div></details>",
            esc(&pretty)
        );
    }
    out.push_str("</div>\n</details>\n");
}

fn include_block(out: &mut String, v: &Value, id: &str) {
    let path = s(v, "path").unwrap_or("(no path)");
    let _ = writeln!(
        out,
        "<p class=\"blk t-archive\" id=\"{}\">Left out of this document: <code>{}</code>{}</p>",
        esc_attr(id),
        esc(path),
        s(v, "note")
            .map(|n| format!(" &mdash; {}", inline(n)))
            .unwrap_or_default()
    );
}

// ---------------------------------------------------------------------------
// figures
// ---------------------------------------------------------------------------

fn figure(out: &mut String, v: &Value, id: &str, tag: &str, diags: &mut Vec<String>) {
    // Accept `{"Figure": {"DepGraph": {...}}}` and `{"Figure": {"kind": "depgraph", ...}}`.
    let (fkind, spec) = match kind_of(v) {
        Some((k, b)) => (k, b),
        None => match v.as_object() {
            Some(m) if m.len() == 1 => {
                let (k, b) = m.iter().next().unwrap();
                (k.to_ascii_lowercase(), b.clone())
            }
            _ => (String::from("unknown"), v.clone()),
        },
    };
    let wide = matches!(fkind.as_str(), "depgraph" | "plot" | "polygon");
    let _ = write!(
        out,
        "<figure class=\"ax-fig blk {tag}{}\" id=\"{}\">\n<div class=\"ax-figframe\">\n",
        if wide { " ax-wide" } else { "" },
        esc_attr(id)
    );
    match fkind.as_str() {
        "depgraph" => dep_graph(out, &spec, id),
        "plot" | "polygon" => xy_plot(out, &spec, id),
        "svg" => raw_svg(out, &spec, id, diags),
        other => {
            diags.push(format!("figure {id}: unknown figure kind `{other}`"));
            let _ = write!(
                out,
                "<div class=\"ax-unrenderable\">unknown figure kind <code>{}</code></div>",
                esc(other)
            );
        }
    }
    out.push_str("</div>\n");
    if let Some(c) = s(&spec, "caption").or(s(v, "caption")) {
        let _ = writeln!(out, "<figcaption>{}</figcaption>", inline(c));
    }
    out.push_str("</figure>\n");
}

/// Wrap a label onto at most two lines for a graph node box.
fn wrap_label(label: &str, max: usize) -> Vec<String> {
    let mut lines: Vec<String> = Vec::new();
    let mut cur = String::new();
    for w in label.split_whitespace() {
        if cur.is_empty() {
            cur = w.to_string();
        } else if cur.chars().count() + 1 + w.chars().count() <= max {
            cur.push(' ');
            cur.push_str(w);
        } else {
            lines.push(std::mem::take(&mut cur));
            cur = w.to_string();
            if lines.len() == 2 {
                break;
            }
        }
    }
    if lines.len() < 2 && !cur.is_empty() {
        lines.push(cur);
    }
    if lines.is_empty() {
        lines.push(String::new());
    }
    // Anything that did not fit is marked, never silently dropped.
    let shown: usize = lines.iter().map(|l| l.chars().count()).sum::<usize>() + lines.len() - 1;
    if shown < label.chars().count() {
        let last = lines.last_mut().unwrap();
        last.push('~');
    }
    lines
}

/// The atlas dependency graph, as inline SVG laid out by [`crate::layout`].
///
/// An edge `from -> to` reads "`from` is used by `to`", so prerequisites sit
/// above the results that rest on them. Ancestor and descendant sets are baked
/// into `data-` attributes at build time: the hover interaction is a class
/// toggle, not a graph traversal, so the page needs no graph library.
fn dep_graph(out: &mut String, spec: &Value, id: &str) {
    let nodes = arr(spec, "nodes");
    if nodes.is_empty() {
        out.push_str("<p class=\"ax-noevidence\">The graph is empty.</p>");
        return;
    }
    let keys: Vec<String> = nodes
        .iter()
        .enumerate()
        .map(|(i, n)| s(n, "key").unwrap_or(&format!("n{i}")).to_string())
        .collect();
    let index = |k: &str| keys.iter().position(|x| x == k);

    let labels: Vec<Vec<String>> = nodes
        .iter()
        .enumerate()
        .map(|(i, n)| wrap_label(s(n, "label").unwrap_or(&keys[i]), 15))
        .collect();
    let specs: Vec<NodeSpec> = labels
        .iter()
        .enumerate()
        .map(|(i, l)| {
            let widest = l.iter().map(|x| x.chars().count()).max().unwrap_or(1);
            let w = (widest as f64 * 6.4 + 32.0).clamp(78.0, 170.0);
            let h = if l.len() > 1 { 42.0 } else { 30.0 };
            NodeSpec::new(&keys[i], w, h)
        })
        .collect();

    let mut edges: Vec<(usize, usize)> = Vec::new();
    for e in arr(spec, "edges") {
        let pair = match e {
            Value::Array(a) if a.len() == 2 => match (a[0].as_u64(), a[1].as_u64()) {
                (Some(x), Some(y)) => Some((x as usize, y as usize)),
                _ => match (a[0].as_str(), a[1].as_str()) {
                    (Some(x), Some(y)) => index(x).zip(index(y)),
                    _ => None,
                },
            },
            _ => s(e, "from").and_then(index).zip(s(e, "to").and_then(index)),
        };
        if let Some(p) = pair
            && p.0 < nodes.len()
            && p.1 < nodes.len()
        {
            edges.push(p);
        }
    }

    let cfg = LayoutConfig::default();
    let l = layout::layered_layout(&specs, &edges, &cfg);
    let (anc, desc) = layout::reachability(specs.len(), &edges);

    let _ = writeln!(
        out,
        "<svg class=\"ax-graph\" viewBox=\"0 0 {:.0} {:.0}\" width=\"{:.0}\" height=\"{:.0}\" role=\"group\" aria-label=\"{}\">",
        l.width,
        l.height,
        l.width,
        l.height,
        esc_attr(s(spec, "caption").unwrap_or("dependency graph"))
    );
    out.push_str("<g class=\"edges\">\n");
    for e in &l.edges {
        let d = layout::edge_path_d(&e.points);
        let _ = writeln!(
            out,
            "<path class=\"gedge\" data-from=\"{}\" data-to=\"{}\" d=\"{}\"/>",
            e.from, e.to, d
        );
        // Arrowhead drawn as geometry rather than a <marker>, so no shared
        // element id can collide when several graphs land in one document.
        if e.points.len() >= 2 {
            let n = e.points.len();
            let (x1, y1) = e.points[n - 1];
            let (x0, y0) = e.points[n - 2];
            let (dx, dy) = (x1 - x0, y1 - y0);
            let len = (dx * dx + dy * dy).sqrt().max(1e-6);
            let (ux, uy) = (dx / len, dy / len);
            let (px, py) = (-uy, ux);
            let (bx, by) = (x1 - ux * 6.5, y1 - uy * 6.5);
            let _ = writeln!(
                out,
                "<path class=\"gedge\" data-from=\"{}\" data-to=\"{}\" style=\"fill:var(--rule-firm);stroke:none\" d=\"M {:.1} {:.1} L {:.1} {:.1} L {:.1} {:.1} Z\"/>",
                e.from,
                e.to,
                x1,
                y1,
                bx + px * 3.0,
                by + py * 3.0,
                bx - px * 3.0,
                by - py * 3.0
            );
        }
    }
    out.push_str("</g>\n<g class=\"nodes\">\n");
    for p in &l.nodes {
        let n = &nodes[p.index];
        let status = s(n, "status").unwrap_or("open");
        let slug_status = badge_shape(status).0;
        let a: Vec<String> = anc[p.index]
            .iter()
            .map(std::string::ToString::to_string)
            .collect();
        let d: Vec<String> = desc[p.index]
            .iter()
            .map(std::string::ToString::to_string)
            .collect();
        let href = s(n, "href")
            .map(|h| format!(" data-href=\"{}\"", esc_attr(&slug(h))))
            .unwrap_or_default();
        let _ = writeln!(
            out,
            "<g class=\"gnode s-{}\" data-n=\"{}\" data-anc=\"{}\" data-desc=\"{}\"{} tabindex=\"0\" role=\"listitem\">",
            slug_status,
            p.index,
            a.join(" "),
            d.join(" "),
            href
        );
        let _ = writeln!(
            out,
            "<title>{} &#x2014; {} &#x2014; {} upstream, {} downstream</title>",
            esc(s(n, "label").unwrap_or(&keys[p.index])),
            esc(status),
            anc[p.index].len(),
            desc[p.index].len()
        );
        let _ = writeln!(
            out,
            "<rect x=\"{:.1}\" y=\"{:.1}\" width=\"{:.1}\" height=\"{:.1}\"/>",
            p.x(),
            p.y(),
            p.width,
            p.height
        );
        let _ = writeln!(
            out,
            "<circle class=\"gdot\" cx=\"{:.1}\" cy=\"{:.1}\" r=\"3.2\"/>",
            p.x() + 9.0,
            p.cy
        );
        let lines = &labels[p.index];
        let first_dy = if lines.len() > 1 { -6.5 } else { 0.0 };
        for (li, line) in lines.iter().enumerate() {
            let _ = writeln!(
                out,
                "<text x=\"{:.1}\" y=\"{:.1}\">{}</text>",
                p.x() + 17.0,
                p.cy + first_dy + li as f64 * 13.0,
                esc(line)
            );
        }
        out.push_str("</g>\n");
    }
    out.push_str("</g>\n</svg>\n");

    // Legend, from the statuses actually present, in a stable order.
    let mut seen: Vec<&str> = Vec::new();
    for n in nodes {
        let st = s(n, "status").unwrap_or("open");
        if !seen.contains(&st) {
            seen.push(st);
        }
    }
    seen.sort_unstable();
    out.push_str("<ul class=\"ax-legend\">\n");
    for st in seen {
        let _ = writeln!(
            out,
            "<li><span class=\"swatch\" style=\"background:var(--s-{}-fg)\"></span>{}</li>",
            badge_shape(st).0,
            esc(st)
        );
    }
    let _ = writeln!(
        out,
        "<li>{} nodes, {} edges, {} crossings</li>",
        l.nodes.len(),
        l.edges.len(),
        l.crossings
    );
    out.push_str("</ul>\n");
    let _ = writeln!(
        out,
        "<p class=\"ax-source\" id=\"{}-note\">Hover or keyboard-focus a node to isolate its \
cone; press Enter on one that links to a card.</p>",
        esc_attr(id)
    );
}

fn nice_ticks(min: f64, max: f64, want: usize) -> Vec<f64> {
    if max <= min || !(max - min).is_finite() {
        return vec![min];
    }
    let raw = (max - min) / want.max(1) as f64;
    let mag = 10f64.powf(raw.log10().floor());
    let norm = raw / mag;
    let step = if norm <= 1.0 {
        1.0
    } else if norm <= 2.0 {
        2.0
    } else if norm <= 5.0 {
        5.0
    } else {
        10.0
    } * mag;
    let start = (min / step).ceil() * step;
    let mut out = Vec::new();
    let mut t = start;
    while t <= max + step * 1e-6 && out.len() < 24 {
        out.push((t * 1e9).round() / 1e9);
        t += step;
    }
    out
}

fn fmt_num(x: f64) -> String {
    if (x - x.round()).abs() < 1e-9 {
        format!("{}", x.round() as i64)
    } else {
        let s = format!("{x:.3}");
        s.trim_end_matches('0').trim_end_matches('.').to_string()
    }
}

/// A small XY figure: step functions, polylines and closed polygons, with
/// labelled vertices whose tooltip is a native `<title>` (so it works with
/// JavaScript disabled).
fn xy_plot(out: &mut String, spec: &Value, _id: &str) {
    let series = arr(spec, "series");
    let mut pts: Vec<(f64, f64)> = Vec::new();
    for se in series {
        for p in arr(se, "points") {
            if let Some(a) = p.as_array()
                && let (Some(x), Some(y)) = (
                    a.first().and_then(serde_json::Value::as_f64),
                    a.get(1).and_then(serde_json::Value::as_f64),
                )
            {
                pts.push((x, y));
            }
        }
    }
    if pts.is_empty() {
        out.push_str("<p class=\"ax-noevidence\">The plot carries no points.</p>");
        return;
    }
    let (mut x0, mut x1) = (f64::INFINITY, f64::NEG_INFINITY);
    let (mut y0, mut y1) = (f64::INFINITY, f64::NEG_INFINITY);
    for &(x, y) in &pts {
        x0 = x0.min(x);
        x1 = x1.max(x);
        y0 = y0.min(y);
        y1 = y1.max(y);
    }
    for (k, slot) in [
        ("x_min", &mut x0),
        ("x_max", &mut x1),
        ("y_min", &mut y0),
        ("y_max", &mut y1),
    ] {
        if let Some(v) = spec.get(k).and_then(serde_json::Value::as_f64) {
            *slot = v;
        }
    }
    if (x1 - x0).abs() < 1e-12 {
        x1 = x0 + 1.0;
    }
    if (y1 - y0).abs() < 1e-12 {
        y1 = y0 + 1.0;
    }
    let pad_y = (y1 - y0) * 0.08;
    y0 -= pad_y;
    y1 += pad_y;

    let (fig_w, fig_h) = (620.0f64, 320.0f64);
    let (ml, mr, mt, mb) = (56.0f64, 18.0f64, 14.0f64, 44.0f64);
    let pw = fig_w - ml - mr;
    let ph = fig_h - mt - mb;
    let sx = move |x: f64| ml + (x - x0) / (x1 - x0) * pw;
    let sy = move |y: f64| mt + ph - (y - y0) / (y1 - y0) * ph;

    let _ = writeln!(
        out,
        "<svg class=\"ax-plot\" viewBox=\"0 0 {fig_w:.0} {fig_h:.0}\" width=\"{fig_w:.0}\" height=\"{fig_h:.0}\" role=\"group\" aria-label=\"{}\">",
        esc_attr(s(spec, "caption").unwrap_or("plot"))
    );
    for t in nice_ticks(y0, y1, 5) {
        let yy = sy(t);
        let _ = writeln!(
            out,
            "<line class=\"grid\" x1=\"{ml:.1}\" y1=\"{yy:.1}\" x2=\"{:.1}\" y2=\"{yy:.1}\"/>",
            ml + pw
        );
        let _ = writeln!(
            out,
            "<text class=\"tick\" x=\"{:.1}\" y=\"{:.1}\" text-anchor=\"end\">{}</text>",
            ml - 7.0,
            yy + 3.5,
            esc(&fmt_num(t))
        );
    }
    for t in nice_ticks(x0, x1, 6) {
        let xx = sx(t);
        let _ = writeln!(
            out,
            "<text class=\"tick\" x=\"{xx:.1}\" y=\"{:.1}\" text-anchor=\"middle\">{}</text>",
            mt + ph + 18.0,
            esc(&fmt_num(t))
        );
    }
    let _ = writeln!(
        out,
        "<path class=\"axis\" d=\"M {ml:.1} {mt:.1} L {ml:.1} {:.1} L {:.1} {:.1}\"/>",
        mt + ph,
        ml + pw,
        mt + ph
    );
    if let Some(xl) = s(spec, "x_label") {
        let _ = writeln!(
            out,
            "<text class=\"axlabel\" x=\"{:.1}\" y=\"{:.1}\" text-anchor=\"middle\">{}</text>",
            ml + pw / 2.0,
            fig_h - 6.0,
            esc(xl)
        );
    }
    if let Some(yl) = s(spec, "y_label") {
        let _ = writeln!(
            out,
            "<text class=\"axlabel\" x=\"{:.1}\" y=\"{:.1}\" text-anchor=\"middle\" transform=\"rotate(-90 {:.1} {:.1})\">{}</text>",
            13.0,
            mt + ph / 2.0,
            13.0,
            mt + ph / 2.0,
            esc(yl)
        );
    }

    for se in series {
        let kind = s(se, "kind").unwrap_or("line");
        let raw: Vec<(f64, f64)> = arr(se, "points")
            .iter()
            .filter_map(|p| p.as_array())
            .filter_map(|a| Some((a.first()?.as_f64()?, a.get(1)?.as_f64()?)))
            .collect();
        if raw.is_empty() {
            continue;
        }
        let mut d = String::new();
        if kind == "step" {
            let _ = write!(d, "M {:.1} {:.1}", sx(raw[0].0), sy(raw[0].1));
            for wpair in raw.windows(2) {
                let (a, b) = (wpair[0], wpair[1]);
                let _ = write!(
                    d,
                    " L {:.1} {:.1} L {:.1} {:.1}",
                    sx(b.0),
                    sy(a.1),
                    sx(b.0),
                    sy(b.1)
                );
            }
        } else {
            let _ = write!(d, "M {:.1} {:.1}", sx(raw[0].0), sy(raw[0].1));
            for &(x, y) in &raw[1..] {
                let _ = write!(d, " L {:.1} {:.1}", sx(x), sy(y));
            }
            if kind == "polygon" {
                d.push_str(" Z");
            }
        }
        if kind == "polygon" {
            let _ = writeln!(out, "<path class=\"series-fill\" d=\"{d}\"/>");
        }
        let _ = writeln!(out, "<path class=\"series\" d=\"{d}\"/>");
        if se
            .get("show_vertices")
            .and_then(serde_json::Value::as_bool)
            .unwrap_or(true)
        {
            let labels = arr(se, "labels");
            for (i, &(x, y)) in raw.iter().enumerate() {
                let lbl = labels.get(i).map(text_of).unwrap_or_default();
                let _ = writeln!(
                    out,
                    "<circle class=\"vertex\" cx=\"{:.1}\" cy=\"{:.1}\" r=\"3.6\" tabindex=\"0\" data-x=\"{}\" data-y=\"{}\"><title>{}({}, {})</title></circle>",
                    sx(x),
                    sy(y),
                    esc_attr(&fmt_num(x)),
                    esc_attr(&fmt_num(y)),
                    if lbl.is_empty() {
                        String::new()
                    } else {
                        format!("{} &#x2014; ", esc(&lbl))
                    },
                    esc(&fmt_num(x)),
                    esc(&fmt_num(y))
                );
                if !lbl.is_empty() {
                    let _ = writeln!(
                        out,
                        "<text class=\"vlabel\" x=\"{:.1}\" y=\"{:.1}\" text-anchor=\"middle\">{}</text>",
                        sx(x),
                        sy(y) - 9.0,
                        esc(&lbl)
                    );
                }
            }
        }
    }
    out.push_str("</svg>\n");
}

/// Pre-rendered SVG from a producer. Passed through only after it clears the
/// self-containment lint; otherwise the page says so instead of embedding it.
fn raw_svg(out: &mut String, spec: &Value, id: &str, diags: &mut Vec<String>) {
    let Some(svg) = s(spec, "svg") else {
        diags.push(format!("figure {id}: svg figure has no `svg` field"));
        out.push_str(
            "<div class=\"ax-unrenderable\">svg figure has no <code>svg</code> field</div>",
        );
        return;
    };
    let findings = lint_self_contained(svg);
    if findings.is_empty() && !svg.contains("<script") && !svg.contains("javascript:") {
        out.push_str(svg);
        out.push('\n');
    } else {
        diags.push(format!(
            "figure {id}: embedded svg failed the self-containment lint"
        ));
        let _ = write!(
            out,
            "<div class=\"ax-unrenderable\">embedded SVG rejected: {} self-containment finding(s). \
It was NOT inlined.</div>",
            findings.len().max(1)
        );
    }
}

// ---------------------------------------------------------------------------
// self-containment lint
// ---------------------------------------------------------------------------

/// One violation of the self-containment law.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LintFinding {
    /// Stable rule name, so a gate can report which law broke.
    pub rule: &'static str,
    pub detail: String,
    pub offset: usize,
}

const RESOURCE_ATTRS: [&str; 8] = [
    "src=",
    "srcset=",
    "xlink:href=",
    "poster=",
    "action=",
    "formaction=",
    "data=",
    "background=",
];

/// Tokens that may not appear anywhere. Written lowercase because the lint
/// lowercases the haystack; a capitalised entry here would never match, which
/// is exactly the silently-inert-gate failure this repository keeps finding.
const FORBIDDEN_TOKENS: [(&str, &str); 11] = [
    ("<iframe", "an iframe loads a second document"),
    ("<script src", "an external script"),
    ("<link ", "a <link> element pulls a stylesheet or icon"),
    ("<object", "an <object> loads external data"),
    ("<embed", "an <embed> loads external data"),
    ("@import", "a CSS @import fetches a stylesheet"),
    ("xmlhttprequest", "a network call"),
    ("navigator.sendbeacon", "a network call"),
    ("websocket(", "a network call"),
    (
        "integrity=",
        "subresource integrity only makes sense for a subresource",
    ),
    ("javascript:", "a javascript: URL"),
];

/// Assert that a document (or an SVG fragment) makes no network request.
///
/// This is a TRUST property, not a style preference, so the rule set is
/// explicit rather than clever:
///
/// * every resource-loading attribute value must be a fragment, a data: URI,
///   or empty;
/// * `href` may be absolute **only** on an element carrying
///   `data-external="1"` -- the marker this emitter puts on links a reader
///   clicks, which are never fetched on load;
/// * `url(...)` in CSS must be a `data:` URI;
/// * a short list of tokens that cannot appear in a self-contained page at all;
/// * exactly one `</style` and at most one `</script` terminator, since a
///   second one means inlined content escaped its element.
///
/// The lint is only worth having if it can fail: `lint_catches_*` unit tests
/// inject one violation each, and each asserts the rule name it expects.
pub fn lint_self_contained(html: &str) -> Vec<LintFinding> {
    let mut out = Vec::new();
    let lower = html.to_ascii_lowercase();

    for (tok, why) in FORBIDDEN_TOKENS {
        let mut from = 0usize;
        while let Some(rel) = lower[from..].find(tok) {
            let at = from + rel;
            out.push(LintFinding {
                rule: "forbidden-token",
                detail: format!("`{tok}`: {why}"),
                offset: at,
            });
            from = at + tok.len();
        }
    }

    for attr in RESOURCE_ATTRS {
        let mut from = 0usize;
        while let Some(rel) = lower[from..].find(attr) {
            let at = from + rel;
            if !in_tag(html, at) {
                // Escaped prose can legitimately contain the text `src="..."`.
                // Only an attribute inside a real tag can load anything.
                from = at + attr.len();
                continue;
            }
            let val = attr_value(html, at + attr.len());
            if !is_local_ref(&val) {
                out.push(LintFinding {
                    rule: "external-resource",
                    detail: format!("{attr}\"{val}\" is not a local reference"),
                    offset: at,
                });
            }
            from = at + attr.len();
        }
    }

    let mut from = 0usize;
    while let Some(rel) = lower[from..].find("href=") {
        let at = from + rel;
        // Only a real `href` attribute, not the tail of `data-href=`. A
        // `data-*` value is never fetched by the browser; absolute URLs hiding
        // in one are caught by the in-tag URL scan below instead.
        let standalone = at == 0 || html.as_bytes()[at - 1].is_ascii_whitespace();
        if !standalone || !in_tag(html, at) {
            from = at + 5;
            continue;
        }
        let val = attr_value(html, at + 5);
        if !is_local_ref(&val) {
            let tag_start = html[..at].rfind('<').unwrap_or(0);
            let marked = html[tag_start..at].contains("data-external=\"1\"");
            let absolute = val.starts_with("http://") || val.starts_with("https://");
            if !(marked && absolute) {
                out.push(LintFinding {
                    rule: if absolute {
                        "unmarked-external-link"
                    } else {
                        "external-resource"
                    },
                    detail: format!(
                        "href=\"{val}\" is not a local reference and is not a marked prose link"
                    ),
                    offset: at,
                });
            }
        }
        from = at + 5;
    }

    // Any absolute URL sitting inside a tag, in whatever attribute, must be on
    // an element explicitly marked as a link the reader clicks. This is the
    // catch-all behind the per-attribute rules: it sees `data-src`, `style`,
    // and anything else an author invents.
    for scheme in ["http://", "https://"] {
        let mut from = 0usize;
        while let Some(rel) = lower[from..].find(scheme) {
            let at = from + rel;
            if in_tag(html, at) {
                let tag_start = html[..at].rfind('<').unwrap_or(0);
                if !html[tag_start..at].contains("data-external=\"1\"") {
                    out.push(LintFinding {
                        rule: "unmarked-external-link",
                        detail: format!("absolute {scheme} URL in an unmarked element"),
                        offset: at,
                    });
                }
            }
            from = at + scheme.len();
        }
    }

    let mut from = 0usize;
    while let Some(rel) = lower[from..].find("url(") {
        let at = from + rel;
        let end = html[at + 4..].find(')').map_or(html.len(), |e| at + 4 + e);
        let val = html[at + 4..end]
            .trim()
            .trim_matches(['"', '\''])
            .to_string();
        if !val.starts_with("data:") {
            out.push(LintFinding {
                rule: "external-resource",
                detail: format!("css url({val}) is not a data: URI"),
                offset: at,
            });
        }
        from = end;
    }

    if lower.matches("</style").count() > 1 {
        out.push(LintFinding {
            rule: "escaped-inline-content",
            detail: "more than one `</style` terminator".to_string(),
            offset: 0,
        });
    }
    if lower.matches("</script").count() > 1 {
        out.push(LintFinding {
            rule: "escaped-inline-content",
            detail: "more than one `</script` terminator".to_string(),
            offset: 0,
        });
    }
    out.sort_by_key(|f| (f.offset, f.rule));
    out
}

/// Is byte offset `at` inside an element tag (between `<` and `>`)?
///
/// Prose text is escaped before it reaches the output, so a literal `<` or `>`
/// in prose becomes an entity; only real markup has unescaped angle brackets.
/// That makes this test exact for documents this emitter produced.
fn in_tag(html: &str, at: usize) -> bool {
    let lt = html[..at].rfind('<');
    let gt = html[..at].rfind('>');
    match (lt, gt) {
        (Some(l), Some(g)) => l > g,
        (Some(_), None) => true,
        _ => false,
    }
}

fn attr_value(html: &str, at: usize) -> String {
    let rest = &html[at..];
    let mut chars = rest.char_indices();
    if let Some((_, q @ ('"' | '\''))) = chars.next() {
        let end = rest[1..].find(q).map_or(rest.len(), |e| e + 1);
        rest[1..end].to_string()
    } else {
        let end = rest
            .find(|c: char| c.is_whitespace() || c == '>')
            .unwrap_or(rest.len());
        rest[..end].to_string()
    }
}

fn is_local_ref(val: &str) -> bool {
    let v = val.trim();
    v.is_empty() || v.starts_with('#') || v.starts_with("data:") || v.starts_with("mailto:")
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    // `json!` borrows rather than moves, so clippy sees an unconsumed value;
    // taking a reference here would only add `&` to twenty call sites.
    #[allow(clippy::needless_pass_by_value)]
    fn doc(blocks: Value) -> Value {
        json!({
            "schema_version": 1,
            "meta": { "title": "T", "epoch": "2026-08-21" },
            "blocks": blocks
        })
    }

    fn render(blocks: Value) -> (String, Vec<String>) {
        emit_with_diagnostics(&doc(blocks), &HtmlOptions::default())
    }

    // ---------- structure ----------

    #[test]
    fn emits_a_whole_document_with_inlined_assets() {
        let (h, d) = render(json!([{ "id": "p", "kind": { "Prose": { "text": "hello" } } }]));
        assert!(d.is_empty(), "{d:?}");
        assert!(h.starts_with("<!doctype html>"));
        assert!(h.contains("<style>") && h.contains("--s-proved-fg"));
        assert!(h.contains("<script>") && h.contains("axeyum: "));
        assert!(h.trim_end().ends_with("</html>"));
        assert!(h.contains("<p>hello</p>"));
    }

    #[test]
    fn both_serde_enum_encodings_are_accepted() {
        let ext = render(json!([{ "kind": { "Prose": { "text": "a" } } }])).0;
        let int = render(json!([{ "kind": "prose", "text": "a" }])).0;
        assert!(ext.contains("<p>a</p>") && int.contains("<p>a</p>"));
    }

    #[test]
    fn unknown_block_is_loud_and_diagnosed() {
        let (h, d) = render(json!([{ "id": "x", "kind": { "Hologram": {} } }]));
        assert_eq!(d.len(), 1, "{d:?}");
        assert!(d[0].contains("unknown kind"));
        assert!(h.contains("ax-unrenderable"));
        // ...and the reader is told the document is incomplete, not just styled.
        assert!(h.contains("the document is incomplete"));
    }

    #[test]
    fn malformed_block_kind_is_diagnosed() {
        let (_, d) = render(json!([{ "id": "x", "kind": { "A": 1, "B": 2 } }]));
        assert_eq!(d.len(), 1);
        assert!(d[0].contains("malformed"));
    }

    #[test]
    fn missing_blocks_array_is_diagnosed() {
        let (h, d) = emit_with_diagnostics(&json!({ "meta": {} }), &HtmlOptions::default());
        assert_eq!(d.len(), 1);
        assert!(h.contains("ax-unrenderable"));
    }

    #[test]
    fn the_whole_document_is_ascii() {
        // Repository-wide rule and `lib.rs` contract point 8. The input here is
        // deliberately full of the glyphs the fact ledger actually carries.
        let (h, _) = render(json!([
            { "kind": { "Prose": { "text": "for all n, $\\lfloor n/2 \\rfloor \\le n$" } } },
            { "kind": { "Statement": { "title": "t", "status": "proved",
                "statement": "for all a b : Nat, a + b = b + a",
                "formal": { "language": "lean4",
                            "statement": "\u{2200} (m n : \u{2115}), Nat.fib (m.gcd n) = ..." } } } }
        ]));
        assert!(h.is_ascii(), "non-ASCII byte in emitted document");
        assert!(h.contains("&#x2200;") && h.contains("&#x2115;"));
    }

    #[test]
    fn output_is_deterministic() {
        let b = json!([
            { "kind": { "Prose": { "text": "x" } } },
            { "kind": { "Claim": { "label": "L", "status": "proved",
                "evidence": [{ "id": "e", "kind": "k", "supports": "s", "check_status": "checked" }] } } }
        ]);
        assert_eq!(render(b.clone()).0, render(b).0);
    }

    #[test]
    fn reading_level_defaults_to_full_so_js_off_hides_nothing() {
        let h = render(json!([])).0;
        assert!(h.contains("data-level=\"full\""));
        // The summary level is CSS-gated, i.e. it needs the script to engage.
        assert!(h.contains("body[data-level=\"summary\"] .t-detail"));
    }

    // ---------- the fail-closed law, as an emitter-side alarm ----------

    #[test]
    fn established_claim_without_evidence_raises_an_alarm() {
        let (h, d) = render(json!([{ "id": "c", "kind": { "Claim": {
            "label": "L", "status": "proved", "evidence": [] } } }]));
        assert_eq!(d.len(), 1, "{d:?}");
        assert!(d[0].contains("fail-closed"));
        assert!(h.contains("ax-unrenderable"));
    }

    #[test]
    fn red_evidence_under_a_green_claim_raises_an_alarm() {
        let (h, d) = render(json!([{ "id": "c", "kind": { "Claim": {
            "label": "L", "status": "checked",
            "evidence": [{ "id": "e", "kind": "run", "supports": "s",
                           "check_status": "checked", "exit_status": 1 }] } } }]));
        assert!(d.iter().any(|x| x.contains("exited 1")), "{d:?}");
        assert!(h.contains("ax-exit-bad"));
    }

    #[test]
    fn open_claim_with_no_evidence_is_normal_and_says_so() {
        let (h, d) = render(json!([{ "id": "c", "kind": { "Claim": {
            "label": "L", "status": "open", "evidence": [] } } }]));
        assert!(d.is_empty(), "{d:?}");
        assert!(h.contains("No evidence is attached"));
    }

    #[test]
    fn certificate_without_exit_status_is_diagnosed() {
        let (h, d) = render(json!([{ "id": "z", "kind": { "Certificate": {
            "summary": "ran", "kind": "ReportRun" } } }]));
        assert_eq!(d.len(), 1, "{d:?}");
        assert!(h.contains("exit status missing"));
    }

    #[test]
    fn certificate_may_declare_why_it_has_no_exit_status() {
        let (h, d) = render(json!([{ "id": "z", "kind": { "Certificate": {
            "summary": "s", "verdict": "checked",
            "no_exit_reason": "a four-hour re-check cannot be a gate" } } }]));
        assert!(d.is_empty(), "{d:?}");
        assert!(h.contains("not re-run: a four-hour re-check cannot be a gate"));
        // ...but it still may not claim a run that returned zero. (Assert on
        // the rendered chip, not the whole file: the stylesheet naturally
        // mentions every class it defines.)
        assert!(!h.contains(">exit 0<"));
    }

    #[test]
    fn certificate_exit_nonzero_renders_in_failure_styling() {
        let h = render(json!([{ "id": "z", "kind": { "Certificate": {
            "summary": "ran", "exit_status": 2, "replay": "cargo test" } } }]))
        .0;
        assert!(h.contains("ax-exit-bad"));
        assert!(
            h.contains("badge-refuted"),
            "a red certificate must not wear a green badge"
        );
    }

    #[test]
    fn unknown_status_is_not_mapped_onto_a_known_one() {
        let h = render(json!([{ "kind": { "Claim": { "label": "L", "status": "sat-unchecked",
            "evidence": [{ "id": "e", "kind": "k", "supports": "s", "check_status": "open" }] } } }])).0;
        assert!(h.contains("badge-unknown"));
        assert!(h.contains("SAT-UNCHECKED"));
        // The card itself must not be styled as any established status. (The
        // stylesheet naturally mentions every badge class, so assert on the
        // card, not on the whole file.)
        assert!(
            h.contains("class=\"card blk t-essential s-unknown\""),
            "{h}"
        );
    }

    #[test]
    fn axiom_free_footprint_reads_as_a_claim_not_an_omission() {
        let h = render(json!([{ "kind": { "Claim": { "label": "L", "status": "proved",
            "proof_route": "kernel-lean", "axiom_footprint": [],
            "evidence": [{ "id": "e", "kind": "kernel-term", "supports": "s", "check_status": "checked" }] } } }])).0;
        assert!(h.contains("axiom-free"));
    }

    #[test]
    fn two_axis_disagreement_in_our_favour_is_marked_a_new_result() {
        let h = render(json!([{ "kind": { "Claim": { "label": "L",
            "status": "computed", "external_status": "open",
            "evidence": [{ "id": "e", "kind": "claim-ref", "supports": "s", "check_status": "checked" }] } } }])).0;
        assert!(h.contains("new result"));
        // The reverse is not a new result.
        let h2 = render(json!([{ "kind": { "Claim": { "label": "L",
            "status": "open", "external_status": "proved", "evidence": [] } } }]))
        .0;
        assert!(!h2.contains("new result"));
    }

    // ---------- escaping ----------

    #[test]
    fn prose_cannot_smuggle_markup() {
        let h =
            render(json!([{ "kind": { "Prose": { "text": "<img src=\"http://x/y.png\">" } } }])).0;
        assert!(!h.contains("<img"));
        assert!(h.contains("&lt;img"));
        assert!(
            lint_self_contained(&h).is_empty(),
            "{:?}",
            lint_self_contained(&h)
        );
    }

    #[test]
    fn attribute_escaping_closes_the_quote_hole() {
        assert_eq!(esc_attr("a\"b'c<d&e"), "a&quot;b&#39;c&lt;d&amp;e");
    }

    #[test]
    fn slug_is_stable_and_safe() {
        assert_eq!(slug("F:nat-add-comm"), "f-nat-add-comm");
        assert_eq!(slug("  !!  "), "x");
        assert_eq!(slug("A B"), "a-b");
    }

    // ---------- inline markup ----------

    #[test]
    fn inline_markup_subset() {
        assert_eq!(inline("a `b` c"), "a <code>b</code> c");
        assert_eq!(inline("**x**"), "<strong>x</strong>");
        assert_eq!(inline("*x*"), "<em>x</em>");
        assert!(inline("[l](#a)").contains("<a href=\"#a\">l</a>"));
    }

    #[test]
    fn emphasis_cannot_eat_a_multiplication() {
        // Verbatim from `F:nat-gcd-bezout`. Every `*` must survive.
        let out = inline("gcd(m, n) + m*mn + n*nn = m*mp + n*np");
        assert_eq!(out.matches('*').count(), 4, "{out}");
        assert!(!out.contains("<em>"), "{out}");
        // ...while ordinary emphasis still works.
        assert_eq!(inline("read it at *full*"), "read it at <em>full</em>");
        assert_eq!(inline("**x** y"), "<strong>x</strong> y");
    }

    #[test]
    fn double_hyphen_becomes_an_em_dash_but_only_when_it_is_one() {
        assert_eq!(inline("a -- b"), "a &#x2014; b");
        // Not inside code, and not a longer run (which is a rule, or a flag).
        assert_eq!(inline("`--flag`"), "<code>--flag</code>");
        assert!(inline("a --- b").contains("---"));
    }

    #[test]
    fn external_link_carries_the_marker_internal_does_not() {
        let ext = inline("[l](https://example.org/p)");
        assert!(ext.contains("data-external=\"1\""));
        assert!(
            lint_self_contained(&ext).is_empty(),
            "{:?}",
            lint_self_contained(&ext)
        );
        let rel = inline("[l](docs/x.md)");
        assert!(
            !rel.contains("<a "),
            "a relative href in a single file is a dead link: {rel}"
        );
        assert!(rel.contains("<code>docs/x.md</code>"));
    }

    // ---------- R-b: math ----------

    #[test]
    fn math_renders_the_p0_constructs() {
        let (m, ok) = latex_to_mathml("\\lfloor n/2 \\rfloor");
        assert!(ok, "{m}");
        assert!(m.contains("&#x230A;") && m.contains("&#x230B;"), "{m}");
        let (m, ok) = latex_to_mathml("\\frac{a}{b}");
        assert!(ok && m.contains("<mfrac>"));
        let (m, ok) = latex_to_mathml("x_1^2");
        assert!(ok, "{m}");
        assert!(m.contains("<msub>") && m.contains("<msup>"));
        let (m, ok) = latex_to_mathml("a \\le b");
        assert!(ok && m.contains("&#x2264;"), "{m}");
        let (m, ok) = latex_to_mathml("\\gcd(m, n)");
        assert!(ok && m.contains("gcd"), "{m}");
    }

    #[test]
    fn math_carries_its_own_source_for_copy_and_grep() {
        let (m, _) = latex_to_mathml("a+b");
        assert!(m.contains("annotation encoding=\"application/x-tex\">a+b</annotation>"));
        assert!(m.contains("alttext=\"a+b\""));
    }

    #[test]
    fn unknown_command_is_visible_never_guessed() {
        let (m, ok) = latex_to_mathml("\\notacommand{x}");
        assert!(!ok, "an unknown command must report failure");
        assert!(m.contains("<merror>"), "{m}");
        assert!(m.contains("notacommand"));
    }

    #[test]
    fn math_escapes_its_own_annotation() {
        let (m, _) = latex_to_mathml("a<b & c");
        assert!(!m.contains("<b "), "{m}");
        assert!(m.contains("&lt;") && m.contains("&amp;"));
    }

    #[test]
    fn math_minus_is_the_minus_sign_not_a_hyphen() {
        let (m, _) = latex_to_mathml("a-b");
        assert!(m.contains("&#x2212;"), "{m}");
        // ...and the emitted bytes are ASCII, so no encoding step can alter it.
        assert!(m.is_ascii(), "{m}");
    }

    #[test]
    fn inline_math_is_reachable_through_prose() {
        let h = render(json!([{ "kind": { "Prose": { "text": "so $\\frac{1}{2}$ then" } } }])).0;
        assert!(h.contains("<mfrac>"));
    }

    // ---------- formal statements are never prettified ----------

    #[test]
    fn formal_statement_is_verbatim_preformatted() {
        let h = render(json!([{ "kind": { "Statement": {
            "title": "t", "status": "proved",
            "formal": { "language": "lean4", "statement": "Eq.{1} Nat (a + b) (b + a)" } } } }]))
        .0;
        assert!(h.contains("<pre><code>Eq.{1} Nat (a + b) (b + a)</code></pre>"));
        assert!(
            !h.contains("<math"),
            "the checked text must not be re-rendered as math"
        );
    }

    // ---------- figures ----------

    #[test]
    fn dep_graph_bakes_the_cone_into_data_attributes() {
        let h = render(json!([{ "kind": { "Figure": { "DepGraph": {
            "caption": "c",
            "nodes": [
                { "key": "a", "label": "A", "status": "proved" },
                { "key": "b", "label": "B", "status": "proved" },
                { "key": "c", "label": "C", "status": "open" }
            ],
            "edges": [ { "from": "a", "to": "b" }, { "from": "b", "to": "c" } ]
        } } } }]))
        .0;
        assert!(h.contains("class=\"ax-graph\""));
        // c's ancestors are a and b.
        assert!(
            h.contains("data-n=\"2\" data-anc=\"0 1\" data-desc=\"\""),
            "{}",
            &h[h.find("gnode").unwrap()..h.find("gnode").unwrap() + 400]
        );
        assert!(h.contains("data-n=\"0\" data-anc=\"\" data-desc=\"1 2\""));
        assert!(h.contains("3 nodes, 2 edges, 0 crossings"));
    }

    #[test]
    fn dep_graph_edges_accept_index_pairs_too() {
        let h = render(json!([{ "kind": { "Figure": { "DepGraph": {
            "nodes": [ { "key": "a", "label": "A" }, { "key": "b", "label": "B" } ],
            "edges": [ [0, 1] ] } } } }]))
        .0;
        assert!(h.contains("2 nodes, 1 edges"));
    }

    #[test]
    fn empty_graph_says_so_instead_of_drawing_nothing() {
        let (h, d) = render(json!([{ "kind": { "Figure": { "DepGraph": { "nodes": [] } } } }]));
        assert!(h.contains("The graph is empty"));
        assert!(d.is_empty());
    }

    #[test]
    fn plot_renders_axes_points_and_native_tooltips() {
        let h = render(json!([{ "kind": { "Figure": { "Plot": {
            "caption": "c", "x_label": "k", "y_label": "d(k)",
            "series": [{ "kind": "step", "points": [[0, 1], [1, 2], [2, 2]], "labels": ["p0", "p1", "p2"] }]
        } } } }])).0;
        assert!(h.contains("class=\"ax-plot\""));
        assert!(h.contains("<title>p1 &#x2014; (1, 2)</title>"), "{h}");
        assert!(h.contains("class=\"series\""));
    }

    #[test]
    fn plot_without_points_says_so() {
        let h = render(json!([{ "kind": { "Figure": { "Plot": { "series": [] } } } }])).0;
        assert!(h.contains("carries no points"));
    }

    #[test]
    fn unknown_figure_kind_is_diagnosed() {
        let (_, d) = render(json!([{ "id": "f", "kind": { "Figure": { "Hologram": {} } } }]));
        assert_eq!(d.len(), 1, "{d:?}");
    }

    #[test]
    fn raw_svg_that_would_phone_home_is_refused_not_embedded() {
        let (h, d) = render(json!([{ "id": "f", "kind": { "Figure": { "Svg": {
            "svg": "<svg><image href=\"https://evil.example/x.png\"/></svg>" } } } }]));
        assert_eq!(d.len(), 1, "{d:?}");
        assert!(h.contains("was NOT inlined") || h.contains("rejected"));
        assert!(!h.contains("evil.example"));
        assert!(lint_self_contained(&h).is_empty());
    }

    #[test]
    fn clean_raw_svg_passes_through() {
        let (h, d) = render(json!([{ "id": "f", "kind": { "Figure": { "Svg": {
            "svg": "<svg viewBox=\"0 0 4 4\"><rect width=\"4\" height=\"4\"/></svg>" } } } }]));
        assert!(d.is_empty(), "{d:?}");
        assert!(h.contains("<rect width=\"4\""));
    }

    // ---------- steps, tables, certificates ----------

    #[test]
    fn steps_render_with_a_keyboard_affordance() {
        let h = render(json!([{ "kind": { "Steps": { "steps": [
            { "op": "rewrite", "input": "a", "output": "b" },
            { "op": "eval", "input": "b", "output": "c" } ] } } }]))
        .0;
        assert_eq!(h.matches("<li><div>").count(), 2);
        assert!(h.contains("<kbd>j</kbd>"));
    }

    #[test]
    fn table_marks_numeric_columns_for_tabular_alignment() {
        let h = render(json!([{ "kind": { "Table": {
            "caption": "c", "columns": ["k", { "label": "d(k)", "align": "right" }],
            "rows": [[1, 2], [3, 4]] } } }]))
        .0;
        assert!(h.contains("<th class=\"num\">d(k)</th>"));
        assert_eq!(h.matches("<td class=\"num\">").count(), 4);
    }

    #[test]
    fn certificate_replay_command_gets_a_copy_button() {
        let h = render(json!([{ "id": "z", "kind": { "Certificate": {
            "summary": "s", "exit_status": 0, "replay": "cargo run -q --example x" } } }]))
        .0;
        assert!(h.contains("data-copy-target=\"z-replay\""));
        assert!(h.contains("id=\"z-replay\""));
        // and it degrades: the command is real text inside the page
        assert!(h.contains("cargo run -q --example x"));
    }

    #[test]
    fn certificate_is_a_details_so_it_folds_without_js() {
        let h = render(json!([{ "id": "z", "kind": { "Certificate": {
            "summary": "s", "exit_status": 0 } } }]))
        .0;
        assert!(h.contains("<details class=\"ax-fold card ax-cert"));
    }

    // ---------- the lint, and its ability to fail ----------

    #[test]
    fn a_rendered_document_passes_the_self_containment_lint() {
        let (h, _) = render(json!([
            { "kind": { "Prose": { "text": "text with [a link](https://example.org) in it" } } },
            { "kind": { "Claim": { "label": "L", "status": "proved",
                "evidence": [{ "id": "e", "kind": "k", "supports": "s", "check_status": "checked",
                               "checker_command": "cargo test" }] } } },
            { "kind": { "Figure": { "DepGraph": {
                "nodes": [{ "key": "a", "label": "A", "status": "proved" }], "edges": [] } } } },
            { "kind": { "Certificate": { "summary": "s", "exit_status": 0, "replay": "ls" } } }
        ]));
        let f = lint_self_contained(&h);
        assert!(f.is_empty(), "{f:#?}");
    }

    #[test]
    fn the_committed_assets_are_themselves_self_contained() {
        assert!(
            lint_self_contained(STYLE_CSS).is_empty(),
            "{:#?}",
            lint_self_contained(STYLE_CSS)
        );
        assert!(
            lint_self_contained(APP_JS).is_empty(),
            "{:#?}",
            lint_self_contained(APP_JS)
        );
    }

    #[test]
    fn lint_catches_an_external_stylesheet() {
        let f = lint_self_contained("<link rel=\"stylesheet\" href=\"https://cdn/x.css\">");
        assert!(f.iter().any(|x| x.rule == "forbidden-token"), "{f:#?}");
    }

    #[test]
    fn lint_ignores_attribute_text_that_is_not_in_a_tag() {
        // Escaped prose, not markup: nothing is fetched.
        assert!(
            lint_self_contained("<p>write src=&quot;https://x/y&quot; to load it</p>").is_empty()
        );
        // ...but the real thing is caught, by both the attribute rule and the
        // catch-all URL rule. Two independent findings for one violation is the
        // intended redundancy.
        let f = lint_self_contained("<p><img src=\"https://x/y\"></p>");
        assert!(f.iter().any(|x| x.rule == "external-resource"), "{f:#?}");
        assert!(
            f.iter().any(|x| x.rule == "unmarked-external-link"),
            "{f:#?}"
        );
    }

    #[test]
    fn lint_catches_an_external_image() {
        let f = lint_self_contained("<img src=\"https://cdn/x.png\">");
        assert!(f.iter().any(|x| x.rule == "external-resource"), "{f:#?}");
    }

    #[test]
    fn lint_catches_a_url_hidden_in_a_data_attribute() {
        let f = lint_self_contained("<div data-src=\"https://x/y\"></div>");
        assert!(
            f.iter().any(|x| x.rule == "unmarked-external-link"),
            "{f:#?}"
        );
        // A local id in a data attribute is fine.
        assert!(lint_self_contained("<g data-href=\"card-a\"></g>").is_empty());
    }

    #[test]
    fn lint_catches_a_webfont() {
        let f = lint_self_contained("@font-face{src:url(https://fonts/x.woff2)}");
        assert!(f.iter().any(|x| x.rule == "external-resource"), "{f:#?}");
    }

    #[test]
    fn lint_catches_an_unmarked_absolute_link() {
        let f = lint_self_contained("<a href=\"https://example.org\">x</a>");
        assert!(!f.is_empty());
        assert!(
            f.iter().all(|x| x.rule == "unmarked-external-link"),
            "{f:#?}"
        );
    }

    #[test]
    fn lint_allows_a_marked_prose_link() {
        let f = lint_self_contained("<a data-external=\"1\" href=\"https://example.org\">x</a>");
        assert!(f.is_empty(), "{f:#?}");
    }

    #[test]
    fn lint_catches_a_relative_resource_which_a_single_file_cannot_resolve() {
        let f = lint_self_contained("<img src=\"figures/a.png\">");
        assert_eq!(f.len(), 1);
    }

    #[test]
    fn lint_catches_a_network_call_in_script() {
        assert!(
            lint_self_contained("new XMLHttpRequest()")
                .iter()
                .any(|x| x.rule == "forbidden-token")
        );
        assert!(
            lint_self_contained("new WebSocket(\"wss://x\")")
                .iter()
                .any(|x| x.rule == "forbidden-token")
        );
    }

    #[test]
    fn lint_catches_an_iframe_and_a_javascript_url() {
        assert!(!lint_self_contained("<iframe src=\"#\"></iframe>").is_empty());
        assert!(!lint_self_contained("<a href=\"javascript:x()\">x</a>").is_empty());
    }

    #[test]
    fn lint_catches_content_that_escaped_its_inline_element() {
        let f = lint_self_contained("<script>var a = \"</script>\";</script>");
        assert!(
            f.iter().any(|x| x.rule == "escaped-inline-content"),
            "{f:#?}"
        );
    }

    // ---------- the committed preview page ----------

    /// The preview page is DESIGN's visual benchmark AND a golden test.
    ///
    /// `render/assets/preview/preview-doc.json` is generated from the real fact
    /// ledger by `build-preview-doc.py`; this test re-renders it and requires
    /// the committed `preview.html` to match byte for byte. So the page cannot
    /// drift away from the emitter, and nothing on it can be edited by hand
    /// into saying something the ledger does not.
    ///
    /// To regenerate after an emitter or stylesheet change:
    ///
    /// ```text
    /// python3 render/assets/preview/build-preview-doc.py > render/assets/preview/preview-doc.json
    /// AXEYUM_RENDER_BLESS=1 cargo test --features html -- preview_page
    /// ```
    #[test]
    fn preview_page_matches_its_source() {
        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("assets/preview");
        let src = dir.join("preview-doc.json");
        let Ok(text) = std::fs::read_to_string(&src) else {
            panic!("missing {}", src.display());
        };
        let doc: Value = serde_json::from_str(&text).expect("preview-doc.json is not JSON");
        let (html, diags) = emit_with_diagnostics(
            &doc,
            &HtmlOptions {
                level: ReadingLevel::Full,
                epoch: None,
            },
        );
        assert!(
            diags.is_empty(),
            "the preview document must render completely: {diags:#?}"
        );
        let findings = lint_self_contained(&html);
        assert!(findings.is_empty(), "{findings:#?}");
        assert!(html.is_ascii());

        let out = dir.join("preview.html");
        if std::env::var("AXEYUM_RENDER_BLESS").is_ok() {
            std::fs::write(&out, &html).expect("write preview.html");
            return;
        }
        let committed = std::fs::read_to_string(&out).unwrap_or_default();
        assert_eq!(
            committed, html,
            "preview.html is stale; re-bless it (see this test's doc comment)"
        );
    }

    #[test]
    fn preview_page_carries_the_statuses_the_ledger_carries() {
        // A second, independent reading: the page must show the real ledger
        // vocabulary, including the combination that makes a new result.
        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("assets/preview");
        let html = std::fs::read_to_string(dir.join("preview.html")).unwrap_or_default();
        for token in ["PROVED", "COMPUTED", "REFUTED", "CHECKED", "new result"] {
            assert!(html.contains(token), "preview page is missing `{token}`");
        }
        assert!(
            html.contains("data-claim="),
            "no machine-recoverable claim pairing"
        );
    }

    #[test]
    fn lint_accepts_data_uris_and_fragments() {
        assert!(
            lint_self_contained("<img src=\"data:image/png;base64,AA\"><a href=\"#x\">y</a>")
                .is_empty()
        );
    }
}

// ---------------------------------------------------------------------------
// integration with `assemble::ResolvedDocument`
// ---------------------------------------------------------------------------

/// Translate a serialized [`crate::assemble::ResolvedDocument`] into the shape
/// this module renders.
///
/// It works on JSON rather than on the Rust types on purpose: the resolved
/// types are another lane's, the translation is the part most likely to drift
/// when they change, and going through `serde_json::to_value` means this
/// function is unit-testable here without the rest of the package. Every field
/// it does not understand is dropped **loudly** -- the emitter's diagnostics
/// fire on anything that arrives in an unexpected shape.
///
/// Two contract points from `lib.rs` are honoured here rather than downstream:
///
/// * point 3 -- nothing branches on `exit_status`. A certificate's verdict is
///   taken from the resolved `claim_status`, never derived from whether a
///   process returned zero. Exit status is passed through for DISPLAY only.
/// * point 8 -- the output is ASCII, which [`esc`] guarantees.
pub fn normalize_resolved(doc: &Value) -> Value {
    use serde_json::{Map, json};

    let mut meta = Map::new();
    for (from, to) in [
        ("title", "title"),
        ("subtitle", "subtitle"),
        ("doc_id", "doc_id"),
    ] {
        if let Some(x) = s(doc, from) {
            meta.insert(to.into(), json!(x));
        }
    }
    if let Some(g) = doc.get("genre") {
        meta.insert("genre".into(), json!(text_of(g)));
    }
    if let Some(e) = doc.get("epoch_unix").and_then(Value::as_i64) {
        let src = s(doc, "epoch_source").unwrap_or("commit");
        meta.insert("epoch".into(), json!(format!("{e} ({src})")));
    }
    if let Some(c) = s(doc, "commit") {
        meta.insert("source".into(), json!(format!("`{c}`")));
    }

    let blocks: Vec<Value> = doc
        .get("blocks")
        .and_then(Value::as_array)
        .map(|bs| bs.iter().map(normalize_block).collect())
        .unwrap_or_default();

    json!({ "schema_version": 1, "meta": Value::Object(meta), "blocks": blocks })
}

fn rich(v: Option<&Value>) -> Option<String> {
    let v = v?;
    match v {
        Value::String(x) if !x.is_empty() => Some(x.clone()),
        Value::Object(_) => s(v, "text").map(str::to_string),
        _ => None,
    }
}

fn normalize_block(b: &Value) -> Value {
    use serde_json::json;
    let id = s(b, "anchor").or_else(|| s(b, "id")).unwrap_or("b");
    let tag = b.get("tag").map_or_else(|| "essential".into(), text_of);
    let title = s(b, "title");
    let Some((name, body)) = kind_of(b) else {
        return json!({ "id": id, "tag": tag, "kind": Value::Null });
    };
    let inner: Value = match name.as_str() {
        "prose" => {
            let mut m = json!({ "text": rich(body.get("text")).unwrap_or_default() });
            if let Some(t) = title {
                m["heading"] = json!(t);
                if let Some(l) = body.get("heading_level").and_then(Value::as_u64) {
                    m["level"] = json!(l);
                }
            }
            json!({ "Prose": m })
        }
        "claim" => json!({ "Claim": {
            "label": s(&body, "label").unwrap_or("Claim"),
            "statement": rich(body.get("statement")).unwrap_or_default(),
            "status": body.get("status").map_or_else(|| "open".into(), text_of),
            "notes": rich(body.get("note")),
            "evidence": arr(&body, "evidence").iter().map(normalize_evidence).collect::<Vec<_>>(),
        }}),
        "statement" => {
            let f = body.get("formal").cloned().unwrap_or(Value::Null);
            json!({ "Statement": {
                "title": s(&f, "title").or(title).unwrap_or("Statement"),
                "ref": s(&f, "key"),
                "statement": s(&f, "prose"),
                "status": s(&f, "epistemic_status").unwrap_or("open"),
                "external_status": s(&f, "external_status"),
                "proof_route": s(&f, "proof_route"),
                "axiom_footprint": f.get("axiom_footprint").cloned().unwrap_or(Value::Null),
                "formal": { "language": s(&f, "language").unwrap_or("formal"),
                            "statement": s(&f, "formal"), "fragment": s(&f, "fragment") },
            }})
        }
        "steps" => json!({ "Steps": {
            "heading": title,
            "caption": rich(body.get("caption")),
            "steps": arr(&body, "steps").iter().map(|st| json!({
                "op": s(st, "op"),
                "input": rich(st.get("input")),
                "output": rich(st.get("output")),
                "note": rich(st.get("note")),
            })).collect::<Vec<_>>(),
        }}),
        "table" => json!({ "Table": {
            "heading": title,
            "caption": rich(body.get("caption")),
            "columns": arr(&body, "columns").iter().map(|c| json!({
                "label": s(c, "header").unwrap_or_else(|| s(c, "key").unwrap_or("")),
                "align": c.get("align").map(text_of),
            })).collect::<Vec<_>>(),
            "rows": body.get("rows").cloned().unwrap_or(Value::Null),
            "source": body.get("source").cloned().unwrap_or(Value::Null),
        }}),
        "certificate" => {
            let ev = arr(&body, "evidence");
            // Contract point 3: the verdict is resolved data, not a reading of
            // an exit code.
            let verdict = ev
                .iter()
                .find_map(|e| e.get("claim_status").filter(|x| !x.is_null()).map(text_of))
                .unwrap_or_else(|| "open".into());
            json!({ "Certificate": {
                "kind": body.get("cert_kind").map(text_of),
                "summary": rich(body.get("summary")).unwrap_or_default(),
                "verdict": verdict,
                "exit_status": ev.first().and_then(|e| e.get("exit_status").and_then(Value::as_i64)),
                "generator": ev.first().and_then(|e| s(e, "generator")),
                "replay": s(&body, "replay").or_else(|| body.get("replay").and_then(|r| s(r, "line"))),
                "inputs": arr(&body, "artifact_refs").iter().map(|a| json!({
                    "path": s(a, "path").unwrap_or("?"),
                    "sha256": s(a, "sha256").unwrap_or("(not pinned)"),
                })).collect::<Vec<_>>(),
            }})
        }
        "figure" => {
            let caption = rich(body.get("caption"));
            let spec = body.get("spec").cloned().unwrap_or(Value::Null);
            json!({ "Figure": normalize_figure(&spec, caption.as_deref()) })
        }
        "include" => json!({ "Include": {
            "path": s(&body, "path").unwrap_or("?"),
            "note": title,
        }}),
        _ => Value::Null,
    };
    json!({ "id": id, "tag": tag, "kind": inner,
            "provenance": b.get("provenance").cloned().unwrap_or(Value::Null) })
}

fn normalize_evidence(e: &Value) -> Value {
    use serde_json::json;
    json!({
        "id": s(e, "record_id").unwrap_or("?"),
        "kind": s(e, "role").map_or_else(|| "run-record".to_string(), str::to_string),
        "supports": s(e, "claim_statement").or_else(|| s(e, "summary")),
        // The badge comes from the resolved claim status only. When assembly
        // recorded none, this renders `open` -- deliberately the weakest
        // reading, never an inference from the exit code.
        "check_status": e.get("claim_status").filter(|x| !x.is_null()).map_or_else(|| "open".into(), text_of),
        "exit_status": e.get("exit_status").cloned().unwrap_or(Value::Null),
        "checkers": s(e, "generator").map(|g| vec![Value::String(g.to_string())]),
        "checker_command": e.get("replay").and_then(|r| s(r, "line")).or_else(|| s(e, "command")),
        "artifact": s(e, "path"),
    })
}

fn normalize_figure(spec: &Value, caption: Option<&str>) -> Value {
    use serde_json::json;
    let Some((name, b)) = kind_of(&json!({ "kind": spec.clone() })) else {
        return json!({ "Unknown": { "caption": caption } });
    };
    match name.as_str() {
        "depgraph" => json!({ "DepGraph": {
            "caption": caption,
            "nodes": arr(&b, "nodes").iter().map(|n| json!({
                "key": s(n, "id").unwrap_or("?"),
                "label": s(n, "label").or_else(|| s(n, "id")).unwrap_or("?"),
                "status": n.get("status").filter(|x| !x.is_null()).map_or_else(|| "open".into(), text_of),
                "href": s(n, "href"),
            })).collect::<Vec<_>>(),
            "edges": b.get("edges").cloned().unwrap_or(Value::Null),
        }}),
        "plot" => json!({ "Plot": {
            "caption": caption,
            "x_label": s(&b, "x_label"), "y_label": s(&b, "y_label"),
            "x_min": b.get("x_range").and_then(|r| r.get(0)).and_then(Value::as_f64),
            "x_max": b.get("x_range").and_then(|r| r.get(1)).and_then(Value::as_f64),
            "y_min": b.get("y_range").and_then(|r| r.get(0)).and_then(Value::as_f64),
            "y_max": b.get("y_range").and_then(|r| r.get(1)).and_then(Value::as_f64),
            "series": arr(&b, "series").iter().map(|se| json!({
                "name": s(se, "label"),
                "kind": match b.get("plot_type").map(text_of).unwrap_or_default().as_str() {
                    "steps" => "step",
                    "scatter" => "scatter",
                    _ => "line",
                },
                "points": se.get("points").cloned().unwrap_or(Value::Null),
            })).collect::<Vec<_>>(),
        }}),
        "polygon" => json!({ "Plot": {
            "caption": caption,
            "x_label": s(&b, "x_label"), "y_label": s(&b, "y_label"),
            "series": [ { "kind": if b.get("closed").and_then(Value::as_bool).unwrap_or(true) { "polygon" } else { "line" },
                          "points": b.get("vertices").cloned().unwrap_or(Value::Null) } ],
        }}),
        "svg" => json!({ "Svg": { "caption": caption, "svg": s(&b, "svg") } }),
        other => json!({ other: { "caption": caption } }),
    }
}

/// The HTML emitter, as registered by `crate::emitter_for`.
#[cfg(feature = "html")]
#[derive(Debug, Clone, Copy, Default)]
pub struct HtmlEmitter;

#[cfg(feature = "html")]
impl crate::Emitter for HtmlEmitter {
    fn format_name(&self) -> &'static str {
        "html"
    }

    fn primary_extension(&self) -> &'static str {
        "html"
    }

    fn emit(&self, doc: &crate::assemble::ResolvedDocument) -> crate::EmitOutput {
        // Total, as the contract requires: a serialization failure cannot
        // happen for these types, and if it somehow did the document says so
        // rather than the emitter refusing.
        let v = serde_json::to_value(doc).unwrap_or(Value::Null);
        let normalized = normalize_resolved(&v);
        let opts = HtmlOptions {
            level: ReadingLevel::Full,
            epoch: Some(format!("{} ({})", doc.epoch_unix, doc.epoch_source)),
        };
        crate::EmitOutput::new(emit(&normalized, &opts))
    }
}
