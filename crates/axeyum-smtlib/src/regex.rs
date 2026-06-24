//! Bounded regular-expression matching for `QF_S` `str.in_re` over the
//! self-describing packed-bit-vector string layout (ADR-0029, slice 5).
//!
//! A `RegLan` regex is compiled to a Thompson NFA over **byte** character
//! classes (the packed string model is one byte per character, matching the
//! existing `str.at`/`str.to_code` byte semantics). `(str.in_re s R)` for a
//! string `s` of bounded maximum length `m` is then encoded as a bounded
//! reachable-state formula: Boolean variables `reach[pos][q]` for each position
//! `pos ∈ 0..=m` and NFA state `q`, with
//!
//! - `reach[0]` = ε-closure of the start state;
//! - `reach[pos+1][t]` if some state `q` with `reach[pos][q]` has a `q → t`
//!   character transition whose predicate accepts `s[pos]`, **and** byte `pos`
//!   is present (`pos < len(s)`); then ε-closure;
//! - accept iff a final state is in `reach[len(s)]`, selected by the `len(s)`
//!   field of the packed string.
//!
//! The encoding is **denotation-preserving for the bounded string**: it decides
//! `str.in_re` exactly for the ≤`m`-byte representation of `s`. The only
//! incompleteness is the same length bound the rest of the bounded-string front
//! end already carries — a satisfying assignment that needs a string longer than
//! the bound is excluded by well-formedness and surfaces as a sound `unknown`
//! (never a wrong `unsat`/`sat`). Constructs outside the supported fragment, or
//! an NFA that would exceed a sane state cap, decline cleanly as
//! [`SmtError::Unsupported`] — never a wrong verdict.
//!
//! ## Supported `RegLan` constructs (each checked against the SMT-LIB
//! `UnicodeStrings`/`RegLan` theory)
//!
//! - `(str.to_re "literal")` — matches exactly the literal byte string.
//! - `(re.range "a" "z")` — a single character whose code point is in the
//!   inclusive byte range (both arguments must be single-byte literals; an empty
//!   or multi-byte argument denotes the empty language `∅`, per the theory).
//! - `re.allchar` — any single character (`Σ`, here any one byte).
//! - `re.all` — `Σ*` (every string).
//! - `re.none` — `∅` (no string).
//! - `(re.++ R1 R2 …)` — concatenation (left-associative, `≥ 1` arg).
//! - `(re.union R1 R2 …)` — alternation (`≥ 1` arg).
//! - `(re.inter R1 R2 …)` — intersection (`≥ 1` arg), via the product NFA; kept
//!   only while the product stays under the state cap (else a clean decline).
//! - `(re.* R)` — Kleene star.
//! - `(re.+ R)` — one or more (`R ++ R*`).
//! - `(re.opt R)` — zero or one (`R | ε`).
//!
//! - `(re.comp R)` — complement `Σ* \ L(R)`, via determinization to a **complete**
//!   DFA (subset construction over the full byte alphabet, missing transitions
//!   routed to an explicit dead state) followed by flipping the accepting set.
//!   Complement is sound **only** over a complete DFA, so the completion is
//!   mandatory before the flip (a partial DFA would wrongly reject strings whose
//!   run "falls off" the transition table).
//! - `(re.diff R1 R2)` — difference `L(R1) \ L(R2)`, defined as
//!   `R1 ∩ comp(R2)` and built by reusing the [`product_intersection`] machinery
//!   over `R1` and the complemented DFA of `R2`.
//!
//! ## Declined (clean `Unsupported`, never a wrong verdict)
//!
//! `(re.loop …)` / `(_ re.^ n)`, `str.indexof_re` (not in the SMT-LIB
//! `UnicodeStrings` theory and unsupported by the Z3 oracle), `str.to_re` of a
//! **non-literal** string (would require matching against a symbolic string),
//! `str.replace_re`/`str.replace_re_all` over a **non-constant** string operand
//! (the leftmost-shortest regex splice over a symbolic string is a scoped
//! follow-up), and any regex whose NFA/DFA exceeds [`MAX_NFA_STATES`].

use std::collections::BTreeSet;

use axeyum_ir::{Sort, TermArena, TermId};

use crate::SmtError;
use crate::sexpr::SExpr;

/// Hard cap on the NFA state count. A regex compiling past this declines as
/// [`SmtError::Unsupported`] (a sound `unknown`) rather than building a giant
/// `reach[pos][state]` formula or hanging. Generous enough for the curated
/// corpus's regexes, bounded enough to keep `m × |NFA|` formulas tractable.
const MAX_NFA_STATES: usize = 256;

/// A character-class predicate on a single byte of the string.
#[derive(Clone, Copy, Debug)]
enum CharClass {
    /// Any byte (`re.allchar` / the per-position class of `re.all`).
    Any,
    /// Exactly this byte (one character of a `str.to_re` literal).
    Exact(u8),
    /// A byte in the inclusive range `lo..=hi` (`re.range`).
    Range(u8, u8),
}

impl CharClass {
    /// Builds the Boolean predicate "`byte` (a `BitVec(8)`) is in this class".
    fn predicate(self, arena: &mut TermArena, byte: TermId) -> Result<TermId, SmtError> {
        match self {
            CharClass::Any => Ok(arena.bool_const(true)),
            CharClass::Exact(b) => {
                let c = arena.bv_const(8, u128::from(b))?;
                arena.eq(byte, c).map_err(SmtError::Ir)
            }
            CharClass::Range(lo, hi) => {
                let loc = arena.bv_const(8, u128::from(lo))?;
                let hic = arena.bv_const(8, u128::from(hi))?;
                let ge = arena.bv_ule(loc, byte)?; // lo ≤ byte
                let le = arena.bv_ule(byte, hic)?; // byte ≤ hi
                arena.and(ge, le).map_err(SmtError::Ir)
            }
        }
    }
}

/// Whether byte `b` is in character class `class` (concrete companion of
/// [`CharClass::predicate`], used by the product construction).
fn class_matches(class: CharClass, b: u8) -> bool {
    match class {
        CharClass::Any => true,
        CharClass::Exact(x) => b == x,
        CharClass::Range(lo, hi) => lo <= b && b <= hi,
    }
}

/// One NFA transition out of a state: an ε-move (`None`) or a character move
/// (`Some(class)`) consuming one byte.
#[derive(Clone, Copy, Debug)]
struct Transition {
    /// `None` for an ε-transition; `Some(class)` for a character transition.
    class: Option<CharClass>,
    /// Destination state index.
    to: usize,
}

/// A Thompson NFA: states `0..states`, a single `start`, a set of `accepting`
/// states, and an adjacency list of out-transitions per state.
#[derive(Clone, Debug)]
struct Nfa {
    start: usize,
    accepting: BTreeSet<usize>,
    /// `out[q]` = transitions leaving state `q`.
    out: Vec<Vec<Transition>>,
}

impl Nfa {
    fn new() -> Self {
        Nfa {
            start: 0,
            accepting: BTreeSet::new(),
            out: Vec::new(),
        }
    }

    /// Allocates a fresh state, declining if the cap would be exceeded.
    fn fresh(&mut self) -> Result<usize, SmtError> {
        if self.out.len() >= MAX_NFA_STATES {
            return Err(SmtError::Unsupported(format!(
                "regex NFA exceeds the {MAX_NFA_STATES}-state cap (ADR-0029); declined"
            )));
        }
        let q = self.out.len();
        self.out.push(Vec::new());
        Ok(q)
    }

    fn add_eps(&mut self, from: usize, to: usize) {
        self.out[from].push(Transition { class: None, to });
    }

    fn add_char(&mut self, from: usize, class: CharClass, to: usize) {
        self.out[from].push(Transition {
            class: Some(class),
            to,
        });
    }

    /// The ε-closure of `seed`: every state reachable through ε-transitions
    /// alone. Used to seed `reach[0]` and to close each post-step set.
    fn eps_closure(&self, seed: &BTreeSet<usize>) -> BTreeSet<usize> {
        let mut closure = seed.clone();
        let mut stack: Vec<usize> = seed.iter().copied().collect();
        while let Some(q) = stack.pop() {
            for t in &self.out[q] {
                if t.class.is_none() && closure.insert(t.to) {
                    stack.push(t.to);
                }
            }
        }
        closure
    }
}

/// A compiled regex fragment: an NFA with a single `start` and a single `exit`
/// (the Thompson invariant), so fragments compose by ε-wiring `exit → start`.
struct Fragment {
    start: usize,
    exit: usize,
}

/// A parsed regex AST over byte character classes. The variants mirror the
/// supported `RegLan` constructs; everything else declines at parse time.
#[derive(Clone, Debug)]
enum Regex {
    /// The empty string `ε` (e.g. `(str.to_re "")`).
    Empty,
    /// The empty language `∅` (`re.none`, or a degenerate `re.range`).
    None,
    /// A single character matching this class.
    Char(CharClass),
    /// Concatenation `R1 R2 …`.
    Concat(Vec<Regex>),
    /// Alternation `R1 | R2 | …`.
    Union(Vec<Regex>),
    /// Intersection `R1 ∩ R2 ∩ …` (top-level only).
    Inter(Vec<Regex>),
    /// Complement `Σ* \ R` (top-level only; built by DFA determinization + flip).
    Comp(Box<Regex>),
    /// Difference `R1 \ R2` = `R1 ∩ comp(R2)` (top-level only).
    Diff(Box<Regex>, Box<Regex>),
    /// Kleene star `R*`.
    Star(Box<Regex>),
    /// One or more `R+`.
    Plus(Box<Regex>),
    /// Zero or one `R?`.
    Opt(Box<Regex>),
}

/// Compiles the regex `expr` into `nfa`, returning the fragment's
/// (start, exit) states. The fragment matches its language between `start`
/// (entry) and `exit` (a single accepting hand-off).
fn compile(nfa: &mut Nfa, expr: &Regex) -> Result<Fragment, SmtError> {
    match expr {
        Regex::Empty => {
            // ε: a start that ε-moves to its exit (matches the empty string).
            let start = nfa.fresh()?;
            let exit = nfa.fresh()?;
            nfa.add_eps(start, exit);
            Ok(Fragment { start, exit })
        }
        Regex::None => {
            // ∅: a start and a *disconnected* exit — no path, matches nothing.
            let start = nfa.fresh()?;
            let exit = nfa.fresh()?;
            Ok(Fragment { start, exit })
        }
        Regex::Char(class) => {
            let start = nfa.fresh()?;
            let exit = nfa.fresh()?;
            nfa.add_char(start, *class, exit);
            Ok(Fragment { start, exit })
        }
        Regex::Concat(parts) => {
            // ε-wire the parts end-to-start. An empty concat is ε.
            if parts.is_empty() {
                return compile(nfa, &Regex::Empty);
            }
            let mut iter = parts.iter();
            let first = compile(nfa, iter.next().expect("non-empty"))?;
            let start = first.start;
            let mut exit = first.exit;
            for part in iter {
                let frag = compile(nfa, part)?;
                nfa.add_eps(exit, frag.start);
                exit = frag.exit;
            }
            Ok(Fragment { start, exit })
        }
        Regex::Union(parts) => {
            // A fresh start ε-branches into each alternative; each alternative's
            // exit ε-merges into a fresh exit. An empty union is ∅.
            if parts.is_empty() {
                return compile(nfa, &Regex::None);
            }
            let start = nfa.fresh()?;
            let exit = nfa.fresh()?;
            for part in parts {
                let frag = compile(nfa, part)?;
                nfa.add_eps(start, frag.start);
                nfa.add_eps(frag.exit, exit);
            }
            Ok(Fragment { start, exit })
        }
        Regex::Star(inner) => {
            // start ─ε→ exit (zero), start ─ε→ inner.start, inner.exit ─ε→
            // inner.start (loop) and ─ε→ exit.
            let start = nfa.fresh()?;
            let exit = nfa.fresh()?;
            let frag = compile(nfa, inner)?;
            nfa.add_eps(start, frag.start);
            nfa.add_eps(start, exit);
            nfa.add_eps(frag.exit, frag.start);
            nfa.add_eps(frag.exit, exit);
            Ok(Fragment { start, exit })
        }
        Regex::Plus(inner) => {
            // R+ = R ++ R*: like star but the entry must take the body at least
            // once (no start ─ε→ exit edge).
            let start = nfa.fresh()?;
            let exit = nfa.fresh()?;
            let frag = compile(nfa, inner)?;
            nfa.add_eps(start, frag.start);
            nfa.add_eps(frag.exit, frag.start);
            nfa.add_eps(frag.exit, exit);
            Ok(Fragment { start, exit })
        }
        Regex::Opt(inner) => {
            // R? = R | ε.
            let start = nfa.fresh()?;
            let exit = nfa.fresh()?;
            let frag = compile(nfa, inner)?;
            nfa.add_eps(start, frag.start);
            nfa.add_eps(start, exit);
            nfa.add_eps(frag.exit, exit);
            Ok(Fragment { start, exit })
        }
        Regex::Inter(_) => {
            // Intersection has no single-fragment Thompson form; it is handled at
            // the top level by an explicit product. It cannot appear nested here
            // because `build_nfa`/`build_inter_nfa` special-case it.
            Err(SmtError::Unsupported(
                "re.inter nested inside another regex construct is declined (ADR-0029)".to_owned(),
            ))
        }
        Regex::Comp(_) | Regex::Diff(..) => {
            // Complement/difference require a *complete* determinized DFA; there is
            // no single-fragment Thompson form. They are handled at the top level by
            // [`build_nfa`]. Nesting one inside another construct is declined.
            Err(SmtError::Unsupported(
                "re.comp/re.diff nested inside another regex construct is declined (ADR-0029)"
                    .to_owned(),
            ))
        }
    }
}

/// A minimal borrowed view of a regex s-expression. The parser hands its own
/// [`SExpr`] regex argument and we convert it here, so the regex module sees only
/// atoms and `(head, args)` applications.
pub(crate) enum RegexSexpr<'a> {
    Atom(&'a str),
    List(&'a str, Vec<RegexSexpr<'a>>),
}

/// Converts a parser [`SExpr`] into a [`RegexSexpr`]. An application whose head
/// is **not** a plain atom — e.g. the indexed `((_ re.loop 0 2) R)` form — has no
/// supported regex op, so it is mapped to an unrecognized `List` head that
/// [`parse_regex_app`] declines cleanly.
fn from_sexpr(e: &SExpr) -> RegexSexpr<'_> {
    match e {
        SExpr::Atom(a) => RegexSexpr::Atom(a),
        SExpr::List(items) => {
            let head = items
                .first()
                .and_then(SExpr::atom)
                .unwrap_or("(unsupported-head)");
            let args = items[1.min(items.len())..].iter().map(from_sexpr).collect();
            RegexSexpr::List(head, args)
        }
    }
}

/// The outcome of decoding a string-literal s-expression atom into SMT-LIB
/// **code points** (characters). The byte model represents one character as one
/// byte, so a code point outside `0..=255` cannot be represented — that case is
/// distinguished from "not a literal" so the regex parser **declines** (never
/// silently treating it as the empty language, which would risk a wrong verdict).
enum LiteralChars {
    /// Not a string-literal atom at all.
    NotLiteral,
    /// A literal whose every code point is `≤ 255` (representable as a byte).
    Bytes(Vec<u8>),
    /// A literal containing a code point `> 255` (or a malformed escape): the
    /// byte model cannot represent it, so the enclosing regex must decline.
    OutOfByteRange,
}

/// Decodes a string-literal atom (`"..."`) into its SMT-LIB code points and maps
/// each to a byte when `≤ 255`. Handles the `UnicodeStrings` escapes `\u{X…}`
/// (1–5 hex digits in braces) and `\uXXXX` (exactly four hex digits); a doubled
/// `""` is one literal quote; every other byte is taken verbatim (the corpus
/// literals are ASCII/Latin-1 outside the escapes). Any code point above `255`
/// or a malformed escape yields [`LiteralChars::OutOfByteRange`] so the caller
/// declines rather than guesses.
fn literal_chars(atom: &str) -> LiteralChars {
    if !(atom.len() >= 2 && atom.starts_with('"') && atom.ends_with('"')) {
        return LiteralChars::NotLiteral;
    }
    let inner = atom[1..atom.len() - 1].replace("\"\"", "\"");
    let bytes = inner.as_bytes();
    let mut out: Vec<u8> = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        // An SMT-LIB Unicode escape begins `\u`. Everything else is one verbatim
        // byte (the literal's own UTF-8 byte, which for ASCII is the character).
        if bytes[i] == b'\\' && i + 1 < bytes.len() && bytes[i + 1] == b'u' {
            let after = i + 2;
            let code = if bytes.get(after) == Some(&b'{') {
                // \u{H…}: hex digits until the closing brace.
                let Some(close) = bytes[after + 1..].iter().position(|&c| c == b'}') else {
                    return LiteralChars::OutOfByteRange; // malformed
                };
                let hex = &inner[after + 1..after + 1 + close];
                let Ok(v) = u32::from_str_radix(hex, 16) else {
                    return LiteralChars::OutOfByteRange;
                };
                i = after + 1 + close + 1;
                v
            } else if after + 4 <= bytes.len() {
                // \uXXXX: exactly four hex digits.
                let hex = &inner[after..after + 4];
                let Ok(v) = u32::from_str_radix(hex, 16) else {
                    return LiteralChars::OutOfByteRange;
                };
                i = after + 4;
                v
            } else {
                return LiteralChars::OutOfByteRange; // malformed `\u`
            };
            if code > 0xff {
                return LiteralChars::OutOfByteRange;
            }
            out.push(u8::try_from(code).expect("code ≤ 0xff"));
        } else {
            out.push(bytes[i]);
            i += 1;
        }
    }
    LiteralChars::Bytes(out)
}

/// Decodes a `re.range` endpoint literal to its single byte. Returns
/// `Ok(Some(b))` for a single-character literal in the byte range, `Ok(None)`
/// for a literal that is empty or has more than one character (a degenerate
/// range → the empty language `∅`, per the theory), and `Err(Unsupported)` when
/// the endpoint is not a literal at all or holds a code point outside the byte
/// model (where collapsing to `∅` could be a wrong verdict).
fn range_endpoint(atom: &str) -> Result<Option<u8>, SmtError> {
    match literal_chars(atom) {
        LiteralChars::Bytes(bytes) => match bytes.as_slice() {
            [b] => Ok(Some(*b)),
            // Empty or multi-character endpoint: degenerate range → ∅.
            _ => Ok(None),
        },
        LiteralChars::NotLiteral => Err(SmtError::Unsupported(
            "re.range endpoint is not a string literal; declined (ADR-0029)".to_owned(),
        )),
        LiteralChars::OutOfByteRange => Err(SmtError::Unsupported(
            "re.range endpoint has a code point outside the byte model (> 255); \
             declined (ADR-0029)"
                .to_owned(),
        )),
    }
}

/// A literal byte string compiled to a regex matching exactly those bytes
/// (`(str.to_re lit)`): an empty literal is `ε`, otherwise a concatenation of
/// exact-byte single characters.
fn literal_regex(bytes: &[u8]) -> Regex {
    if bytes.is_empty() {
        Regex::Empty
    } else {
        Regex::Concat(
            bytes
                .iter()
                .map(|&b| Regex::Char(CharClass::Exact(b)))
                .collect(),
        )
    }
}

/// Parses a `RegLan` s-expression into a [`Regex`]. Declines (clean
/// [`SmtError::Unsupported`]) any construct outside the supported fragment, so a
/// regex the encoding cannot prove correct never produces a verdict.
fn parse_regex(re: &RegexSexpr<'_>) -> Result<Regex, SmtError> {
    match re {
        RegexSexpr::Atom(a) => match *a {
            "re.allchar" => Ok(Regex::Char(CharClass::Any)),
            "re.all" => Ok(Regex::Star(Box::new(Regex::Char(CharClass::Any)))),
            "re.none" => Ok(Regex::None),
            other => Err(SmtError::Unsupported(format!(
                "regex constant `{other}` is outside the wired bounded subset (ADR-0029)"
            ))),
        },
        RegexSexpr::List(head, args) => parse_regex_app(head, args),
    }
}

/// Parses a regex *application* `(head arg …)`.
fn parse_regex_app(head: &str, args: &[RegexSexpr<'_>]) -> Result<Regex, SmtError> {
    match head {
        "str.to_re" => {
            let [arg] = args else {
                return Err(SmtError::Unsupported(
                    "str.to_re expects exactly one argument".to_owned(),
                ));
            };
            // Only a literal string compiles to a fixed-language regex. A
            // symbolic `str.to_re x` would require matching against an unknown
            // string — declined as a sound `unknown`. A literal with a code point
            // outside the byte model (`> 255`) also declines (never a wrong
            // verdict from silently dropping it).
            let RegexSexpr::Atom(a) = arg else {
                return Err(SmtError::Unsupported(
                    "str.to_re of a non-literal string is declined (ADR-0029)".to_owned(),
                ));
            };
            match literal_chars(a) {
                LiteralChars::Bytes(bytes) => Ok(literal_regex(&bytes)),
                LiteralChars::NotLiteral => Err(SmtError::Unsupported(
                    "str.to_re of a non-literal string is declined (ADR-0029)".to_owned(),
                )),
                LiteralChars::OutOfByteRange => Err(SmtError::Unsupported(
                    "str.to_re literal has a code point outside the byte model (> 255); \
                     declined (ADR-0029)"
                        .to_owned(),
                )),
            }
        }
        "re.range" => {
            let [lo, hi] = args else {
                return Err(SmtError::Unsupported(
                    "re.range expects exactly two arguments".to_owned(),
                ));
            };
            // `(re.range l h)` matches a single character whose code point is in
            // `[l, h]` when `l`, `h` are single-character literals. Per the
            // SMT-LIB UnicodeStrings theory a non-single-character endpoint (or
            // `l > h`) denotes the empty language `∅`. But an endpoint whose code
            // point is **outside the byte model** is not "empty" — it is a real
            // character we cannot represent, so we **decline** (Unsupported)
            // rather than collapse to `∅` (which would risk a wrong verdict).
            let (RegexSexpr::Atom(la), RegexSexpr::Atom(ha)) = (lo, hi) else {
                return Ok(Regex::None);
            };
            let l = range_endpoint(la)?;
            let h = range_endpoint(ha)?;
            match (l, h) {
                (Some(l), Some(h)) if l <= h => Ok(Regex::Char(CharClass::Range(l, h))),
                // `l > h`, or a non-single-character endpoint → empty language.
                _ => Ok(Regex::None),
            }
        }
        "re.++" => Ok(Regex::Concat(parse_regex_args(args)?)),
        "re.union" => Ok(Regex::Union(parse_regex_args(args)?)),
        "re.inter" => Ok(Regex::Inter(parse_regex_args(args)?)),
        "re.comp" => Ok(Regex::Comp(Box::new(parse_regex_one(args)?))),
        "re.diff" => {
            let [r1, r2] = args else {
                return Err(SmtError::Unsupported(
                    "re.diff expects exactly two arguments".to_owned(),
                ));
            };
            Ok(Regex::Diff(
                Box::new(parse_regex(r1)?),
                Box::new(parse_regex(r2)?),
            ))
        }
        "re.*" => Ok(Regex::Star(Box::new(parse_regex_one(args)?))),
        "re.+" => Ok(Regex::Plus(Box::new(parse_regex_one(args)?))),
        "re.opt" => Ok(Regex::Opt(Box::new(parse_regex_one(args)?))),
        other => Err(SmtError::Unsupported(format!(
            "regex operator `{other}` is outside the wired bounded subset (ADR-0029)"
        ))),
    }
}

/// Parses each argument as a regex (for the n-ary `re.++`/`re.union`/`re.inter`).
fn parse_regex_args(args: &[RegexSexpr<'_>]) -> Result<Vec<Regex>, SmtError> {
    if args.is_empty() {
        return Err(SmtError::Unsupported(
            "n-ary regex operator with no arguments is declined (ADR-0029)".to_owned(),
        ));
    }
    args.iter().map(parse_regex).collect()
}

/// Parses the single argument of `re.*`/`re.+`/`re.opt`.
fn parse_regex_one(args: &[RegexSexpr<'_>]) -> Result<Regex, SmtError> {
    let [arg] = args else {
        return Err(SmtError::Unsupported(
            "unary regex operator expects exactly one argument".to_owned(),
        ));
    };
    parse_regex(arg)
}

/// Compiles a [`Regex`] AST to a single NFA, handling a **top-level**
/// `re.inter` by an explicit product (intersection has no single-fragment
/// Thompson form). A nested `re.inter` declines (see [`compile`]).
fn build_nfa(regex: &Regex) -> Result<Nfa, SmtError> {
    match regex {
        Regex::Inter(parts) => return build_inter_nfa(parts),
        Regex::Comp(inner) => return build_comp_nfa(inner),
        // `R1 \ R2` = `R1 ∩ comp(R2)`: reuse the intersection product over `R1` and
        // the complemented DFA of `R2`.
        Regex::Diff(r1, r2) => {
            let n1 = build_nfa(r1)?;
            let n2 = build_comp_nfa(r2)?;
            return product_intersection(&[n1, n2]);
        }
        _ => {}
    }
    let mut nfa = Nfa::new();
    let frag = compile(&mut nfa, regex)?;
    nfa.start = frag.start;
    nfa.accepting.insert(frag.exit);
    Ok(nfa)
}

/// Builds the NFA (a complete DFA) for `(re.comp R)` = `Σ* \ L(R)`.
///
/// Determinizes `R`'s NFA to a DFA by the subset construction over the full byte
/// alphabet, **completes** the transition function by routing every missing
/// `state × byte` to an explicit dead (empty-subset) state, then flips the
/// accepting set. Completion is what makes the flip a sound complement: in a
/// complete DFA every string drives the run to exactly one state, so "`R` rejects
/// `w`" ⇔ "the run on `w` ends in a non-`R`-accepting (hence dead-or-other) DFA
/// state" ⇔ "the run ends in an accepting state of the flipped automaton". A
/// *partial* DFA would let a run "fall off" with no state, and flipping would
/// then wrongly classify that string. Bounded by [`MAX_NFA_STATES`]; a blow-up of
/// the subset construction declines as a sound `unknown`. A nested complement /
/// difference declines (see [`compile`]).
fn build_comp_nfa(inner: &Regex) -> Result<Nfa, SmtError> {
    if matches!(inner, Regex::Comp(_) | Regex::Diff(..) | Regex::Inter(_)) {
        return Err(SmtError::Unsupported(
            "re.comp of a re.comp/re.diff/re.inter is declined (ADR-0029)".to_owned(),
        ));
    }
    let nfa = build_nfa(inner)?;
    let dfa = determinize_complete(&nfa)?;
    Ok(complement_dfa(dfa))
}

/// Subset-constructs a **complete** DFA from `nfa`: a deterministic, fully
/// total automaton whose every state has a transition on each of the 256 bytes
/// (missing transitions go to an explicit dead state, the empty subset). The
/// result is itself an [`Nfa`] (a DFA is a special NFA) with ε-free
/// [`CharClass::Exact`] transitions, exactly one per `(state, byte)`. Bounded by
/// [`MAX_NFA_STATES`].
fn determinize_complete(nfa: &Nfa) -> Result<Nfa, SmtError> {
    use std::collections::HashMap;

    let mut dfa = Nfa::new();
    // Index a DFA state by its ε-closed NFA subset. The dead state is the **empty**
    // subset; create it eagerly so completion always has a target.
    let mut index: HashMap<BTreeSet<usize>, usize> = HashMap::new();

    let empty: BTreeSet<usize> = BTreeSet::new();
    let dead = dfa.fresh()?;
    index.insert(empty.clone(), dead);
    // The dead state self-loops on every byte (it is a sink); add those edges so
    // the DFA is complete and the dead subset is reachable/total.
    for byte in 0u16..256 {
        let b = u8::try_from(byte).expect("0..256");
        dfa.add_char(dead, CharClass::Exact(b), dead);
    }

    let mut start_seed = BTreeSet::new();
    start_seed.insert(nfa.start);
    let start = nfa.eps_closure(&start_seed);
    let q0 = if start.is_empty() {
        dead
    } else {
        let id = dfa.fresh()?;
        index.insert(start.clone(), id);
        id
    };
    dfa.start = q0;

    let mut worklist: Vec<(BTreeSet<usize>, usize)> = Vec::new();
    if q0 != dead {
        worklist.push((start, q0));
    }
    while let Some((subset, did)) = worklist.pop() {
        if subset.iter().any(|q| nfa.accepting.contains(q)) {
            dfa.accepting.insert(did);
        }
        for byte in 0u16..256 {
            let b = u8::try_from(byte).expect("0..256");
            let stepped = step_byte(nfa, &subset, b);
            let closed = nfa.eps_closure(&stepped);
            let to = if let Some(&id) = index.get(&closed) {
                id
            } else {
                // A genuinely-empty step lands on the pre-made dead state; a new
                // non-empty subset becomes a fresh DFA state.
                let id = dfa.fresh()?;
                index.insert(closed.clone(), id);
                worklist.push((closed, id));
                id
            };
            dfa.add_char(did, CharClass::Exact(b), to);
        }
    }
    Ok(dfa)
}

/// Flips the accepting set of a **complete** DFA in place: a state is accepting
/// in the complement iff it was non-accepting in `dfa`. The caller guarantees
/// completeness (every `state × byte` has a target), so the flip is the exact
/// complement language `Σ* \ L(dfa)`.
fn complement_dfa(mut dfa: Nfa) -> Nfa {
    let n = dfa.out.len();
    let new_accepting: BTreeSet<usize> = (0..n).filter(|q| !dfa.accepting.contains(q)).collect();
    dfa.accepting = new_accepting;
    dfa
}

/// Builds the NFA for a top-level `(re.inter R1 R2 …)` by the synchronous
/// product of the component NFAs (a determinized subset product over the byte
/// alphabet). Bounded by [`MAX_NFA_STATES`]; a blow-up declines as a sound
/// `unknown`. A nested `re.inter` is declined.
fn build_inter_nfa(parts: &[Regex]) -> Result<Nfa, SmtError> {
    if parts.is_empty() {
        return Err(SmtError::Unsupported(
            "re.inter with no arguments is declined (ADR-0029)".to_owned(),
        ));
    }
    let mut comps: Vec<Nfa> = Vec::with_capacity(parts.len());
    for part in parts {
        if matches!(part, Regex::Inter(_)) {
            return Err(SmtError::Unsupported(
                "nested re.inter is declined (ADR-0029)".to_owned(),
            ));
        }
        comps.push(build_nfa(part)?);
    }
    product_intersection(&comps)
}

/// The subset/product intersection of `comps`, returned as an ε-free NFA whose
/// states are tuples of ε-closed subsets (one per component): a product state is
/// accepting iff every component subset contains one of its accepting states,
/// and reads byte `b` to the product of each component's `b`-successor subset.
/// Bounded by [`MAX_NFA_STATES`].
fn product_intersection(comps: &[Nfa]) -> Result<Nfa, SmtError> {
    use std::collections::HashMap;

    // A product state is one ε-closed subset per component.
    type ProductState = Vec<BTreeSet<usize>>;

    let start: ProductState = comps
        .iter()
        .map(|c| {
            let mut s = BTreeSet::new();
            s.insert(c.start);
            c.eps_closure(&s)
        })
        .collect();

    let mut nfa = Nfa::new();
    let mut index: HashMap<ProductState, usize> = HashMap::new();
    let q0 = nfa.fresh()?;
    index.insert(start.clone(), q0);
    nfa.start = q0;
    let mut worklist = vec![(start, q0)];

    while let Some((pstate, pid)) = worklist.pop() {
        let all_accept = comps
            .iter()
            .zip(&pstate)
            .all(|(c, sub)| sub.iter().any(|q| c.accepting.contains(q)));
        if all_accept {
            nfa.accepting.insert(pid);
        }
        // Enumerate the full byte alphabet: the product is exact for `Any`/`Range`
        // classes because each byte is classified concretely. `m × 256` work is
        // bounded and the construction is obviously correct.
        for byte in 0u16..256 {
            let b = u8::try_from(byte).expect("0..256");
            let mut next: ProductState = Vec::with_capacity(comps.len());
            let mut dead = false;
            for (c, sub) in comps.iter().zip(&pstate) {
                let stepped = step_byte(c, sub, b);
                if stepped.is_empty() {
                    dead = true;
                    break;
                }
                next.push(c.eps_closure(&stepped));
            }
            if dead {
                continue;
            }
            let to = if let Some(&id) = index.get(&next) {
                id
            } else {
                let id = nfa.fresh()?;
                index.insert(next.clone(), id);
                worklist.push((next, id));
                id
            };
            nfa.add_char(pid, CharClass::Exact(b), to);
        }
    }
    Ok(nfa)
}

/// The set of states reachable from the ε-closed subset `sub` of NFA `c` by
/// consuming one byte equal to `b` (before re-ε-closing). Used by the product
/// intersection.
fn step_byte(c: &Nfa, sub: &BTreeSet<usize>, b: u8) -> BTreeSet<usize> {
    let mut out = BTreeSet::new();
    for &q in sub {
        for t in &c.out[q] {
            if let Some(class) = t.class
                && class_matches(class, b)
            {
                out.insert(t.to);
            }
        }
    }
    out
}

/// Encodes `(str.in_re s R)` over the packed string `s` as a Boolean term: the
/// bounded reachable-state acceptance described in the module docs.
///
/// `s` must be a packed-string-shaped bit-vector (else a clean decline). The
/// returned term is `true` exactly when the ≤`m`-byte string `s` is in the
/// language of `R`.
///
/// # Errors
///
/// [`SmtError::Unsupported`] when `R` uses a declined construct, when its NFA
/// exceeds the state cap, or when `s` is not a packed string.
pub(crate) fn encode_in_re(
    arena: &mut TermArena,
    s: TermId,
    re: &SExpr,
) -> Result<TermId, SmtError> {
    let view = from_sexpr(re);
    let regex = parse_regex(&view)?;
    let nfa = build_nfa(&regex)?;
    let m = packed_string_max_len(arena, s)?;
    encode_match(arena, s, &nfa, m)
}

/// A compiled regex over the byte alphabet, ready for **concrete** simulation on
/// a known byte string. Used by the ground `str.replace_re`/`str.replace_re_all`
/// path (where `s` is a literal): a compiled regex is matched against each
/// substring `s[i..j]` to find the leftmost-shortest match.
pub(crate) struct CompiledRegex {
    nfa: Nfa,
}

impl CompiledRegex {
    /// Whether `bytes` is in the language of the compiled regex (a concrete NFA
    /// simulation: track the ε-closed reachable-state set across the bytes, accept
    /// iff a final state is reached after the last byte).
    pub(crate) fn matches(&self, bytes: &[u8]) -> bool {
        let mut seed = BTreeSet::new();
        seed.insert(self.nfa.start);
        let mut cur = self.nfa.eps_closure(&seed);
        for &b in bytes {
            let stepped = step_byte(&self.nfa, &cur, b);
            cur = self.nfa.eps_closure(&stepped);
            if cur.is_empty() {
                return false; // stuck — no continuation can accept
            }
        }
        cur.iter().any(|q| self.nfa.accepting.contains(q))
    }
}

/// Compiles a `RegLan` s-expression into a [`CompiledRegex`] for concrete
/// substring matching. Declines (clean [`SmtError::Unsupported`]) the same
/// constructs [`encode_in_re`] declines, including a DFA/NFA over the state cap.
pub(crate) fn compile_regex(re: &SExpr) -> Result<CompiledRegex, SmtError> {
    let view = from_sexpr(re);
    let regex = parse_regex(&view)?;
    let nfa = build_nfa(&regex)?;
    Ok(CompiledRegex { nfa })
}

/// Recovers the bounded maximum length `m` of the packed string `s` from its
/// bit-vector width. Declines if `s` is not a packed-string-shaped bit-vector.
fn packed_string_max_len(arena: &TermArena, s: TermId) -> Result<u32, SmtError> {
    let Sort::BitVec(w) = arena.sort_of(s) else {
        return Err(SmtError::Unsupported(
            "str.in_re of a non-string operand is declined (ADR-0029)".to_owned(),
        ));
    };
    // Mirror `string_max_len_of` / `string_total` from `parse.rs`: a packed
    // string of max length `m` has width `len_width(m) + 8m`.
    (1..=crate::parse::STRING_BOUND_CAP)
        .find(|&m| crate::parse::string_total(m) == w)
        .ok_or_else(|| {
            SmtError::Unsupported(format!(
                "str.in_re of a non-string `BitVec({w})` is declined (ADR-0029)"
            ))
        })
}

/// Balanced disjunction of `terms` (empty ⇒ `false`). A pairwise tree keeps the
/// resulting term **shallow** (depth `O(log k)`), so a large NFA cannot build a
/// linear-depth `or` chain that overflows the stack of a downstream recursive
/// traversal (the hard rule against adversarial-depth blow-ups).
fn balanced_or(arena: &mut TermArena, terms: &[TermId]) -> Result<TermId, SmtError> {
    if terms.is_empty() {
        return Ok(arena.bool_const(false));
    }
    let mut layer: Vec<TermId> = terms.to_vec();
    while layer.len() > 1 {
        let mut next = Vec::with_capacity(layer.len().div_ceil(2));
        let mut i = 0;
        while i + 1 < layer.len() {
            next.push(arena.or(layer[i], layer[i + 1])?);
            i += 2;
        }
        if i < layer.len() {
            next.push(layer[i]);
        }
        layer = next;
    }
    Ok(layer[0])
}

/// For each NFA state `q`, the set of states ε-reachable from `q` (including `q`
/// itself). Precomputed once so the symbolic step's ε-closure is a single **flat,
/// balanced** disjunction per state rather than a deep `n`-round fixpoint of
/// chained `or`s (which produced linear-depth terms and overflowed downstream).
fn eps_reach_sets(nfa: &Nfa) -> Vec<BTreeSet<usize>> {
    (0..nfa.out.len())
        .map(|q| {
            let mut seed = BTreeSet::new();
            seed.insert(q);
            nfa.eps_closure(&seed)
        })
        .collect()
}

/// The core bounded-matching encoding: `reach[pos][q]` Booleans for
/// `pos ∈ 0..=m`, accept selected at `pos = len(s)`.
fn encode_match(arena: &mut TermArena, s: TermId, nfa: &Nfa, m: u32) -> Result<TermId, SmtError> {
    let n = nfa.out.len();
    let lwm = crate::parse::len_width(m);
    let len = arena.extract(lwm - 1, 0, s)?; // length field, BitVec(lwm)

    // Static ε-closure per state (independent of the string) — see docs above.
    let eps_from = eps_reach_sets(nfa);
    // Inverse: `eps_into[t]` = every `q` that ε-reaches `t`. A `t` is in the
    // closed set iff some such `q` is in the raw set.
    let mut eps_into: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (q, set) in eps_from.iter().enumerate() {
        for &t in set {
            eps_into[t].push(q);
        }
    }

    // reach[0] = ε-closure of {start}, as Boolean constants.
    let mut seed = BTreeSet::new();
    seed.insert(nfa.start);
    let start_closure = nfa.eps_closure(&seed);
    let mut reach: Vec<TermId> = (0..n)
        .map(|q| arena.bool_const(start_closure.contains(&q)))
        .collect();

    // accept_here[pos] terms (collected, then balanced-OR'd at the end).
    let mut accept_terms: Vec<TermId> = Vec::with_capacity(m as usize + 1);

    for pos in 0..=m {
        let pconst = arena.bv_const(lwm, u128::from(pos))?;
        let len_is_pos = arena.eq(len, pconst)?;
        let finals: Vec<TermId> = nfa.accepting.iter().map(|&f| reach[f]).collect();
        let any_final = balanced_or(arena, &finals)?;
        let accept_here = arena.and(len_is_pos, any_final)?;
        accept_terms.push(accept_here);

        if pos == m {
            break; // no byte at position m; the loop only advances `reach` below.
        }

        // Advance one byte: raw[t] from char transitions reading s[pos], guarded
        // by present(pos) = (pos < len); then ε-close flatly into `closed`.
        let byte = packed_byte(arena, s, pos, m)?;
        let pconst_pres = arena.bv_const(lwm, u128::from(pos))?;
        let present = arena.bv_ult(pconst_pres, len)?; // pos < len(s)

        // raw_terms[t] = list of (reach[q] ∧ present ∧ class(byte)) over q→t edges.
        let mut raw_terms: Vec<Vec<TermId>> = vec![Vec::new(); n];
        for (q, edges) in nfa.out.iter().enumerate() {
            for t in edges {
                if let Some(class) = t.class {
                    let pred = class.predicate(arena, byte)?;
                    let step0 = arena.and(reach[q], present)?;
                    let step = arena.and(step0, pred)?;
                    raw_terms[t.to].push(step);
                }
            }
        }
        let raw: Vec<TermId> = raw_terms
            .iter()
            .map(|ts| balanced_or(arena, ts))
            .collect::<Result<_, _>>()?;

        // closed[t] = ∨ over q that ε-reaches t of raw[q]. Flat balanced OR — the
        // static ε-closure already captured arbitrary ε-chains, so no fixpoint
        // and no deep chaining.
        let mut closed: Vec<TermId> = Vec::with_capacity(n);
        for into in &eps_into {
            let sources: Vec<TermId> = into.iter().map(|&q| raw[q]).collect();
            closed.push(balanced_or(arena, &sources)?);
        }
        reach = closed;
    }

    balanced_or(arena, &accept_terms)
}

/// Content byte `pos` (a `BitVec(8)`) of a packed string of max length `m`
/// (mirrors `string_byte_m` in `parse.rs`).
fn packed_byte(arena: &mut TermArena, s: TermId, pos: u32, m: u32) -> Result<TermId, SmtError> {
    let lo = crate::parse::len_width(m) + pos * 8;
    arena.extract(lo + 7, lo, s).map_err(SmtError::Ir)
}
