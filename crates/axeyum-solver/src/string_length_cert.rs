//! Length/code-point abstraction refutations for the string family: abstract
//! every string term to an integer length variable, name the theory lemmas the
//! argument actually uses, and close with a Farkas-style linear combination.
//!
//! # The shapes, all from committed corpus files
//!
//! ```text
//! QF_S/cvc5-regress-clean/r0_QF_SLIA_str004.smt2
//!   (assert (> (str.len yy) (str.len xx)))  (assert (= xx (str.++ xx yy)))
//!   -- |xx| = |xx| + |yy| forces |yy| = 0, contradicting |yy| > |xx| >= 0
//!
//! QF_S/cvc5-regress-clean/r0_QF_S_str005.smt2
//!   (assert (= (str.len yy) 0))  (assert (not (= yy "")))
//!   -- |yy| = 0 and yy != "" (so |yy| >= 1)
//!
//! QF_S/cvc5-regress-clean/r1_QF_SLIA_str-code-unsat-2.smt2
//!   (assert (= (str.len x) 1))
//!   (assert (or (< (str.to_code x) 0) (> (str.to_code x) 10^28)))
//!   -- |x| = 1 puts (str.to_code x) in [0, 0x2FFFF]; both arms leave it
//! ```
//!
//! All three shipped as bare `Evidence::Unsat(None)` from the string front door
//! (`bench-results/dominance/qf-s-cvc5-regress-clean-dominance-audit.json`): the
//! verdict was correct and nothing a third party could read came with it.
//!
//! # Why the certificate is keyed on SOURCE S-EXPRESSIONS, not `TermId`s
//!
//! A string script's *flat* arena view is the ADR-0029 bounded packed-BV
//! encoding (or, under the word-first fallback, empty). It is deliberately not a
//! faithful checking subject — `EvidenceWithScript::arena_view_faithful` is
//! `false` for exactly this reason — and the dominance audit re-checks string
//! evidence against `&[]`. So a certificate over `TermId`s would be meaningless
//! twice over: arena ids are run-local (the failure
//! `crates/axeyum-solver/tests/certified_implies_revalidatable.rs` exists to
//! catch), and the arena that *would* be handed to the checker does not contain
//! the string query at all.
//!
//! This certificate therefore carries the script's own top-level commands as
//! [`SExpr`]s — the same self-contained posture as [`Evidence::UnsatWordClash`]
//! and [`Evidence::UnsatRegexEmptiness`] (ADR-0061) — and every abstraction
//! variable is a **source name**.
//!
//! [`Evidence::UnsatWordClash`]: crate::Evidence::UnsatWordClash
//! [`Evidence::UnsatRegexEmptiness`]: crate::Evidence::UnsatRegexEmptiness
//!
//! # The checker is two stages, and neither subsumes the other
//!
//! Stage 1 **binds**: it re-derives the sort environment and the premise
//! conjuncts from the carried commands itself, then checks that every carried
//! lemma instance is a legal instance of its schema *against those conjuncts* —
//! `NonEmptyLen` needs the query to actually assert `x != ""`, `SingletonCodeNonneg`
//! needs it to actually pin `|x| = 1`. Stage 2 **re-derives** the refutation from
//! the resulting linear facts alone: multiplier signs, the cancellation to a
//! constant, and the strictness bookkeeping. A certificate can fail either stage
//! independently, and neither is `carried == recomputed`.
//!
//! # The lemma set is deliberately tiny
//!
//! Five schemas, each one line of mathematics:
//!
//! | schema | statement | side condition |
//! |---|---|---|
//! | [`LengthLemma::LenNonneg`] | `\|x\| >= 0` | `x` is a declared `String` |
//! | [`LengthLemma::WordLenCongruence`] | `\|u\| - \|v\| = 0` | conjunct `i` is `(= u v)` over words |
//! | [`LengthLemma::NonEmptyLen`] | `\|x\| - 1 >= 0` | conjunct `i` is `x != ""` |
//! | [`LengthLemma::CodeUpperBound`] | `0x2FFFF - code(x) >= 0` | none (SMT-LIB total) |
//! | [`LengthLemma::SingletonCodeNonneg`] | `code(x) >= 0` | conjunct `i` pins `\|x\| = 1` |
//!
//! `|u . v| = |u| + |v|` and `|"lit"| = k` are not lemma *instances*: they are the
//! homomorphism the abstraction is built from, applied by both the producer and
//! the checker when they turn a word into a linear form.
//!
//! `CodeUpperBound` is unconditional on purpose. SMT-LIB `str.to_code` is total:
//! it is the code point when `|x| = 1` and `-1` otherwise, so `code(x) <= 0x2FFFF`
//! needs no premise, while `code(x) >= 0` needs `|x| = 1` and is a separate
//! schema. Merging them would have made the `-1` case invisible.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::Rational;
use axeyum_smtlib::SExpr;

/// The largest SMT-LIB code point, `\u{2FFFF}`; `str.to_code` never exceeds it.
const MAX_CODE_POINT: i128 = 0x2_FFFF;

/// Refuse scripts whose command forest is larger than this many s-expression
/// nodes. The abstraction declines on any unsupported operator anyway; this is
/// the belt on the certificate's own size.
const MAX_SOURCE_NODES: usize = 4096;

/// Refuse a Fourier–Motzkin stage with more than this many inequalities.
const MAX_FM_ROWS: usize = 256;

/// Fact-table key for the branch's assumed disjunct. Premise conjuncts key on
/// their own (small) index, so these two reserved keys cannot collide with one.
const ARM_KEY: usize = usize::MAX;
/// Fact-table key base for lemma instance `i`.
const LEMMA_BASE: usize = usize::MAX / 2;

/// An abstraction variable, keyed on the **source name** it came from.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum AbsVar {
    /// `(str.len x)` for a declared `String` symbol `x`.
    Len(String),
    /// `(str.to_code x)` for a declared `String` symbol `x`.
    Code(String),
    /// A declared `Int` symbol.
    Int(String),
}

impl AbsVar {
    /// A Lean-safe identifier base naming the SOURCE this variable abstracts,
    /// so a rendered reconstruction reads `len_yy` rather than `x.3`.
    ///
    /// Only cosmetic: the kernel name a reconstruction mints appends a unique
    /// counter, so two source names that sanitize alike still get distinct
    /// constants.
    pub(crate) fn lean_base(&self) -> String {
        let (prefix, name) = match self {
            AbsVar::Len(name) => ("len", name),
            AbsVar::Code(name) => ("code", name),
            AbsVar::Int(name) => ("int", name),
        };
        let sanitized: String = name
            .chars()
            .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
            .collect();
        format!("{prefix}_{sanitized}")
    }
}

/// A linear form `Σ cᵥ·v + k` over [`AbsVar`]s, exact over the rationals.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Lin {
    pub(crate) coeffs: BTreeMap<AbsVar, Rational>,
    pub(crate) constant: Rational,
}

impl Lin {
    fn constant(value: Rational) -> Self {
        Self {
            coeffs: BTreeMap::new(),
            constant: value,
        }
    }

    fn var(v: AbsVar) -> Self {
        let mut coeffs = BTreeMap::new();
        coeffs.insert(v, Rational::integer(1));
        Self {
            coeffs,
            constant: Rational::zero(),
        }
    }

    fn add_var(&mut self, v: AbsVar, c: Rational) -> Option<()> {
        if c.is_zero() {
            return Some(());
        }
        match self.coeffs.get(&v).copied() {
            None => {
                self.coeffs.insert(v, c);
            }
            Some(prev) => {
                let sum = prev.checked_add(c)?;
                if sum.is_zero() {
                    self.coeffs.remove(&v);
                } else {
                    self.coeffs.insert(v, sum);
                }
            }
        }
        Some(())
    }

    fn add(&self, other: &Self) -> Option<Self> {
        let mut out = self.clone();
        for (v, &c) in &other.coeffs {
            out.add_var(v.clone(), c)?;
        }
        out.constant = out.constant.checked_add(other.constant)?;
        Some(out)
    }

    fn scale(&self, factor: Rational) -> Option<Self> {
        let mut out = Lin::default();
        for (v, &c) in &self.coeffs {
            out.add_var(v.clone(), c.checked_mul(factor)?)?;
        }
        out.constant = self.constant.checked_mul(factor)?;
        Some(out)
    }

    fn sub(&self, other: &Self) -> Option<Self> {
        self.add(&other.scale(Rational::integer(-1))?)
    }

    fn is_constant(&self) -> bool {
        self.coeffs.is_empty()
    }

    fn coefficient(&self, v: &AbsVar) -> Rational {
        self.coeffs.get(v).copied().unwrap_or_else(Rational::zero)
    }
}

/// How a linear form is compared against zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Rel {
    /// `expr >= 0`
    Ge,
    /// `expr > 0`
    Gt,
    /// `expr = 0`
    Eq,
}

/// A linear fact: `expr ⋈ 0`.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Atom {
    expr: Lin,
    rel: Rel,
}

/// One of the five theory lemma schemas, as an **instance** over source names.
///
/// Each is independently auditable by reading it: the statement is in the table
/// in the module docs, and the side condition names the premise conjunct that
/// licenses it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LengthLemma {
    /// `|x| >= 0`. Valid for any declared `String` symbol; no premise needed.
    LenNonneg {
        /// The source name of the string symbol.
        var: String,
    },
    /// `|u| - |v| = 0`, because premise conjunct `conjunct` asserts `(= u v)`
    /// between two *words* (string literals, declared string symbols, and
    /// `str.++` of those).
    WordLenCongruence {
        /// Index into the premise conjunct list.
        conjunct: usize,
    },
    /// `|x| - 1 >= 0`, because premise conjunct `conjunct` asserts `x != ""`.
    ///
    /// This is the `|x| = 0 <-> x = ""` lemma in the only direction a linear
    /// refutation can use.
    NonEmptyLen {
        /// Index into the premise conjunct list.
        conjunct: usize,
        /// The source name of the string symbol asserted non-empty.
        var: String,
    },
    /// `0x2FFFF - code(x) >= 0`. Unconditional: SMT-LIB `str.to_code` is total
    /// and returns either `-1` or a code point in `[0, 0x2FFFF]`.
    CodeUpperBound {
        /// The source name of the string symbol.
        var: String,
    },
    /// `code(x) >= 0`, because premise conjunct `conjunct` pins `|x| = 1` — the
    /// only case in which `str.to_code` is not `-1`.
    SingletonCodeNonneg {
        /// Index into the premise conjunct list that pins the length.
        conjunct: usize,
        /// The source name of the string symbol.
        var: String,
    },
}

/// Which fact a multiplier applies to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FactRef {
    /// Premise conjunct `i`, which must itself abstract to a linear atom.
    Conjunct(usize),
    /// Lemma instance `i` of the certificate's lemma list.
    Lemma(usize),
    /// The disjunct this branch assumes (only in a case-split certificate).
    Arm,
}

/// A rational on the wire: `(numerator, denominator)`.
type WireRat = (i128, i128);

/// One branch's Farkas combination: `(fact, multiplier)` pairs.
type Combination = Vec<(FactRef, WireRat)>;

/// A refutation of a string query by length/code-point abstraction.
///
/// Carries the script's own top-level commands (so the checker re-derives the
/// premises rather than trusting a digest of them), the lemma instances used,
/// and one Farkas combination per case-split branch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StringLengthRefutationCertificate {
    /// The script's top-level commands, verbatim.
    commands: Vec<SExpr>,
    /// The theory lemma instances the refutation uses.
    lemmas: Vec<LengthLemma>,
    /// The premise conjunct that is case-split, when the refutation needs one.
    /// `None` is a purely conjunctive refutation with exactly one branch.
    split: Option<usize>,
    /// One combination per branch; with `split = Some(i)` there is one per
    /// disjunct of conjunct `i`, in source order.
    branches: Vec<Combination>,
}

impl StringLengthRefutationCertificate {
    /// The theory lemma instances this refutation uses.
    #[must_use]
    pub fn lemmas(&self) -> &[LengthLemma] {
        &self.lemmas
    }

    /// The number of case-split branches (1 for a conjunctive refutation).
    #[must_use]
    pub fn branch_count(&self) -> usize {
        self.branches.len()
    }

    /// Whether the refutation splits on a disjunction.
    #[must_use]
    pub const fn is_case_split(&self) -> bool {
        self.split.is_some()
    }

    /// Re-point this certificate at a different script. **Testing only.**
    ///
    /// The carried commands ARE the premises, so a certificate whose commands
    /// were replaced is a forgery — which is exactly what a checker or
    /// reconstruction test needs in order to show the re-derivation is load
    /// bearing rather than decorative.
    #[cfg(test)]
    pub(crate) fn testing_set_commands(&mut self, commands: Vec<SExpr>) {
        self.commands = commands;
    }
}

// ---------------------------------------------------------------------------
// Source-level abstraction. Shared by the producer and the checker: the
// asymmetry that matters is that the producer SEARCHES for a combination and
// the checker VERIFIES the one it is given.
// ---------------------------------------------------------------------------

/// The declared 0-ary symbols of the script, by sort.
#[derive(Debug, Default)]
struct Env {
    strings: BTreeSet<String>,
    ints: BTreeSet<String>,
}

fn head(e: &SExpr) -> Option<&str> {
    e.list()?.first()?.atom()
}

fn node_count(e: &SExpr) -> usize {
    e.descendants().count()
}

/// Build the sort environment and the flattened premise conjuncts from a
/// script's top-level commands, or decline.
///
/// Declining is the fail-closed direction: an unrecognized command shape means
/// the source may say something this abstraction cannot see.
fn read_source(commands: &[SExpr]) -> Option<(Env, Vec<SExpr>)> {
    if commands.iter().map(node_count).sum::<usize>() > MAX_SOURCE_NODES {
        return None;
    }
    let mut env = Env::default();
    let mut asserts: Vec<SExpr> = Vec::new();
    let mut check_sats = 0usize;
    for command in commands {
        let Some(name) = head(command) else {
            // A bare atom at top level is not a command this reader understands.
            return None;
        };
        let items = command.list()?;
        match name {
            "declare-fun" => {
                // `(declare-fun x () Sort)`; a positive arity is a function
                // symbol, which the abstraction has no variable for.
                let [_, sym, params, sort] = items else {
                    return None;
                };
                let sym = sym.atom()?;
                if !params.list()?.is_empty() {
                    continue;
                }
                note_sort(&mut env, sym, sort);
            }
            "declare-const" => {
                let [_, sym, sort] = items else { return None };
                note_sort(&mut env, sym.atom()?, sort);
            }
            "assert" => {
                let [_, body] = items else { return None };
                asserts.push(body.clone());
            }
            "check-sat" => check_sats += 1,
            // Informational / harmless commands.
            "set-logic" | "set-info" | "set-option" | "exit" | "get-model" | "get-value"
            | "get-info" | "get-unsat-core" | "get-proof" | "echo" => {}
            // ALLOW-LIST, not a block-list. Anything unrecognized declines: a
            // macro (`define-fun` — the assertion's meaning is elsewhere),
            // incremental scoping (`push`/`pop` — the active stack is not the
            // assertion list), a user sort, or a command SMT-LIB has not grown
            // yet. A block-list of the four shapes known today would let the
            // fifth through silently, and a guard listing them separately was
            // dead code: mutation-checking it killed nothing, because every
            // name it named already landed here.
            _ => return None,
        }
    }
    // One query only: with several `check-sat`s the assertion list is not the
    // query at any one of them.
    if check_sats != 1 {
        return None;
    }
    let mut conjuncts = Vec::new();
    for body in &asserts {
        flatten_and(body, &mut conjuncts);
    }
    Some((env, conjuncts))
}

fn note_sort(env: &mut Env, symbol: &str, sort: &SExpr) {
    match sort.atom() {
        Some("String") => {
            env.strings.insert(symbol.to_owned());
        }
        Some("Int") => {
            env.ints.insert(symbol.to_owned());
        }
        // Any other sort: the symbol is simply not an abstraction variable, and
        // every use of it declines.
        _ => {}
    }
}

fn flatten_and(e: &SExpr, out: &mut Vec<SExpr>) {
    if head(e) == Some("and")
        && let Some(items) = e.list()
    {
        for arg in &items[1..] {
            flatten_and(arg, out);
        }
        return;
    }
    out.push(e.clone());
}

/// An SMT-LIB numeral (or `(- n)`) as an exact rational.
fn numeral(e: &SExpr) -> Option<Rational> {
    if let Some(a) = e.atom() {
        if a.is_empty() || !a.bytes().all(|b| b.is_ascii_digit()) {
            return None;
        }
        return a.parse::<i128>().ok().map(Rational::integer);
    }
    let items = e.list()?;
    let [op, only] = items else { return None };
    if op.atom()? != "-" {
        return None;
    }
    numeral(only)?.checked_neg()
}

/// The code-point length of a string literal atom, or `None` when `e` is not a
/// well-formed string literal.
fn literal_len(e: &SExpr) -> Option<Rational> {
    let cps = axeyum_smtlib::string_literal_code_points(e.atom()?)?;
    Some(Rational::integer(i128::try_from(cps.len()).ok()?))
}

/// `|w|` as a linear form, for a *word*: a string literal, a declared string
/// symbol, or `str.++` of words. `None` for anything else.
///
/// This is where the homomorphism `|u . v| = |u| + |v|` and `|"lit"| = k` are
/// applied; they are not carried as lemma instances because they are structural.
fn word_len(env: &Env, e: &SExpr) -> Option<Lin> {
    if let Some(a) = e.atom() {
        if let Some(k) = literal_len(e) {
            return Some(Lin::constant(k));
        }
        if env.strings.contains(a) {
            return Some(Lin::var(AbsVar::Len(a.to_owned())));
        }
        return None;
    }
    let items = e.list()?;
    if items.first()?.atom()? != "str.++" {
        return None;
    }
    let mut acc = Lin::constant(Rational::zero());
    for part in &items[1..] {
        acc = acc.add(&word_len(env, part)?)?;
    }
    Some(acc)
}

/// A declared string symbol name, or `None`.
fn string_symbol(env: &Env, e: &SExpr) -> Option<String> {
    let a = e.atom()?;
    env.strings.contains(a).then(|| a.to_owned())
}

/// An `Int`-sorted source expression as a linear form over the abstraction.
fn int_lin(env: &Env, e: &SExpr) -> Option<Lin> {
    if let Some(a) = e.atom() {
        if let Some(k) = numeral(e) {
            return Some(Lin::constant(k));
        }
        if env.ints.contains(a) {
            return Some(Lin::var(AbsVar::Int(a.to_owned())));
        }
        return None;
    }
    let items = e.list()?;
    let op = items.first()?.atom()?;
    let args = &items[1..];
    match op {
        "str.len" | "seq.len" => {
            let [only] = args else { return None };
            word_len(env, only)
        }
        "str.to_code" => {
            let [only] = args else { return None };
            Some(Lin::var(AbsVar::Code(string_symbol(env, only)?)))
        }
        "+" => {
            let mut acc = Lin::constant(Rational::zero());
            for arg in args {
                acc = acc.add(&int_lin(env, arg)?)?;
            }
            Some(acc)
        }
        "-" => match args {
            [only] => int_lin(env, only)?.scale(Rational::integer(-1)),
            [first, rest @ ..] if !rest.is_empty() => {
                let mut acc = int_lin(env, first)?;
                for arg in rest {
                    acc = acc.sub(&int_lin(env, arg)?)?;
                }
                Some(acc)
            }
            _ => None,
        },
        "*" => {
            // Linear only: at most one non-constant factor.
            let mut factor = Rational::integer(1);
            let mut symbolic: Option<Lin> = None;
            for arg in args {
                if let Some(k) = numeral(arg) {
                    factor = factor.checked_mul(k)?;
                    continue;
                }
                if symbolic.is_some() {
                    return None;
                }
                symbolic = Some(int_lin(env, arg)?);
            }
            match symbolic {
                None => Some(Lin::constant(factor)),
                Some(term) => term.scale(factor),
            }
        }
        _ => None,
    }
}

/// A source conjunct as a linear atom `expr ⋈ 0`, or `None` when it is outside
/// the abstraction (a string equality, a regex membership, a disjunction, …).
fn atom_of(env: &Env, e: &SExpr) -> Option<Atom> {
    let items = e.list()?;
    let op = items.first()?.atom()?;
    if op == "not" {
        let [_, inner] = items else { return None };
        let inner_atom = atom_of(env, inner)?;
        // `not (e >= 0)` is `-e > 0`; `not (e > 0)` is `-e >= 0`. A negated
        // EQUALITY is a disequality, which is not a linear atom.
        let rel = match inner_atom.rel {
            Rel::Ge => Rel::Gt,
            Rel::Gt => Rel::Ge,
            Rel::Eq => return None,
        };
        return Some(Atom {
            expr: inner_atom.expr.scale(Rational::integer(-1))?,
            rel,
        });
    }
    let [_, lhs, rhs] = items else {
        // Chainable n-ary comparisons are declined rather than guessed.
        return None;
    };
    let (left, right) = (int_lin(env, lhs)?, int_lin(env, rhs)?);
    let (expr, rel) = match op {
        ">" => (left.sub(&right)?, Rel::Gt),
        ">=" => (left.sub(&right)?, Rel::Ge),
        "<" => (right.sub(&left)?, Rel::Gt),
        "<=" => (right.sub(&left)?, Rel::Ge),
        "=" => (left.sub(&right)?, Rel::Eq),
        _ => return None,
    };
    Some(Atom { expr, rel })
}

/// The two operands of a conjunct asserting `a != b` — either `(not (= a b))` or
/// `(distinct a b)`.
fn disequality_operands(e: &SExpr) -> Option<(&SExpr, &SExpr)> {
    let items = e.list()?;
    match items.first()?.atom()? {
        "not" => {
            let [_, inner] = items else { return None };
            let inner_items = inner.list()?;
            let [eq, lhs, rhs] = inner_items else {
                return None;
            };
            (eq.atom()? == "=").then_some((lhs, rhs))
        }
        "distinct" => {
            let [_, lhs, rhs] = items else { return None };
            Some((lhs, rhs))
        }
        _ => None,
    }
}

/// Is `e` the empty string literal?
fn is_empty_literal(e: &SExpr) -> bool {
    literal_len(e).is_some_and(|k| k == Rational::zero())
}

// ---------------------------------------------------------------------------
// Stage 1: bind each carried lemma instance to what the query asserts.
// ---------------------------------------------------------------------------

/// The atom a lemma instance contributes, or `None` when its side condition does
/// not hold against the premise conjuncts the checker just re-derived.
///
/// This is the whole of stage 1: a lemma whose premise the query does not assert
/// is rejected here, before any arithmetic runs.
fn lemma_atom(env: &Env, conjuncts: &[SExpr], lemma: &LengthLemma) -> Option<Atom> {
    match lemma {
        LengthLemma::LenNonneg { var } => {
            if !env.strings.contains(var) {
                return None;
            }
            Some(Atom {
                expr: Lin::var(AbsVar::Len(var.clone())),
                rel: Rel::Ge,
            })
        }
        LengthLemma::WordLenCongruence { conjunct } => {
            let items = conjuncts.get(*conjunct)?.list()?;
            let [eq, lhs, rhs] = items else { return None };
            if eq.atom()? != "=" {
                return None;
            }
            // BOTH sides must be words. `(= (str.len x) 0)` is an Int equality,
            // not a word equality, and licenses no length congruence of its own.
            let (left, right) = (word_len(env, lhs)?, word_len(env, rhs)?);
            Some(Atom {
                expr: left.sub(&right)?,
                rel: Rel::Eq,
            })
        }
        LengthLemma::NonEmptyLen { conjunct, var } => {
            let (lhs, rhs) = disequality_operands(conjuncts.get(*conjunct)?)?;
            // One side is the symbol named, the other is exactly `""`.
            let named = |side: &SExpr| string_symbol(env, side).is_some_and(|s| s == *var);
            if !((named(lhs) && is_empty_literal(rhs)) || (named(rhs) && is_empty_literal(lhs))) {
                return None;
            }
            let mut expr = Lin::var(AbsVar::Len(var.clone()));
            expr.constant = Rational::integer(-1);
            Some(Atom { expr, rel: Rel::Ge })
        }
        LengthLemma::CodeUpperBound { var } => {
            if !env.strings.contains(var) {
                return None;
            }
            let mut expr = Lin::var(AbsVar::Code(var.clone())).scale(Rational::integer(-1))?;
            expr.constant = Rational::integer(MAX_CODE_POINT);
            Some(Atom { expr, rel: Rel::Ge })
        }
        LengthLemma::SingletonCodeNonneg { conjunct, var } => {
            if !env.strings.contains(var) {
                return None;
            }
            // The side condition: this conjunct really pins `|var| = 1`.
            let pinned = atom_of(env, conjuncts.get(*conjunct)?)?;
            if pinned.rel != Rel::Eq {
                return None;
            }
            let mut want = Lin::var(AbsVar::Len(var.clone()));
            want.constant = Rational::integer(-1);
            let negated = want.scale(Rational::integer(-1))?;
            if pinned.expr != want && pinned.expr != negated {
                return None;
            }
            Some(Atom {
                expr: Lin::var(AbsVar::Code(var.clone())),
                rel: Rel::Ge,
            })
        }
    }
}

// ---------------------------------------------------------------------------
// Stage 2: re-derive the linear refutation from the bound facts alone.
// ---------------------------------------------------------------------------

/// Re-derive one branch: the multipliers have legal signs, the combination
/// cancels to a constant, and that constant contradicts the direction the facts
/// establish.
///
/// The sign bookkeeping is the entire soundness argument. `e >= 0` may only be
/// multiplied by a **positive** rational (a negative one flips it); `e = 0` may
/// be multiplied by anything nonzero. The combination then satisfies `Σ >= 0`,
/// or `Σ > 0` when some strict fact carried a positive multiplier. A sum that
/// cancels to the constant `c` therefore contradicts `c < 0` in the first case
/// and `c <= 0` in the second. Getting that backwards certifies satisfiable
/// queries.
fn derive_branch(
    facts: &BTreeMap<usize, Atom>,
    combination: &Combination,
    keys: &[usize],
    branch: usize,
) -> Option<Vec<CheckedFact>> {
    let mut sum = Lin::constant(Rational::zero());
    let mut strict = false;
    let mut used: BTreeSet<usize> = BTreeSet::new();
    let mut derived: Vec<CheckedFact> = Vec::with_capacity(combination.len());
    for ((reference, multiplier), index) in combination.iter().zip(keys) {
        // `Rational::checked_new` PANICS on a zero denominator (it treats that as
        // a usage error, not an overflow), and a hand-written certificate can
        // contain one. Reject before constructing, never after.
        if multiplier.1 == 0 {
            return None;
        }
        let lambda = Rational::checked_new(multiplier.0, multiplier.1)?;
        let atom = facts.get(index)?;
        // A repeated fact would let one entry's sign launder another's.
        if !used.insert(*index) {
            return None;
        }
        match atom.rel {
            Rel::Ge | Rel::Gt => {
                if lambda <= Rational::zero() {
                    return None;
                }
                if atom.rel == Rel::Gt {
                    strict = true;
                }
            }
            Rel::Eq => {
                if lambda.is_zero() {
                    return None;
                }
            }
        }
        let scaled = atom.expr.scale(lambda)?;
        sum = sum.add(&scaled)?;
        derived.push(CheckedFact {
            role: match *reference {
                FactRef::Conjunct(i) => FactRole::Conjunct(i),
                FactRef::Lemma(i) => FactRole::Lemma(i),
                FactRef::Arm => FactRole::Arm(branch),
            },
            expr: atom.expr.clone(),
            rel: atom.rel,
            multiplier: lambda,
        });
    }
    if !sum.is_constant() {
        return None;
    }
    let zero = Rational::zero();
    let closes = if strict {
        // Σ > 0, so Σ = c is impossible for c <= 0.
        sum.constant <= zero
    } else {
        // Σ >= 0, so Σ = c is impossible for c < 0. An EMPTY combination lands
        // here with `c = 0` and is rejected by this line, so it needs no guard
        // of its own — one was written, mutation-checked, and killed nothing.
        sum.constant < zero
    };
    closes.then_some(derived)
}

/// Where a re-derived fact came from. Every fact of a checked refutation is one
/// of these three, and nothing else can enter the combination.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FactRole {
    /// Premise conjunct `i` — an actual `(assert …)` line of the carried script
    /// (or one conjunct of one, after `and`-flattening).
    Conjunct(usize),
    /// Theory lemma instance `i`, whose side condition stage 1 bound to a
    /// premise conjunct.
    Lemma(usize),
    /// The disjunct branch `i` assumes, discharged by the case analysis.
    Arm(usize),
}

/// One fact of a re-derived refutation: where it came from, the linear atom
/// stage 1 bound it to, and the multiplier stage 2 accepted for it.
#[derive(Clone, Debug)]
pub(crate) struct CheckedFact {
    /// The fact's provenance.
    pub(crate) role: FactRole,
    /// `Σ cᵥ·v + k`, compared against zero by [`Self::rel`](CheckedFact::rel).
    pub(crate) expr: Lin,
    /// How `expr` is compared against zero.
    pub(crate) rel: Rel,
    /// The multiplier the combination applies to this fact.
    pub(crate) multiplier: Rational,
}

/// A refutation as the checker re-derived it, for consumers that must rebuild
/// the argument rather than merely accept it (the Lean reconstruction).
///
/// Produced by [`checked_refutation`], which is also what
/// [`check_string_length_refutation`] is: there is exactly one derivation, so an
/// exported view cannot drift from the one that was validated.
#[derive(Clone, Debug)]
pub(crate) struct CheckedRefutation {
    /// One fact list per case-split branch, in source order.
    pub(crate) branches: Vec<Vec<CheckedFact>>,
    /// The abstraction variables any branch mentions, in a deterministic order.
    pub(crate) variables: Vec<AbsVar>,
}

/// Independently re-validate a certificate and return the refutation it
/// re-derived. Arena-free by construction: the premises are the carried source
/// commands.
///
/// Stage 1 re-derives the sort environment and premise conjuncts from those
/// commands and binds every lemma instance to the conjunct that licenses it;
/// stage 2 re-derives each branch's Farkas combination from the bound facts.
pub(crate) fn checked_refutation(
    certificate: &StringLengthRefutationCertificate,
) -> Option<CheckedRefutation> {
    let (env, conjuncts) = read_source(&certificate.commands)?;

    // Stage 1: bind. Every lemma must be a legal instance of its schema against
    // the conjuncts just re-derived; a lemma whose premise the query does not
    // assert dies here.
    let mut lemma_atoms = Vec::with_capacity(certificate.lemmas.len());
    for lemma in &certificate.lemmas {
        lemma_atoms.push(lemma_atom(&env, &conjuncts, lemma)?);
    }

    // The conjunctive facts: every premise conjunct that abstracts to a linear
    // atom. The split conjunct (a disjunction) is not one of them.
    let mut base: BTreeMap<usize, Atom> = BTreeMap::new();
    for (i, conjunct) in conjuncts.iter().enumerate() {
        if Some(i) == certificate.split {
            continue;
        }
        if let Some(atom) = atom_of(&env, conjunct) {
            base.insert(i, atom);
        }
    }

    // Arms, one per branch.
    let arms: Vec<Option<Atom>> = match certificate.split {
        None => {
            if certificate.branches.len() != 1 {
                return None;
            }
            vec![None]
        }
        Some(index) => {
            let disjunction = conjuncts.get(index)?;
            let items = disjunction.list()?;
            if items.first().and_then(SExpr::atom) != Some("or") || items.len() < 2 {
                return None;
            }
            // EVERY disjunct must have its own refutation: a model satisfies at
            // least one of them, so leaving one branch out proves nothing.
            if certificate.branches.len() != items.len() - 1 {
                return None;
            }
            let mut arms = Vec::with_capacity(items.len() - 1);
            for disjunct in &items[1..] {
                arms.push(Some(atom_of(&env, disjunct)?));
            }
            arms
        }
    };

    // Stage 2: re-derive each branch from the bound facts alone.
    let mut derived: Vec<Vec<CheckedFact>> = Vec::with_capacity(certificate.branches.len());
    for (branch_index, (branch, arm)) in certificate.branches.iter().zip(arms).enumerate() {
        let mut facts = base.clone();
        if let Some(atom) = arm {
            facts.insert(ARM_KEY, atom);
        }
        for (i, atom) in lemma_atoms.iter().enumerate() {
            facts.insert(LEMMA_BASE + i, atom.clone());
        }
        // Every reference is resolved through `facts`, and `facts` contains
        // exactly the conjuncts that abstract to an atom (minus the split), the
        // lemmas, and — only when there is a split — the arm. So a reference to
        // the split conjunct, to a conjunct with no linear atom, to a lemma that
        // does not exist, or to an arm when there is no case analysis all land on
        // an absent key and are rejected by ONE guard in `derive_branch`.
        // Separate range checks here were mutation-checked and killed nothing:
        // they were spelling out what the lookup already decides.
        let mut keys = Vec::with_capacity(branch.len());
        for (fact, _) in branch {
            keys.push(match *fact {
                FactRef::Conjunct(i) => i,
                // `checked_add` for overflow, not for range: a hand-written
                // `Lemma(usize::MAX)` would otherwise panic in debug before the
                // lookup could reject it.
                FactRef::Lemma(i) => LEMMA_BASE.checked_add(i)?,
                FactRef::Arm => ARM_KEY,
            });
        }
        derived.push(derive_branch(&facts, branch, &keys, branch_index)?);
    }

    let mut variables: BTreeSet<AbsVar> = BTreeSet::new();
    for facts in &derived {
        for fact in facts {
            variables.extend(fact.expr.coeffs.keys().cloned());
        }
    }
    Some(CheckedRefutation {
        branches: derived,
        variables: variables.into_iter().collect(),
    })
}

/// Independently re-validate a certificate: `checked_refutation` succeeded.
///
/// The boolean form is the whole of the check — there is one derivation, and
/// this is it, so the exported `CheckedRefutation` a reconstruction consumes
/// is by construction the one that was validated rather than a parallel reading
/// of the same certificate.
#[must_use]
pub fn check_string_length_refutation(certificate: &StringLengthRefutationCertificate) -> bool {
    checked_refutation(certificate).is_some()
}

// ---------------------------------------------------------------------------
// The producer: search for a combination by Fourier–Motzkin with multiplier
// provenance, then self-check the certificate it built.
// ---------------------------------------------------------------------------

/// One row of the elimination: `expr >= 0` (or `> 0`), with the multipliers that
/// produced it recorded against the original fact keys.
#[derive(Clone, Debug)]
struct Row {
    expr: Lin,
    strict: bool,
    provenance: BTreeMap<usize, Rational>,
}

impl Row {
    fn combine(&self, other: &Self, a: Rational, b: Rational) -> Option<Self> {
        let expr = self.expr.scale(a)?.add(&other.expr.scale(b)?)?;
        let mut provenance = BTreeMap::new();
        for (source, weights) in [(&self.provenance, a), (&other.provenance, b)] {
            for (&key, &value) in source {
                let scaled = value.checked_mul(weights)?;
                let slot = provenance.entry(key).or_insert_with(Rational::zero);
                *slot = slot.checked_add(scaled)?;
            }
        }
        provenance.retain(|_, v| !v.is_zero());
        Some(Row {
            expr,
            strict: self.strict || other.strict,
            provenance,
        })
    }
}

/// Fourier–Motzkin over the given facts; returns the multipliers of the first
/// contradictory constant row found.
fn find_combination(facts: &BTreeMap<usize, Atom>) -> Option<BTreeMap<usize, Rational>> {
    let mut rows: Vec<Row> = Vec::new();
    for (&key, atom) in facts {
        let one = Rational::integer(1);
        match atom.rel {
            Rel::Ge | Rel::Gt => rows.push(Row {
                expr: atom.expr.clone(),
                strict: atom.rel == Rel::Gt,
                provenance: BTreeMap::from([(key, one)]),
            }),
            Rel::Eq => {
                // Both directions, so the provenance can end up with either sign
                // on the equality — which is exactly what an equality licenses.
                rows.push(Row {
                    expr: atom.expr.clone(),
                    strict: false,
                    provenance: BTreeMap::from([(key, one)]),
                });
                rows.push(Row {
                    expr: atom.expr.scale(Rational::integer(-1))?,
                    strict: false,
                    provenance: BTreeMap::from([(key, one.checked_neg()?)]),
                });
            }
        }
    }

    let mut variables: BTreeSet<AbsVar> = BTreeSet::new();
    for row in &rows {
        variables.extend(row.expr.coeffs.keys().cloned());
    }

    for variable in variables {
        if let Some(found) = contradictory(&rows) {
            return Some(found);
        }
        let mut positive = Vec::new();
        let mut negative = Vec::new();
        let mut neutral = Vec::new();
        for row in rows {
            let c = row.expr.coefficient(&variable);
            match c.cmp(&Rational::zero()) {
                std::cmp::Ordering::Greater => positive.push(row),
                std::cmp::Ordering::Less => negative.push(row),
                std::cmp::Ordering::Equal => neutral.push(row),
            }
        }
        let mut next = neutral;
        for p in &positive {
            for n in &negative {
                let pc = p.expr.coefficient(&variable);
                let nc = n.expr.coefficient(&variable).checked_neg()?;
                // Eliminate `variable`: nc·p + pc·n has coefficient nc·pc − pc·nc.
                let combined = p.combine(n, nc, pc)?;
                next.push(combined);
                if next.len() > MAX_FM_ROWS {
                    return None;
                }
            }
        }
        rows = next;
    }
    contradictory(&rows)
}

/// The first constant row that is itself a contradiction.
fn contradictory(rows: &[Row]) -> Option<BTreeMap<usize, Rational>> {
    let zero = Rational::zero();
    rows.iter()
        .find(|row| {
            row.expr.is_constant()
                && !row.provenance.is_empty()
                && if row.strict {
                    row.expr.constant <= zero
                } else {
                    row.expr.constant < zero
                }
        })
        .map(|row| row.provenance.clone())
}

/// Candidate lemma instances for a query, in a deterministic order.
fn candidate_lemmas(env: &Env, conjuncts: &[SExpr]) -> Vec<LengthLemma> {
    let mut out = Vec::new();
    for var in &env.strings {
        out.push(LengthLemma::LenNonneg { var: var.clone() });
        out.push(LengthLemma::CodeUpperBound { var: var.clone() });
    }
    for i in 0..conjuncts.len() {
        out.push(LengthLemma::WordLenCongruence { conjunct: i });
        for var in &env.strings {
            out.push(LengthLemma::NonEmptyLen {
                conjunct: i,
                var: var.clone(),
            });
            out.push(LengthLemma::SingletonCodeNonneg {
                conjunct: i,
                var: var.clone(),
            });
        }
    }
    // Keep only the instances whose side condition actually holds.
    out.retain(|lemma| lemma_atom(env, conjuncts, lemma).is_some());
    out
}

/// Derive a certificate from a script's top-level commands, or decline.
///
/// The search is Fourier–Motzkin with multiplier provenance over the query's
/// linear conjuncts plus every licensed lemma instance; a purely conjunctive
/// refutation is tried first, then a single case split on one asserted `or`.
#[must_use]
pub fn string_length_refutation(commands: &[SExpr]) -> Option<StringLengthRefutationCertificate> {
    let (env, conjuncts) = read_source(commands)?;
    let lemmas = candidate_lemmas(&env, &conjuncts);
    let lemma_atoms: Vec<Atom> = lemmas
        .iter()
        .filter_map(|lemma| lemma_atom(&env, &conjuncts, lemma))
        .collect();
    if lemma_atoms.len() != lemmas.len() {
        return None;
    }
    let facts_for = |split: Option<usize>, arm: Option<Atom>| -> BTreeMap<usize, Atom> {
        let mut facts: BTreeMap<usize, Atom> = BTreeMap::new();
        for (i, conjunct) in conjuncts.iter().enumerate() {
            if Some(i) == split {
                continue;
            }
            if let Some(atom) = atom_of(&env, conjunct) {
                facts.insert(i, atom);
            }
        }
        for (i, atom) in lemma_atoms.iter().enumerate() {
            facts.insert(LEMMA_BASE + i, atom.clone());
        }
        if let Some(atom) = arm {
            facts.insert(ARM_KEY, atom);
        }
        facts
    };

    let to_combination = |weights: &BTreeMap<usize, Rational>| -> Option<Combination> {
        let mut out = Combination::new();
        for (&key, &weight) in weights {
            let reference = if key == ARM_KEY {
                FactRef::Arm
            } else if key >= LEMMA_BASE {
                FactRef::Lemma(key - LEMMA_BASE)
            } else {
                FactRef::Conjunct(key)
            };
            out.push((reference, (weight.numerator(), weight.denominator())));
        }
        (!out.is_empty()).then_some(out)
    };

    // (1) A conjunctive refutation.
    let mut candidate = find_combination(&facts_for(None, None))
        .as_ref()
        .and_then(to_combination)
        .map(|combination| StringLengthRefutationCertificate {
            commands: commands.to_vec(),
            lemmas: lemmas.clone(),
            split: None,
            branches: vec![combination],
        });

    // (2) One case split on an asserted `or`, every arm refuted separately.
    if candidate.is_none() {
        for (index, conjunct) in conjuncts.iter().enumerate() {
            let Some(items) = conjunct.list() else {
                continue;
            };
            if items.first().and_then(SExpr::atom) != Some("or") || items.len() < 2 {
                continue;
            }
            let mut branches = Vec::with_capacity(items.len() - 1);
            for disjunct in &items[1..] {
                let Some(arm) = atom_of(&env, disjunct) else {
                    branches.clear();
                    break;
                };
                let Some(combination) = find_combination(&facts_for(Some(index), Some(arm)))
                    .as_ref()
                    .and_then(to_combination)
                else {
                    branches.clear();
                    break;
                };
                branches.push(combination);
            }
            if branches.len() == items.len() - 1 {
                candidate = Some(StringLengthRefutationCertificate {
                    commands: commands.to_vec(),
                    lemmas: lemmas.clone(),
                    split: Some(index),
                    branches,
                });
                break;
            }
        }
    }

    let mut certificate = candidate?;
    prune_unused_lemmas(&mut certificate);
    // Never emit a certificate the checker rejects: producer and checker
    // disagreeing is the soundness alarm, not something to ship — this
    // repository has published `certified=1` alongside a FAILED re-check once
    // already (`UnsatQuantInstanceSet`, 2026-08-17).
    //
    // Mutation-checked: deleting this line kills no test, and that is the
    // CORRECT result rather than a missing fixture. It is a cross-check between
    // two implementations of the same argument; a test can only kill it once one
    // of them is already wrong, which is exactly the state it exists to catch.
    check_string_length_refutation(&certificate).then_some(certificate)
}

/// Drop the lemma instances no branch references and reindex, so the emitted
/// lemma set is the one the argument actually uses.
fn prune_unused_lemmas(certificate: &mut StringLengthRefutationCertificate) {
    let mut used: BTreeSet<usize> = BTreeSet::new();
    for branch in &certificate.branches {
        for (fact, _) in branch {
            if let FactRef::Lemma(i) = *fact {
                used.insert(i);
            }
        }
    }
    let remap: BTreeMap<usize, usize> = used
        .iter()
        .enumerate()
        .map(|(new, &old)| (old, new))
        .collect();
    let kept: Vec<LengthLemma> = used
        .iter()
        .filter_map(|&i| certificate.lemmas.get(i).cloned())
        .collect();
    certificate.lemmas = kept;
    for branch in &mut certificate.branches {
        for (fact, _) in branch.iter_mut() {
            if let FactRef::Lemma(i) = *fact {
                *fact = FactRef::Lemma(remap[&i]);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_smtlib::read_all;

    /// `r0_QF_SLIA_str004.smt2`, verbatim.
    const STR004: &str = "(set-logic QF_SLIA)\n(set-info :status unsat)\n\
        (declare-fun xx () String)\n(declare-fun yy () String)\n\
        (assert (> (str.len yy) (str.len xx)))\n\
        (assert (= xx (str.++ xx yy)))\n(check-sat)";

    /// `r0_QF_S_str005.smt2`, verbatim.
    const STR005: &str = "(set-logic QF_S)\n(set-info :status unsat)\n\
        (declare-fun yy () String)\n\
        (assert (= (str.len yy) 0))\n(assert (not (= yy \"\")))\n(check-sat)";

    /// `r1_QF_SLIA_str-code-unsat-2.smt2`, verbatim.
    const CODE2: &str = "(set-logic QF_SLIA)\n(set-info :status unsat)\n\
        (declare-fun x () String)\n(assert (= (str.len x) 1))\n\
        (assert (or (< (str.to_code x) 0) \
        (> (str.to_code x) 10000000000000000000000000000)))\n(check-sat)";

    fn commands(text: &str) -> Vec<SExpr> {
        read_all(text).expect("reads")
    }

    fn cert_for(text: &str) -> StringLengthRefutationCertificate {
        string_length_refutation(&commands(text)).expect("certificate")
    }

    #[test]
    fn all_three_corpus_shapes_certify_and_verify() {
        for text in [STR004, STR005, CODE2] {
            let cert = string_length_refutation(&commands(text)).expect("certificate");
            assert!(check_string_length_refutation(&cert));
        }
    }

    #[test]
    fn the_lemma_set_is_small_and_named() {
        // str004 needs the concat congruence and one nonnegativity.
        let s4 = cert_for(STR004);
        assert!(
            s4.lemmas().len() <= 3,
            "str004 lemma set grew: {:?}",
            s4.lemmas()
        );
        assert!(
            s4.lemmas()
                .iter()
                .any(|l| matches!(l, LengthLemma::WordLenCongruence { .. })),
            "str004 must use |u . v| = |u| + |v| through a word equality: {:?}",
            s4.lemmas()
        );
        assert!(!s4.is_case_split());

        // str005 needs exactly the `|x| = 0 <-> x = ""` direction.
        let s5 = cert_for(STR005);
        assert!(
            s5.lemmas()
                .iter()
                .any(|l| matches!(l, LengthLemma::NonEmptyLen { .. })),
            "{:?}",
            s5.lemmas()
        );

        // The code shape is a two-branch split using both code lemmas.
        let c2 = cert_for(CODE2);
        assert!(c2.is_case_split());
        assert_eq!(c2.branch_count(), 2);
        assert!(
            c2.lemmas()
                .iter()
                .any(|l| matches!(l, LengthLemma::SingletonCodeNonneg { .. }))
        );
        assert!(
            c2.lemmas()
                .iter()
                .any(|l| matches!(l, LengthLemma::CodeUpperBound { .. }))
        );
    }

    #[test]
    fn a_certificate_for_another_query_is_rejected() {
        // The commands ARE the premises, so swapping them must make the carried
        // combination stop closing.
        let mut forged = cert_for(STR004);
        forged.commands = commands(STR005);
        assert!(!check_string_length_refutation(&forged));
    }

    /// **SATISFIABLE**: `|yy| = 0` with `yy` unconstrained. Without the `x != ""`
    /// premise the `NonEmptyLen` lemma has no licence, and this is the shape that
    /// would be certified if stage 1 stopped checking side conditions.
    #[test]
    fn a_lemma_whose_premise_the_query_does_not_assert_is_rejected() {
        let sat_text = "(set-logic QF_S)\n(declare-fun yy () String)\n\
            (assert (= (str.len yy) 0))\n(assert (= (str.len yy) 0))\n(check-sat)";
        assert!(
            string_length_refutation(&commands(sat_text)).is_none(),
            "the producer must not refute a satisfiable query"
        );
        // ...and the CHECKER must reject the hand-built forgery too: conjunct 1
        // exists, it is simply not a disequality against `\"\"`.
        let forged = StringLengthRefutationCertificate {
            commands: commands(sat_text),
            lemmas: vec![LengthLemma::NonEmptyLen {
                conjunct: 1,
                var: "yy".to_owned(),
            }],
            split: None,
            branches: vec![vec![
                (FactRef::Conjunct(0), (-1, 1)),
                (FactRef::Lemma(0), (1, 1)),
            ]],
        };
        assert!(!check_string_length_refutation(&forged));
    }

    /// A `str.to_code` lower bound without `|x| = 1` is FALSE: `str.to_code` of a
    /// two-character string is `-1`. Certifying it would report a satisfiable
    /// query as unsat.
    #[test]
    fn the_code_lower_bound_needs_the_singleton_premise() {
        let sat_text = "(set-logic QF_SLIA)\n(declare-fun x () String)\n\
            (assert (= (str.len x) 2))\n(assert (< (str.to_code x) 0))\n(check-sat)";
        assert!(
            string_length_refutation(&commands(sat_text)).is_none(),
            "x = \"ab\" satisfies this: str.to_code of a non-singleton is -1"
        );
        let forged = StringLengthRefutationCertificate {
            commands: commands(sat_text),
            lemmas: vec![LengthLemma::SingletonCodeNonneg {
                conjunct: 0,
                var: "x".to_owned(),
            }],
            split: None,
            branches: vec![vec![
                (FactRef::Conjunct(1), (1, 1)),
                (FactRef::Lemma(0), (1, 1)),
            ]],
        };
        assert!(
            !check_string_length_refutation(&forged),
            "conjunct 0 pins |x| = 2, which does not licence code(x) >= 0"
        );
    }

    /// A negative multiplier on an inequality flips it, and `-(|x| >= 0)` is
    /// `|x| <= 0`, which this query does not say. The query is **SATISFIABLE**
    /// (`x = "abc"`), every fact in the forgery is genuinely available, and the
    /// combination does cancel to `-3` -- only the sign rule stops it.
    #[test]
    fn a_negative_multiplier_on_an_inequality_is_rejected() {
        let text = "(set-logic QF_S)\n(declare-fun x () String)\n\
            (assert (>= (str.len x) 3))\n(check-sat)";
        assert!(string_length_refutation(&commands(text)).is_none());
        let forged = StringLengthRefutationCertificate {
            commands: commands(text),
            lemmas: vec![LengthLemma::LenNonneg {
                var: "x".to_owned(),
            }],
            split: None,
            // (|x| - 3) - |x| = -3 < 0 -- with a NEGATIVE multiplier on `|x| >= 0`.
            branches: vec![vec![
                (FactRef::Conjunct(0), (1, 1)),
                (FactRef::Lemma(0), (-1, 1)),
            ]],
        };
        assert!(!check_string_length_refutation(&forged));
        // Positive control: with the sign the rule allows, the same two facts do
        // not cancel at all, so this test is not passing for another reason.
        let honest = StringLengthRefutationCertificate {
            branches: vec![vec![
                (FactRef::Conjunct(0), (1, 1)),
                (FactRef::Lemma(0), (1, 1)),
            ]],
            ..forged
        };
        assert!(!check_string_length_refutation(&honest));
    }

    /// The strictness rule: a combination of NON-strict facts cancelling to
    /// exactly `0` proves nothing (`0 >= 0` is no contradiction). This query is
    /// satisfiable at `x = ""`, so accepting it would be a wrong verdict.
    #[test]
    fn a_nonstrict_combination_cancelling_to_zero_is_rejected() {
        let text = "(set-logic QF_S)\n(declare-fun x () String)\n\
            (assert (<= (str.len x) 0))\n(check-sat)";
        assert!(string_length_refutation(&commands(text)).is_none());
        let forged = StringLengthRefutationCertificate {
            commands: commands(text),
            lemmas: vec![LengthLemma::LenNonneg {
                var: "x".to_owned(),
            }],
            // `-|x| >= 0` plus `|x| >= 0` cancels to 0, and 0 >= 0 holds.
            split: None,
            branches: vec![vec![
                (FactRef::Conjunct(0), (1, 1)),
                (FactRef::Lemma(0), (1, 1)),
            ]],
        };
        assert!(!check_string_length_refutation(&forged));
    }

    /// The other half of the strictness rule: with one STRICT fact the same
    /// cancellation to `0` IS a contradiction. Without this, the guard above
    /// could be satisfied by never accepting a cancellation to zero at all --
    /// which is exactly what `str004` needs.
    #[test]
    fn a_strict_combination_cancelling_to_zero_is_accepted() {
        let cert = cert_for(STR004);
        assert!(check_string_length_refutation(&cert));
    }

    /// Every arm of the split must be refuted. Dropping one leaves a model.
    #[test]
    fn a_case_split_missing_an_arm_is_rejected() {
        let mut forged = cert_for(CODE2);
        forged.branches.truncate(1);
        assert!(!check_string_length_refutation(&forged));
    }

    /// The combination must cancel to a constant; a leftover variable means the
    /// sum's sign is unknown.
    #[test]
    fn a_combination_that_does_not_cancel_is_rejected() {
        let text = "(set-logic QF_SLIA)\n(declare-fun x () String)\n\
            (declare-fun n () Int)\n(assert (< n 0))\n\
            (assert (>= (str.len x) 0))\n(check-sat)";
        let forged = StringLengthRefutationCertificate {
            commands: commands(text),
            lemmas: Vec::new(),
            split: None,
            // `-n > 0` alone: constant 0, still carrying `n`.
            branches: vec![vec![(FactRef::Conjunct(0), (1, 1))]],
        };
        assert!(!check_string_length_refutation(&forged));
    }

    /// With more than one `check-sat` the assertion list is not the query at any
    /// one of them — the query at the FIRST is a strict subset. Refuting the
    /// whole accumulated conjunction says nothing about it, and here the first
    /// query is genuinely SATISFIABLE (`yy = ""`), so accepting the refutation
    /// would report a wrong verdict for the check-sat it is attached to.
    #[test]
    fn a_script_with_several_queries_is_declined() {
        let text = "(set-logic QF_S)\n(declare-fun yy () String)\n\
            (assert (= (str.len yy) 0))\n(check-sat)\n\
            (assert (not (= yy \"\")))\n(check-sat)";
        assert!(string_length_refutation(&commands(text)).is_none());
        // The checker must refuse to bind against it too, so a certificate built
        // from the one-query form cannot be re-pointed at the two-query script.
        let mut forged = cert_for(STR005);
        forged.commands = commands(text);
        assert!(!check_string_length_refutation(&forged));
        // ...and a script that asks NOTHING has no query to refute.
        let no_query = "(set-logic QF_S)\n(declare-fun yy () String)\n\
            (assert (= (str.len yy) 0))\n(assert (not (= yy \"\")))";
        assert!(string_length_refutation(&commands(no_query)).is_none());
    }

    /// A macro-bearing or incremental script is declined outright: its assertion
    /// list is not the query.
    #[test]
    fn macros_and_incremental_scoping_are_declined() {
        let macro_text = "(set-logic QF_S)\n(declare-fun yy () String)\n\
            (define-fun p () Bool (= (str.len yy) 0))\n\
            (assert (= (str.len yy) 0))\n(assert (not (= yy \"\")))\n(check-sat)";
        assert!(string_length_refutation(&commands(macro_text)).is_none());
        let push_text = "(set-logic QF_S)\n(declare-fun yy () String)\n\
            (push 1)\n(assert (= (str.len yy) 0))\n(assert (not (= yy \"\")))\n(check-sat)";
        assert!(string_length_refutation(&commands(push_text)).is_none());
        // ...and the checker independently refuses to bind against them, so a
        // certificate cannot be smuggled past by hand.
        let mut forged = cert_for(STR005);
        forged.commands = commands(push_text);
        assert!(!check_string_length_refutation(&forged));
    }

    /// Literal lengths are CODE POINTS, and the escape grammar is part of it.
    /// A generator or decoder that treats `\u{1F600}` as seven characters gets a
    /// different length and therefore a different verdict.
    #[test]
    fn literal_lengths_are_code_points_including_escapes() {
        for (literal, want) in [
            ("\"\"", 0),
            ("\"abc\"", 3),
            ("\"\\u{62}\"", 1),
            ("\"\\u0062\"", 1),
            ("\"\\u{1F600}\"", 1),
            ("\"a\"\"b\"", 3),
        ] {
            let e = SExpr::Atom(literal.to_owned());
            assert_eq!(
                literal_len(&e),
                Some(Rational::integer(want)),
                "literal {literal}"
            );
        }
        // A non-literal atom is not a literal length.
        assert_eq!(literal_len(&SExpr::Atom("xx".to_owned())), None);
    }

    /// [`MAX_CODE_POINT`] is this module's copy of the SMT-LIB alphabet bound,
    /// and the parser's literal decoder has its own. Two constants for one bound
    /// is two chances to disagree about a verdict, so this pins them to each
    /// other from the outside: the decoder must accept exactly up to the value
    /// the `CodeUpperBound` lemma asserts, and decline the next one rather than
    /// truncate it.
    #[test]
    fn the_code_point_cap_matches_the_parsers_alphabet_bound() {
        let at_cap = format!("\"\\u{{{MAX_CODE_POINT:X}}}\"");
        assert_eq!(
            literal_len(&SExpr::Atom(at_cap)),
            Some(Rational::integer(1)),
            "the decoder must accept the largest code point the lemma allows"
        );
        let above = format!("\"\\u{{{:X}}}\"", MAX_CODE_POINT + 1);
        assert_eq!(
            literal_len(&SExpr::Atom(above)),
            None,
            "one above the cap must be DECLINED, never silently truncated"
        );
    }

    /// A concatenation with an escaped literal must still refute: this is the
    /// same argument as str004 with `|"\u{1F600}"| = 1` doing the arithmetic.
    #[test]
    fn escaped_literals_participate_in_the_abstraction() {
        let text = "(set-logic QF_SLIA)\n(declare-fun x () String)\n\
            (assert (= x (str.++ x \"\\u{1F600}\")))\n(check-sat)";
        let cert = string_length_refutation(&commands(text)).expect("certificate");
        assert!(check_string_length_refutation(&cert));
    }

    /// The producer must not fire on a satisfiable length system.
    #[test]
    fn satisfiable_length_systems_are_declined() {
        for text in [
            "(set-logic QF_S)\n(declare-fun x () String)\n\
             (assert (> (str.len x) 3))\n(check-sat)",
            "(set-logic QF_S)\n(declare-fun x () String)(declare-fun y () String)\n\
             (assert (= x (str.++ y \"a\")))\n(assert (not (= y \"\")))\n(check-sat)",
            "(set-logic QF_SLIA)\n(declare-fun x () String)\n\
             (assert (= (str.len x) 1))\n(assert (> (str.to_code x) 60))\n(check-sat)",
        ] {
            assert!(
                string_length_refutation(&commands(text)).is_none(),
                "certified a satisfiable query: {text}"
            );
        }
    }

    /// One entry per fact. Splitting a multiplier across two entries leaves the
    /// SUM identical, so nothing but this rule tells the two apart -- and a
    /// combination whose entries are not a function from fact to multiplier is
    /// not the object a reader is being asked to audit.
    #[test]
    fn a_fact_named_twice_in_one_combination_is_rejected() {
        let lemmas = vec![LengthLemma::NonEmptyLen {
            conjunct: 1,
            var: "yy".to_owned(),
        }];
        let forged = StringLengthRefutationCertificate {
            commands: commands(STR005),
            lemmas: lemmas.clone(),
            split: None,
            branches: vec![vec![
                (FactRef::Conjunct(0), (-1, 2)),
                (FactRef::Conjunct(0), (-1, 2)),
                (FactRef::Lemma(0), (1, 1)),
            ]],
        };
        assert!(!check_string_length_refutation(&forged));
        // Positive control: the same total, written once, verifies.
        let honest = StringLengthRefutationCertificate {
            commands: commands(STR005),
            lemmas,
            split: None,
            branches: vec![vec![
                (FactRef::Conjunct(0), (-1, 1)),
                (FactRef::Lemma(0), (1, 1)),
            ]],
        };
        assert!(check_string_length_refutation(&honest));
    }

    /// A zero multiplier contributes nothing, so a combination carrying one is
    /// not the combination it prints. The REST of this one closes, so only the
    /// nonzero rule tells it apart from the honest two-line version.
    #[test]
    fn a_zero_multiplier_on_an_equality_is_rejected() {
        let text = "(set-logic QF_SLIA)\n(declare-fun yy () String)\n\
            (declare-fun n () Int)\n(assert (= (str.len yy) 0))\n\
            (assert (= n 7))\n(assert (not (= yy \"\")))\n(check-sat)";
        let lemmas = vec![LengthLemma::NonEmptyLen {
            conjunct: 2,
            var: "yy".to_owned(),
        }];
        // `n = 7` is a genuine equality fact of this query; multiplying it by
        // zero is the only thing wrong with the certificate.
        let forged = StringLengthRefutationCertificate {
            commands: commands(text),
            lemmas: lemmas.clone(),
            split: None,
            branches: vec![vec![
                (FactRef::Conjunct(0), (-1, 1)),
                (FactRef::Conjunct(1), (0, 1)),
                (FactRef::Lemma(0), (1, 1)),
            ]],
        };
        assert!(!check_string_length_refutation(&forged));
        // Positive control: drop the dead entry and the same argument verifies.
        let honest = StringLengthRefutationCertificate {
            commands: commands(text),
            lemmas,
            split: None,
            branches: vec![vec![
                (FactRef::Conjunct(0), (-1, 1)),
                (FactRef::Lemma(0), (1, 1)),
            ]],
        };
        assert!(check_string_length_refutation(&honest));
    }

    /// A zero denominator is not a rational. It cannot come from the producer,
    /// and a hand-written certificate can contain one.
    #[test]
    fn a_malformed_multiplier_is_rejected() {
        let mut forged = cert_for(STR005);
        forged.branches[0][0].1 = (1, 0);
        assert!(!check_string_length_refutation(&forged));
    }

    /// An empty combination proves nothing; without this guard the vacuous sum
    /// is the constant `0`, and `0 < 0` is false only by accident of the sign
    /// rule rather than by design.
    #[test]
    fn an_empty_combination_is_rejected() {
        let mut forged = cert_for(STR005);
        forged.branches[0].clear();
        assert!(!check_string_length_refutation(&forged));
    }

    /// A conjunctive certificate must have exactly one branch: a second one is
    /// a case analysis with no case to analyse.
    #[test]
    fn a_conjunctive_certificate_with_two_branches_is_rejected() {
        let mut forged = cert_for(STR005);
        let branch = forged.branches[0].clone();
        forged.branches.push(branch);
        assert!(!check_string_length_refutation(&forged));
    }

    /// A reference to a fact this query does not have is rejected, not silently
    /// skipped. Each bogus reference is APPENDED to a combination that already
    /// closes, so a checker that ignored the bad entry would accept every one.
    #[test]
    fn a_reference_to_a_fact_that_does_not_exist_is_rejected() {
        for bogus in [
            FactRef::Lemma(99),
            FactRef::Conjunct(99),
            // Exists, but abstracts to NO linear atom: `yy != ""` is a
            // disequality, not a comparison.
            FactRef::Conjunct(1),
            // No case analysis in this certificate, so there is no arm.
            FactRef::Arm,
        ] {
            let mut forged = cert_for(STR005);
            forged.branches[0].push((bogus, (1, 1)));
            assert!(
                !check_string_length_refutation(&forged),
                "accepted a combination naming {bogus:?}"
            );
        }
    }

    /// The split conjunct itself is assumed only through its arms; using it as a
    /// conjunctive fact would double-count the disjunction.
    #[test]
    fn the_split_conjunct_cannot_also_be_used_as_a_fact() {
        let mut forged = cert_for(CODE2);
        let split = forged.split.expect("case split");
        forged.branches[0][0].0 = FactRef::Conjunct(split);
        assert!(!check_string_length_refutation(&forged));
    }

    /// A split must name a disjunction. Pointing it at a plain conjunct would
    /// silently DROP that conjunct from the fact set and invent arms.
    #[test]
    fn a_split_on_a_non_disjunction_is_rejected() {
        let mut forged = cert_for(CODE2);
        forged.split = Some(0); // conjunct 0 is `(= (str.len x) 1)`
        assert!(!check_string_length_refutation(&forged));
    }

    /// Every arm must abstract to a linear atom; an arm the checker cannot read
    /// is an arm it cannot refute.
    #[test]
    fn a_split_with_an_unreadable_arm_is_declined() {
        // The second disjunct is a regex membership, outside the abstraction.
        let text = "(set-logic QF_SLIA)\n(declare-fun x () String)\n\
            (assert (= (str.len x) 1))\n\
            (assert (or (< (str.to_code x) 0) (str.in_re x (str.to_re \"ab\"))))\n(check-sat)";
        assert!(
            string_length_refutation(&commands(text)).is_none(),
            "an arm outside the abstraction must not be silently skipped"
        );
    }

    /// A lemma about a symbol the script never declares is not a lemma about
    /// this query. It is appended to a combination that already closes, so a
    /// checker that admitted it would accept the whole certificate.
    #[test]
    fn a_lemma_about_an_undeclared_symbol_is_rejected() {
        let mut forged = cert_for(STR005);
        forged.lemmas.push(LengthLemma::LenNonneg {
            var: "never_declared".to_owned(),
        });
        assert!(!check_string_length_refutation(&forged));
    }

    /// A case split must name a DISJUNCTION. `(=> A B)` is `¬A ∨ B`, not
    /// `A ∨ B`, so refuting `A` and `B` separately proves nothing about it --
    /// and this query is **SATISFIABLE** (the implication is a tautology, and
    /// `|x| >= 0` always holds).
    #[test]
    fn a_split_on_an_implication_is_rejected() {
        let text = "(set-logic QF_SLIA)\n(declare-fun x () String)\n\
            (assert (>= (str.len x) 0))\n\
            (assert (=> (< (str.len x) 0) (< (str.len x) 0)))\n(check-sat)";
        assert!(string_length_refutation(&commands(text)).is_none());
        let branch = vec![(FactRef::Arm, (1, 1)), (FactRef::Lemma(0), (1, 1))];
        let forged = StringLengthRefutationCertificate {
            commands: commands(text),
            lemmas: vec![LengthLemma::LenNonneg {
                var: "x".to_owned(),
            }],
            split: Some(1),
            // Both "arms" of the implication really are refutable; reading `=>`
            // as `or` is the entire error.
            branches: vec![branch.clone(), branch],
        };
        assert!(!check_string_length_refutation(&forged));
    }

    /// An arm the abstraction cannot read is an arm the certificate has not
    /// refuted. This query is **SATISFIABLE** at `x = "ab"`, and every other
    /// part of the forgery is genuine: the first arm really is refuted.
    #[test]
    fn a_split_arm_the_abstraction_cannot_read_is_rejected() {
        let text = "(set-logic QF_SLIA)\n(declare-fun x () String)\n\
            (assert (>= (str.len x) 0))\n\
            (assert (or (< (str.len x) 0) (str.in_re x (str.to_re \"ab\"))))\n(check-sat)";
        assert!(string_length_refutation(&commands(text)).is_none());
        let forged = StringLengthRefutationCertificate {
            commands: commands(text),
            lemmas: vec![LengthLemma::LenNonneg {
                var: "x".to_owned(),
            }],
            split: Some(1),
            branches: vec![
                vec![(FactRef::Arm, (1, 1)), (FactRef::Lemma(0), (1, 1))],
                vec![(FactRef::Arm, (1, 1))],
            ],
        };
        assert!(!check_string_length_refutation(&forged));
    }

    /// A DISEQUALITY is not an equality. Reading `(not (= |x| 2))` as
    /// `|x| = 2` would refute this **SATISFIABLE** query (`x = "abc"`) by
    /// cancelling it against `|x| > 2`.
    #[test]
    fn a_negated_equality_is_not_a_linear_atom() {
        let text = "(set-logic QF_SLIA)\n(declare-fun x () String)\n\
            (assert (not (= (str.len x) 2)))\n(assert (> (str.len x) 2))\n(check-sat)";
        assert!(string_length_refutation(&commands(text)).is_none());
    }

    /// The producer never emits a certificate its own checker rejects: producer
    /// and checker disagreeing is the soundness alarm, not a shipping state.
    #[test]
    fn the_producer_self_checks() {
        for text in [STR004, STR005, CODE2] {
            let cert = string_length_refutation(&commands(text)).expect("certificate");
            assert!(
                check_string_length_refutation(&cert),
                "producer emitted a certificate its checker rejects"
            );
        }
    }
}
