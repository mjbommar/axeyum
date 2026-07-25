//! The **regex-membership side channel** (P2.7 T-C.5, ADR-0054).
//!
//! A parser-side translation of a script's regex-membership fragment into a set
//! of single-variable [`axeyum_strings::Membership`] problems over the code-point
//! [`Regex`](axeyum_strings::Regex) engine. It is the regex
//! analogue of the [`WordProblem`](crate::Script::word_problem) side channel: the
//! solver consults it *strictly after* the bounded route and the word routes
//! decline, and the symbolic-derivative membership solver decides it (witness +
//! replay for `sat`, a re-checked emptiness certificate for `unsat`).
//!
//! ## The recognized fragment
//!
//! The side channel retains these asserted conjuncts:
//!
//! * `(str.in_re X R)` / `(not (str.in_re X R))` where `X` is a declared string
//!   variable and `R` translates to a code-point [`Regex`] — a positive/negative
//!   membership on `X`;
//! * a unique top-level definition `(= A R)` (or symmetric) of a declared 0-ary
//!   `RegLan` alias `A` by a concrete supported regex `R`; the alias is substituted
//!   into membership regexes;
//! * `(str.in_re "lit" R)` / its negation over a **string literal** operand — a
//!   ground membership atom the solver checks by the reference matcher;
//! * a length atom `(≷ (str.len X) n)` / `(≷ n (str.len X))` for
//!   `≷ ∈ {<, <=, >, >=, =}` and a non-negative numeral `n` — a length bound on
//!   `X`;
//! * `(= (str.to_int X) n)` / `(= n (str.to_int X))` for a non-negative numeral
//!   `n` — the exact decimal language of `n`, including leading zeroes;
//! * `(= X "lit")` / `(= "lit" X)` — pins `X` to a string literal;
//! * `(= OUT (str.++ X Y …))` (or symmetric) when `OUT` occurs nowhere else and
//!   every input variable has retained membership constraints — a model-defining
//!   concatenation evaluated after the input witnesses are checked;
//! * `(and …)` of the above, and the trivial `true`.
//!
//! An unrecognized conjunct makes [`MembershipProblem::complete`] false but does
//! not discard recognized conjuncts. This incomplete problem is usable only for
//! `unsat`: unsatisfiability of a conjunctive subset proves the full script
//! unsatisfiable, while satisfiability of that subset proves nothing and must
//! decline. Incremental scoping and macros still collapse the channel to `None`,
//! because the active-assertion subset is no longer fixed.
//!
//! ## Character-set caveat
//!
//! String literals are decoded to Unicode **code points** (SMT-LIB `\u{…}` /
//! `\uXXXX` escapes handled), matching the `axeyum-strings` `BitVec(18)` alphabet
//! (ADR-0051). A literal or `re.range` endpoint whose code point exceeds
//! [`ALPHABET_MAX`](axeyum_strings::regex::ALPHABET_MAX) is not retained rather
//! than translated unfaithfully; any other retained membership conjuncts make an
//! incomplete, `unsat`-only problem.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::{Sort, SymbolId, TermArena};
use axeyum_strings::Membership;
use axeyum_strings::regex::{ALPHABET_MAX, Regex};

use crate::sexpr::SExpr;

/// A translated regex-membership problem: one [`MemberVar`] per constrained
/// variable (or synthetic ground atom).
#[derive(Clone, Debug, Default)]
pub struct MembershipProblem {
    /// The per-variable membership constraints (user variables first, in
    /// declaration order, then synthetic ground-atom entries).
    pub vars: Vec<MemberVar>,
    /// Model-defining concatenations evaluated after all input membership
    /// witnesses have been checked.
    pub definitions: Vec<MemberConcatDefinition>,
    /// `true` exactly when every asserted conjunct was represented. A complete
    /// problem may decide `sat` or `unsat`; an incomplete problem may only prove
    /// `unsat` from its retained conjunctive subset.
    pub complete: bool,
}

/// A safe existential output definition `output = concat(inputs...)`. The parser
/// admits it only when `output` occurs exactly once across all assertions, is not
/// independently constrained, and every input has a retained membership class.
#[derive(Clone, Debug)]
pub struct MemberConcatDefinition {
    /// The `!weq!<name>` symbol to bind to the concatenated input witnesses.
    pub output: SymbolId,
    /// Input `!weq!<name>` symbols in source concatenation order.
    pub inputs: Vec<SymbolId>,
}

/// One variable's membership constraint set, or a synthetic ground membership
/// atom (a literal-operand membership, carried as a [`pinned`](Self::pinned)
/// entry with no [`sym`](Self::sym)).
#[derive(Clone, Debug)]
pub struct MemberVar {
    /// The `!weq!<name>` `Seq`-sorted symbol a returned model binds, or `None`
    /// for a synthetic ground atom (nothing to bind).
    pub sym: Option<SymbolId>,
    /// The source variable name (or a synthetic `!const!k` for a ground atom).
    pub name: String,
    /// The translated membership constraints.
    pub membership: Membership,
    /// A fixed witness (the variable is pinned to a string literal, or this is a
    /// ground literal-operand atom); the solver validates it via the reference
    /// matcher instead of searching.
    pub pinned: Option<Vec<u32>>,
}

impl MembershipProblem {
    /// Builds the side channel from the post-desugar top-level command
    /// s-expressions, or `None` when there is no supported membership atom (or
    /// fixed active assertion set) to retain; see the module documentation.
    #[must_use]
    pub fn build(arena: &mut TermArena, exprs: &[SExpr]) -> Option<MembershipProblem> {
        // Incremental scoping / macros break the "active subset ⊆ all asserts"
        // soundness argument — decline wholesale (mirrors `build_word_problem`).
        for e in exprs {
            if let Some(
                "push" | "pop" | "check-sat-assuming" | "reset-assertions" | "define-fun"
                | "define-fun-rec" | "define-funs-rec" | "define-sort",
            ) = e.list().and_then(|l| l.first()).and_then(SExpr::atom)
            {
                return None;
            }
        }

        // Unique top-level definitions of declared 0-ary RegLan constants are
        // exact aliases. Only concrete right-hand sides are admitted here: alias
        // dependency ordering and recursive definitions remain unsupported.
        let regex_vars: BTreeSet<String> = exprs
            .iter()
            .filter_map(declared_regex_var)
            .map(str::to_owned)
            .collect();
        let regex_defs = collect_regex_definitions(exprs, &regex_vars);

        // Declared string variables → a fresh `Seq`-sorted symbol each (shared
        // with the word channels via the `!weq!<name>` naming convention).
        let mut vars: BTreeMap<String, SymbolId> = BTreeMap::new();
        let mut order: Vec<String> = Vec::new();
        for e in exprs {
            if let Some(name) = declared_string_var(e)
                && !vars.contains_key(name)
            {
                let sym = arena
                    .declare_internal(&format!("!weq!{name}"), Sort::string())
                    .ok()?;
                vars.insert(name.to_owned(), sym);
                order.push(name.to_owned());
            }
        }
        let mut string_occurrences: BTreeMap<String, usize> = BTreeMap::new();
        for e in exprs {
            if let Some(body) = asserted_body(e) {
                count_string_var_occurrences(body, &vars, &mut string_occurrences);
            }
        }

        let mut builder = Builder {
            vars: &vars,
            regex_defs: &regex_defs,
            per_var: BTreeMap::new(),
            definitions: Vec::new(),
            grounds: Vec::new(),
            saw_membership: false,
            complete: true,
        };
        for e in exprs {
            let Some(items) = e.list() else { continue };
            if items.first().and_then(SExpr::atom) == Some("assert") {
                let [_, body] = items else { return None };
                // A unique top-level RegLan definition is represented by exact
                // substitution in every retained membership atom.
                if concrete_regex_definition(body, &regex_vars)
                    .is_some_and(|(name, _)| regex_defs.contains_key(&name))
                {
                    continue;
                }
                if !builder.atom(body) {
                    builder.complete = false;
                }
            }
        }
        // Require at least one genuine membership atom, else this is not a regex
        // problem this route should claim.
        if !builder.saw_membership {
            return None;
        }

        // A concatenation equality is model-defining only when its output is a
        // fresh existential sink and every input already receives a checked
        // membership witness. Anything more connected remains an unsupported
        // conjunct, making the retained problem UNSAT-only.
        let (definitions, definitions_complete) = validate_concat_definitions(
            &builder.definitions,
            &string_occurrences,
            &builder.per_var,
            &vars,
        );
        builder.complete &= definitions_complete;

        let mut out = MembershipProblem {
            vars: Vec::new(),
            definitions,
            complete: builder.complete,
        };
        for name in &order {
            if let Some(state) = builder.per_var.remove(name) {
                out.vars.push(MemberVar {
                    sym: Some(vars[name]),
                    name: name.clone(),
                    membership: state.membership,
                    pinned: state.pinned,
                });
            }
        }
        for (i, g) in builder.grounds.into_iter().enumerate() {
            out.vars.push(MemberVar {
                sym: None,
                name: format!("!const!{i}"),
                membership: g.0,
                pinned: Some(g.1),
            });
        }
        Some(out)
    }
}

/// Per-variable accumulator during the build.
#[derive(Default)]
struct VarState {
    membership: Membership,
    pinned: Option<Vec<u32>>,
}

struct Builder<'a> {
    vars: &'a BTreeMap<String, SymbolId>,
    regex_defs: &'a BTreeMap<String, Regex>,
    per_var: BTreeMap<String, VarState>,
    /// Candidate existential output definitions, validated after all membership
    /// classes and source occurrences are known.
    definitions: Vec<(String, Vec<String>)>,
    /// Ground literal-operand atoms: `(membership-over-literal, literal-codepoints)`.
    grounds: Vec<(Membership, Vec<u32>)>,
    saw_membership: bool,
    complete: bool,
}

/// Validates candidate existential concatenation sinks after every asserted
/// variable occurrence and membership class is known.
fn validate_concat_definitions(
    candidates: &[(String, Vec<String>)],
    occurrences: &BTreeMap<String, usize>,
    per_var: &BTreeMap<String, VarState>,
    vars: &BTreeMap<String, SymbolId>,
) -> (Vec<MemberConcatDefinition>, bool) {
    let mut definitions = Vec::new();
    let mut outputs = BTreeSet::new();
    let mut complete = true;
    for (output, inputs) in candidates {
        let valid = occurrences.get(output) == Some(&1)
            && !per_var.contains_key(output)
            && outputs.insert(output.clone())
            && inputs
                .iter()
                .all(|input| input != output && per_var.contains_key(input));
        if valid {
            definitions.push(MemberConcatDefinition {
                output: vars[output],
                inputs: inputs.iter().map(|input| vars[input]).collect(),
            });
        } else {
            complete = false;
        }
    }
    (definitions, complete)
}

impl Builder<'_> {
    /// Retains one asserted conjunct, returning `false` when that conjunct is
    /// outside the recognized fragment. A top-level `and` visits every child even
    /// after one child is unsupported, so later usable conjuncts are not lost.
    fn atom(&mut self, e: &SExpr) -> bool {
        if e.atom() == Some("true") {
            return true;
        }
        let Some(items) = e.list() else { return false };
        let Some(head) = items.first().and_then(SExpr::atom) else {
            return false;
        };
        match head {
            "and" => {
                let mut complete = true;
                for child in &items[1..] {
                    complete &= self.atom(child);
                }
                complete
            }
            "str.in_re" if items.len() == 3 => self.membership_atom(&items[1], &items[2], true),
            "not" if items.len() == 2 => {
                let Some(inner) = items[1].list() else {
                    return false;
                };
                if inner.first().and_then(SExpr::atom) == Some("str.in_re") && inner.len() == 3 {
                    self.membership_atom(&inner[1], &inner[2], false)
                } else {
                    false
                }
            }
            "=" if items.len() == 3 => {
                if let Some((name, value)) = to_int_equality(&items[1], &items[2], self.vars) {
                    self.per_var
                        .entry(name)
                        .or_default()
                        .membership
                        .positives
                        .push(decimal_value_regex(value));
                    true
                } else if let Some(definition) = concat_definition(e, self.vars) {
                    self.definitions.push(definition);
                    true
                } else {
                    self.pin_atom(&items[1], &items[2])
                }
            }
            "<" | "<=" | ">" | ">=" if items.len() == 3 => {
                self.length_atom(head, &items[1], &items[2])
            }
            _ => false,
        }
    }

    /// `(str.in_re operand R)` (or its negation): `operand` is a declared variable
    /// (per-variable constraint) or a string literal (ground atom).
    fn membership_atom(&mut self, operand: &SExpr, re: &SExpr, positive: bool) -> bool {
        let Some(regex) = translate_regex_with_defs(re, self.regex_defs) else {
            return false;
        };
        self.saw_membership = true;
        if let Some(name) = variable_name(operand, self.vars) {
            let state = self.per_var.entry(name).or_default();
            if positive {
                state.membership.positives.push(regex);
            } else {
                state.membership.negatives.push(regex);
            }
            true
        } else if let Some(cps) = literal_code_points(operand) {
            let mut m = Membership::default();
            if positive {
                m.positives.push(regex);
            } else {
                m.negatives.push(regex);
            }
            self.grounds.push((m, cps));
            true
        } else {
            false
        }
    }

    /// `(= X "lit")` / `(= "lit" X)`: pins the variable `X` to the literal.
    fn pin_atom(&mut self, a: &SExpr, b: &SExpr) -> bool {
        let (var, lit) = match (variable_name(a, self.vars), variable_name(b, self.vars)) {
            (Some(name), None) => (name, b),
            (None, Some(name)) => (name, a),
            // Two variables or two literals: not a pin this route handles.
            _ => return false,
        };
        let Some(cps) = literal_code_points(lit) else {
            return false;
        };
        let state = self.per_var.entry(var).or_default();
        match &state.pinned {
            // A second, conflicting pin: represent as an unsatisfiable length
            // window so the solver reports `unsat` (two literals cannot be equal).
            Some(prev) if *prev != cps => {
                state.membership.len_lo = 1;
                state.membership.len_hi = Some(0);
                true
            }
            _ => {
                state.pinned = Some(cps);
                true
            }
        }
    }

    /// A length atom `(op (str.len X) n)` or `(op n (str.len X))` for
    /// `op ∈ {<,<=,>,>=}` and a non-negative numeral `n`.
    fn length_atom(&mut self, op: &str, lhs: &SExpr, rhs: &SExpr) -> bool {
        // Identify which side is `(str.len X)` and which is the numeral, and
        // normalize `op` so the variable is on the left.
        let (name, bound, op) = match (str_len_var(lhs, self.vars), numeral(rhs)) {
            (Some(name), Some(n)) => (name, n, op.to_owned()),
            _ => match (numeral(lhs), str_len_var(rhs, self.vars)) {
                (Some(n), Some(name)) => (name, n, flip_op(op)),
                _ => return false,
            },
        };
        let state = self.per_var.entry(name).or_default();
        let mem = &mut state.membership;
        // len(X) `op` bound, all bounds inclusive on `[len_lo, len_hi]`.
        match op.as_str() {
            ">=" => mem.len_lo = mem.len_lo.max(bound),
            ">" => mem.len_lo = mem.len_lo.max(bound.saturating_add(1)),
            "<=" => mem.len_hi = Some(mem.len_hi.map_or(bound, |h| h.min(bound))),
            "<" => {
                if bound == 0 {
                    // len < 0 is impossible for an unsigned length ⇒ unsat window.
                    mem.len_lo = 1;
                    mem.len_hi = Some(0);
                } else {
                    let hi = bound - 1;
                    mem.len_hi = Some(mem.len_hi.map_or(hi, |cur| cur.min(hi)));
                }
            }
            _ => return false,
        }
        true
    }
}

/// An equality between `(str.to_int X)` and a non-negative numeral, accepting
/// either orientation.
fn to_int_equality(
    left: &SExpr,
    right: &SExpr,
    vars: &BTreeMap<String, SymbolId>,
) -> Option<(String, u32)> {
    match (str_to_int_var(left, vars), numeral(right)) {
        (Some(name), Some(value)) => Some((name, value)),
        _ => Some((str_to_int_var(right, vars)?, numeral(left)?)),
    }
}

/// The declared string variable inside `(str.to_int X)`.
fn str_to_int_var(e: &SExpr, vars: &BTreeMap<String, SymbolId>) -> Option<String> {
    let items = e.list()?;
    (items.len() == 2 && items[0].atom() == Some("str.to_int"))
        .then(|| variable_name(&items[1], vars))?
}

/// The exact language of strings whose SMT-LIB `str.to_int` value is `value`.
/// Decimal strings may contain arbitrary leading zeroes; zero itself requires at
/// least one zero (`""` maps to `-1`, not zero).
fn decimal_value_regex(value: u32) -> Regex {
    let zero = Regex::character(u32::from(b'0'));
    if value == 0 {
        Regex::plus(zero)
    } else {
        let digits: Vec<u32> = value.to_string().bytes().map(u32::from).collect();
        Regex::concat(Regex::star(zero), literal_regex(&digits))
    }
}

/// The declared name of a 0-ary `String`-sorted symbol, if `e` is such a
/// declaration (`(declare-const x String)` / `(declare-fun x () String)`).
fn declared_string_var(e: &SExpr) -> Option<&str> {
    let items = e.list()?;
    match items.first().and_then(SExpr::atom)? {
        "declare-const" if items.len() == 3 => {
            (items[2].atom() == Some("String")).then(|| items[1].atom())?
        }
        "declare-fun" if items.len() == 4 => {
            let empty_params = items[2].list().is_some_and(<[SExpr]>::is_empty);
            (empty_params && items[3].atom() == Some("String")).then(|| items[1].atom())?
        }
        _ => None,
    }
}

/// The declared name of a 0-ary `RegLan`-sorted symbol, if any.
fn declared_regex_var(e: &SExpr) -> Option<&str> {
    let items = e.list()?;
    match items.first().and_then(SExpr::atom)? {
        "declare-const" if items.len() == 3 => {
            (items[2].atom() == Some("RegLan")).then(|| items[1].atom())?
        }
        "declare-fun" if items.len() == 4 => {
            let empty_params = items[2].list().is_some_and(<[SExpr]>::is_empty);
            (empty_params && items[3].atom() == Some("RegLan")).then(|| items[1].atom())?
        }
        _ => None,
    }
}

/// The body of a well-formed top-level `(assert body)` command.
fn asserted_body(e: &SExpr) -> Option<&SExpr> {
    let [head, body] = e.list()? else {
        return None;
    };
    (head.atom() == Some("assert")).then_some(body)
}

/// A concrete definition of a declared `RegLan` alias, in either equality
/// orientation. The regex must not depend on another alias.
fn concrete_regex_definition(e: &SExpr, regex_vars: &BTreeSet<String>) -> Option<(String, Regex)> {
    let items = e.list()?;
    if items.len() != 3 || items[0].atom() != Some("=") {
        return None;
    }
    for (name_expr, regex_expr) in [(&items[1], &items[2]), (&items[2], &items[1])] {
        if let Some(name) = name_expr.atom()
            && regex_vars.contains(name)
        {
            return Some((name.to_owned(), translate_regex(regex_expr)?));
        }
    }
    None
}

/// Collects only uniquely asserted concrete definitions for each regex alias.
fn collect_regex_definitions(
    exprs: &[SExpr],
    regex_vars: &BTreeSet<String>,
) -> BTreeMap<String, Regex> {
    let mut candidates: BTreeMap<String, (usize, Regex)> = BTreeMap::new();
    for e in exprs {
        let Some((name, regex)) =
            asserted_body(e).and_then(|body| concrete_regex_definition(body, regex_vars))
        else {
            continue;
        };
        candidates
            .entry(name)
            .and_modify(|entry| entry.0 += 1)
            .or_insert((1, regex));
    }
    candidates
        .into_iter()
        .filter_map(|(name, (count, regex))| (count == 1).then_some((name, regex)))
        .collect()
}

/// Counts declared string-variable occurrences in one asserted expression.
fn count_string_var_occurrences(
    e: &SExpr,
    vars: &BTreeMap<String, SymbolId>,
    counts: &mut BTreeMap<String, usize>,
) {
    match e {
        SExpr::Atom(atom) => {
            if vars.contains_key(atom) {
                *counts.entry(atom.clone()).or_default() += 1;
            }
        }
        SExpr::List(items) => {
            for item in items {
                count_string_var_occurrences(item, vars, counts);
            }
        }
    }
}

/// A top-level equality defining one declared string variable as a concatenation
/// of at least two declared string variables, in either equality orientation.
fn concat_definition(
    e: &SExpr,
    vars: &BTreeMap<String, SymbolId>,
) -> Option<(String, Vec<String>)> {
    let items = e.list()?;
    if items.len() != 3 || items[0].atom() != Some("=") {
        return None;
    }
    for (output_expr, concat_expr) in [(&items[1], &items[2]), (&items[2], &items[1])] {
        if let Some(output) = variable_name(output_expr, vars) {
            let mut inputs = Vec::new();
            if flatten_concat_vars(concat_expr, vars, &mut inputs) && inputs.len() >= 2 {
                return Some((output, inputs));
            }
        }
    }
    None
}

/// Flattens a `str.++` tree whose leaves are declared string variables.
fn flatten_concat_vars(
    e: &SExpr,
    vars: &BTreeMap<String, SymbolId>,
    out: &mut Vec<String>,
) -> bool {
    if let Some(name) = variable_name(e, vars) {
        out.push(name);
        return true;
    }
    let Some(items) = e.list() else {
        return false;
    };
    if items.first().and_then(SExpr::atom) != Some("str.++") || items.len() < 3 {
        return false;
    }
    items[1..]
        .iter()
        .all(|item| flatten_concat_vars(item, vars, out))
}

/// The variable name if `e` is a declared string variable atom.
fn variable_name(e: &SExpr, vars: &BTreeMap<String, SymbolId>) -> Option<String> {
    let a = e.atom()?;
    vars.contains_key(a).then(|| a.to_owned())
}

/// The variable name if `e` is `(str.len X)` for a declared string variable `X`.
fn str_len_var(e: &SExpr, vars: &BTreeMap<String, SymbolId>) -> Option<String> {
    let items = e.list()?;
    if items.len() == 2 && items[0].atom() == Some("str.len") {
        variable_name(&items[1], vars)
    } else {
        None
    }
}

/// A non-negative decimal numeral atom, capped to `u32`.
fn numeral(e: &SExpr) -> Option<u32> {
    let a = e.atom()?;
    if a.bytes().all(|b| b.is_ascii_digit()) && !a.is_empty() {
        a.parse::<u32>().ok()
    } else {
        None
    }
}

/// The comparison operator with its arguments swapped (`a op b` ⟺ `b flip(op) a`).
fn flip_op(op: &str) -> String {
    match op {
        "<" => ">",
        "<=" => ">=",
        ">" => "<",
        ">=" => "<=",
        other => other,
    }
    .to_owned()
}

/// Decodes an SMT-LIB string literal atom (quotes included) to its Unicode code
/// points, handling `""`-escaped quotes and `\u{…}` / `\uXXXX` escapes. Returns
/// `None` if `e` is not a string literal or a code point exceeds
/// [`ALPHABET_MAX`].
fn literal_code_points(e: &SExpr) -> Option<Vec<u32>> {
    let a = e.atom()?;
    if a.len() < 2 || !a.starts_with('"') || !a.ends_with('"') {
        return None;
    }
    let inner = a[1..a.len() - 1].replace("\"\"", "\"");
    let chars: Vec<char> = inner.chars().collect();
    let mut out: Vec<u32> = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        if chars[i] == '\\' && chars.get(i + 1) == Some(&'u') {
            let after = i + 2;
            let code = if chars.get(after) == Some(&'{') {
                let close = chars[after + 1..].iter().position(|&c| c == '}')?;
                let hex: String = chars[after + 1..after + 1 + close].iter().collect();
                let v = u32::from_str_radix(&hex, 16).ok()?;
                i = after + 1 + close + 1;
                v
            } else if after + 4 <= chars.len() {
                let hex: String = chars[after..after + 4].iter().collect();
                let v = u32::from_str_radix(&hex, 16).ok()?;
                i = after + 4;
                v
            } else {
                return None;
            };
            if code > ALPHABET_MAX {
                return None;
            }
            out.push(code);
        } else {
            let cp = chars[i] as u32;
            if cp > ALPHABET_MAX {
                return None;
            }
            out.push(cp);
            i += 1;
        }
    }
    Some(out)
}

/// Translates a `RegLan` s-expression into a code-point [`Regex`], or `None` when
/// it is outside the supported regex fragment (an unfaithful translation is never
/// produced — it declines instead).
///
/// Shared with the Boolean-structured word skeleton
/// ([`crate::parse`]), which lifts `str.in_re` atoms into theory atoms for the
/// online CDCL(T) route.
pub(crate) fn translate_regex(e: &SExpr) -> Option<Regex> {
    translate_regex_with_defs(e, &BTreeMap::new())
}

/// Translates a regex while resolving exact, concrete `RegLan` aliases gathered
/// from unique top-level definitions.
fn translate_regex_with_defs(e: &SExpr, defs: &BTreeMap<String, Regex>) -> Option<Regex> {
    match e {
        SExpr::Atom(a) => match a.as_str() {
            "re.none" => Some(Regex::none()),
            "re.all" => Some(Regex::star(Regex::any_char())),
            "re.allchar" => Some(Regex::any_char()),
            _ => defs.get(a).cloned(),
        },
        SExpr::List(items) => {
            let head = items.first()?;
            // Indexed forms: `((_ re.loop i j) R)` / `((_ re.^ n) R)`.
            if let Some(list) = head.list() {
                return translate_indexed(list, &items[1..], defs);
            }
            let head = head.atom()?;
            let args = &items[1..];
            match head {
                "str.to_re" if args.len() == 1 => {
                    let cps = literal_code_points(&args[0])?;
                    Some(literal_regex(&cps))
                }
                "re.range" if args.len() == 2 => {
                    let lo = literal_code_points(&args[0])?;
                    let hi = literal_code_points(&args[1])?;
                    match (lo.as_slice(), hi.as_slice()) {
                        // A single-char endpoint pair; `char_range` folds `lo > hi`
                        // to the empty predicate (⇒ ∅).
                        ([l], [h]) => Some(Regex::char_range(*l, *h)),
                        // A degenerate (empty/multi-char) endpoint ⇒ ∅.
                        _ => Some(Regex::none()),
                    }
                }
                "re.++" if !args.is_empty() => {
                    fold_translate(args, Regex::concat, Regex::Empty, defs)
                }
                "re.union" if !args.is_empty() => {
                    fold_translate(args, Regex::union, Regex::none(), defs)
                }
                "re.inter" if !args.is_empty() => {
                    fold_translate(args, Regex::inter, Regex::universal(), defs)
                }
                "re.comp" if args.len() == 1 => {
                    Some(Regex::comp(translate_regex_with_defs(&args[0], defs)?))
                }
                "re.diff" if args.len() == 2 => {
                    let a = translate_regex_with_defs(&args[0], defs)?;
                    let b = translate_regex_with_defs(&args[1], defs)?;
                    Some(Regex::inter(a, Regex::comp(b)))
                }
                "re.*" if args.len() == 1 => {
                    Some(Regex::star(translate_regex_with_defs(&args[0], defs)?))
                }
                "re.+" if args.len() == 1 => {
                    Some(Regex::plus(translate_regex_with_defs(&args[0], defs)?))
                }
                "re.opt" if args.len() == 1 => {
                    Some(Regex::opt(translate_regex_with_defs(&args[0], defs)?))
                }
                _ => None,
            }
        }
    }
}

/// Translates an indexed regex form: `(_ re.loop i j)` / `(_ re.^ n)` applied to
/// `args` (exactly one sub-regex).
fn translate_indexed(
    idx: &[SExpr],
    args: &[SExpr],
    defs: &BTreeMap<String, Regex>,
) -> Option<Regex> {
    if idx.first().and_then(SExpr::atom) != Some("_") || args.len() != 1 {
        return None;
    }
    let inner = translate_regex_with_defs(&args[0], defs)?;
    match idx.get(1).and_then(SExpr::atom) {
        Some("re.loop") if idx.len() == 4 => {
            let lo = numeral(&idx[2])?;
            let hi = numeral(&idx[3])?;
            Some(Regex::repeat(inner, lo, Some(hi)))
        }
        Some("re.^") if idx.len() == 3 => {
            let n = numeral(&idx[2])?;
            Some(Regex::repeat(inner, n, Some(n)))
        }
        _ => None,
    }
}

/// Folds `args` (each translated) with `f`, using `unit` for a single argument's
/// degenerate combination.
fn fold_translate(
    args: &[SExpr],
    f: impl Fn(Regex, Regex) -> Regex,
    _unit: Regex,
    defs: &BTreeMap<String, Regex>,
) -> Option<Regex> {
    let mut acc = translate_regex_with_defs(&args[0], defs)?;
    for a in &args[1..] {
        acc = f(acc, translate_regex_with_defs(a, defs)?);
    }
    Some(acc)
}

/// A literal code-point sequence as a `Regex` (concat of single-character
/// predicates; empty ⇒ `ε`).
fn literal_regex(cps: &[u32]) -> Regex {
    let mut acc: Option<Regex> = None;
    for &c in cps {
        let ch = Regex::character(c);
        acc = Some(match acc {
            None => ch,
            Some(prev) => Regex::concat(prev, ch),
        });
    }
    acc.unwrap_or(Regex::Empty)
}
