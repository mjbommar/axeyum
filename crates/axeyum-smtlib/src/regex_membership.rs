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
//! * `(≷ (str.to_int X) n)` / `(≷ n (str.to_int X))` for
//!   `≷ ∈ {<, <=, >, >=}` and a non-negative numeral `n` — the exact comparison
//!   preimage, including SMT-LIB's `-1` value for non-decimal strings;
//! * `(= X "lit")` / `(= "lit" X)` — pins `X` to a string literal;
//! * `(not (= X "lit"))` / `(not (= "lit" X))` — excludes the singleton
//!   literal language from `X`;
//! * `(= X Y)` between declared string variables — merges their constraints
//!   into one membership class and binds both names to the same checked witness;
//! * `(str.prefixof "lit" X)` / `(str.prefixof X "lit")` and their negations —
//!   respectively the literal-prefix cone and the finite language of literal
//!   prefixes;
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
    /// Other declared string symbols equated to [`Self::sym`]. Every alias is
    /// bound to the same checked witness in a satisfiable model.
    pub aliases: Vec<SymbolId>,
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
            equalities: Vec::new(),
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
        // Merely observing an unsupported membership atom does not create a side
        // channel: preserve the parser's established Unsupported result unless at
        // least one exact constraint was actually retained. A ground `false`
        // conjunct supplies such a constraint; ground `true` does not.
        if builder.per_var.is_empty() && builder.grounds.is_empty() {
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
        for (names, state) in
            merge_equality_classes(&order, &builder.equalities, &mut builder.per_var)
        {
            let primary = &names[0];
            out.vars.push(MemberVar {
                sym: Some(vars[primary]),
                aliases: names[1..].iter().map(|name| vars[name]).collect(),
                name: primary.clone(),
                membership: state.membership,
                pinned: state.pinned,
            });
        }
        for (i, g) in builder.grounds.into_iter().enumerate() {
            out.vars.push(MemberVar {
                sym: None,
                aliases: Vec::new(),
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
    /// Exact equalities between declared string variables. They are merged after
    /// every per-name constraint has been accumulated.
    equalities: Vec<(String, String)>,
    /// Candidate existential output definitions, validated after all membership
    /// classes and source occurrences are known.
    definitions: Vec<(String, Vec<String>)>,
    /// Ground literal-operand atoms: `(membership-over-literal, literal-codepoints)`.
    grounds: Vec<(Membership, Vec<u32>)>,
    saw_membership: bool,
    complete: bool,
}

/// Merges the connected components induced by exact string-variable equalities.
/// Components and their primary names follow declaration order, keeping model
/// construction deterministic.
fn merge_equality_classes(
    order: &[String],
    equalities: &[(String, String)],
    per_var: &mut BTreeMap<String, VarState>,
) -> Vec<(Vec<String>, VarState)> {
    let mut adjacency: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (left, right) in equalities {
        adjacency
            .entry(left.clone())
            .or_default()
            .insert(right.clone());
        adjacency
            .entry(right.clone())
            .or_default()
            .insert(left.clone());
    }

    let mut visited = BTreeSet::new();
    let mut classes = Vec::new();
    for name in order {
        if visited.contains(name) || !per_var.contains_key(name) {
            continue;
        }
        let mut component = BTreeSet::new();
        let mut pending = vec![name.clone()];
        while let Some(current) = pending.pop() {
            if !component.insert(current.clone()) {
                continue;
            }
            if let Some(neighbors) = adjacency.get(&current) {
                pending.extend(neighbors.iter().cloned());
            }
        }
        visited.extend(component.iter().cloned());
        let names: Vec<String> = order
            .iter()
            .filter(|candidate| component.contains(*candidate))
            .cloned()
            .collect();

        let mut merged = VarState::default();
        for member in &names {
            let Some(mut state) = per_var.remove(member) else {
                continue;
            };
            merged
                .membership
                .positives
                .append(&mut state.membership.positives);
            merged
                .membership
                .negatives
                .append(&mut state.membership.negatives);
            merged.membership.len_lo = merged.membership.len_lo.max(state.membership.len_lo);
            merged.membership.len_hi = match (merged.membership.len_hi, state.membership.len_hi) {
                (Some(left), Some(right)) => Some(left.min(right)),
                (left @ Some(_), None) | (None, left @ Some(_)) => left,
                (None, None) => None,
            };
            match (&merged.pinned, state.pinned) {
                (None, pin) => merged.pinned = pin,
                (Some(left), Some(right)) if *left != right => {
                    // Conflicting pins inside one equality class are impossible.
                    merged.membership.len_lo = 1;
                    merged.membership.len_hi = Some(0);
                }
                _ => {}
            }
        }
        classes.push((names, merged));
    }
    classes
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
            "str.prefixof" if items.len() == 3 => {
                self.literal_prefix_atom(&items[1], &items[2], true)
            }
            "not" if items.len() == 2 => {
                let Some(inner) = items[1].list() else {
                    return false;
                };
                if inner.first().and_then(SExpr::atom) == Some("str.in_re") && inner.len() == 3 {
                    self.membership_atom(&inner[1], &inner[2], false)
                } else if inner.first().and_then(SExpr::atom) == Some("str.prefixof")
                    && inner.len() == 3
                {
                    self.literal_prefix_atom(&inner[1], &inner[2], false)
                } else if inner.first().and_then(SExpr::atom) == Some("=") && inner.len() == 3 {
                    if let Some(truth) = ground_numeral_relation("=", &inner[1], &inner[2]) {
                        self.retain_ground_boolean(!truth);
                        true
                    } else {
                        self.literal_disequality_atom(&inner[1], &inner[2])
                    }
                } else {
                    false
                }
            }
            "=" if items.len() == 3 => {
                if let Some(truth) = ground_numeral_relation(head, &items[1], &items[2]) {
                    self.retain_ground_boolean(truth);
                    true
                } else if self.length_atom(head, &items[1], &items[2]) {
                    true
                } else if let Some((name, value)) = to_int_equality(&items[1], &items[2], self.vars)
                {
                    self.per_var
                        .entry(name)
                        .or_default()
                        .membership
                        .positives
                        .push(decimal_value_regex(value));
                    true
                } else if let Some((left, right)) =
                    variable_equality(&items[1], &items[2], self.vars)
                {
                    // Materialize both endpoints so an otherwise unconstrained
                    // alias still receives the shared model witness.
                    self.per_var.entry(left.clone()).or_default();
                    self.per_var.entry(right.clone()).or_default();
                    self.equalities.push((left, right));
                    true
                } else if let Some(definition) = concat_definition(e, self.vars) {
                    self.definitions.push(definition);
                    true
                } else {
                    self.pin_atom(&items[1], &items[2])
                }
            }
            "<" | "<=" | ">" | ">=" if items.len() == 3 => {
                if let Some(truth) = ground_numeral_relation(head, &items[1], &items[2]) {
                    self.retain_ground_boolean(truth);
                    true
                } else if self.length_atom(head, &items[1], &items[2]) {
                    true
                } else if let Some((name, op, bound)) =
                    to_int_comparison(head, &items[1], &items[2], self.vars)
                {
                    self.per_var
                        .entry(name)
                        .or_default()
                        .membership
                        .positives
                        .push(decimal_comparison_regex(&op, bound));
                    true
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    /// `(str.in_re operand R)` (or its negation): `operand` is a declared variable
    /// (per-variable constraint) or a string literal (ground atom).
    fn membership_atom(&mut self, operand: &SExpr, re: &SExpr, positive: bool) -> bool {
        // This is a genuine membership script even when the particular regex is
        // outside the retained fragment. Other exact conjuncts may still refute
        // the full conjunction; subset SAT will decline because `complete=false`.
        self.saw_membership = true;
        let Some(regex) = translate_regex_with_defs(re, self.regex_defs) else {
            return false;
        };
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

    /// Literal/variable `str.prefixof` in either operand orientation. A literal
    /// prefix of a variable is `lit · Σ*`; a variable prefix of a literal is the
    /// finite union of all literal prefixes. Negation becomes negative membership.
    fn literal_prefix_atom(&mut self, prefix: &SExpr, word: &SExpr, positive: bool) -> bool {
        self.saw_membership = true;
        let (name, regex) = match (
            literal_code_points(prefix),
            variable_name(prefix, self.vars),
            literal_code_points(word),
            variable_name(word, self.vars),
        ) {
            (Some(prefix), None, None, Some(name)) => (
                name,
                Regex::concat(literal_regex(&prefix), Regex::star(Regex::any_char())),
            ),
            (None, Some(name), Some(word), None) => (name, prefixes_regex(&word)),
            (Some(prefix), None, Some(word), None) => {
                let truth = word.starts_with(&prefix);
                self.retain_ground_boolean(if positive { truth } else { !truth });
                return true;
            }
            _ => return false,
        };
        let state = self.per_var.entry(name).or_default();
        if positive {
            state.membership.positives.push(regex);
        } else {
            state.membership.negatives.push(regex);
        }
        true
    }

    /// Retains a ground Boolean conjunct. `false` becomes a matcher-rechecked
    /// impossible fixed membership; `true` adds no constraint. This lets an exact
    /// false subset refute a script whose regex atom itself remains unsupported,
    /// while the incomplete-problem gate still forbids a SAT claim.
    fn retain_ground_boolean(&mut self, truth: bool) {
        if truth {
            return;
        }
        let impossible = Membership {
            len_lo: 1,
            len_hi: Some(0),
            ..Membership::default()
        };
        self.grounds.push((impossible, Vec::new()));
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

    /// `(not (= X "lit"))` / `(not (= "lit" X))`: excludes exactly one
    /// literal from the variable's language. This is the negative-membership
    /// analogue of [`Self::pin_atom`], so it composes exactly with regex and
    /// length constraints without introducing a separate reasoning path.
    fn literal_disequality_atom(&mut self, a: &SExpr, b: &SExpr) -> bool {
        let (var, lit) = match (variable_name(a, self.vars), variable_name(b, self.vars)) {
            (Some(name), None) => (name, b),
            (None, Some(name)) => (name, a),
            // Variable-variable and literal-literal disequalities remain outside
            // this single-membership-class fragment.
            _ => return false,
        };
        let Some(cps) = literal_code_points(lit) else {
            return false;
        };
        let state = self.per_var.entry(var).or_default();
        let literal_len = u32::try_from(cps.len()).unwrap_or(u32::MAX);
        if literal_len < state.membership.len_lo
            || state
                .membership
                .len_hi
                .is_some_and(|high| literal_len > high)
        {
            // This literal is already outside the class's length language, so
            // its exclusion is exact but redundant. Avoid injecting a huge
            // singleton into an otherwise cheap derivative intersection.
            return true;
        }
        state.membership.negatives.push(literal_regex(&cps));
        true
    }

    /// A length atom `(op (str.len X) n)` or `(op n (str.len X))` for
    /// `op ∈ {=,<,<=,>,>=}` and a non-negative numeral `n`.
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
            "=" => {
                mem.len_lo = mem.len_lo.max(bound);
                mem.len_hi = Some(mem.len_hi.map_or(bound, |high| high.min(bound)));
            }
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

/// Equality between two declared string variables.
fn variable_equality(
    left: &SExpr,
    right: &SExpr,
    vars: &BTreeMap<String, SymbolId>,
) -> Option<(String, String)> {
    Some((variable_name(left, vars)?, variable_name(right, vars)?))
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

/// A comparison between `(str.to_int X)` and a non-negative numeral, normalized
/// so the string conversion is on the left.
fn to_int_comparison(
    op: &str,
    left: &SExpr,
    right: &SExpr,
    vars: &BTreeMap<String, SymbolId>,
) -> Option<(String, String, u32)> {
    match (str_to_int_var(left, vars), numeral(right)) {
        (Some(name), Some(bound)) => Some((name, op.to_owned(), bound)),
        _ => Some((str_to_int_var(right, vars)?, flip_op(op), numeral(left)?)),
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

/// Exact preimage of an ordered comparison against SMT-LIB `str.to_int`.
/// Non-empty ASCII decimal strings map to their mathematical value (leading
/// zeroes allowed); every other string maps to `-1`.
fn decimal_comparison_regex(op: &str, bound: u32) -> Regex {
    let digit = Regex::char_range(u32::from(b'0'), u32::from(b'9'));
    let non_decimal = Regex::comp(Regex::plus(digit));
    match op {
        ">" => decimal_at_least_regex(bound, false),
        ">=" => decimal_at_least_regex(bound, true),
        "<" if bound == 0 => non_decimal,
        "<" => Regex::union(non_decimal, decimal_at_most_regex(bound - 1)),
        "<=" => Regex::union(non_decimal, decimal_at_most_regex(bound)),
        _ => Regex::none(),
    }
}

/// Non-empty decimal strings whose numeric value is at most `bound`.
fn decimal_at_most_regex(bound: u32) -> Regex {
    let zero = Regex::character(u32::from(b'0'));
    let mut language = Regex::plus(zero.clone());
    if bound == 0 {
        return language;
    }

    let digits = bound.to_string().into_bytes();
    let mut canonical = Regex::none();
    // Every positive canonical decimal with fewer digits is smaller.
    for width in 1..digits.len() {
        canonical = Regex::union(canonical, positive_decimal_width(width));
    }
    // Same-width values: first smaller digit after an equal prefix, or equality.
    for index in 0..digits.len() {
        let lower = if index == 0 { b'1' } else { b'0' };
        if digits[index] > lower {
            let branch = Regex::concat(
                literal_regex(
                    &digits[..index]
                        .iter()
                        .map(|&b| u32::from(b))
                        .collect::<Vec<_>>(),
                ),
                Regex::concat(
                    Regex::char_range(u32::from(lower), u32::from(digits[index] - 1)),
                    decimal_suffix(digits.len() - index - 1, false),
                ),
            );
            canonical = Regex::union(canonical, branch);
        }
    }
    canonical = Regex::union(
        canonical,
        literal_regex(&digits.iter().map(|&b| u32::from(b)).collect::<Vec<_>>()),
    );
    language = Regex::union(language, Regex::concat(Regex::star(zero), canonical));
    language
}

/// Non-empty decimal strings whose numeric value is greater than `bound`, or
/// greater than-or-equal when `include_equal` is true.
fn decimal_at_least_regex(bound: u32, include_equal: bool) -> Regex {
    let digit = Regex::char_range(u32::from(b'0'), u32::from(b'9'));
    if bound == 0 && include_equal {
        return Regex::plus(digit);
    }

    let digits = bound.to_string().into_bytes();
    let mut canonical = Regex::none();
    // Every positive canonical decimal with more digits is larger.
    canonical = Regex::union(
        canonical,
        Regex::concat(
            Regex::char_range(u32::from(b'1'), u32::from(b'9')),
            decimal_suffix(digits.len(), true),
        ),
    );
    // Same-width values: first larger digit after an equal prefix.
    for index in 0..digits.len() {
        if digits[index] < b'9' {
            let branch = Regex::concat(
                literal_regex(
                    &digits[..index]
                        .iter()
                        .map(|&b| u32::from(b))
                        .collect::<Vec<_>>(),
                ),
                Regex::concat(
                    Regex::char_range(u32::from(digits[index] + 1), u32::from(b'9')),
                    decimal_suffix(digits.len() - index - 1, false),
                ),
            );
            canonical = Regex::union(canonical, branch);
        }
    }
    if include_equal {
        canonical = Regex::union(
            canonical,
            literal_regex(&digits.iter().map(|&b| u32::from(b)).collect::<Vec<_>>()),
        );
    }
    Regex::concat(Regex::star(Regex::character(u32::from(b'0'))), canonical)
}

/// Canonical positive decimal strings of exactly `width` digits.
fn positive_decimal_width(width: usize) -> Regex {
    debug_assert!(width > 0);
    Regex::concat(
        Regex::char_range(u32::from(b'1'), u32::from(b'9')),
        decimal_suffix(width - 1, false),
    )
}

/// An exact-width decimal suffix, optionally followed by arbitrary extra digits.
fn decimal_suffix(width: usize, unbounded_tail: bool) -> Regex {
    let digit = Regex::char_range(u32::from(b'0'), u32::from(b'9'));
    let exact = Regex::repeat(
        digit.clone(),
        u32::try_from(width).expect("u32 threshold width fits"),
        Some(u32::try_from(width).expect("u32 threshold width fits")),
    );
    if unbounded_tail {
        Regex::concat(exact, Regex::star(digit))
    } else {
        exact
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

/// Exact ground relation between two non-negative numerals.
fn ground_numeral_relation(op: &str, left: &SExpr, right: &SExpr) -> Option<bool> {
    let left = numeral(left)?;
    let right = numeral(right)?;
    Some(match op {
        "=" => left == right,
        "<" => left < right,
        "<=" => left <= right,
        ">" => left > right,
        ">=" => left >= right,
        _ => return None,
    })
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

/// The finite language containing every prefix of `word`, including `ε` and the
/// complete word.
fn prefixes_regex(word: &[u32]) -> Regex {
    let mut language = Regex::empty();
    for end in 1..=word.len() {
        language = Regex::union(language, literal_regex(&word[..end]));
    }
    language
}

#[cfg(test)]
mod tests {
    use axeyum_strings::regex::matches;

    use super::decimal_comparison_regex;

    fn strings(alphabet: &[u32], max_len: usize) -> Vec<Vec<u32>> {
        fn extend(
            alphabet: &[u32],
            remaining: usize,
            prefix: &mut Vec<u32>,
            out: &mut Vec<Vec<u32>>,
        ) {
            out.push(prefix.clone());
            if remaining == 0 {
                return;
            }
            for &cp in alphabet {
                prefix.push(cp);
                extend(alphabet, remaining - 1, prefix, out);
                prefix.pop();
            }
        }
        let mut out = Vec::new();
        extend(alphabet, max_len, &mut Vec::new(), &mut out);
        out
    }

    fn reference_to_int(input: &[u32]) -> i64 {
        if input.is_empty()
            || input
                .iter()
                .any(|cp| !(u32::from(b'0')..=u32::from(b'9')).contains(cp))
        {
            return -1;
        }
        input.iter().fold(0i64, |value, cp| {
            value * 10 + i64::from(*cp - u32::from(b'0'))
        })
    }

    #[test]
    fn decimal_comparison_preimages_match_reference_exhaustively() {
        let inputs = strings(
            &[
                u32::from(b'0'),
                u32::from(b'1'),
                u32::from(b'2'),
                u32::from(b'a'),
            ],
            4,
        );
        for bound in 0..=25u32 {
            for op in ["<", "<=", ">", ">="] {
                let regex = decimal_comparison_regex(op, bound);
                for input in &inputs {
                    let value = reference_to_int(input);
                    let expected = match op {
                        "<" => value < i64::from(bound),
                        "<=" => value <= i64::from(bound),
                        ">" => value > i64::from(bound),
                        ">=" => value >= i64::from(bound),
                        _ => unreachable!(),
                    };
                    assert_eq!(
                        matches(&regex, input),
                        expected,
                        "op={op}, bound={bound}, input={input:?}, value={value}"
                    );
                }
            }
        }
    }
}
