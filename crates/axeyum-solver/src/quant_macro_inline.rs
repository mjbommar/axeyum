//! **Definitional macro finding and inlining** for quantified queries (ADR-2127).
//!
//! A quantified assertion of the shape
//!
//! ```text
//! ∀ x₁ … xₙ.  f(x₁, …, xₙ) = t[x₁, …, xₙ]
//! ```
//!
//! where `f` is an uninterpreted function of the query, the arguments are
//! **distinct bound variables covering the whole binder**, and `f` does **not**
//! occur in `t`, is not a constraint on `f` — it is a *definition* of `f`. Every
//! application `f(a₁, …, aₙ)` anywhere in the query may be replaced by
//! `t[x̄ := ā]`, and the defining assertion dropped. `f` then does not occur in
//! the query at all, and one universally quantified assertion has become ground
//! content.
//!
//! This is z3's `macro_finder`. The criteria below are transcribed from it with
//! `file:line`, because each one is load-bearing for soundness and none is
//! obvious from the shape alone.
//!
//! # Why this exists
//!
//! `bench-results/dt-ground-probe-20260916/README.md` established that
//! ADR-2114's `GROUND` attribution is **z3's preprocessing of the quantified
//! assertions**, not a separable set of ground assertions: deleting every
//! quantified assertion from those 83 files and asking plain z3 gives 83 of 83
//! `sat`. It named two mechanisms. The first — skolemizing an existential at
//! positive polarity — turned out to be **already implemented and already
//! firing** here ([`crate::quant_skolemize`], measured 0 bails and 0 no-ops over
//! 90 undecided files, `bench-results/quant-preprocess-20260916/skolem-reach/`).
//! This module is the second.
//!
//! # The criteria, and why each is soundness and not taste
//!
//! [`is_macro_head`] is z3 `macro_util::is_macro_head`
//! (`references/z3/src/ast/macros/macro_util.cpp:139-165`):
//!
//! - **The head is an uninterpreted function.** A theory symbol already has a
//!   fixed meaning; "defining" it is a constraint, not a definition.
//! - **Arity equals the binder size** (`macro_util.cpp:143`, `==` and not `>=`;
//!   `>=` is exactly the quasi-macro relaxation this module does not implement).
//! - **The arguments are distinct bound variables** (`macro_util.cpp:147-152`).
//!   Without distinctness, `∀x. f(x,x) = t` constrains only the diagonal, and
//!   rewriting `f(a,b)` with it is **unsound** — it can turn a satisfiable query
//!   unsat.
//! - **They cover the whole binder.** In z3 this is derived rather than checked:
//!   arity `n` plus distinctness plus every index `< n` makes the map from
//!   positions to indices an injection into a set of the same size, hence a
//!   bijection (z3 states the outcome at `macro_util.cpp:135-137`). Here it is
//!   checked explicitly. A binder variable not reachable from the head is
//!   universally quantified over the **body**, so the assertion says something
//!   about `t` for all its values — again a constraint, not a definition.
//!
//! [`occurs_func`] is the **occurs check**, z3
//! `macro_util::is_left_simple_macro`'s `!occurs(to_app(lhs)->get_decl(), rhs)`
//! (`macro_util.cpp:182`, mirrored at `:222`, traversal at `occurs.cpp:76-85`).
//! `∀x. f(x) = g(f(x))` is a recursive constraint; inlining it does not
//! terminate and does not preserve models.
//!
//! [`acyclic`] is z3 `macro_manager::insert`'s dependency-cycle rejection
//! (`macro_manager.cpp:130-134`). Each definition passes the occurs check on its
//! own and two of them can still close a loop: `∀x. f(x) = g(x)` together with
//! `∀x. g(x) = f(x)` is two legal macros whose inlining diverges. The occurs
//! check is per-assertion and cannot see this; only a check over the whole
//! definition set can.
//!
//! A symbol defined **more than once** is refused outright rather than
//! first-definition-wins. z3 takes the same position at
//! `macro_manager.cpp:120-123`, and the reason is that the second assertion is
//! then a genuine constraint that dropping would lose.
//!
//! # Soundness, and what does NOT transfer
//!
//! Given all of the above, inlining is an **equivalence**: the models of the
//! rewritten query are exactly the models of the original restricted away from
//! `f`, and `f`'s interpretation is recoverable from `t`. So `unsat` transfers
//! back to the original unconditionally.
//!
//! `sat` does **not** transfer through this module, and the reason is a project
//! rule rather than a gap in the mathematics: every `sat` must be checkable by
//! evaluating the **original** term against the lifted model (CLAUDE.md, Hard
//! Rules), and a model of the rewritten query has no interpretation for `f` at
//! all — `f` is gone. Recovering it means evaluating `t` at every argument tuple
//! the model distinguishes, which is model reconstruction this module does not
//! do. [`MacroInlining::sat_transfers`] is therefore `false` and the caller must
//! not hand back a bare `sat` from an inlined query. This mirrors
//! [`crate::quant_skolemize`], whose `sat` does not transfer either.
//!
//! # Determinism
//!
//! Definitions are collected in **assertion order** and applied in a single
//! fixpoint whose iteration order is the assertion order, never a hash-map
//! order. The refusal cases are total orders on the same data. Two runs on the
//! same input produce byte-identical output (CLAUDE.md, Hard Rules).
//!
//! # The lever
//!
//! Off unless `AXEYUM_MACRO_INLINE=1`. See [`macro_inline_enabled`].

use std::collections::{HashMap, HashSet};

use axeyum_ir::{FuncId, Op, SymbolId, TermArena, TermId, TermNode};

/// Whether definitional macro inlining is armed.
///
/// **OFF unless `AXEYUM_MACRO_INLINE=1`.** The polarity is stated rather than
/// implied: this lever is opt-IN, so the shipped binary is byte-identical to one
/// built without this module on its path, and an A/B is one binary and two
/// environment values.
///
/// Read once through a `OnceLock` so an A/B cannot be perturbed mid-run by a
/// later `set_var`. The spelling is parsed by [`parse_macro_inline_lever`],
/// split out so the ON/OFF polarity is testable **without touching process
/// environment** — a test that mutates the environment is a test that races
/// every other test in the binary.
#[must_use]
pub(crate) fn macro_inline_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| {
        parse_macro_inline_lever(std::env::var("AXEYUM_MACRO_INLINE").ok().as_deref())
    })
}

/// Parses [`macro_inline_enabled`]'s spelling: armed only by exactly `"1"`.
///
/// Anything else — unset, empty, `"0"`, `"true"`, whitespace — is OFF. A lever
/// that accepts several spellings for ON is a lever whose A/B arms cannot be
/// stated in one line.
fn parse_macro_inline_lever(raw: Option<&str>) -> bool {
    raw == Some("1")
}

/// A definition `f(x̄) := body[x̄]` recovered from one assertion.
#[derive(Debug, Clone)]
struct MacroDef {
    /// The binder variables, in the head's **argument** order — so `params[i]`
    /// is substituted by the `i`th actual, whatever order the binder declared
    /// them in. z3 handles the permutation with `normalize_expr`
    /// (`macro_util.cpp:503-538`); recording argument order does the same job.
    params: Vec<SymbolId>,
    /// The definition body.
    body: TermId,
    /// The assertion this came from, so it can be dropped.
    source: TermId,
}

/// Outcome of [`inline_definitional_macros`].
#[derive(Debug, Clone)]
pub(crate) struct MacroInlining {
    /// The rewritten assertion set, with defining assertions dropped.
    pub(crate) assertions: Vec<TermId>,
    /// Whether anything was inlined at all. `false` means `assertions` equals
    /// the input and the caller should proceed exactly as before.
    pub(crate) changed: bool,
    /// How many definitions were inlined.
    pub(crate) inlined: usize,
    /// Whether a `sat` from the rewritten query transfers to the original.
    ///
    /// Always `false` while this module does no model reconstruction. It is a
    /// field rather than a constant so the caller reads the answer from the
    /// producer instead of restating it, and so a future reconstruction route
    /// flips one place.
    pub(crate) sat_transfers: bool,
}

impl MacroInlining {
    /// The unchanged outcome: the input, untouched.
    fn unchanged(assertions: &[TermId]) -> Self {
        Self {
            assertions: assertions.to_vec(),
            changed: false,
            inlined: 0,
            sat_transfers: false,
        }
    }
}

/// Finds definitional macros in `assertions` and inlines them.
///
/// Returns [`MacroInlining::unchanged`] whenever nothing qualifies, or whenever
/// any of the refusal conditions fires — this pass never partially applies a
/// definition set it could not fully justify.
///
/// # Errors
///
/// Returns [`axeyum_ir::IrError`] only from term construction.
pub(crate) fn inline_definitional_macros(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<MacroInlining, axeyum_ir::IrError> {
    let defs = collect_definitions(arena, assertions);
    if defs.is_empty() {
        return Ok(MacroInlining::unchanged(assertions));
    }
    if !acyclic(arena, &defs) {
        return Ok(MacroInlining::unchanged(assertions));
    }

    let sources: HashSet<TermId> = defs.values().map(|d| d.source).collect();
    let mut out = Vec::with_capacity(assertions.len());
    // `defs.len() + 1` bounds the substitution depth: each level must consume at
    // least one distinct definition or `acyclic` would have refused, so a run
    // that needs more levels than there are definitions has found a cycle the
    // check missed, and declining is the only safe answer.
    let fuel = defs.len() + 1;
    for &assertion in assertions {
        if sources.contains(&assertion) {
            continue;
        }
        let mut memo: HashMap<TermId, TermId> = HashMap::new();
        let Some(rewritten) = expand(arena, assertion, &defs, &mut memo, fuel)? else {
            return Ok(MacroInlining::unchanged(assertions));
        };
        out.push(rewritten);
    }

    Ok(MacroInlining {
        assertions: out,
        changed: true,
        inlined: defs.len(),
        sat_transfers: false,
    })
}

/// Collects every definitional macro in `assertions`, in assertion order.
///
/// A function defined **twice** is removed from the result entirely rather than
/// keeping the first: the second assertion is a real constraint on `f`, and
/// inlining the first while dropping only the first would be sound but inlining
/// while dropping both would not. Refusing the symbol keeps both assertions.
fn collect_definitions(arena: &TermArena, assertions: &[TermId]) -> HashMap<FuncId, MacroDef> {
    let mut defs: HashMap<FuncId, MacroDef> = HashMap::new();
    let mut duplicated: HashSet<FuncId> = HashSet::new();
    for &assertion in assertions {
        let Some((func, def)) = read_definition(arena, assertion) else {
            continue;
        };
        if defs.insert(func, def).is_some() {
            duplicated.insert(func);
        }
    }
    for func in duplicated {
        defs.remove(&func);
    }
    // There is deliberately NO "every free symbol of the body is a parameter"
    // guard here. It could not fire: an assertion is closed, and
    // `is_macro_head` forces every binder variable into the head, so a symbol
    // free in the body is either a parameter or a constant the query declares
    // -- and a declared constant is ground and travels with the body. A guard
    // that cannot fire reads as protection and provides none (CLAUDE.md).
    defs
}

/// Reads one assertion as `∀x̄. f(x̄) = t[x̄]`, if it is one.
///
/// Both orientations are tried, left first, matching z3's `is_simple_macro`
/// (`macro_util.h:99-101`). The Boolean `↔` case needs no separate branch: in
/// this IR, as in z3 (`ast.h:2197`), `iff` is `Eq` at Bool sort.
fn read_definition(arena: &TermArena, assertion: TermId) -> Option<(FuncId, MacroDef)> {
    let (binders, body) = peel_foralls(arena, assertion);
    if binders.is_empty() {
        return None;
    }
    let TermNode::App { op: Op::Eq, args } = arena.node(body) else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let (lhs, rhs) = (args[0], args[1]);
    for (head, def_body) in [(lhs, rhs), (rhs, lhs)] {
        let Some((func, params)) = is_macro_head(arena, head, &binders) else {
            continue;
        };
        if occurs_func(arena, def_body, func) {
            continue;
        }
        return Some((
            func,
            MacroDef {
                params,
                body: def_body,
                source: assertion,
            },
        ));
    }
    None
}

/// Peels a chain of `Forall` binders, returning the bound symbols (outermost
/// first) and the body beneath them.
///
/// This IR spells `∀x y. φ` as `Forall(x)(Forall(y)(φ))`, one symbol per node,
/// so the binder of an n-ary macro is a chain and not a list.
fn peel_foralls(arena: &TermArena, term: TermId) -> (Vec<SymbolId>, TermId) {
    let mut binders = Vec::new();
    let mut current = term;
    while let TermNode::App {
        op: Op::Forall(var),
        args,
    } = arena.node(current)
    {
        if args.len() != 1 {
            break;
        }
        binders.push(*var);
        current = args[0];
    }
    (binders, current)
}

/// z3 `macro_util::is_macro_head` (`macro_util.cpp:139-165`).
///
/// Returns the head function and its parameters **in argument order** when
/// `head` is an application of an uninterpreted function whose arguments are
/// distinct bound variables covering every binder variable.
///
/// The parameter order matters and is the subtle part: `∀x y. f(y, x) = t` is a
/// legal macro, and rewriting `f(a, b)` with it must bind `y := a`, `x := b`.
/// Returning the binder order instead would silently swap them.
fn is_macro_head(
    arena: &TermArena,
    head: TermId,
    binders: &[SymbolId],
) -> Option<(FuncId, Vec<SymbolId>)> {
    let TermNode::App {
        op: Op::Apply(func),
        args,
    } = arena.node(head)
    else {
        return None;
    };
    if args.len() != binders.len() {
        return None;
    }
    let bound: HashSet<SymbolId> = binders.iter().copied().collect();
    let mut params = Vec::with_capacity(args.len());
    let mut seen: HashSet<SymbolId> = HashSet::new();
    for &arg in args {
        let TermNode::Symbol(sym) = arena.node(arg) else {
            return None;
        };
        if !bound.contains(sym) || !seen.insert(*sym) {
            return None;
        }
        params.push(*sym);
    }
    // Distinct, all bound, and as many as the binder: an injection between two
    // sets of equal size, hence onto. Coverage holds; asserting it costs one
    // comparison and makes the argument checkable rather than inferred.
    debug_assert_eq!(seen.len(), bound.len());
    if seen.len() != bound.len() {
        return None;
    }
    Some((*func, params))
}

/// The OCCURS CHECK: whether `func` is applied anywhere in `term`.
///
/// z3 `occurs(func_decl*, expr*)` (`occurs.cpp:76-85`), which matches on the
/// declaration and descends into nested quantifiers. So does this.
fn occurs_func(arena: &TermArena, term: TermId, func: FuncId) -> bool {
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(t) {
            if matches!(op, Op::Apply(f) if *f == func) {
                return true;
            }
            stack.extend(args.iter().copied());
        }
    }
    false
}

/// DFS colouring for [`acyclic`]: a function on the current path is `Open`, one
/// whose whole subtree is explored is `Done`, and reaching an `Open` node again
/// is the cycle.
#[derive(Clone, Copy, PartialEq)]
enum Mark {
    Open,
    Done,
}

/// z3 `macro_manager::insert`'s acyclicity check (`macro_manager.cpp:130-134`).
///
/// Each definition passes the occurs check alone and a SET of them can still
/// close a loop — `∀x. f(x) = g(x)` with `∀x. g(x) = f(x)` is two legal macros
/// whose expansion diverges. Nothing per-assertion can see that.
///
/// The graph is `f → {every defined function applied in f's body}`; a cycle
/// anywhere means refuse the whole set.
fn acyclic(arena: &TermArena, defs: &HashMap<FuncId, MacroDef>) -> bool {
    // Iterative DFS with the colouring above. `keys` is sorted so the visit
    // order does not depend on hash-map iteration order — the ANSWER here is
    // order-independent, but a future debug print of the cycle would not be.
    let mut keys: Vec<FuncId> = defs.keys().copied().collect();
    keys.sort_unstable();

    let mut mark: HashMap<FuncId, Mark> = HashMap::new();

    for &root in &keys {
        if mark.contains_key(&root) {
            continue;
        }
        let mut stack: Vec<(FuncId, bool)> = vec![(root, false)];
        while let Some((func, finishing)) = stack.pop() {
            if finishing {
                mark.insert(func, Mark::Done);
                continue;
            }
            match mark.get(&func) {
                Some(Mark::Done) => continue,
                Some(Mark::Open) => return false,
                None => {}
            }
            mark.insert(func, Mark::Open);
            stack.push((func, true));
            let Some(def) = defs.get(&func) else {
                // Not a defined function: a leaf of this graph.
                continue;
            };
            let mut next: Vec<FuncId> = applied_functions(arena, def.body)
                .into_iter()
                .filter(|f| defs.contains_key(f))
                .collect();
            next.sort_unstable();
            for f in next {
                stack.push((f, false));
            }
        }
    }
    true
}

/// Every function applied anywhere in `term`, deduplicated.
fn applied_functions(arena: &TermArena, term: TermId) -> Vec<FuncId> {
    let mut found: HashSet<FuncId> = HashSet::new();
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(t) {
            if let Op::Apply(f) = op {
                found.insert(*f);
            }
            stack.extend(args.iter().copied());
        }
    }
    let mut out: Vec<FuncId> = found.into_iter().collect();
    out.sort_unstable();
    out
}

/// Rewrites `term`, replacing every application of a defined function by its
/// instantiated body, to a fixpoint.
///
/// `Ok(None)` means the fuel ran out, i.e. a definition cycle [`acyclic`] did
/// not catch; the caller then declines the whole inlining rather than shipping a
/// partially expanded query.
fn expand(
    arena: &mut TermArena,
    term: TermId,
    defs: &HashMap<FuncId, MacroDef>,
    memo: &mut HashMap<TermId, TermId>,
    fuel: usize,
) -> Result<Option<TermId>, axeyum_ir::IrError> {
    if fuel == 0 {
        return Ok(None);
    }
    if let Some(&cached) = memo.get(&term) {
        return Ok(Some(cached));
    }
    let rewritten = match arena.node(term).clone() {
        TermNode::App { op, args } => {
            let mut new_args = Vec::with_capacity(args.len());
            for arg in &args {
                let Some(e) = expand(arena, *arg, defs, memo, fuel)? else {
                    return Ok(None);
                };
                new_args.push(e);
            }
            let rebuilt = arena.rebuild_with_args(term, &new_args);
            if let Op::Apply(func) = op
                && let Some(def) = defs.get(&func)
            {
                // The arguments are already expanded, so the instantiated body
                // still needs one more expansion pass only if the BODY itself
                // applies a defined function. Spending one unit of fuel per
                // nesting level is what bounds that.
                let bindings: Vec<(SymbolId, TermId)> =
                    def.params.iter().copied().zip(new_args).collect();
                let instantiated = substitute_symbols(arena, def.body, &bindings)?;
                let Some(e) = expand(arena, instantiated, defs, memo, fuel - 1)? else {
                    return Ok(None);
                };
                e
            } else {
                rebuilt
            }
        }
        _ => term,
    };
    memo.insert(term, rewritten);
    Ok(Some(rewritten))
}

/// Substitutes `bindings` (symbol → term) throughout `term`.
///
/// Capture cannot occur here: the replacements are the actual arguments of an
/// application in the query, and a macro body's free symbols are its parameters
/// plus declared constants — neither can be captured by a binder inside the
/// body, because a binder inside the body binds a symbol the query declares
/// separately. The walk still stops descending into a binder that shadows a
/// parameter, which is the only shape that could go wrong.
fn substitute_symbols(
    arena: &mut TermArena,
    term: TermId,
    bindings: &[(SymbolId, TermId)],
) -> Result<TermId, axeyum_ir::IrError> {
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    substitute_inner(arena, term, bindings, &mut memo)
}

fn substitute_inner(
    arena: &mut TermArena,
    term: TermId,
    bindings: &[(SymbolId, TermId)],
    memo: &mut HashMap<TermId, TermId>,
) -> Result<TermId, axeyum_ir::IrError> {
    if let Some(&cached) = memo.get(&term) {
        return Ok(cached);
    }
    let out = match arena.node(term).clone() {
        TermNode::Symbol(sym) => bindings
            .iter()
            .find(|(s, _)| *s == sym)
            .map_or(term, |(_, t)| *t),
        TermNode::App { op, args } => {
            // A binder that rebinds one of our parameters shadows it: below that
            // node the parameter is a different variable and must not be
            // replaced. Dropping the shadowed binding is the whole fix.
            let shadowed: Option<SymbolId> = match op {
                Op::Forall(v) | Op::Exists(v) => Some(v),
                _ => None,
            };
            let filtered: Vec<(SymbolId, TermId)>;
            let active: &[(SymbolId, TermId)] = match shadowed {
                Some(v) if bindings.iter().any(|(s, _)| *s == v) => {
                    filtered = bindings.iter().copied().filter(|(s, _)| *s != v).collect();
                    &filtered
                }
                _ => bindings,
            };
            if active.is_empty() {
                return Ok(term);
            }
            let mut new_args = Vec::with_capacity(args.len());
            for arg in &args {
                new_args.push(substitute_inner(arena, *arg, active, memo)?);
            }
            arena.rebuild_with_args(term, &new_args)
        }
        _ => term,
    };
    memo.insert(term, out);
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::Sort;

    /// Builds `∀x. f(x) = <body built from x>` style fixtures.
    struct Fix {
        arena: TermArena,
    }

    impl Fix {
        fn new() -> Self {
            Self {
                arena: TermArena::new(),
            }
        }

        fn int_sym(&mut self, name: &str) -> (SymbolId, TermId) {
            let sym = self.arena.declare(name, Sort::Int).unwrap();
            let term = self.arena.var(sym);
            (sym, term)
        }

        fn int_fn(&mut self, name: &str, arity: usize) -> FuncId {
            let params: Vec<Sort> = vec![Sort::Int; arity];
            self.arena.declare_fun(name, &params, Sort::Int).unwrap()
        }
    }

    #[test]
    fn lever_is_off_unless_exactly_one() {
        // The polarity is the thing a reader gets wrong, so it is pinned in both
        // directions, and without touching process environment.
        assert!(!parse_macro_inline_lever(None));
        assert!(!parse_macro_inline_lever(Some("0")));
        assert!(!parse_macro_inline_lever(Some("")));
        assert!(!parse_macro_inline_lever(Some("true")));
        assert!(!parse_macro_inline_lever(Some(" 1")));
        assert!(parse_macro_inline_lever(Some("1")));
    }

    #[test]
    fn a_simple_definition_is_inlined_and_its_assertion_dropped() {
        // POSITIVE CONTROL. Every refusal test below is only evidence because
        // this one passes: if nothing ever inlined, `changed == false` would be
        // true for the wrong reason everywhere.
        let mut fix = Fix::new();
        let (x, xt) = fix.int_sym("x");
        let (_a, at) = fix.int_sym("a");
        let f = fix.int_fn("f", 1);
        let one = fix.arena.int_const(1);

        let fx = fix.arena.apply(f, &[xt]).unwrap();
        let body = fix.arena.int_add(xt, one).unwrap();
        let eq = fix.arena.eq(fx, body).unwrap();
        let def = fix.arena.forall(x, eq).unwrap();

        let fa = fix.arena.apply(f, &[at]).unwrap();
        let goal = fix.arena.eq(fa, one).unwrap();

        let out = inline_definitional_macros(&mut fix.arena, &[def, goal]).unwrap();
        assert!(out.changed);
        assert_eq!(out.inlined, 1);
        assert_eq!(out.assertions.len(), 1, "the defining assertion is dropped");
        assert!(
            !occurs_func(&fix.arena, out.assertions[0], f),
            "f must not survive anywhere in the rewritten query"
        );
    }

    #[test]
    fn sat_never_transfers_through_an_inlined_query() {
        // The rewritten query's model has NO interpretation for `f`, so it
        // cannot be replayed against the original term. This is the project's
        // Hard Rule, and it is asserted on the PRODUCER's own report rather than
        // restated at the call site.
        let mut fix = Fix::new();
        let (x, xt) = fix.int_sym("x");
        let f = fix.int_fn("f", 1);
        let one = fix.arena.int_const(1);
        let fx = fix.arena.apply(f, &[xt]).unwrap();
        let body = fix.arena.int_add(xt, one).unwrap();
        let eq = fix.arena.eq(fx, body).unwrap();
        let def = fix.arena.forall(x, eq).unwrap();
        let t = fix.arena.bool_const(true);

        let out = inline_definitional_macros(&mut fix.arena, &[def, t]).unwrap();
        assert!(out.changed);
        assert!(!out.sat_transfers);
    }

    #[test]
    fn occurs_check_refuses_a_recursive_definition() {
        // SOUNDNESS NEGATIVE. `∀x. f(x) = g(f(x))` is not a definition: inlining
        // it does not terminate and does not preserve models.
        let mut fix = Fix::new();
        let (x, xt) = fix.int_sym("x");
        let f = fix.int_fn("f", 1);
        let g = fix.int_fn("g", 1);

        let fx = fix.arena.apply(f, &[xt]).unwrap();
        let gfx = fix.arena.apply(g, &[fx]).unwrap();
        let eq = fix.arena.eq(fx, gfx).unwrap();
        let def = fix.arena.forall(x, eq).unwrap();
        let t = fix.arena.bool_const(true);

        let out = inline_definitional_macros(&mut fix.arena, &[def, t]).unwrap();
        assert!(!out.changed, "the occurs check must refuse this");
        assert_eq!(out.inlined, 0);
    }

    #[test]
    fn partial_coverage_is_refused() {
        // SOUNDNESS NEGATIVE. `∀x. h(x, c) = x + 1` says nothing about `h(a, b)`
        // for `b != c`. Inlining it would turn a satisfiable query unsat, which
        // is exactly the wrong-unsat this project must never ship.
        let mut fix = Fix::new();
        let (x, xt) = fix.int_sym("x");
        let (_c, ct) = fix.int_sym("c");
        let h = fix.int_fn("h", 2);
        let one = fix.arena.int_const(1);

        let hxc = fix.arena.apply(h, &[xt, ct]).unwrap();
        let body = fix.arena.int_add(xt, one).unwrap();
        let eq = fix.arena.eq(hxc, body).unwrap();
        let def = fix.arena.forall(x, eq).unwrap();
        let t = fix.arena.bool_const(true);

        let out = inline_definitional_macros(&mut fix.arena, &[def, t]).unwrap();
        assert!(!out.changed, "a ground argument is not full coverage");
    }

    #[test]
    fn a_repeated_variable_argument_is_refused() {
        // SOUNDNESS NEGATIVE. `∀x. h(x, x) = x + 1` constrains only the
        // diagonal; `h(a, b)` with `a != b` is unconstrained.
        let mut fix = Fix::new();
        let (x, xt) = fix.int_sym("x");
        let h = fix.int_fn("h", 2);
        let one = fix.arena.int_const(1);

        let hxx = fix.arena.apply(h, &[xt, xt]).unwrap();
        let body = fix.arena.int_add(xt, one).unwrap();
        let eq = fix.arena.eq(hxx, body).unwrap();
        let def = fix.arena.forall(x, eq).unwrap();
        let t = fix.arena.bool_const(true);

        let out = inline_definitional_macros(&mut fix.arena, &[def, t]).unwrap();
        assert!(!out.changed, "distinctness is not optional");
    }

    #[test]
    fn a_binder_variable_missing_from_the_head_is_refused() {
        // `∀x y. f(x) = y` is a constraint ("f(x) equals everything"), not a
        // definition, and it is UNSATISFIABLE for a non-trivial sort. Inlining
        // it as `f(a) := y` would lose that.
        let mut fix = Fix::new();
        let (x, xt) = fix.int_sym("x");
        let (y, yt) = fix.int_sym("y");
        let f = fix.int_fn("f", 1);

        let fx = fix.arena.apply(f, &[xt]).unwrap();
        let eq = fix.arena.eq(fx, yt).unwrap();
        let inner = fix.arena.forall(y, eq).unwrap();
        let def = fix.arena.forall(x, inner).unwrap();
        let t = fix.arena.bool_const(true);

        let out = inline_definitional_macros(&mut fix.arena, &[def, t]).unwrap();
        assert!(!out.changed);
    }

    #[test]
    fn two_definitions_of_one_function_are_both_kept() {
        // The second assertion is a real constraint. First-definition-wins would
        // inline one and drop it while keeping the other, which is sound but
        // loses the chance to see the contradiction; dropping BOTH is unsound.
        // Refusing the symbol keeps both.
        let mut fix = Fix::new();
        let (x, xt) = fix.int_sym("x");
        let f = fix.int_fn("f", 1);
        let one = fix.arena.int_const(1);
        let two = fix.arena.int_const(2);

        let fx = fix.arena.apply(f, &[xt]).unwrap();
        let b1 = fix.arena.int_add(xt, one).unwrap();
        let b2 = fix.arena.int_add(xt, two).unwrap();
        let d1 = {
            let e = fix.arena.eq(fx, b1).unwrap();
            fix.arena.forall(x, e).unwrap()
        };
        let d2 = {
            let e = fix.arena.eq(fx, b2).unwrap();
            fix.arena.forall(x, e).unwrap()
        };

        let out = inline_definitional_macros(&mut fix.arena, &[d1, d2]).unwrap();
        assert!(!out.changed, "a twice-defined symbol is not a macro");
    }

    #[test]
    fn mutually_recursive_definitions_are_refused_by_the_cycle_check() {
        // SOUNDNESS NEGATIVE, and the one NO per-assertion check can catch.
        // `∀x. f(x) = g(x)` and `∀x. g(x) = f(x)` each pass the occurs check on
        // their own; together they diverge.
        let mut fix = Fix::new();
        let (x, xt) = fix.int_sym("x");
        let f = fix.int_fn("f", 1);
        let g = fix.int_fn("g", 1);

        let fx = fix.arena.apply(f, &[xt]).unwrap();
        let gx = fix.arena.apply(g, &[xt]).unwrap();
        let d1 = {
            let e = fix.arena.eq(fx, gx).unwrap();
            fix.arena.forall(x, e).unwrap()
        };
        let d2 = {
            let e = fix.arena.eq(gx, fx).unwrap();
            fix.arena.forall(x, e).unwrap()
        };

        let out = inline_definitional_macros(&mut fix.arena, &[d1, d2]).unwrap();
        assert!(!out.changed, "a definition cycle must refuse the whole set");
    }

    #[test]
    fn head_on_the_right_is_found_too() {
        let mut fix = Fix::new();
        let (x, xt) = fix.int_sym("x");
        let (_a, at) = fix.int_sym("a");
        let f = fix.int_fn("f", 1);
        let one = fix.arena.int_const(1);

        let fx = fix.arena.apply(f, &[xt]).unwrap();
        let body = fix.arena.int_add(xt, one).unwrap();
        let eq = fix.arena.eq(body, fx).unwrap();
        let def = fix.arena.forall(x, eq).unwrap();
        let fa = fix.arena.apply(f, &[at]).unwrap();
        let goal = fix.arena.eq(fa, one).unwrap();

        let out = inline_definitional_macros(&mut fix.arena, &[def, goal]).unwrap();
        assert!(out.changed);
        assert!(!occurs_func(&fix.arena, out.assertions[0], f));
    }

    #[test]
    fn permuted_arguments_bind_in_argument_order_not_binder_order() {
        // `∀x y. f(y, x) = y` defines `f`'s FIRST argument as its value. If the
        // parameters were recorded in binder order, `f(a, b)` would rewrite to
        // `b` instead of `a` -- a wrong answer that no coverage or occurs check
        // can see, because both hold.
        let mut fix = Fix::new();
        let (x, xt) = fix.int_sym("x");
        let (y, yt) = fix.int_sym("y");
        let (_a, at) = fix.int_sym("a");
        let (_b, bt) = fix.int_sym("b");
        let f = fix.int_fn("f", 2);

        let fyx = fix.arena.apply(f, &[yt, xt]).unwrap();
        let eq = fix.arena.eq(fyx, yt).unwrap();
        let inner = fix.arena.forall(y, eq).unwrap();
        let def = fix.arena.forall(x, inner).unwrap();

        let fab = fix.arena.apply(f, &[at, bt]).unwrap();
        let zero = fix.arena.int_const(0);
        let goal = fix.arena.eq(fab, zero).unwrap();

        let out = inline_definitional_macros(&mut fix.arena, &[def, goal]).unwrap();
        assert!(out.changed);
        let expected = fix.arena.eq(at, zero).unwrap();
        assert_eq!(
            out.assertions[0], expected,
            "f(a, b) must become a, the actual matching the head's first argument"
        );
    }

    #[test]
    fn nested_definitions_expand_to_a_fixpoint() {
        // `g` is defined in terms of `f`. Inlining must leave neither behind.
        let mut fix = Fix::new();
        let (x, xt) = fix.int_sym("x");
        let (_a, at) = fix.int_sym("a");
        let f = fix.int_fn("f", 1);
        let g = fix.int_fn("g", 1);
        let one = fix.arena.int_const(1);

        let fx = fix.arena.apply(f, &[xt]).unwrap();
        let fbody = fix.arena.int_add(xt, one).unwrap();
        let df = {
            let e = fix.arena.eq(fx, fbody).unwrap();
            fix.arena.forall(x, e).unwrap()
        };
        let gx = fix.arena.apply(g, &[xt]).unwrap();
        let dg = {
            let e = fix.arena.eq(gx, fx).unwrap();
            fix.arena.forall(x, e).unwrap()
        };

        let ga = fix.arena.apply(g, &[at]).unwrap();
        let goal = fix.arena.eq(ga, one).unwrap();

        let out = inline_definitional_macros(&mut fix.arena, &[df, dg, goal]).unwrap();
        assert!(out.changed);
        assert_eq!(out.inlined, 2);
        assert_eq!(out.assertions.len(), 1);
        assert!(!occurs_func(&fix.arena, out.assertions[0], f));
        assert!(!occurs_func(&fix.arena, out.assertions[0], g));
    }

    #[test]
    fn a_query_with_no_definition_is_returned_untouched() {
        let mut fix = Fix::new();
        let (_a, at) = fix.int_sym("a");
        let one = fix.arena.int_const(1);
        let goal = fix.arena.eq(at, one).unwrap();

        let out = inline_definitional_macros(&mut fix.arena, &[goal]).unwrap();
        assert!(!out.changed);
        assert_eq!(out.assertions, vec![goal]);
    }

    #[test]
    fn inlining_reaches_inside_another_quantifier_body() {
        // The defining assertion is dropped, so an application of `f` left
        // inside some OTHER universal's body would become unconstrained -- that
        // is the unsound direction, and it is why the walk must descend through
        // binders rather than stopping at them.
        let mut fix = Fix::new();
        let (x, xt) = fix.int_sym("x");
        let (y, yt) = fix.int_sym("y");
        let f = fix.int_fn("f", 1);
        let one = fix.arena.int_const(1);

        let fx = fix.arena.apply(f, &[xt]).unwrap();
        let fbody = fix.arena.int_add(xt, one).unwrap();
        let def = {
            let e = fix.arena.eq(fx, fbody).unwrap();
            fix.arena.forall(x, e).unwrap()
        };

        // `∀y. g(f(y)) = 0` is deliberately NOT itself a definition: the head
        // `g(f(y))` has a non-variable argument, so `is_macro_head` refuses it,
        // and `0` is not a head either. An earlier draft of this fixture used
        // `∀y. f(y) = 0`, which IS a second definition of `f` -- the test then
        // passed through the duplicate-definition refusal and measured that
        // instead of what it is named for.
        let g = fix.int_fn("g", 1);
        let fy = fix.arena.apply(f, &[yt]).unwrap();
        let gfy = fix.arena.apply(g, &[fy]).unwrap();
        let zero = fix.arena.int_const(0);
        let inner = fix.arena.eq(gfy, zero).unwrap();
        let other = fix.arena.forall(y, inner).unwrap();

        let out = inline_definitional_macros(&mut fix.arena, &[def, other]).unwrap();
        assert!(out.changed);
        assert_eq!(out.assertions.len(), 1);
        assert!(
            !occurs_func(&fix.arena, out.assertions[0], f),
            "an application under another binder must be inlined too"
        );
    }
}
