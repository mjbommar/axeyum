//! Native datatype solving for free variables by eager tag/field expansion
//! (ADR-0022 step B).
//!
//! After read-over-construct simplification ([`simplify_datatypes`]), a query
//! may still mention **free datatype variables** under `is-c`/`select`. This
//! module decides such queries by eagerly expanding each datatype variable
//! `o : D` into
//!
//! - a **tag** bit-vector `tag_o` (which constructor `o` uses), constrained to
//!   the constructor range, and
//! - a **field variable** `f_{o,c,i}` for every constructor `c` and field `i`,
//!
//! then replacing `is-c(o)` with `tag_o == c` and `select_{c,i}(o)` with
//! `f_{o,c,i}`. Structural equality `o == o'` of two datatype variables reduces
//! to `tag_o == tag_o'` conjoined with field-wise equality (exact given the
//! default guards below). To keep the expansion faithful to the *total* `select`
//! convention ([`well_founded_default`]), each non-active field is pinned to its
//! sort's well-founded default by a guard `tag_o == c \/ f_{o,c,i} == default`,
//! so `select_{c,i}(o)` when `o`'s constructor is not `c` yields the same default
//! the evaluator does. The residual is datatype-free and goes to the normal
//! dispatcher.
//!
//! Soundness. The expansion is equisatisfiable with the input: from a model of
//! the input, set `tag_o` to `o`'s constructor and the field variables to `o`'s
//! fields (non-active fields to their default, satisfying the guards); from a
//! model of the expansion, project `o = c_{tag_o}(f_{o,c,i}...)` and the guards
//! make every `select` agree with the evaluator. So `unsat` transfers, and a
//! `sat` model is projected back to a `Value::Datatype` and **replayed against
//! the original assertions** with the ground evaluator before it is returned —
//! a projection bug surfaces as a replay error, never a wrong `sat`.
//!
//! Recursive datatypes are handled **as long as their datatype-typed fields are
//! never traversed** (no `select` into a datatype field) or compared (`==`):
//! such a field never affects satisfiability, so it gets no expansion variable
//! and is projected to its [`well_founded_default`]. This keeps the whole
//! reduction equisatisfiable (sound `sat` *and* `unsat`, no depth bound) — e.g.
//! `is-cons(l)`, `select head(l) == 5`, and the sound `unsat` of
//! `is-cons(l) ∧ is-nil(l)` all work on `IntList = nil | cons(head, tail)`.
//!
//! Outside this fragment — `select` *into* a datatype field (which traverses the
//! recursive structure and needs depth-bounded unfolding, the next unit), `==`
//! over a datatype that has datatype fields, array/UF fields, or `is`/`select`/`==`
//! over a non-variable datatype term — the function returns
//! [`SolverError::Unsupported`]; the bounded unfolding and a fuller native theory
//! (acyclicity + congruence) are future work.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use axeyum_ir::{
    ConstructorId, DatatypeId, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval,
    well_founded_default,
};
use axeyum_rewrite::{replace_subterms, simplify_datatypes};

use crate::auto::solve;
use crate::backend::{CheckResult, SolverConfig, SolverError};
use crate::model::Model;

/// Decides a query with free datatype variables by eager tag/field expansion.
///
/// `assertions` are simplified (read-over-construct folded) first; the residual
/// free-variable fragment is expanded to a datatype-free query, solved by the
/// dispatcher, and on `sat` projected back to datatype values and replayed.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for datatype content outside the
/// non-recursive scalar-field free-variable fragment, or a [`SolverError`] from
/// the rewrite, the dispatcher, or a failed `sat` replay.
pub fn check_with_datatype_native(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let simplified =
        simplify_datatypes(arena, assertions).map_err(|e| SolverError::Backend(e.to_string()))?;

    // Immutable scan: validate the fragment and collect the datatype variables
    // used, the `is`/`select` sites to rewrite, and per-datatype layout.
    let scan = scan_fragment(arena, &simplified)?;
    if scan.dt_symbols.is_empty() {
        // No datatype variables remain (read-over-construct sufficed).
        return solve(arena, &simplified, config);
    }

    // Mutable phase: declare tag/field symbols, build the replacement map and the
    // domain/guard constraints, then rewrite the assertions.
    let mut layout: BTreeMap<SymbolId, SymVars> = BTreeMap::new();
    let mut extra: Vec<TermId> = Vec::new();
    for (&sym, &dt) in &scan.dt_symbols {
        let vars = build_sym_vars(arena, sym, dt, &scan.layouts[&dt], &mut extra)?;
        layout.insert(sym, vars);
    }

    let mut replacements: HashMap<TermId, TermId> = HashMap::new();
    for site in &scan.tests {
        let vars = &layout[&site.symbol];
        let tag_const = arena
            .bv_const(vars.tag_width, site.ctor_index as u128)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        let tag_var = arena.var(vars.tag);
        let eq = arena
            .eq(tag_var, tag_const)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        replacements.insert(site.term, eq);
    }
    for site in &scan.selects {
        let vars = &layout[&site.symbol];
        // The scan rejects selects of datatype-typed fields, so this is `Some`.
        let Some(field) = vars.fields[site.ctor_index][site.field_index] else {
            return Err(SolverError::Backend(
                "scalar-field select site mapped to a datatype field".to_owned(),
            ));
        };
        replacements.insert(site.term, arena.var(field));
    }
    for site in &scan.eqs {
        let eq_term = build_dt_eq(arena, &layout[&site.left], &layout[&site.right])?;
        replacements.insert(site.term, eq_term);
    }

    let mut reduced = Vec::with_capacity(simplified.len() + extra.len());
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    for &assertion in &simplified {
        let rewritten = replace_subterms(arena, assertion, &replacements, &mut memo)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        reduced.push(rewritten);
    }
    reduced.extend(extra);

    let result = solve(arena, &reduced, config)?;
    let CheckResult::Sat(model) = result else {
        // `unsat`/`unknown` transfer: the expansion is equisatisfiable.
        return Ok(result);
    };

    project_and_replay(arena, &simplified, &scan, &layout, &model)
}

/// Per-symbol expansion variables.
struct SymVars {
    tag: SymbolId,
    tag_width: u32,
    /// `fields[constructor_index][field_index]` — the fresh field variable, or
    /// `None` for a datatype-typed field (not expanded in this slice; never
    /// traversed, so it is projected to a well-founded default).
    fields: Vec<Vec<Option<SymbolId>>>,
}

/// An `is-c(o)` rewrite site.
struct TestSite {
    term: TermId,
    symbol: SymbolId,
    ctor_index: usize,
}

/// A `select_{c,i}(o)` rewrite site.
struct SelectSite {
    term: TermId,
    symbol: SymbolId,
    ctor_index: usize,
    field_index: usize,
}

/// An `o == o'` rewrite site over two datatype variables.
struct EqSite {
    term: TermId,
    left: SymbolId,
    right: SymbolId,
}

/// Result of the immutable fragment scan.
struct Scan {
    dt_symbols: BTreeMap<SymbolId, DatatypeId>,
    /// Per datatype: its constructors with their field sorts (owned, so the
    /// mutable build phase need not re-borrow the arena).
    layouts: BTreeMap<DatatypeId, Vec<(ConstructorId, Vec<Sort>)>>,
    tests: Vec<TestSite>,
    selects: Vec<SelectSite>,
    eqs: Vec<EqSite>,
}

fn scan_fragment(arena: &TermArena, roots: &[TermId]) -> Result<Scan, SolverError> {
    let mut dt_symbols: BTreeMap<SymbolId, DatatypeId> = BTreeMap::new();
    let mut layouts: BTreeMap<DatatypeId, Vec<(ConstructorId, Vec<Sort>)>> = BTreeMap::new();
    let mut tests = Vec::new();
    let mut selects = Vec::new();
    let mut eqs = Vec::new();

    let mut seen = BTreeSet::new();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        let TermNode::App { op, args } = arena.node(term) else {
            continue;
        };
        let op = *op;
        let args = args.clone();
        match op {
            Op::DtConstruct { .. } => {
                return Err(unsupported(
                    "a datatype constructor survives read-over-construct elimination \
                     (only `is`/`select` over free datatype variables are supported)",
                ));
            }
            Op::DtTest(ctor) => {
                let sym = expect_dt_symbol(arena, args[0])?;
                let dt = arena.constructor_datatype(ctor);
                register_datatype(arena, dt, &mut layouts)?;
                dt_symbols.insert(sym, dt);
                tests.push(TestSite {
                    term,
                    symbol: sym,
                    ctor_index: ctor_position(arena, dt, ctor),
                });
            }
            Op::DtSelect { constructor, index } => {
                let sym = expect_dt_symbol(arena, args[0])?;
                let dt = arena.constructor_datatype(constructor);
                // Selecting a *datatype-typed* field traverses into the recursive
                // structure, which needs depth-bounded unfolding (the next unit);
                // selecting a scalar field is in this fragment.
                if matches!(
                    arena.constructor_fields(constructor)[index as usize].1,
                    Sort::Datatype(_)
                ) {
                    return Err(unsupported(
                        "select of a datatype-typed field traverses recursive structure; \
                         needs depth-bounded unfolding",
                    ));
                }
                register_datatype(arena, dt, &mut layouts)?;
                dt_symbols.insert(sym, dt);
                selects.push(SelectSite {
                    term,
                    symbol: sym,
                    ctor_index: ctor_position(arena, dt, constructor),
                    field_index: index as usize,
                });
            }
            Op::Eq if matches!(arena.sort_of(args[0]), Sort::Datatype(_)) => {
                // Structural equality of two datatype variables. Constructors on
                // either side are not handled in this slice (they should fold
                // first; otherwise Unsupported).
                let Sort::Datatype(dt) = arena.sort_of(args[0]) else {
                    unreachable!("matched datatype sort");
                };
                // Equality over a datatype with datatype-typed fields would have
                // to compare those (untraversed, defaulted) fields; that is only
                // exact once they are expanded (the next unit). Restrict equality
                // to fully-scalar datatypes.
                if dt_has_datatype_field(arena, dt) {
                    return Err(unsupported(
                        "equality over a datatype with datatype-typed fields needs the \
                         recursive field expansion (next unit)",
                    ));
                }
                let left = expect_dt_symbol(arena, args[0])?;
                let right = expect_dt_symbol(arena, args[1])?;
                register_datatype(arena, dt, &mut layouts)?;
                dt_symbols.insert(left, dt);
                dt_symbols.insert(right, dt);
                eqs.push(EqSite { term, left, right });
            }
            _ => {
                reject_stray_datatype_operands(arena, &args)?;
                stack.extend(args.iter().copied());
            }
        }
    }

    Ok(Scan {
        dt_symbols,
        layouts,
        tests,
        selects,
        eqs,
    })
}

/// Rejects a datatype-sorted operand of a non-datatype op (e.g. `ite` of a
/// datatype) that is neither a free variable nor a constructor — such terms
/// cannot be expanded by this fragment.
fn reject_stray_datatype_operands(arena: &TermArena, args: &[TermId]) -> Result<(), SolverError> {
    for &arg in args {
        if matches!(arena.sort_of(arg), Sort::Datatype(_))
            && !matches!(
                arena.node(arg),
                TermNode::App {
                    op: Op::DtConstruct { .. },
                    ..
                }
            )
            && !matches!(arena.node(arg), TermNode::Symbol(_))
        {
            return Err(unsupported(
                "a datatype-sorted term other than a free variable or constructor \
                 reaches a non-datatype operator",
            ));
        }
    }
    Ok(())
}

/// Requires `term` to be a datatype-sorted variable; returns its symbol.
fn expect_dt_symbol(arena: &TermArena, term: TermId) -> Result<SymbolId, SolverError> {
    match arena.node(term) {
        TermNode::Symbol(s) => Ok(*s),
        _ => Err(unsupported(
            "`is`/`select` over a non-variable datatype term (constructors should fold first)",
        )),
    }
}

/// Records `dt`'s constructor/field layout.
///
/// Scalar (`Bool`/`BitVec`) fields are expanded to field variables; datatype and
/// array fields are recorded too (kept in `field_sorts`) but get no expansion
/// variable — they are sound only as long as they are never traversed by a
/// `select` or compared by `==`, which the scan enforces, so they are projected
/// to a well-founded default. Other non-scalar fields (e.g. arrays) are rejected.
fn register_datatype(
    arena: &TermArena,
    dt: DatatypeId,
    layouts: &mut BTreeMap<DatatypeId, Vec<(ConstructorId, Vec<Sort>)>>,
) -> Result<(), SolverError> {
    if layouts.contains_key(&dt) {
        return Ok(());
    }
    // Insert a placeholder first so a recursive field (`Sort::Datatype(dt)`)
    // does not recurse forever through `register_datatype`.
    layouts.insert(dt, Vec::new());
    let mut ctors = Vec::new();
    for &ctor in arena.datatype_constructors(dt) {
        let mut field_sorts = Vec::new();
        for (_, sort) in arena.constructor_fields(ctor) {
            match sort {
                Sort::Bool | Sort::BitVec(_) => field_sorts.push(*sort),
                Sort::Datatype(inner) => {
                    register_datatype(arena, *inner, layouts)?;
                    field_sorts.push(*sort);
                }
                _ => {
                    return Err(unsupported(
                        "native datatype solving supports scalar and datatype fields; \
                         array/UF datatype fields are not yet supported",
                    ));
                }
            }
        }
        ctors.push((ctor, field_sorts));
    }
    layouts.insert(dt, ctors);
    Ok(())
}

/// Whether any constructor of `dt` has a datatype-typed field.
fn dt_has_datatype_field(arena: &TermArena, dt: DatatypeId) -> bool {
    arena.datatype_constructors(dt).iter().any(|&ctor| {
        arena
            .constructor_fields(ctor)
            .iter()
            .any(|(_, sort)| matches!(sort, Sort::Datatype(_)))
    })
}

fn ctor_position(arena: &TermArena, dt: DatatypeId, ctor: ConstructorId) -> usize {
    arena
        .datatype_constructors(dt)
        .iter()
        .position(|&c| c == ctor)
        .expect("constructor belongs to its datatype")
}

/// Bits needed to tag `count` constructors (at least 1).
fn tag_width_for(count: usize) -> u32 {
    if count <= 1 {
        1
    } else {
        let max = u32::try_from(count - 1).unwrap_or(u32::MAX);
        u32::BITS - max.leading_zeros()
    }
}

/// Declares the tag and field variables for one datatype symbol and emits the
/// domain and field-default guard constraints into `extra`.
fn build_sym_vars(
    arena: &mut TermArena,
    sym: SymbolId,
    _dt: DatatypeId,
    ctors: &[(ConstructorId, Vec<Sort>)],
    extra: &mut Vec<TermId>,
) -> Result<SymVars, SolverError> {
    let oidx = sym.index();
    let count = ctors.len();
    let tag_width = tag_width_for(count);

    let tag = arena
        .declare(&format!("!dt_tag_{oidx}"), Sort::BitVec(tag_width))
        .map_err(|e| SolverError::Backend(e.to_string()))?;
    let tag_var = arena.var(tag);

    // Domain: tag < count, when count is not the full 2^tag_width range.
    if (count as u128) < (1u128 << tag_width) {
        let bound = arena
            .bv_const(tag_width, count as u128)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        let lt = arena
            .bv_ult(tag_var, bound)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        extra.push(lt);
    }

    let mut fields = Vec::with_capacity(count);
    for (j, (_ctor, field_sorts)) in ctors.iter().enumerate() {
        let tag_eq_j = {
            let c = arena
                .bv_const(tag_width, j as u128)
                .map_err(|e| SolverError::Backend(e.to_string()))?;
            arena
                .eq(tag_var, c)
                .map_err(|e| SolverError::Backend(e.to_string()))?
        };
        let mut row = Vec::with_capacity(field_sorts.len());
        for (i, &fsort) in field_sorts.iter().enumerate() {
            // Datatype-typed fields are never traversed (the scan rejects such
            // `select`/`==`), so they get no variable and no guard — they are
            // projected to a well-founded default. Only scalar fields expand.
            if matches!(fsort, Sort::Datatype(_)) {
                row.push(None);
                continue;
            }
            let field = arena
                .declare(&format!("!dt_fld_{oidx}_{j}_{i}"), fsort)
                .map_err(|e| SolverError::Backend(e.to_string()))?;
            row.push(Some(field));

            // Guard: non-active fields take their well-founded default, matching
            // the total `select` convention so projection replays exactly.
            let default = well_founded_default(arena, fsort)
                .expect("scalar field sorts are inhabited");
            let default_term =
                value_to_term(arena, &default).map_err(|e| SolverError::Backend(e.to_string()))?;
            let field_var = arena.var(field);
            let field_eq_default = arena
                .eq(field_var, default_term)
                .map_err(|e| SolverError::Backend(e.to_string()))?;
            let guard = arena
                .or(tag_eq_j, field_eq_default)
                .map_err(|e| SolverError::Backend(e.to_string()))?;
            extra.push(guard);
        }
        fields.push(row);
    }

    Ok(SymVars {
        tag,
        tag_width,
        fields,
    })
}

/// Builds the reduced term for `o == o'` over two same-datatype variables:
/// `tag_l == tag_r` conjoined with field-wise equality across all constructors.
///
/// This is exact structural equality given the field-default guards: non-active
/// fields are pinned to the same default on both sides, so they compare equal
/// automatically, leaving the active constructor's fields to decide equality.
fn build_dt_eq(
    arena: &mut TermArena,
    left: &SymVars,
    right: &SymVars,
) -> Result<TermId, SolverError> {
    let lt = arena.var(left.tag);
    let rt = arena.var(right.tag);
    let mut conj = arena
        .eq(lt, rt)
        .map_err(|e| SolverError::Backend(e.to_string()))?;
    for (lrow, rrow) in left.fields.iter().zip(&right.fields) {
        for (lf, rf) in lrow.iter().zip(rrow) {
            // Equality is admitted only for fully-scalar datatypes, so every
            // field has a variable; a `None` (datatype field) cannot occur here.
            let (Some(lf), Some(rf)) = (lf, rf) else {
                continue;
            };
            let lfv = arena.var(*lf);
            let rfv = arena.var(*rf);
            let fe = arena
                .eq(lfv, rfv)
                .map_err(|e| SolverError::Backend(e.to_string()))?;
            conj = arena
                .and(conj, fe)
                .map_err(|e| SolverError::Backend(e.to_string()))?;
        }
    }
    Ok(conj)
}

/// Projects the expansion model back to datatype values and replays it against
/// the (simplified, equisatisfiable) assertions before returning `sat`.
fn project_and_replay(
    arena: &TermArena,
    assertions: &[TermId],
    scan: &Scan,
    layout: &BTreeMap<SymbolId, SymVars>,
    model: &Model,
) -> Result<CheckResult, SolverError> {
    let mut assignment = model.to_assignment();
    for (&sym, dt) in &scan.dt_symbols {
        let vars = &layout[&sym];
        let tag = match assignment.get(vars.tag) {
            Some(Value::Bv { value, .. }) => usize::try_from(value).unwrap_or(usize::MAX),
            _ => {
                return Err(SolverError::Backend(
                    "datatype expansion model lacks a tag value".to_owned(),
                ));
            }
        };
        let ctors = &scan.layouts[dt];
        if tag >= ctors.len() {
            return Err(SolverError::Backend(
                "datatype tag out of constructor range in expansion model".to_owned(),
            ));
        }
        let (ctor, field_sorts) = &ctors[tag];
        let mut field_vals = Vec::with_capacity(field_sorts.len());
        for (i, &fsort) in field_sorts.iter().enumerate() {
            let value = match vars.fields[tag][i] {
                // Scalar field: read its expansion variable.
                Some(field) => assignment.get(field).ok_or_else(|| {
                    SolverError::Backend(
                        "datatype expansion model lacks a field value".to_owned(),
                    )
                })?,
                // Datatype field (never traversed): the well-founded default.
                None => well_founded_default(arena, fsort).ok_or_else(|| {
                    SolverError::Backend(
                        "uninhabited datatype field has no default for projection".to_owned(),
                    )
                })?,
            };
            field_vals.push(value);
        }
        assignment.set(
            sym,
            Value::Datatype {
                datatype: *dt,
                constructor: *ctor,
                fields: field_vals,
            },
        );
    }

    for &assertion in assertions {
        match eval(arena, assertion, &assignment) {
            Ok(Value::Bool(true)) => {}
            Ok(other) => {
                return Err(SolverError::Backend(format!(
                    "datatype sat model replay failed: assertion #{} evaluated to {other}",
                    assertion.index()
                )));
            }
            Err(error) => {
                return Err(SolverError::Backend(format!(
                    "datatype sat model replay failed: assertion #{} failed evaluation: {error}",
                    assertion.index()
                )));
            }
        }
    }

    // Build a model over the original symbols, dropping the internal tag/field
    // variables introduced by the expansion.
    let mut out = Model::new();
    for (symbol, name, _sort) in arena.symbols() {
        if name.starts_with("!dt_") {
            continue;
        }
        if let Some(value) = assignment.get(symbol) {
            out.set(symbol, value);
        }
    }
    Ok(CheckResult::Sat(out))
}

fn value_to_term(arena: &mut TermArena, value: &Value) -> Result<TermId, axeyum_ir::IrError> {
    match value {
        Value::Bool(b) => Ok(arena.bool_const(*b)),
        Value::Bv { width, value } => arena.bv_const(*width, *value),
        _ => unreachable!("scalar field defaults are Bool/BitVec"),
    }
}

fn unsupported(what: &str) -> SolverError {
    SolverError::Unsupported(format!("{what} (ADR-0022)"))
}
