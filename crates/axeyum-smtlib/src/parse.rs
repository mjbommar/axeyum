//! SMT-LIB 2 script parser for the `QF_BV` benchmark slice.
//!
//! Scope (formats note): benchmarks-as-data — `set-logic`, `set-info`,
//! `declare-fun`/`declare-const` (0-ary), `define-fun` (0-ary, as aliases),
//! `assert`, `check-sat`, `exit`. Incremental scripting (`push`/`pop`) is
//! rejected with a clear error. Term conversion is iterative, so deep
//! benchmark terms cannot overflow the stack.

use std::collections::HashMap;

use axeyum_ir::{Sort, TermArena, TermId};

use crate::SmtError;
use crate::sexpr::{SExpr, read_all};

/// A parsed benchmark script.
#[derive(Debug, Default)]
#[non_exhaustive]
pub struct Script {
    /// Arena holding all parsed terms.
    pub arena: TermArena,
    /// Asserted formulas, in script order.
    pub assertions: Vec<TermId>,
    /// `set-logic` value, if present.
    pub logic: Option<String>,
    /// `(set-info :status ...)` value, if present (benchmark ground truth).
    pub status: Option<String>,
    /// Number of `check-sat` commands seen.
    pub check_sats: u32,
}

/// Parses an SMT-LIB script.
///
/// # Errors
///
/// [`SmtError::Syntax`] for malformed input, [`SmtError::Unsupported`] for
/// constructs outside the `QF_BV` benchmark slice, and sort errors surfaced
/// as [`SmtError::Ir`].
pub fn parse_script(input: &str) -> Result<Script, SmtError> {
    let exprs = read_all(input)?;
    let mut script = Script::default();
    let mut aliases: HashMap<String, TermId> = HashMap::new();
    let mut macros: HashMap<String, MacroDef<'_>> = HashMap::new();

    for command in &exprs {
        parse_command(&mut script, &mut aliases, &mut macros, command)?;
    }
    Ok(script)
}

fn parse_command<'a>(
    script: &mut Script,
    aliases: &mut HashMap<String, TermId>,
    macros: &mut HashMap<String, MacroDef<'a>>,
    command: &'a SExpr,
) -> Result<(), SmtError> {
    let items = command
        .list()
        .ok_or_else(|| SmtError::Syntax("top-level atom".to_owned()))?;
    let head = items
        .first()
        .and_then(SExpr::atom)
        .ok_or_else(|| SmtError::Syntax("empty command".to_owned()))?;
    match head {
        "set-logic" => {
            exact_len(items, 2, head)?;
            script.logic = items.get(1).and_then(SExpr::atom).map(str::to_owned);
        }
        "set-info" => {
            exact_len(items, 3, head)?;
            if items.get(1).and_then(SExpr::atom) == Some(":status") {
                script.status = items.get(2).and_then(SExpr::atom).map(str::to_owned);
            }
        }
        "set-option" => exact_len(items, 3, head)?,
        "get-model" | "exit" => exact_len(items, 1, head)?,
        "get-info" => exact_len(items, 2, head)?,
        "check-sat-assuming" => {
            return Err(SmtError::Unsupported("check-sat-assuming".to_owned()));
        }
        "check-sat" => {
            exact_len(items, 1, head)?;
            script.check_sats += 1;
        }
        "declare-fun" => parse_declare_fun(script, items)?,
        "declare-const" => parse_declare_const(script, items)?,
        "define-fun" => parse_define_fun(script, aliases, macros, items)?,
        "assert" => {
            exact_len(items, 2, head)?;
            let t = parse_term(&mut script.arena, sexpr_at(items, 1)?, aliases, macros)?;
            script.assertions.push(t);
        }
        "push" | "pop" => {
            return Err(SmtError::Unsupported(format!(
                "incremental command `{head}`"
            )));
        }
        other => return Err(SmtError::Unsupported(format!("command `{other}`"))),
    }
    Ok(())
}

fn parse_declare_fun(script: &mut Script, items: &[SExpr]) -> Result<(), SmtError> {
    exact_len(items, 4, "declare-fun")?;
    let name = atom_at(items, 1)?;
    let args = items
        .get(2)
        .and_then(SExpr::list)
        .ok_or_else(|| SmtError::Syntax("declare-fun args".to_owned()))?;
    if !args.is_empty() {
        return Err(SmtError::Unsupported(format!(
            "uninterpreted function `{name}` with arguments"
        )));
    }
    let sort = parse_sort(sexpr_at(items, 3)?)?;
    script.arena.declare(name, sort)?;
    Ok(())
}

fn parse_declare_const(script: &mut Script, items: &[SExpr]) -> Result<(), SmtError> {
    exact_len(items, 3, "declare-const")?;
    let name = atom_at(items, 1)?;
    let sort = parse_sort(sexpr_at(items, 2)?)?;
    script.arena.declare(name, sort)?;
    Ok(())
}

fn parse_define_fun<'a>(
    script: &mut Script,
    aliases: &mut HashMap<String, TermId>,
    macros: &mut HashMap<String, MacroDef<'a>>,
    items: &'a [SExpr],
) -> Result<(), SmtError> {
    exact_len(items, 5, "define-fun")?;
    let name = atom_at(items, 1)?;
    let args = items
        .get(2)
        .and_then(SExpr::list)
        .ok_or_else(|| SmtError::Syntax("define-fun args".to_owned()))?;
    let declared_sort = parse_sort(sexpr_at(items, 3)?)?;
    let body_expr = sexpr_at(items, 4)?;
    if args.is_empty() {
        parse_define_fun_alias(script, aliases, macros, name, declared_sort, body_expr)
    } else {
        macros.insert(
            name.to_owned(),
            MacroDef {
                params: parse_params(args)?,
                result_sort: declared_sort,
                body: body_expr,
            },
        );
        Ok(())
    }
}

fn parse_define_fun_alias(
    script: &mut Script,
    aliases: &mut HashMap<String, TermId>,
    macros: &HashMap<String, MacroDef<'_>>,
    name: &str,
    declared_sort: Sort,
    body_expr: &SExpr,
) -> Result<(), SmtError> {
    let body = parse_term(&mut script.arena, body_expr, aliases, macros)?;
    let body_sort = script.arena.sort_of(body);
    if body_sort != declared_sort {
        return Err(SmtError::Ir(axeyum_ir::IrError::SortsDiffer(
            declared_sort,
            body_sort,
        )));
    }
    aliases.insert(name.to_owned(), body);
    Ok(())
}

#[derive(Clone, Copy)]
struct Param<'a> {
    name: &'a str,
    sort: Sort,
}

struct MacroDef<'a> {
    params: Vec<Param<'a>>,
    result_sort: Sort,
    body: &'a SExpr,
}

fn parse_params(args: &[SExpr]) -> Result<Vec<Param<'_>>, SmtError> {
    let mut params = Vec::with_capacity(args.len());
    for arg in args {
        let pair = arg
            .list()
            .filter(|p| p.len() == 2)
            .ok_or_else(|| SmtError::Syntax("define-fun parameter".to_owned()))?;
        let name = pair[0]
            .atom()
            .ok_or_else(|| SmtError::Syntax("define-fun parameter name".to_owned()))?;
        if params.iter().any(|p: &Param<'_>| p.name == name) {
            return Err(SmtError::Syntax(format!(
                "duplicate define-fun parameter `{name}`"
            )));
        }
        params.push(Param {
            name,
            sort: parse_sort(&pair[1])?,
        });
    }
    Ok(params)
}

fn exact_len(items: &[SExpr], expected: usize, head: &str) -> Result<(), SmtError> {
    if items.len() == expected {
        Ok(())
    } else {
        Err(SmtError::Syntax(format!(
            "`{head}` expects {} arguments, got {}",
            expected.saturating_sub(1),
            items.len().saturating_sub(1)
        )))
    }
}

fn atom_at(items: &[SExpr], i: usize) -> Result<&str, SmtError> {
    items
        .get(i)
        .and_then(SExpr::atom)
        .ok_or_else(|| SmtError::Syntax(format!("expected atom at position {i}")))
}

fn sexpr_at(items: &[SExpr], i: usize) -> Result<&SExpr, SmtError> {
    items
        .get(i)
        .ok_or_else(|| SmtError::Syntax(format!("expected argument at position {i}")))
}

fn parse_sort(e: &SExpr) -> Result<Sort, SmtError> {
    match e {
        SExpr::Atom(a) if a == "Bool" => Ok(Sort::Bool),
        SExpr::List(items) => {
            if items.len() == 3
                && items[0].atom() == Some("_")
                && items[1].atom() == Some("BitVec")
                && let Some(w) = items[2].atom().and_then(|s| s.parse::<u32>().ok())
            {
                return Ok(Sort::BitVec(w));
            }
            Err(SmtError::Unsupported(format!("sort {e:?}")))
        }
        SExpr::Atom(a) => Err(SmtError::Unsupported(format!("sort `{a}`"))),
    }
}

/// One frame of the iterative term converter.
enum Frame<'a> {
    /// Evaluate this expression (pushing children first when needed).
    Eval(&'a SExpr),
    /// Pop `argc` results and apply the operator list.
    Apply { items: &'a [SExpr], argc: usize },
    /// Pop `argc` results and expand a parameterized `define-fun` body.
    ApplyMacro { name: &'a str, argc: usize },
    /// Check the sort of the most recent result.
    CheckSort { expected: Sort, context: &'a str },
    /// Pop one binding scope after a `let` body finishes.
    PopScope,
    /// Pop `count` evaluated binding values, bind them, then queue the body.
    BindLet {
        names: Vec<&'a str>,
        body: &'a SExpr,
    },
}

fn parse_term<'a>(
    arena: &mut TermArena,
    root: &'a SExpr,
    aliases: &HashMap<String, TermId>,
    macros: &HashMap<String, MacroDef<'a>>,
) -> Result<TermId, SmtError> {
    let mut frames: Vec<Frame> = vec![Frame::Eval(root)];
    let mut results: Vec<TermId> = Vec::new();
    let mut scopes: Vec<HashMap<&'a str, TermId>> = Vec::new();

    while let Some(frame) = frames.pop() {
        match frame {
            Frame::Eval(e) => queue_eval(
                arena,
                e,
                aliases,
                macros,
                &scopes,
                &mut frames,
                &mut results,
            )?,
            Frame::Apply { items, argc } => {
                let args = results.split_off(results.len() - argc);
                results.push(apply_op(arena, items, &args)?);
            }
            Frame::ApplyMacro { name, argc } => {
                queue_macro_expansion(
                    arena,
                    macros,
                    &mut scopes,
                    &mut frames,
                    &mut results,
                    name,
                    argc,
                )?;
            }
            Frame::CheckSort { expected, context } => {
                check_recent_sort(arena, &results, expected, context)?;
            }
            Frame::BindLet { names, body } => {
                bind_let_scope(&mut scopes, &mut results, names);
                frames.push(Frame::PopScope);
                frames.push(Frame::Eval(body));
            }
            Frame::PopScope => {
                scopes.pop();
            }
        }
    }
    if results.len() == 1 {
        Ok(results.pop().expect("one result"))
    } else {
        Err(SmtError::Syntax(format!(
            "term conversion produced {} results",
            results.len()
        )))
    }
}

fn queue_eval<'a>(
    arena: &mut TermArena,
    expr: &'a SExpr,
    aliases: &HashMap<String, TermId>,
    macros: &HashMap<String, MacroDef<'a>>,
    scopes: &[HashMap<&'a str, TermId>],
    frames: &mut Vec<Frame<'a>>,
    results: &mut Vec<TermId>,
) -> Result<(), SmtError> {
    match expr {
        SExpr::Atom(a) => results.push(parse_atom(arena, a, aliases, scopes)?),
        SExpr::List(items) => queue_list_eval(arena, items, macros, frames, results)?,
    }
    Ok(())
}

fn queue_list_eval<'a>(
    arena: &mut TermArena,
    items: &'a [SExpr],
    macros: &HashMap<String, MacroDef<'a>>,
    frames: &mut Vec<Frame<'a>>,
    results: &mut Vec<TermId>,
) -> Result<(), SmtError> {
    let head = items
        .first()
        .ok_or_else(|| SmtError::Syntax("empty application".to_owned()))?;
    if head.atom() == Some("_") {
        results.push(parse_indexed_constant(arena, items)?);
    } else if head.atom() == Some("let") {
        queue_let(items, frames)?;
    } else if let Some(name) = head.atom()
        && macros.contains_key(name)
    {
        queue_children(
            items,
            frames,
            Frame::ApplyMacro {
                name,
                argc: items.len() - 1,
            },
        );
    } else {
        queue_children(
            items,
            frames,
            Frame::Apply {
                items,
                argc: items.len() - 1,
            },
        );
    }
    Ok(())
}

fn queue_children<'a>(items: &'a [SExpr], frames: &mut Vec<Frame<'a>>, apply: Frame<'a>) {
    frames.push(apply);
    for child in items[1..].iter().rev() {
        frames.push(Frame::Eval(child));
    }
}

fn queue_let<'a>(items: &'a [SExpr], frames: &mut Vec<Frame<'a>>) -> Result<(), SmtError> {
    exact_len(items, 3, "let")?;
    let bindings = items
        .get(1)
        .and_then(SExpr::list)
        .ok_or_else(|| SmtError::Syntax("let bindings".to_owned()))?;
    let body = sexpr_at(items, 2)?;
    let names = parse_let_names(bindings)?;
    frames.push(Frame::BindLet { names, body });
    for b in bindings.iter().rev() {
        frames.push(Frame::Eval(&b.list().expect("checked")[1]));
    }
    Ok(())
}

fn parse_let_names(bindings: &[SExpr]) -> Result<Vec<&str>, SmtError> {
    let mut names = Vec::with_capacity(bindings.len());
    for binding in bindings {
        let pair = binding
            .list()
            .filter(|p| p.len() == 2)
            .ok_or_else(|| SmtError::Syntax("let binding pair".to_owned()))?;
        names.push(
            pair[0]
                .atom()
                .ok_or_else(|| SmtError::Syntax("let name".to_owned()))?,
        );
    }
    for (i, name) in names.iter().enumerate() {
        if names[..i].contains(name) {
            return Err(SmtError::Syntax(format!("duplicate let binding `{name}`")));
        }
    }
    Ok(names)
}

fn queue_macro_expansion<'a>(
    arena: &TermArena,
    macros: &HashMap<String, MacroDef<'a>>,
    scopes: &mut Vec<HashMap<&'a str, TermId>>,
    frames: &mut Vec<Frame<'a>>,
    results: &mut Vec<TermId>,
    name: &'a str,
    arity: usize,
) -> Result<(), SmtError> {
    let actuals = results.split_off(results.len() - arity);
    let def = macros
        .get(name)
        .ok_or_else(|| SmtError::Unsupported(format!("operator `{name}`")))?;
    if actuals.len() != def.params.len() {
        return Err(SmtError::Syntax(format!(
            "`{name}` expects {} arguments, got {}",
            def.params.len(),
            actuals.len()
        )));
    }
    let mut scope = HashMap::new();
    for (param, arg) in def.params.iter().zip(actuals) {
        let actual = arena.sort_of(arg);
        if actual != param.sort {
            return Err(SmtError::Ir(axeyum_ir::IrError::SortsDiffer(
                param.sort, actual,
            )));
        }
        scope.insert(param.name, arg);
    }
    scopes.push(scope);
    frames.push(Frame::PopScope);
    frames.push(Frame::CheckSort {
        expected: def.result_sort,
        context: name,
    });
    frames.push(Frame::Eval(def.body));
    Ok(())
}

fn check_recent_sort(
    arena: &TermArena,
    results: &[TermId],
    expected: Sort,
    context: &str,
) -> Result<(), SmtError> {
    let Some(&term) = results.last() else {
        return Err(SmtError::Syntax(format!(
            "`{context}` body produced no result"
        )));
    };
    let actual = arena.sort_of(term);
    if actual != expected {
        return Err(SmtError::Ir(axeyum_ir::IrError::SortsDiffer(
            expected, actual,
        )));
    }
    Ok(())
}

fn bind_let_scope<'a>(
    scopes: &mut Vec<HashMap<&'a str, TermId>>,
    results: &mut Vec<TermId>,
    names: Vec<&'a str>,
) {
    let values = results.split_off(results.len() - names.len());
    let mut scope = HashMap::new();
    for (name, value) in names.into_iter().zip(values) {
        scope.insert(name, value);
    }
    scopes.push(scope);
}

fn parse_atom(
    arena: &mut TermArena,
    a: &str,
    aliases: &HashMap<String, TermId>,
    scopes: &[HashMap<&str, TermId>],
) -> Result<TermId, SmtError> {
    for scope in scopes.iter().rev() {
        if let Some(&t) = scope.get(a) {
            return Ok(t);
        }
    }
    match a {
        "true" => return Ok(arena.bool_const(true)),
        "false" => return Ok(arena.bool_const(false)),
        _ => {}
    }
    if let Some(hex) = a.strip_prefix("#x") {
        let value = u128::from_str_radix(hex, 16)
            .map_err(|_| SmtError::Syntax(format!("bad hex literal `{a}`")))?;
        return Ok(arena.bv_const(
            4 * u32::try_from(hex.len())
                .map_err(|_| SmtError::Syntax("literal too wide".to_owned()))?,
            value,
        )?);
    }
    if let Some(bin) = a.strip_prefix("#b") {
        let value = u128::from_str_radix(bin, 2)
            .map_err(|_| SmtError::Syntax(format!("bad binary literal `{a}`")))?;
        return Ok(arena.bv_const(
            u32::try_from(bin.len())
                .map_err(|_| SmtError::Syntax("literal too wide".to_owned()))?,
            value,
        )?);
    }
    if let Some(&t) = aliases.get(a) {
        return Ok(t);
    }
    if let Some(sym) = arena.find_symbol(a) {
        return Ok(arena.var(sym));
    }
    Err(SmtError::Unsupported(format!("unknown identifier `{a}`")))
}

fn parse_indexed_constant(arena: &mut TermArena, items: &[SExpr]) -> Result<TermId, SmtError> {
    if items.len() == 3
        && let Some(name) = items[1].atom()
        && let Some(num) = name.strip_prefix("bv")
        && let (Ok(value), Some(Ok(width))) =
            (num.parse::<u128>(), items[2].atom().map(str::parse::<u32>))
    {
        return Ok(arena.bv_const(width, value)?);
    }
    Err(SmtError::Unsupported(format!("indexed term {items:?}")))
}

/// Applies an operator list head to evaluated arguments.
// Flat dispatch over the operator vocabulary; length is inherent.
#[allow(clippy::too_many_lines)]
fn apply_op(arena: &mut TermArena, items: &[SExpr], args: &[TermId]) -> Result<TermId, SmtError> {
    // Parameterized head: ((_ extract h l) x) etc.
    if let Some(head_items) = items[0].list() {
        return apply_parameterized(arena, head_items, args);
    }
    let op = items[0].atom().expect("list head checked");
    let need = |n: usize| -> Result<(), SmtError> {
        if args.len() == n {
            Ok(())
        } else {
            Err(SmtError::Syntax(format!(
                "`{op}` expects {n} arguments, got {}",
                args.len()
            )))
        }
    };
    let fold = |arena: &mut TermArena,
                f: fn(&mut TermArena, TermId, TermId) -> Result<TermId, axeyum_ir::IrError>|
     -> Result<TermId, SmtError> {
        if args.len() < 2 {
            return Err(SmtError::Syntax(format!("`{op}` expects >= 2 arguments")));
        }
        let mut acc = args[0];
        for &next in &args[1..] {
            acc = f(arena, acc, next)?;
        }
        Ok(acc)
    };
    Ok(match op {
        "not" => {
            need(1)?;
            arena.not(args[0])?
        }
        "and" => fold(arena, TermArena::and)?,
        "or" => fold(arena, TermArena::or)?,
        "xor" => fold(arena, TermArena::xor)?,
        "=>" => {
            // Right-associative.
            if args.len() < 2 {
                return Err(SmtError::Syntax("`=>` expects >= 2 arguments".to_owned()));
            }
            let mut acc = *args.last().expect("nonempty");
            for &prev in args[..args.len() - 1].iter().rev() {
                acc = arena.implies(prev, acc)?;
            }
            acc
        }
        "=" => {
            // n-ary chaining: pairwise equalities conjoined.
            if args.len() < 2 {
                return Err(SmtError::Syntax("`=` expects >= 2 arguments".to_owned()));
            }
            let mut acc = arena.eq(args[0], args[1])?;
            for pair in args.windows(2).skip(1) {
                let e = arena.eq(pair[0], pair[1])?;
                acc = arena.and(acc, e)?;
            }
            acc
        }
        "distinct" => {
            if args.len() < 2 {
                return Err(SmtError::Syntax(
                    "`distinct` expects >= 2 arguments".to_owned(),
                ));
            }
            let mut acc = None;
            for i in 0..args.len() {
                for j in i + 1..args.len() {
                    let e = arena.eq(args[i], args[j])?;
                    let ne = arena.not(e)?;
                    acc = Some(match acc {
                        Some(prev) => arena.and(prev, ne)?,
                        None => ne,
                    });
                }
            }
            acc.expect("args length checked")
        }
        "ite" => {
            need(3)?;
            arena.ite(args[0], args[1], args[2])?
        }
        "bvnot" => {
            need(1)?;
            arena.bv_not(args[0])?
        }
        "bvneg" => {
            need(1)?;
            arena.bv_neg(args[0])?
        }
        "bvand" => fold(arena, TermArena::bv_and)?,
        "bvor" => fold(arena, TermArena::bv_or)?,
        "bvxor" => fold(arena, TermArena::bv_xor)?,
        "bvadd" => fold(arena, TermArena::bv_add)?,
        "bvmul" => fold(arena, TermArena::bv_mul)?,
        "concat" => fold(arena, TermArena::concat)?,
        "bvsub" => {
            need(2)?;
            arena.bv_sub(args[0], args[1])?
        }
        "bvnand" => bin(arena, TermArena::bv_nand, args, op)?,
        "bvnor" => bin(arena, TermArena::bv_nor, args, op)?,
        "bvxnor" => bin(arena, TermArena::bv_xnor, args, op)?,
        "bvudiv" => bin(arena, TermArena::bv_udiv, args, op)?,
        "bvurem" => bin(arena, TermArena::bv_urem, args, op)?,
        "bvsdiv" => bin(arena, TermArena::bv_sdiv, args, op)?,
        "bvsrem" => bin(arena, TermArena::bv_srem, args, op)?,
        "bvsmod" => bin(arena, TermArena::bv_smod, args, op)?,
        "bvshl" => bin(arena, TermArena::bv_shl, args, op)?,
        "bvlshr" => bin(arena, TermArena::bv_lshr, args, op)?,
        "bvashr" => bin(arena, TermArena::bv_ashr, args, op)?,
        "bvult" => bin(arena, TermArena::bv_ult, args, op)?,
        "bvule" => bin(arena, TermArena::bv_ule, args, op)?,
        "bvugt" => bin(arena, TermArena::bv_ugt, args, op)?,
        "bvuge" => bin(arena, TermArena::bv_uge, args, op)?,
        "bvslt" => bin(arena, TermArena::bv_slt, args, op)?,
        "bvsle" => bin(arena, TermArena::bv_sle, args, op)?,
        "bvsgt" => bin(arena, TermArena::bv_sgt, args, op)?,
        "bvsge" => bin(arena, TermArena::bv_sge, args, op)?,
        "bvcomp" => bin(arena, TermArena::bv_comp, args, op)?,
        other => return Err(SmtError::Unsupported(format!("operator `{other}`"))),
    })
}

fn bin(
    arena: &mut TermArena,
    f: fn(&mut TermArena, TermId, TermId) -> Result<TermId, axeyum_ir::IrError>,
    args: &[TermId],
    op: &str,
) -> Result<TermId, SmtError> {
    if args.len() != 2 {
        return Err(SmtError::Syntax(format!(
            "`{op}` expects 2 arguments, got {}",
            args.len()
        )));
    }
    Ok(f(arena, args[0], args[1])?)
}

fn apply_parameterized(
    arena: &mut TermArena,
    head: &[SExpr],
    args: &[TermId],
) -> Result<TermId, SmtError> {
    if head.first().and_then(SExpr::atom) != Some("_") || args.len() != 1 {
        return Err(SmtError::Unsupported(format!("application head {head:?}")));
    }
    let name = head
        .get(1)
        .and_then(SExpr::atom)
        .ok_or_else(|| SmtError::Syntax("indexed operator name".to_owned()))?;
    let expect_head_len = |n: usize| -> Result<(), SmtError> {
        if head.len() == n {
            Ok(())
        } else {
            Err(SmtError::Syntax(format!(
                "`{name}` expects {} indices, got {}",
                n.saturating_sub(2),
                head.len().saturating_sub(2)
            )))
        }
    };
    let index = |i: usize| -> Result<u32, SmtError> {
        head.get(i)
            .and_then(SExpr::atom)
            .and_then(|s| s.parse::<u32>().ok())
            .ok_or_else(|| SmtError::Syntax(format!("`{name}` index {i}")))
    };
    Ok(match name {
        "extract" => {
            expect_head_len(4)?;
            arena.extract(index(2)?, index(3)?, args[0])?
        }
        "zero_extend" => {
            expect_head_len(3)?;
            arena.zero_ext(index(2)?, args[0])?
        }
        "sign_extend" => {
            expect_head_len(3)?;
            arena.sign_ext(index(2)?, args[0])?
        }
        "rotate_left" => {
            expect_head_len(3)?;
            arena.rotate_left(index(2)?, args[0])?
        }
        "rotate_right" => {
            expect_head_len(3)?;
            arena.rotate_right(index(2)?, args[0])?
        }
        "repeat" => {
            expect_head_len(3)?;
            let n = index(2)?;
            if n == 0 {
                return Err(SmtError::Syntax("`repeat` index must be >= 1".to_owned()));
            }
            let mut acc = args[0];
            for _ in 1..n {
                acc = arena.concat(acc, args[0])?;
            }
            acc
        }
        other => return Err(SmtError::Unsupported(format!("indexed operator `{other}`"))),
    })
}
