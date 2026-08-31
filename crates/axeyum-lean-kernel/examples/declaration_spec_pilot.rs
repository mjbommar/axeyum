//! L3 phase D1 pilot (ADR-0965): interpret a declarative declaration-spec
//! JSON file and admit its declarations into the kernel via a small generic
//! expression-DSL interpreter, then compare the result against the
//! hand-written `crates/axeyum-lean-kernel/src/nat_prelude/squarefree.rs`
//! declarations it describes.
//!
//! Two modes:
//!
//! - default: build the hand-written Nat prelude (which already contains
//!   `Nat.squarefreeAux`/`Squarefree`), interpret
//!   `artifacts/declaration-spec/nat-squarefree.json` to build the SAME two
//!   declarations under shadow names in the SAME kernel instance, and
//!   compare. This kernel hash-conses expressions (`Kernel::intern_expr`),
//!   so two structurally identical terms built by two different code paths
//!   intern to the literal same `ExprId` -- that identity check, plus a
//!   portable SHA-256 digest of each declaration's rendered type/value, is
//!   the "identical declaration ... type/value digests" exit criterion.
//!   Also demonstrates that attempting to declare under the REAL, already-taken
//!   name is refused by the kernel's own admission gate (a second, in-kernel
//!   layer beneath the Python pre-construction guards).
//! - `--dump-names`: build the Int prelude (a superset of the Nat prelude
//!   that also declares `Nat.inverseIndex` from `int_prelude/wilson.rs`) and
//!   print every declared name, one per line -- the snapshot
//!   `scripts/gen-declaration-spec.py`'s cross-prelude duplicate guard reads.
//!
//! Nothing here is proof content: both declarations are pure `Definition`s
//! with no proof body, so the kernel's admission gate is the only place
//! correctness (well-typedness) is decided, exactly as for the hand-written
//! version. See ADR-0965 for the full TCB argument.

use std::collections::HashMap;
use std::path::PathBuf;
use std::process::ExitCode;

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, KernelError, NameId, NatDev, NatOps, NatPrelude,
    ReducibilityHint, build_int_prelude, build_nat_prelude,
};
use serde_json::Value;
use sha2::{Digest, Sha256};

include!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../artifacts/declaration-spec/generated/nat_squarefree_names.rs"
));

// ---------------------------------------------------------------------------
// Expression DSL
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
enum Node {
    NatTy,
    BoolTy,
    Arrow(Box<Node>, Box<Node>),
    Lam {
        param: String,
        domain: Box<Node>,
        body: Box<Node>,
    },
    Var(String),
    Zero,
    Num(u32),
    Succ(Box<Node>),
    Mul(Box<Node>, Box<Node>),
    Mod(Box<Node>, Box<Node>),
    Beq(Box<Node>, Box<Node>),
    BoolTrue,
    BoolFalse,
    BoolIte {
        cond: Box<Node>,
        then_branch: Box<Node>,
        else_branch: Box<Node>,
    },
    Apply {
        func: Box<Node>,
        args: Vec<Node>,
    },
    ConstRef(String),
    NatRec {
        motive_codomain: Box<Node>,
        base: Box<Node>,
        step: Box<Node>,
        target: Box<Node>,
    },
}

fn parse_node(v: &Value) -> Node {
    let op = v["op"]
        .as_str()
        .unwrap_or_else(|| panic!("DSL node missing 'op': {v}"));
    match op {
        "nat_ty" => Node::NatTy,
        "bool_ty" => Node::BoolTy,
        "arrow" => Node::Arrow(
            Box::new(parse_node(&v["dom"])),
            Box::new(parse_node(&v["cod"])),
        ),
        "lam" => Node::Lam {
            param: v["param"].as_str().expect("lam.param").to_string(),
            domain: Box::new(parse_node(&v["domain"])),
            body: Box::new(parse_node(&v["body"])),
        },
        "var" => Node::Var(v["name"].as_str().expect("var.name").to_string()),
        "zero" => Node::Zero,
        "num" => Node::Num(
            u32::try_from(v["value"].as_u64().expect("num.value")).expect("num.value fits u32"),
        ),
        "succ" => Node::Succ(Box::new(parse_node(&v["arg"]))),
        "mul" => Node::Mul(
            Box::new(parse_node(&v["lhs"])),
            Box::new(parse_node(&v["rhs"])),
        ),
        "mod" => Node::Mod(
            Box::new(parse_node(&v["dividend"])),
            Box::new(parse_node(&v["divisor"])),
        ),
        "beq" => Node::Beq(
            Box::new(parse_node(&v["lhs"])),
            Box::new(parse_node(&v["rhs"])),
        ),
        "bool_true" => Node::BoolTrue,
        "bool_false" => Node::BoolFalse,
        "bool_ite" => Node::BoolIte {
            cond: Box::new(parse_node(&v["cond"])),
            then_branch: Box::new(parse_node(&v["then"])),
            else_branch: Box::new(parse_node(&v["else"])),
        },
        "apply" => Node::Apply {
            func: Box::new(parse_node(&v["func"])),
            args: v["args"]
                .as_array()
                .expect("apply.args")
                .iter()
                .map(parse_node)
                .collect(),
        },
        "const_ref" => Node::ConstRef(v["name"].as_str().expect("const_ref.name").to_string()),
        "nat_rec" => Node::NatRec {
            motive_codomain: Box::new(parse_node(&v["motive_codomain"])),
            base: Box::new(parse_node(&v["base"])),
            step: Box::new(parse_node(&v["step"])),
            target: Box::new(parse_node(&v["target"])),
        },
        other => panic!("unsupported declaration-spec DSL op: {other}"),
    }
}

/// `if condition then on_true else on_false` at `Bool` -- mirrors
/// `nat_prelude/squarefree.rs`'s private `bool_select_bool` exactly (same
/// construction: a `Bool.rec` applied at a `Bool`-valued motive). Duplicated
/// here rather than imported because it is `pub(super)`-scoped to
/// `nat_prelude`; this is a builder PRIMITIVE, not a proof, so the
/// duplication carries no soundness risk (a divergence here would produce a
/// kernel rejection or a digest mismatch, not a wrong theorem).
fn bool_select_bool(
    d: &mut NatDev<'_>,
    condition: ExprId,
    on_true: ExprId,
    on_false: ExprId,
) -> ExprId {
    let bool_ty = d.bool_ty();
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, bool_ty, bool_ty, BinderInfo::Default);
    let one = d.level_one();
    let bool_rec = d.prelude().logic.bool_rec;
    let rec = d.kernel().const_(bool_rec, vec![one]);
    d.apply(rec, &[motive, on_false, on_true, condition])
}

#[allow(clippy::many_single_char_names)]
fn eval(
    node: &Node,
    d: &mut NatDev<'_>,
    env: &HashMap<String, ExprId>,
    consts: &HashMap<String, NameId>,
) -> ExprId {
    match node {
        Node::NatTy => d.nat_ty(),
        Node::BoolTy => d.bool_ty(),
        Node::Arrow(dom, cod) => {
            let a = eval(dom, d, env, consts);
            let b = eval(cod, d, env, consts);
            d.arrow(a, b)
        }
        Node::Lam {
            param,
            domain,
            body,
        } => {
            let ty = eval(domain, d, env, consts);
            let fv = d.fresh_fvar();
            let fv_expr = d.kernel().fvar(fv);
            let mut env2 = env.clone();
            env2.insert(param.clone(), fv_expr);
            let body_expr = eval(body, d, &env2, consts);
            d.lam_fv(fv, ty, body_expr)
        }
        Node::Var(name) => *env
            .get(name)
            .unwrap_or_else(|| panic!("unbound DSL variable '{name}'")),
        Node::Zero => d.zero(),
        Node::Num(n) => d.num(*n),
        Node::Succ(a) => {
            let x = eval(a, d, env, consts);
            d.succ(x)
        }
        Node::Mul(a, b) => {
            let x = eval(a, d, env, consts);
            let y = eval(b, d, env, consts);
            d.mul(x, y)
        }
        Node::Mod(a, b) => {
            let x = eval(a, d, env, consts);
            let y = eval(b, d, env, consts);
            d.modulo(x, y)
        }
        Node::Beq(a, b) => {
            let x = eval(a, d, env, consts);
            let y = eval(b, d, env, consts);
            d.beq(x, y)
        }
        Node::BoolTrue => d.bool_true(),
        Node::BoolFalse => d.bool_false(),
        Node::BoolIte {
            cond,
            then_branch,
            else_branch,
        } => {
            let c = eval(cond, d, env, consts);
            let t = eval(then_branch, d, env, consts);
            let e = eval(else_branch, d, env, consts);
            bool_select_bool(d, c, t, e)
        }
        Node::Apply { func, args } => {
            let f = eval(func, d, env, consts);
            let a: Vec<ExprId> = args.iter().map(|x| eval(x, d, env, consts)).collect();
            d.apply(f, &a)
        }
        Node::ConstRef(name) => {
            let n = *consts.get(name).unwrap_or_else(|| {
                panic!("unresolved const_ref '{name}' -- not yet declared in this spec")
            });
            d.kernel().const_(n, vec![])
        }
        Node::NatRec {
            motive_codomain,
            base,
            step,
            target,
        } => {
            let codomain_ty = eval(motive_codomain, d, env, consts);
            let nat = d.nat_ty();
            let anon = d.anon_name();
            let motive = d.kernel().lam(anon, nat, codomain_ty, BinderInfo::Default);
            let base_e = eval(base, d, env, consts);
            let step_e = eval(step, d, env, consts);
            let target_e = eval(target, d, env, consts);
            let one = d.level_one();
            let rec_name = d.prelude().rec;
            let rec = d.kernel().const_(rec_name, vec![one]);
            d.apply(rec, &[motive, base_e, step_e, target_e])
        }
    }
}

// ---------------------------------------------------------------------------
// Spec loading + interpretation
// ---------------------------------------------------------------------------

fn spec_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../artifacts/declaration-spec/nat-squarefree.json")
}

fn parse_reducibility_hint(s: &str) -> ReducibilityHint {
    if s == "Opaque" {
        return ReducibilityHint::Opaque;
    }
    if s == "Abbrev" {
        return ReducibilityHint::Abbrev;
    }
    let inner = s
        .strip_prefix("Regular(")
        .and_then(|s| s.strip_suffix(')'))
        .unwrap_or_else(|| panic!("bad reducibility_hint: {s}"));
    ReducibilityHint::Regular(inner.parse().expect("Regular(u16)"))
}

/// Interpret every declaration in the spec, admitting each under a shadow
/// name (`<local_name>SpecGen` in the same namespace) so it coexists with
/// the hand-written declarations already in `kernel`. Returns the shadow
/// `NameId` for each spec-local declaration, in spec order.
fn interpret_spec(d: &mut NatDev<'_>, spec: &Value) -> Vec<(String, NameId)> {
    let decls = spec["declarations"].as_array().expect("declarations array");
    let mut consts: HashMap<String, NameId> = HashMap::new();
    let mut order: Vec<(String, NameId)> = Vec::new();

    for decl in decls {
        let local_name = decl["local_name"].as_str().expect("local_name").to_string();
        let namespace = decl["namespace"].as_str().expect("namespace");
        let shadow_local = format!("{local_name}SpecGen");
        let parent = if namespace == "Nat" {
            d.prelude().logic.nat
        } else if namespace.is_empty() {
            d.kernel().anon()
        } else {
            panic!(
                "declaration_spec_pilot only supports 'Nat' and root namespaces, got {namespace:?}"
            );
        };
        let shadow_name = d.kernel().name_str(parent, shadow_local.clone());

        let env = HashMap::new();
        let ty_node = parse_node(&decl["type"]);
        let value_node = parse_node(&decl["value"]);
        let ty = eval(&ty_node, d, &env, &consts);
        let value = eval(&value_node, d, &env, &consts);
        let hint =
            parse_reducibility_hint(decl["reducibility_hint"].as_str().unwrap_or("Regular(0)"));

        d.kernel()
            .add_declaration(Declaration::Definition {
                name: shadow_name,
                uparams: vec![],
                ty,
                value,
                hint,
            })
            .unwrap_or_else(|e| {
                panic!("generated declaration '{shadow_local}' rejected by kernel: {e:?}")
            });

        consts.insert(local_name.clone(), shadow_name);
        order.push((local_name, shadow_name));
    }
    order
}

fn decl_ty_value(kernel: &mut Kernel, name: NameId) -> (ExprId, ExprId) {
    match kernel.environment().get(name) {
        Some(Declaration::Definition { ty, value, .. }) => (*ty, *value),
        other => panic!("expected a Definition, got {other:?}"),
    }
}

/// This pilot declares its generated output under shadow names
/// (`<local_name>SpecGen`) so it can coexist with the hand-written
/// declarations already admitted into the same kernel -- the only way to
/// get a literal `ExprId` identity check via hash-consing (see the module
/// doc). A declaration that references a SIBLING spec-local declaration
/// (here, `Squarefree` calling `squarefreeAux`) therefore renders with a
/// `SpecGen`-suffixed name on the generated side even when semantically
/// identical, since it names a structurally different `Const` (a different
/// `NameId`) than the hand-written cross-reference. Stripping that one
/// cosmetic suffix before hashing is sound specifically because
/// `SpecGen` is not a substring this development uses anywhere else (no
/// real declaration name collides with the normalized form), so this
/// cannot mask a genuine structural divergence -- confirmed by the
/// eta-expansion bug this exact check caught before this normalization was
/// added (see docs/plan/status/l3-d1-declaration-spec.md).
fn normalize_shadow_names(rendered: &str) -> String {
    rendered.replace("SpecGen", "")
}

fn digest_of(kernel: &mut Kernel, ty: ExprId, value: ExprId) -> String {
    use std::fmt::Write as _;

    let mut hasher = Sha256::new();
    hasher.update(normalize_shadow_names(&kernel.render_lean(ty)).as_bytes());
    hasher.update([0u8]);
    hasher.update(normalize_shadow_names(&kernel.render_lean(value)).as_bytes());
    let mut hex = String::with_capacity(64);
    for byte in hasher.finalize() {
        let _ = write!(hex, "{byte:02x}");
    }
    hex
}

// ---------------------------------------------------------------------------
// Modes
// ---------------------------------------------------------------------------

fn dump_names() -> ExitCode {
    let mut kernel = Kernel::new();
    match build_int_prelude(&mut kernel) {
        Ok(_) => {}
        Err(e) => {
            eprintln!("DECLARATION_SPEC_PILOT|mode=dump-names|verdict=BUILD_FAILED|error={e:?}");
            return ExitCode::FAILURE;
        }
    }
    let mut count = 0usize;
    for (name, _decl) in kernel.environment().iter() {
        println!("{}", kernel.display_name(*name));
        count += 1;
    }
    eprintln!("DECLARATION_SPEC_PILOT|mode=dump-names|names={count}|verdict=OK");
    ExitCode::SUCCESS
}

#[allow(clippy::too_many_lines)]
fn run_pilot() -> ExitCode {
    let mut kernel = Kernel::new();
    let prelude: NatPrelude = match build_nat_prelude(&mut kernel) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("DECLARATION_SPEC_PILOT|verdict=BUILD_FAILED|error={e:?}");
            return ExitCode::FAILURE;
        }
    };

    let spec_text = match std::fs::read_to_string(spec_path()) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("DECLARATION_SPEC_PILOT|verdict=SPEC_READ_FAILED|error={e}");
            return ExitCode::FAILURE;
        }
    };
    let spec: Value = match serde_json::from_str(&spec_text) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("DECLARATION_SPEC_PILOT|verdict=SPEC_PARSE_FAILED|error={e}");
            return ExitCode::FAILURE;
        }
    };
    if spec["spec_version"].as_i64() != Some(1) {
        eprintln!("DECLARATION_SPEC_PILOT|verdict=BAD_SPEC_VERSION");
        return ExitCode::FAILURE;
    }
    let decl_count = spec["declarations"].as_array().map_or(0, Vec::len);
    if decl_count == 0 {
        eprintln!("DECLARATION_SPEC_PILOT|verdict=EMPTY_SPEC");
        return ExitCode::FAILURE;
    }

    let mut d = NatDev::new(&mut kernel, prelude);
    let generated = interpret_spec(&mut d, &spec);

    // Kernel construction happened via `d`, which mutably borrowed `kernel`;
    // reborrow for the read-only comparison below.
    let hand_by_local: HashMap<&str, NameId> = HashMap::from([
        ("squarefreeAux", prelude.squarefree_aux),
        ("Squarefree", prelude.squarefree),
    ]);

    // Declarations with no spec-local dependency reference no shadow name at
    // all, so exact `ExprId` identity is the right bar for them. A
    // declaration that DOES reference a spec-sibling (here, `Squarefree`
    // calling `squarefreeAux`) legitimately differs by exactly the shadow
    // suffix -- see `normalize_shadow_names`'s doc comment -- so only the
    // normalized digest is enforced for those.
    let leaf_names: std::collections::HashSet<String> = spec["declarations"]
        .as_array()
        .expect("declarations array")
        .iter()
        .filter(|d| d["dependencies"].as_array().is_none_or(Vec::is_empty))
        .map(|d| d["local_name"].as_str().expect("local_name").to_string())
        .collect();

    let mut mismatches = 0usize;
    let mut checked = 0usize;
    for (local_name, gen_name) in &generated {
        let hand_name = if let Some(n) = hand_by_local.get(local_name.as_str()) {
            *n
        } else {
            eprintln!("DECLARATION_SPEC_PILOT|verdict=NO_HAND_REFERENCE|local_name={local_name}");
            mismatches += 1;
            continue;
        };
        let (hand_ty, hand_value) = decl_ty_value(d.kernel(), hand_name);
        let (gen_ty, gen_value) = decl_ty_value(d.kernel(), *gen_name);

        let identical_ids = hand_ty == gen_ty && hand_value == gen_value;
        let hand_digest = digest_of(d.kernel(), hand_ty, hand_value);
        let gen_digest = digest_of(d.kernel(), gen_ty, gen_value);
        let identical_digest = hand_digest == gen_digest;

        let is_leaf = leaf_names.contains(local_name);
        checked += 1;
        println!(
            "DECLARATION_SPEC_PILOT|decl={local_name}|is_leaf={is_leaf}|identical_expr_id={identical_ids}|\
             identical_digest={identical_digest}|hand_digest={hand_digest}|gen_digest={gen_digest}"
        );
        let required_ok = if is_leaf {
            identical_ids && identical_digest
        } else {
            identical_digest
        };
        if !required_ok {
            eprintln!(
                "---HAND {local_name} ty---\n{}",
                d.kernel().render_lean(hand_ty)
            );
            eprintln!(
                "---GEN  {local_name} ty---\n{}",
                d.kernel().render_lean(gen_ty)
            );
            eprintln!(
                "---HAND {local_name} value---\n{}",
                d.kernel().render_lean(hand_value)
            );
            eprintln!(
                "---GEN  {local_name} value---\n{}",
                d.kernel().render_lean(gen_value)
            );
            mismatches += 1;
        }
    }

    // Order check: the generated sequence must match the spec's own
    // declaration order, which for this pilot is exactly the hand-written
    // module's order (squarefreeAux, then Squarefree).
    let expected_order = ["squarefreeAux", "Squarefree"];
    let actual_order: Vec<&str> = generated.iter().map(|(n, _)| n.as_str()).collect();
    let order_ok = actual_order == expected_order;
    println!("DECLARATION_SPEC_PILOT|order_identical={order_ok}|order={actual_order:?}");
    if !order_ok {
        mismatches += 1;
    }

    // Duplicate-name-at-construction-time demonstration: try to declare a
    // trivial definition under the REAL, already-taken name `Nat.squarefreeAux`
    // and confirm the kernel's own gate refuses it (a second, in-kernel layer
    // beneath the Python pre-construction guards, which run before this).
    {
        let real_name = prelude.squarefree_aux;
        let bool_ty = d.bool_ty();
        let trivial_value = d.bool_true();
        let result = d.kernel().add_declaration(Declaration::Definition {
            name: real_name,
            uparams: vec![],
            ty: bool_ty,
            value: trivial_value,
            hint: ReducibilityHint::Opaque,
        });
        let refused = matches!(result, Err(KernelError::DeclarationExists { .. }));
        println!("DECLARATION_SPEC_PILOT|duplicate_name_refused_by_kernel={refused}");
        if !refused {
            mismatches += 1;
        }
    }

    // Equation checks, from the generated Rust table (SPEC_EQUATIONS,
    // include!'d above from scripts/gen-declaration-spec.py's output).
    let mut eq_pass = 0usize;
    let mut eq_fail = 0usize;
    for row in SPEC_EQUATIONS {
        let gen_name = generated
            .iter()
            .find(|(n, _)| n == row.local_name)
            .map_or_else(
                || {
                    panic!(
                        "SPEC_EQUATIONS names unknown declaration {}",
                        row.local_name
                    )
                },
                |(_, id)| *id,
            );
        let const_expr = d.kernel().const_(gen_name, vec![]);
        let args: Vec<ExprId> = row
            .args
            .iter()
            .map(|a| d.num(u32::try_from(*a).expect("equation arg fits u32")))
            .collect();
        let applied = d.apply(const_expr, &args);
        let expected = if row.expect_bool {
            d.bool_true()
        } else {
            d.bool_false()
        };
        let ok = d.kernel().def_eq(applied, expected);
        if ok {
            eq_pass += 1;
        } else {
            eq_fail += 1;
            eprintln!(
                "DECLARATION_SPEC_PILOT|equation_failed|decl={}|args={:?}|expect={}",
                row.local_name, row.args, row.expect_bool
            );
        }
    }
    println!(
        "DECLARATION_SPEC_PILOT|equations_checked={}|equations_passed={eq_pass}|equations_failed={eq_fail}",
        eq_pass + eq_fail
    );
    if eq_fail > 0 || eq_pass == 0 {
        mismatches += 1;
    }

    if checked == 0 {
        eprintln!("DECLARATION_SPEC_PILOT|verdict=NOTHING_CHECKED");
        return ExitCode::FAILURE;
    }

    if mismatches == 0 {
        println!(
            "DECLARATION_SPEC_PILOT|verdict=DIGESTS_IDENTICAL|declarations_checked={checked}|\
             equations_checked={}",
            eq_pass + eq_fail
        );
        ExitCode::SUCCESS
    } else {
        println!("DECLARATION_SPEC_PILOT|verdict=MISMATCH|mismatches={mismatches}");
        ExitCode::FAILURE
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    if args.iter().any(|a| a == "--dump-names") {
        dump_names()
    } else {
        run_pilot()
    }
}
