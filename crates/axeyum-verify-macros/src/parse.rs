//! syn → runtime-AST translation for `#[axeyum::verify]`.
//!
//! Produces a `proc_macro2::TokenStream` that (1) re-emits the original function
//! and (2) emits a `#[test]` building the `axeyum_verify::ast::Program` and
//! running the verifier — failing the test on a `Counterexample` (after
//! confirming the witness reproduces a panic in the original fn) or an
//! out-of-fragment `Unknown`.
//!
//! Out-of-subset constructs raise a `syn::Error` at the offending span, so the
//! user gets a precise compile error, not a silent mis-model.

use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::spanned::Spanned;
use syn::{
    BinOp as SynBinOp, Block, Expr, ExprBinary, ExprUnary, FnArg, ItemFn, Lit, Local, Pat, Stmt,
    Type, UnOp as SynUnOp,
};

/// The bit width `usize`/`isize` are modeled at for the bounded check. Rust does
/// not fix the pointer width, so we pick a documented, deterministic default
/// (64-bit, the dominant target); a narrower target only *removes* reachable
/// values, so a 64-bit model is the conservative (sound) over-approximation for
/// index reasoning. Documented in STATUS.md.
const USIZE_WIDTH: u32 = 64;

/// A parsed scalar type.
#[derive(Clone, Copy, PartialEq, Eq)]
struct Ty {
    width: Option<u32>, // None ⇒ bool
    signed: bool,
    /// `true` for `usize`/`isize` (modeled at [`USIZE_WIDTH`] bits but written
    /// back as `usize`/`isize` in the reproduction so the call type-checks).
    is_size: bool,
}

impl Ty {
    fn bool() -> Self {
        Ty {
            width: None,
            signed: false,
            is_size: false,
        }
    }
    /// Tokens building the runtime `axeyum_verify::ast::Ty`.
    fn to_tokens(self) -> TokenStream {
        match self.width {
            None => quote! { axeyum_verify::ast::Ty::Bool },
            Some(w) => {
                let signed = self.signed;
                quote! { axeyum_verify::ast::Ty::Int { width: #w, signed: #signed } }
            }
        }
    }
}

/// Parse a scalar `uN`/`iN`/`bool` type from a syn `Type`.
fn parse_scalar_ty(ty: &Type) -> syn::Result<Ty> {
    let Type::Path(tp) = ty else {
        return Err(syn::Error::new(
            ty.span(),
            "axeyum::verify: only `uN`/`iN`/`bool` scalar types are supported here",
        ));
    };
    let ident = tp
        .path
        .get_ident()
        .ok_or_else(|| syn::Error::new(ty.span(), "axeyum::verify: unsupported type path"))?;
    let s = ident.to_string();
    if s == "bool" {
        return Ok(Ty::bool());
    }
    // `usize`/`isize` map to a configured width (64-bit default); documented.
    if s == "usize" {
        return Ok(Ty {
            width: Some(USIZE_WIDTH),
            signed: false,
            is_size: true,
        });
    }
    if s == "isize" {
        return Ok(Ty {
            width: Some(USIZE_WIDTH),
            signed: true,
            is_size: true,
        });
    }
    let (signed, rest) = if let Some(r) = s.strip_prefix('u') {
        (false, r)
    } else if let Some(r) = s.strip_prefix('i') {
        (true, r)
    } else {
        return Err(syn::Error::new(
            ty.span(),
            format!("axeyum::verify: unsupported scalar type `{s}` (expected uN/iN/bool)"),
        ));
    };
    let width: u32 = rest.parse().map_err(|_| {
        syn::Error::new(
            ty.span(),
            format!("axeyum::verify: unsupported integer type `{s}`"),
        )
    })?;
    if !(1..=128).contains(&width) {
        return Err(syn::Error::new(
            ty.span(),
            format!("axeyum::verify: unsupported integer width {width}"),
        ));
    }
    Ok(Ty {
        width: Some(width),
        signed,
        is_size: false,
    })
}

/// The collected parameter info: name, runtime-Ty tokens, and the Ty (for the
/// reproduction glue).
struct ParamInfo {
    name: String,
    ty: Ty,
}

/// A fixed-length array parameter: `name: [elem; len]` or `name: &[elem; len]`.
/// Slices (`&[T]`) without a compile-time length are rejected — the bounded
/// check needs a fixed element count.
struct ArrayInfo {
    name: String,
    elem: Ty,
    len: u128,
    /// `true` if the parameter was a reference `&[T; N]` (so the reproduction
    /// call passes `&arr`, not `arr`).
    by_ref: bool,
}

/// A parameter is either a scalar or a fixed-length array.
enum ParsedArg {
    Scalar(ParamInfo),
    Array(ArrayInfo),
}

/// Classify a `name: ty` parameter as scalar (`uN`/`iN`/`bool`/`usize`/`isize`)
/// or a fixed-length array (`[T; N]` / `&[T; N]`).
fn parse_arg(name: String, ty: &Type) -> syn::Result<ParsedArg> {
    if let Some(info) = try_parse_array_ty(&name, ty)? {
        return Ok(ParsedArg::Array(info));
    }
    let scalar = parse_scalar_ty(ty)?;
    Ok(ParsedArg::Scalar(ParamInfo { name, ty: scalar }))
}

/// Recognize a fixed-length array type `[elem; N]` or a reference to one
/// `&[elem; N]`. Returns `None` for non-array types (so the caller falls back to
/// scalar parsing); errors for an array with a bad element type or a non-literal
/// length, and for an unsized slice `&[T]` (no fixed length to bound).
fn try_parse_array_ty(name: &str, ty: &Type) -> syn::Result<Option<ArrayInfo>> {
    match ty {
        Type::Array(arr) => {
            let elem = parse_scalar_ty(&arr.elem)?;
            let len = parse_array_len(&arr.len)?;
            Ok(Some(ArrayInfo {
                name: name.to_string(),
                elem,
                len,
                by_ref: false,
            }))
        }
        Type::Reference(r) => match &*r.elem {
            Type::Array(arr) => {
                let elem = parse_scalar_ty(&arr.elem)?;
                let len = parse_array_len(&arr.len)?;
                Ok(Some(ArrayInfo {
                    name: name.to_string(),
                    elem,
                    len,
                    by_ref: true,
                }))
            }
            Type::Slice(s) => Err(syn::Error::new(
                s.span(),
                "axeyum::verify: an unsized slice `&[T]` needs a fixed length for the \
                 bounded check — use `&[T; N]` (or `[T; N]`)",
            )),
            other => Err(syn::Error::new(
                other.span(),
                "axeyum::verify: only `&[T; N]` references are supported",
            )),
        },
        _ => Ok(None),
    }
}

/// Parse the `N` in `[T; N]` — a non-negative integer literal.
fn parse_array_len(len: &Expr) -> syn::Result<u128> {
    if let Expr::Lit(el) = len {
        return lit_u128(&el.lit, el.span());
    }
    Err(syn::Error::new(
        len.span(),
        "axeyum::verify: array length must be an integer literal",
    ))
}

/// Expand the whole function. `expect_bug` flips the generated `#[test]` to
/// assert that a counterexample is *found* (and reproduces a panic in the
/// original) rather than asserting the function verifies.
pub fn expand(func: &ItemFn, expect_bug: bool) -> syn::Result<TokenStream> {
    let fn_name = func.sig.ident.to_string();

    // --- parse parameters ---------------------------------------------------
    let mut params: Vec<ParamInfo> = Vec::new();
    let mut arrays: Vec<ArrayInfo> = Vec::new();
    for arg in &func.sig.inputs {
        let FnArg::Typed(pt) = arg else {
            return Err(syn::Error::new(
                arg.span(),
                "axeyum::verify: `self` receivers are not supported",
            ));
        };
        let Pat::Ident(pi) = &*pt.pat else {
            return Err(syn::Error::new(
                pt.pat.span(),
                "axeyum::verify: only simple `name: ty` parameters are supported",
            ));
        };
        match parse_arg(pi.ident.to_string(), &pt.ty)? {
            ParsedArg::Scalar(p) => params.push(p),
            ParsedArg::Array(a) => arrays.push(a),
        }
    }

    // --- parse body into runtime-AST-building tokens ------------------------
    // Function-level unwind bound (`#[axeyum::unwind(K)]` alongside the verify
    // attribute), applied to every loop in the body.
    let fn_unwind = extract_unwind(&func.attrs)?;
    let mut ctx = Lowerer::new(fn_unwind);
    for p in &params {
        ctx.declare(&p.name, p.ty);
    }
    for a in &arrays {
        ctx.declare_array(&a.name, a.elem, a.len);
    }
    let body_tokens = ctx.lower_block(&func.block)?;

    let param_tokens: Vec<TokenStream> = params
        .iter()
        .map(|p| {
            let name = &p.name;
            let ty = p.ty.to_tokens();
            quote! { axeyum_verify::ast::Param { name: #name.into(), ty: #ty } }
        })
        .collect();

    let array_tokens: Vec<TokenStream> = arrays
        .iter()
        .map(|a| {
            let name = &a.name;
            let elem = a.elem.to_tokens();
            let len = a.len;
            quote! { axeyum_verify::ast::ArrayParam { name: #name.into(), elem: #elem, len: #len } }
        })
        .collect();

    // --- reproduction glue: call the original fn on the witness -------------
    let repro = reproduction_glue(func, &params, &arrays, expect_bug);

    let test_ident = format_ident!("axeyum_verify_{}", func.sig.ident);
    let verdict_ident = format_ident!("{}__axeyum_verdict", func.sig.ident);
    let program_ident = format_ident!("{}__axeyum_program", func.sig.ident);
    let original = func;

    Ok(quote! {
        #original

        /// Builds the bounded-check program lowered from this `#[verify]` function.
        #[doc(hidden)]
        #[allow(non_snake_case)]
        fn #program_ident() -> axeyum_verify::ast::Program {
            axeyum_verify::ast::Program {
                name: #fn_name.into(),
                params: vec![ #(#param_tokens),* ],
                arrays: vec![ #(#array_tokens),* ],
                body: vec![ #(#body_tokens),* ],
            }
        }

        /// Runs the bounded check and returns the verdict (no asserts). Callers
        /// that want to inspect a counterexample use this; the `#[test]` below
        /// is the default cargo-test gate.
        #[doc(hidden)]
        #[allow(non_snake_case)]
        fn #verdict_ident() -> axeyum_verify::Verdict {
            let program = #program_ident();
            axeyum_verify::verify_program(&program, &axeyum_verify::default_config())
                .expect("axeyum-verify: solver hard error")
        }

        #[test]
        fn #test_ident() {
            match #verdict_ident() {
                axeyum_verify::Verdict::Verified { certified, lean_module } => {
                    assert!(
                        !#expect_bug,
                        "axeyum::verify[{}]: expected a bug (#[verify(expect_bug)]) but the \
                         function VERIFIED (certified={})", #fn_name, certified
                    );
                    eprintln!(
                        "axeyum::verify[{}]: VERIFIED (certified={}, lean={})",
                        #fn_name, certified, lean_module.is_some()
                    );
                }
                axeyum_verify::Verdict::Counterexample { class, inputs } => {
                    #repro
                }
                axeyum_verify::Verdict::Unknown { reason } => {
                    panic!(
                        "axeyum::verify[{}]: UNKNOWN — {} (out of the bounded fragment)",
                        #fn_name, reason
                    );
                }
            }
        }
    })
}

/// Builds the `Counterexample` arm: extract typed witnesses, run the original
/// function under `catch_unwind`, and assert it actually panics (DISAGREE=0),
/// then fail the test reporting the reproducing inputs.
///
/// The call arguments are emitted in the **original signature order** (scalars
/// and arrays interleaved), keyed by parameter name into the witness list.
fn reproduction_glue(
    func: &ItemFn,
    params: &[ParamInfo],
    arrays: &[ArrayInfo],
    expect_bug: bool,
) -> TokenStream {
    let fn_ident = &func.sig.ident;
    let mut bindings = Vec::new();
    let mut call_args = Vec::new();
    let mut fmt_parts = Vec::new();
    // Iterate the original signature so call args are in declaration order.
    for (idx, arg) in func.sig.inputs.iter().enumerate() {
        let FnArg::Typed(pt) = arg else { continue };
        let Pat::Ident(pi) = &*pt.pat else { continue };
        let pname = pi.ident.to_string();
        let var = format_ident!("__w{idx}");
        if let Some(p) = params.iter().find(|p| p.name == pname) {
            scalar_binding(&var, &p.name, p.ty, &mut bindings);
            call_args.push(quote! { #var });
            fmt_parts.push(quote! { format!("{}={:?}", #pname, #var) });
        } else if let Some(a) = arrays.iter().find(|a| a.name == pname) {
            array_binding(&var, a, &mut bindings);
            if a.by_ref {
                call_args.push(quote! { &#var });
            } else {
                call_args.push(quote! { #var });
            }
            fmt_parts.push(quote! { format!("{}={:?}", #pname, #var) });
        }
    }

    // When `expect_bug`, a confirmed reproduction is a PASS (the demonstration);
    // otherwise the found bug fails the test (the bug is the reproduction).
    let outcome = if expect_bug {
        quote! {
            eprintln!(
                "axeyum::verify[{}]: BUG FOUND & REPRODUCED — class `{}`, inputs: {}",
                stringify!(#fn_ident), class, __args.join(", ")
            );
        }
    } else {
        quote! {
            panic!(
                "axeyum::verify[{}]: BUG FOUND — class `{}`, reproducing inputs: {} (the original function panics on these; this failing test IS the reproduction)",
                stringify!(#fn_ident), class, __args.join(", ")
            );
        }
    };

    quote! {
        #(#bindings)*
        let __args: Vec<String> = vec![ #(#fmt_parts),* ];
        let __reproduces = axeyum_verify::reproduce::panics_on(|| {
            let _ = #fn_ident( #(#call_args),* );
        });
        assert!(
            __reproduces,
            "axeyum::verify: counterexample ({}) for `{}` did NOT reproduce a panic in the original function — lowering defect (class: {})",
            __args.join(", "), stringify!(#fn_ident), class
        );
        #outcome
    }
}

/// Emits a `let __wN: RustTy = <witness lookup>;` binding for one scalar param.
fn scalar_binding(var: &proc_macro2::Ident, pname: &str, ty: Ty, bindings: &mut Vec<TokenStream>) {
    match ty.width {
        None => {
            bindings.push(quote! {
                let #var: bool = inputs.iter().find_map(|w| match w {
                    axeyum_verify::Witness::Bool { name, value } if name == #pname => Some(*value),
                    _ => None,
                }).unwrap_or(false);
            });
        }
        Some(width) => {
            let rust_ty = rust_int_ident(ty, width);
            if ty.signed {
                bindings.push(quote! {
                    let #var: #rust_ty = {
                        let (w, _, bits) = inputs.iter().find_map(|wit| match wit {
                            axeyum_verify::Witness::Int { name, width, signed, bits } if name == #pname => Some((*width, *signed, *bits)),
                            _ => None,
                        }).unwrap_or((#width, true, 0));
                        let v = axeyum_verify::signed_value(w, bits);
                        <#rust_ty as ::core::convert::TryFrom<i128>>::try_from(v).unwrap_or_default()
                    };
                });
            } else {
                bindings.push(quote! {
                    let #var: #rust_ty = {
                        let bits = inputs.iter().find_map(|wit| match wit {
                            axeyum_verify::Witness::Int { name, bits, .. } if name == #pname => Some(*bits),
                            _ => None,
                        }).unwrap_or(0);
                        <#rust_ty as ::core::convert::TryFrom<u128>>::try_from(bits).unwrap_or_default()
                    };
                });
            }
        }
    }
}

/// Emits a `let __wN: [RustTy; len] = [..];` binding for one array param,
/// decoding each element from the array witness (defaulting missing elements to
/// 0 — a don't-care, since the bad state already captures the reachable panic).
fn array_binding(var: &proc_macro2::Ident, a: &ArrayInfo, bindings: &mut Vec<TokenStream>) {
    let pname = &a.name;
    let len = usize::try_from(a.len).unwrap_or(usize::MAX);
    // Array elements are integers in the supported fragment (bool arrays are
    // rejected at lowering); the element width is always set.
    let width = a.elem.width.unwrap_or(8);
    let rust_ty = rust_int_ident(a.elem, width);
    let decode = if a.elem.signed {
        quote! {
            let v = axeyum_verify::signed_value(#width, *bits);
            <#rust_ty as ::core::convert::TryFrom<i128>>::try_from(v).unwrap_or_default()
        }
    } else {
        quote! {
            <#rust_ty as ::core::convert::TryFrom<u128>>::try_from(*bits).unwrap_or_default()
        }
    };
    bindings.push(quote! {
        let #var: [#rust_ty; #len] = {
            let ints: Vec<u128> = inputs.iter().find_map(|wit| match wit {
                axeyum_verify::Witness::Array { name, ints, .. } if name == #pname => Some(ints.clone()),
                _ => None,
            }).unwrap_or_default();
            let mut arr = [<#rust_ty as ::core::default::Default>::default(); #len];
            for (slot, bits) in arr.iter_mut().zip(ints.iter()) {
                *slot = { #decode };
            }
            arr
        };
    });
}

/// The Rust integer type identifier for an integer scalar `Ty`. `usize`/`isize`
/// are written back as `usize`/`isize` (so the reproduction call type-checks);
/// every other width maps to `uN`/`iN`.
fn rust_int_ident(ty: Ty, width: u32) -> proc_macro2::Ident {
    if ty.is_size {
        format_ident!("{}size", if ty.signed { "i" } else { "u" })
    } else {
        format_ident!("{}{}", if ty.signed { "i" } else { "u" }, width)
    }
}

// --- body lowering -----------------------------------------------------------

/// Tracks declared variable types for whitelisting (lets the translator reject
/// references to undeclared names and emit correct literal types).
struct Lowerer {
    scopes: Vec<std::collections::HashMap<String, Ty>>,
    /// array name → (element type, length). Arrays live at function scope (they
    /// are parameters), so a single map suffices.
    arrays: std::collections::HashMap<String, (Ty, u128)>,
    /// Scoped `Option`-typed bindings from `let x = a.checked_*(b);` — `x` is
    /// *virtual* (no IR value), expanded at use sites (`unwrap`/`unwrap_or`/
    /// `is_some`/`is_none`/`match`). Any other use of `x` is a fragment error
    /// (sound: rejected, never a wrong verdict). Parallels `scopes`.
    option_lets: Vec<std::collections::HashMap<String, OptBind>>,
    /// The function-level `#[axeyum::unwind(K)]` bound applied to every loop
    /// (`None` ⇒ loops are rejected; the user must supply a bound).
    unwind: Option<u64>,
}

/// A virtual `Option` binding: `Some(wrap_op(lhs, rhs))` when `ovf_op(lhs, rhs)`
/// does not overflow, else `None`. The operand tokens are already lowered.
#[derive(Clone)]
struct OptBind {
    /// `Add`/`Sub`/`Mul` — the overflow predicate operator.
    ovf_op: &'static str,
    /// `WrappingAdd`/`WrappingSub`/`WrappingMul` — the carried (real) value op.
    wrap_op: &'static str,
    /// Lowered left operand.
    lhs: TokenStream,
    /// Lowered right operand.
    rhs: TokenStream,
    /// The carried value's integer type.
    ty: Ty,
}

impl Lowerer {
    fn new(unwind: Option<u64>) -> Self {
        Lowerer {
            scopes: vec![std::collections::HashMap::new()],
            arrays: std::collections::HashMap::new(),
            option_lets: vec![std::collections::HashMap::new()],
            unwind,
        }
    }

    /// Find a virtual `Option` binding by name (innermost scope first).
    fn lookup_option(&self, name: &str) -> Option<OptBind> {
        self.option_lets
            .iter()
            .rev()
            .find_map(|s| s.get(name).cloned())
    }

    fn declare(&mut self, name: &str, ty: Ty) {
        self.scopes
            .last_mut()
            .expect("at least one scope")
            .insert(name.to_string(), ty);
    }

    /// Register a fixed-length array parameter for `a[i]` indexing.
    fn declare_array(&mut self, name: &str, elem: Ty, len: u128) {
        self.arrays.insert(name.to_string(), (elem, len));
    }

    fn lookup_array(&self, name: &str) -> Option<(Ty, u128)> {
        self.arrays.get(name).copied()
    }

    fn lookup(&self, name: &str) -> Option<Ty> {
        self.scopes.iter().rev().find_map(|s| s.get(name).copied())
    }

    fn push_scope(&mut self) {
        self.scopes.push(std::collections::HashMap::new());
        self.option_lets.push(std::collections::HashMap::new());
    }
    fn pop_scope(&mut self) {
        self.scopes.pop();
        self.option_lets.pop();
    }

    /// Lower a block into a `Vec<TokenStream>` of `Stmt`-building expressions.
    fn lower_block(&mut self, block: &Block) -> syn::Result<Vec<TokenStream>> {
        let mut out = Vec::new();
        let n = block.stmts.len();
        for (i, stmt) in block.stmts.iter().enumerate() {
            // A trailing expression with no semicolon is the return value; we
            // still evaluate it for panic-class side effects.
            let is_tail = i + 1 == n;
            self.lower_stmt(stmt, is_tail, &mut out)?;
        }
        Ok(out)
    }

    fn lower_stmt(
        &mut self,
        stmt: &Stmt,
        is_tail: bool,
        out: &mut Vec<TokenStream>,
    ) -> syn::Result<()> {
        match stmt {
            Stmt::Local(local) => {
                // `let x = a.checked_*(b);` binds a *virtual* Option (no IR value
                // / no emitted statement); expanded at use sites.
                if self.try_record_option_let(local)? {
                    return Ok(());
                }
                let (name, ty, value_tok) = self.lower_let(local)?;
                let ty_tok = ty.to_tokens();
                self.declare(&name, ty);
                out.push(quote! {
                    axeyum_verify::ast::Stmt::Let {
                        name: #name.into(),
                        ty: #ty_tok,
                        value: #value_tok,
                    }
                });
                Ok(())
            }
            Stmt::Expr(expr, semi) => {
                // Distinguish statement-position constructs from value exprs.
                if let Some(s) = self.try_lower_stmt_expr(expr)? {
                    out.push(s);
                    return Ok(());
                }
                // assignment `name = expr;`
                if let Expr::Assign(assign) = expr {
                    let Expr::Path(p) = &*assign.left else {
                        return Err(syn::Error::new(
                            assign.left.span(),
                            "axeyum::verify: assignment target must be a simple variable",
                        ));
                    };
                    let name = path_ident(p)?;
                    // Coerce an untyped int literal RHS to the target's type, as
                    // the let-init and compound-assignment paths do.
                    let (val, _ty) = if is_untyped_int_lit(&assign.right) {
                        if let (Some(lty), Expr::Lit(el)) = (self.lookup(&name), &*assign.right) {
                            if lty.width.is_some() {
                                lower_lit_as(&el.lit, lty, el.span())?
                            } else {
                                self.lower_expr(&assign.right)?
                            }
                        } else {
                            self.lower_expr(&assign.right)?
                        }
                    } else {
                        self.lower_expr(&assign.right)?
                    };
                    out.push(quote! {
                        axeyum_verify::ast::Stmt::Assign { name: #name.into(), value: #val }
                    });
                    return Ok(());
                }
                // compound assignment `name op= expr;` → `name = name op expr;`
                if let Expr::Binary(b) = expr {
                    if let Some(s) = self.try_lower_compound_assign(b)? {
                        out.push(s);
                        return Ok(());
                    }
                }
                // a bare/tail expression: evaluate for side effects.
                let _ = (semi, is_tail);
                let (val, _ty) = self.lower_expr(expr)?;
                out.push(quote! { axeyum_verify::ast::Stmt::Eval(#val) });
                Ok(())
            }
            Stmt::Item(item) => Err(syn::Error::new(
                item.span(),
                "axeyum::verify: nested items are not supported",
            )),
            Stmt::Macro(m) => {
                let s = self.lower_macro_stmt(&m.mac)?;
                out.push(s);
                Ok(())
            }
        }
    }

    /// Recognize a compound assignment `name op= rhs` (`+=`, `-=`, …) and lower
    /// it as `name = name op rhs;`. Returns `None` if `b.op` is not a compound
    /// assignment (the caller then treats `b` as a value expression).
    fn try_lower_compound_assign(&mut self, b: &ExprBinary) -> syn::Result<Option<TokenStream>> {
        let variant = match b.op {
            SynBinOp::AddAssign(_) => "Add",
            SynBinOp::SubAssign(_) => "Sub",
            SynBinOp::MulAssign(_) => "Mul",
            SynBinOp::DivAssign(_) => "Div",
            SynBinOp::RemAssign(_) => "Rem",
            SynBinOp::BitAndAssign(_) => "BitAnd",
            SynBinOp::BitOrAssign(_) => "BitOr",
            SynBinOp::BitXorAssign(_) => "BitXor",
            SynBinOp::ShlAssign(_) => "Shl",
            SynBinOp::ShrAssign(_) => "Shr",
            _ => return Ok(None),
        };
        let Expr::Path(p) = &*b.left else {
            return Err(syn::Error::new(
                b.left.span(),
                "axeyum::verify: compound-assignment target must be a simple variable",
            ));
        };
        let name = path_ident(p)?;
        let lty = self.lookup(&name).ok_or_else(|| {
            syn::Error::new(
                p.span(),
                format!("axeyum::verify: unknown variable `{name}`"),
            )
        })?;
        // RHS, coercing an untyped literal to the target's type (as `bin_op` does).
        let (rhs_tok, _rty) = if is_untyped_int_lit(&b.right) && lty.width.is_some() {
            if let Expr::Lit(el) = &*b.right {
                lower_lit_as(&el.lit, lty, el.span())?
            } else {
                self.lower_expr(&b.right)?
            }
        } else {
            self.lower_expr(&b.right)?
        };
        let op_ident = format_ident!("{}", variant);
        Ok(Some(quote! {
            axeyum_verify::ast::Stmt::Assign {
                name: #name.into(),
                value: axeyum_verify::ast::Expr::Binary {
                    op: axeyum_verify::ast::BinOp::#op_ident,
                    lhs: Box::new(axeyum_verify::ast::Expr::Var(#name.into())),
                    rhs: Box::new(#rhs_tok),
                },
            }
        }))
    }

    /// If `local` is `let x [: T] = a.checked_{add,sub,mul}(b);`, record `x` as a
    /// virtual `Option` binding and return `true` (no statement emitted). The
    /// binding is expanded at use sites; any other use of `x` is rejected.
    fn try_record_option_let(&mut self, local: &Local) -> syn::Result<bool> {
        let name = match &local.pat {
            Pat::Ident(pi) => pi.ident.to_string(),
            Pat::Type(pt) => match &*pt.pat {
                Pat::Ident(pi) => pi.ident.to_string(),
                _ => return Ok(false),
            },
            _ => return Ok(false),
        };
        let Some(init) = &local.init else {
            return Ok(false);
        };
        let Expr::MethodCall(call) = &*init.expr else {
            return Ok(false);
        };
        let Some((ovf_op, wrap_op)) = checked_ops(&call.method.to_string()) else {
            return Ok(false);
        };
        if call.args.len() != 1 {
            return Err(syn::Error::new(
                call.span(),
                "axeyum::verify: `checked_*` takes exactly one argument",
            ));
        }
        let (lhs, lty) = self.lower_expr(&call.receiver)?;
        let arg = call.args.first().unwrap();
        let rhs = if is_untyped_int_lit(arg) && lty.width.is_some() {
            if let Expr::Lit(el) = arg {
                lower_lit_as(&el.lit, lty, el.span())?.0
            } else {
                self.lower_expr(arg)?.0
            }
        } else {
            self.lower_expr(arg)?.0
        };
        self.option_lets
            .last_mut()
            .expect("at least one option scope")
            .insert(
                name,
                OptBind {
                    ovf_op,
                    wrap_op,
                    lhs,
                    rhs,
                    ty: lty,
                },
            );
        Ok(true)
    }

    /// Expand a method call on a virtual `Option` binding `b`.
    fn lower_option_method(
        &mut self,
        method: &str,
        mc: &syn::ExprMethodCall,
        b: &OptBind,
    ) -> syn::Result<(TokenStream, Ty)> {
        let OptBind {
            ovf_op,
            wrap_op,
            lhs,
            rhs,
            ty,
        } = b;
        let ovf_ident = format_ident!("{}", *ovf_op);
        let wrap_ident = format_ident!("{}", *wrap_op);
        let overflows = quote! {
            axeyum_verify::ast::Expr::Overflows {
                op: axeyum_verify::ast::BinOp::#ovf_ident,
                lhs: Box::new(#lhs),
                rhs: Box::new(#rhs),
            }
        };
        match method {
            // unwrap/expect = the plain checked op (panics on overflow).
            "unwrap" | "expect" => Ok((
                quote! {
                    axeyum_verify::ast::Expr::Binary {
                        op: axeyum_verify::ast::BinOp::#ovf_ident,
                        lhs: Box::new(#lhs),
                        rhs: Box::new(#rhs),
                    }
                },
                *ty,
            )),
            // unwrap_or(d) = ite(!overflows, wrapping_op, d).
            "unwrap_or" => {
                if mc.args.len() != 1 {
                    return Err(syn::Error::new(
                        mc.span(),
                        "axeyum::verify: `.unwrap_or()` takes exactly one argument",
                    ));
                }
                let arg = mc.args.first().unwrap();
                let default = if is_untyped_int_lit(arg) && ty.width.is_some() {
                    if let Expr::Lit(el) = arg {
                        lower_lit_as(&el.lit, *ty, el.span())?.0
                    } else {
                        self.lower_expr(arg)?.0
                    }
                } else {
                    self.lower_expr(arg)?.0
                };
                Ok((
                    quote! {
                        axeyum_verify::ast::Expr::Ite {
                            cond: Box::new(axeyum_verify::ast::Expr::Unary {
                                op: axeyum_verify::ast::UnOp::Not,
                                operand: Box::new(#overflows),
                            }),
                            then: Box::new(axeyum_verify::ast::Expr::Binary {
                                op: axeyum_verify::ast::BinOp::#wrap_ident,
                                lhs: Box::new(#lhs),
                                rhs: Box::new(#rhs),
                            }),
                            els: Box::new(#default),
                        }
                    },
                    *ty,
                ))
            }
            // is_some / is_none are the (negated) overflow predicate.
            "is_some" => Ok((
                quote! {
                    axeyum_verify::ast::Expr::Unary {
                        op: axeyum_verify::ast::UnOp::Not,
                        operand: Box::new(#overflows),
                    }
                },
                Ty::bool(),
            )),
            "is_none" => Ok((overflows, Ty::bool())),
            other => Err(syn::Error::new(
                mc.span(),
                format!("axeyum::verify: unsupported method `.{other}()` on an Option"),
            )),
        }
    }

    /// `let name: ty = expr;` → (name, Ty, value tokens). Requires a type
    /// annotation (the symbolic width must be known).
    fn lower_let(&mut self, local: &Local) -> syn::Result<(String, Ty, TokenStream)> {
        let Pat::Type(pt) = &local.pat else {
            // Allow `let name = expr;` only if we can infer the type from the rhs.
            if let Pat::Ident(pi) = &local.pat {
                let init = local.init.as_ref().ok_or_else(|| {
                    syn::Error::new(local.span(), "axeyum::verify: `let` needs an initializer")
                })?;
                let (val, ty) = self.lower_expr(&init.expr)?;
                return Ok((pi.ident.to_string(), ty, val));
            }
            return Err(syn::Error::new(
                local.pat.span(),
                "axeyum::verify: only `let name: ty = ..;` bindings are supported",
            ));
        };
        let Pat::Ident(pi) = &*pt.pat else {
            return Err(syn::Error::new(
                pt.pat.span(),
                "axeyum::verify: `let` binding must be a simple name",
            ));
        };
        let ty = parse_scalar_ty(&pt.ty)?;
        let init = local.init.as_ref().ok_or_else(|| {
            syn::Error::new(local.span(), "axeyum::verify: `let` needs an initializer")
        })?;
        // An unsuffixed integer-literal initializer adopts the declared type
        // (Rust's literal inference), so `let q: u8 = 0;` type-checks.
        let val = if is_untyped_int_lit(&init.expr) && ty.width.is_some() {
            if let Expr::Lit(el) = &*init.expr {
                lower_lit_as(&el.lit, ty, el.span())?.0
            } else {
                self.lower_expr(&init.expr)?.0
            }
        } else {
            self.lower_expr(&init.expr)?.0
        };
        Ok((pi.ident.to_string(), ty, val))
    }

    /// Try to interpret a statement-position expression as a control-flow
    /// statement (`if`, `for`, `while`). Returns `None` for value expressions.
    fn try_lower_stmt_expr(&mut self, expr: &Expr) -> syn::Result<Option<TokenStream>> {
        match expr {
            Expr::If(eif) => {
                let (cond, _) = self.lower_expr(&eif.cond)?;
                self.push_scope();
                let then = self.lower_block(&eif.then_branch)?;
                self.pop_scope();
                let els = match &eif.else_branch {
                    None => Vec::new(),
                    Some((_, else_expr)) => {
                        self.push_scope();
                        let e = self.lower_else(else_expr)?;
                        self.pop_scope();
                        e
                    }
                };
                Ok(Some(quote! {
                    axeyum_verify::ast::Stmt::If {
                        cond: #cond,
                        then: vec![ #(#then),* ],
                        els: vec![ #(#els),* ],
                    }
                }))
            }
            Expr::ForLoop(forloop) => Ok(Some(self.lower_for(forloop)?)),
            Expr::While(w) => Ok(Some(self.lower_while(w)?)),
            Expr::Match(em) => Ok(Some(self.lower_match(em)?)),
            _ => Ok(None),
        }
    }

    /// `match scrut { lit => {..}, .., _ => {..} }` over an integer scrutinee,
    /// desugared to a nested `if`/`else` chain (`scrut == lit_i`). Arm patterns
    /// must be integer literals or `_`; a `_` arm is required (exhaustiveness).
    /// Guards, bindings, and or-patterns are rejected (out of fragment).
    fn lower_match(&mut self, em: &syn::ExprMatch) -> syn::Result<TokenStream> {
        // `match a.checked_*(b) { Some(v) => .., None => .. }` is Option-flow, not
        // an integer match — desugar it separately.
        if let Some(ts) = self.try_lower_checked_option_match(em)? {
            return Ok(ts);
        }
        let (scrut, scrut_ty) = self.lower_expr(&em.expr)?;
        let mut lit_arms: Vec<(TokenStream, Vec<TokenStream>)> = Vec::new();
        let mut wildcard: Option<Vec<TokenStream>> = None;
        for arm in &em.arms {
            if arm.guard.is_some() {
                return Err(syn::Error::new(
                    arm.pat.span(),
                    "axeyum::verify: `match` guards are not supported",
                ));
            }
            // Lower the arm body (a block or a single expression) as statements.
            self.push_scope();
            let mut body = Vec::new();
            match &*arm.body {
                Expr::Block(b) => body = self.lower_block(&b.block)?,
                other => self.lower_stmt(&Stmt::Expr(other.clone(), None), false, &mut body)?,
            }
            self.pop_scope();
            match &arm.pat {
                syn::Pat::Wild(_) => {
                    if wildcard.is_some() {
                        return Err(syn::Error::new(
                            arm.pat.span(),
                            "axeyum::verify: duplicate `_` arm in `match`",
                        ));
                    }
                    wildcard = Some(body);
                }
                syn::Pat::Lit(lit) => {
                    // Coerce an unsuffixed integer arm literal to the scrutinee's
                    // integer type so `scrut == lit` type-checks (Rust's literal
                    // inference, mirroring the binary-operand coercion above).
                    let lit_tok = if scrut_ty.width.is_some()
                        && matches!(&lit.lit, Lit::Int(li) if li.suffix().is_empty())
                    {
                        let (t, _) = lower_lit_as(&lit.lit, scrut_ty, lit.span())?;
                        t
                    } else {
                        self.lower_expr(&Expr::Lit(lit.clone()))?.0
                    };
                    let cond = quote! {
                        axeyum_verify::ast::Expr::Binary {
                            op: axeyum_verify::ast::BinOp::Eq,
                            lhs: Box::new(#scrut),
                            rhs: Box::new(#lit_tok),
                        }
                    };
                    lit_arms.push((cond, body));
                }
                other => {
                    return Err(syn::Error::new(
                        other.span(),
                        "axeyum::verify: `match` arm patterns must be an integer literal or `_`",
                    ));
                }
            }
        }
        let wildcard = wildcard.ok_or_else(|| {
            syn::Error::new(
                em.span(),
                "axeyum::verify: `match` must have a `_` arm (exhaustiveness)",
            )
        })?;
        // Fold right: the wildcard is the innermost `else`; each literal arm wraps.
        let mut els: Vec<TokenStream> = wildcard;
        for (cond, body) in lit_arms.into_iter().rev() {
            let if_stmt = quote! {
                axeyum_verify::ast::Stmt::If {
                    cond: #cond,
                    then: vec![ #(#body),* ],
                    els: vec![ #(#els),* ],
                }
            };
            els = vec![if_stmt];
        }
        // `els` now holds the outermost statement(s); wrap in a true-guarded `If`
        // when there were no literal arms so a single `Stmt` is returned.
        if els.len() == 1 {
            let single = &els[0];
            Ok(quote! { #single })
        } else {
            Ok(quote! {
                axeyum_verify::ast::Stmt::If {
                    cond: axeyum_verify::ast::Expr::BoolLit(true),
                    then: vec![ #(#els),* ],
                    els: vec![],
                }
            })
        }
    }

    /// `match a.checked_{add,sub,mul}(b) { Some(v) => .., None => .. }` →
    /// `if !Overflows(op, a, b) { let v = wrapping_op(a, b); <some> } else
    /// { <none> }`. Returns `Ok(None)` when the scrutinee is not a `checked_*`
    /// call (so the caller falls back to the integer-`match` path).
    #[allow(clippy::too_many_lines)]
    fn try_lower_checked_option_match(
        &mut self,
        em: &syn::ExprMatch,
    ) -> syn::Result<Option<TokenStream>> {
        // Resolve the Option scrutinee from either a `checked_*` call or a virtual
        // `Option` binding (`let x = a.checked_*(b)`). Otherwise this isn't an
        // Option match — fall back to the integer-`match` path.
        let (ovf_op, wrap_op, lhs, rhs, lty): (&str, &str, TokenStream, TokenStream, Ty) =
            if let Expr::MethodCall(call) = &*em.expr {
                let Some((ovf_op, wrap_op)) = checked_ops(&call.method.to_string()) else {
                    return Ok(None);
                };
                if call.args.len() != 1 {
                    return Err(syn::Error::new(
                        call.span(),
                        "axeyum::verify: `checked_*` takes exactly one argument",
                    ));
                }
                let (lhs, lty) = self.lower_expr(&call.receiver)?;
                let arg_expr = call.args.first().unwrap();
                let rhs = if is_untyped_int_lit(arg_expr) && lty.width.is_some() {
                    if let Expr::Lit(el) = arg_expr {
                        lower_lit_as(&el.lit, lty, el.span())?.0
                    } else {
                        self.lower_expr(arg_expr)?.0
                    }
                } else {
                    self.lower_expr(arg_expr)?.0
                };
                (ovf_op, wrap_op, lhs, rhs, lty)
            } else if let Expr::Path(p) = &*em.expr {
                let Ok(name) = path_ident(p) else {
                    return Ok(None);
                };
                let Some(b) = self.lookup_option(&name) else {
                    return Ok(None);
                };
                (b.ovf_op, b.wrap_op, b.lhs, b.rhs, b.ty)
            } else {
                return Ok(None);
            };

        if em.arms.len() != 2 {
            return Err(syn::Error::new(
                em.span(),
                "axeyum::verify: `match` on `checked_*` must have exactly `Some(x)` and `None` arms",
            ));
        }
        let path_is =
            |p: &syn::Path, name: &str| p.segments.last().is_some_and(|s| s.ident == name);
        let mut some_arm: Option<(String, &syn::Arm)> = None;
        let mut none_arm: Option<&syn::Arm> = None;
        for arm in &em.arms {
            if arm.guard.is_some() {
                return Err(syn::Error::new(
                    arm.pat.span(),
                    "axeyum::verify: `match` guards are not supported",
                ));
            }
            match &arm.pat {
                syn::Pat::TupleStruct(ts) if path_is(&ts.path, "Some") => {
                    if ts.elems.len() != 1 {
                        return Err(syn::Error::new(
                            ts.span(),
                            "axeyum::verify: `Some(..)` arm must bind exactly one value",
                        ));
                    }
                    let syn::Pat::Ident(pi) = ts.elems.first().unwrap() else {
                        return Err(syn::Error::new(
                            ts.elems.span(),
                            "axeyum::verify: `Some(x)` binding must be a simple name",
                        ));
                    };
                    some_arm = Some((pi.ident.to_string(), arm));
                }
                syn::Pat::Ident(pi) if pi.ident == "None" => none_arm = Some(arm),
                syn::Pat::Path(p) if path_is(&p.path, "None") => none_arm = Some(arm),
                syn::Pat::Wild(_) => none_arm = Some(arm),
                other => {
                    return Err(syn::Error::new(
                        other.span(),
                        "axeyum::verify: arms must be `Some(x)` and `None`",
                    ));
                }
            }
        }
        let (bind, some_a) = some_arm
            .ok_or_else(|| syn::Error::new(em.span(), "axeyum::verify: missing `Some(x)` arm"))?;
        let none_a = none_arm
            .ok_or_else(|| syn::Error::new(em.span(), "axeyum::verify: missing `None` arm"))?;

        // Some-arm body, with `bind` in scope holding the (wrapping == real) value.
        self.push_scope();
        self.declare(&bind, lty);
        let mut some_body = Vec::new();
        match &*some_a.body {
            Expr::Block(b) => some_body = self.lower_block(&b.block)?,
            other => {
                self.lower_stmt(&Stmt::Expr(other.clone(), None), false, &mut some_body)?;
            }
        }
        self.pop_scope();

        self.push_scope();
        let mut none_body = Vec::new();
        match &*none_a.body {
            Expr::Block(b) => none_body = self.lower_block(&b.block)?,
            other => {
                self.lower_stmt(&Stmt::Expr(other.clone(), None), false, &mut none_body)?;
            }
        }
        self.pop_scope();

        let ty_tok = lty.to_tokens();
        let ovf_ident = format_ident!("{}", ovf_op);
        let wrap_ident = format_ident!("{}", wrap_op);
        Ok(Some(quote! {
            axeyum_verify::ast::Stmt::If {
                cond: axeyum_verify::ast::Expr::Unary {
                    op: axeyum_verify::ast::UnOp::Not,
                    operand: Box::new(axeyum_verify::ast::Expr::Overflows {
                        op: axeyum_verify::ast::BinOp::#ovf_ident,
                        lhs: Box::new(#lhs),
                        rhs: Box::new(#rhs),
                    }),
                },
                then: {
                    let mut stmts = vec![ axeyum_verify::ast::Stmt::Let {
                        name: #bind.into(),
                        ty: #ty_tok,
                        value: axeyum_verify::ast::Expr::Binary {
                            op: axeyum_verify::ast::BinOp::#wrap_ident,
                            lhs: Box::new(#lhs),
                            rhs: Box::new(#rhs),
                        },
                    } ];
                    stmts.extend(vec![ #(#some_body),* ]);
                    stmts
                },
                els: vec![ #(#none_body),* ],
            }
        }))
    }

    /// `#[axeyum::unwind(K)] for var in 0..N { body }` — fully unrolled to
    /// `min(K, N)` iterations. The unwind attribute is required (it is the honest
    /// bound); the loop variable is an integer constant per iteration.
    fn lower_for(&mut self, forloop: &syn::ExprForLoop) -> syn::Result<TokenStream> {
        // A per-loop `#[axeyum::unwind(K)]` (nightly-only on expressions) is
        // honored if present; otherwise the function-level bound applies.
        let unwind = extract_unwind(&forloop.attrs)?
            .or(self.unwind)
            .ok_or_else(|| {
                syn::Error::new(
                    forloop.span(),
                    "axeyum::verify: a `for` loop needs an unwind bound — put \
                     `#[axeyum::unwind(K)]` on the function (alongside `#[axeyum::verify]`)",
                )
            })?;
        // Pattern: a simple `var`.
        let Pat::Ident(pi) = &*forloop.pat else {
            return Err(syn::Error::new(
                forloop.pat.span(),
                "axeyum::verify: loop variable must be a simple name",
            ));
        };
        let var = pi.ident.to_string();
        // Range: `lo..hi` with `lo == 0` and a literal `hi`.
        let (lo, hi, hi_ty) = parse_simple_range(&forloop.expr)?;
        if lo != 0 {
            return Err(syn::Error::new(
                forloop.expr.span(),
                "axeyum::verify: loop range must start at 0 (`0..N`)",
            ));
        }
        let bound = std::cmp::min(u128::from(unwind), hi);
        // Loop variable type: the upper-bound literal's suffix (`0..4u16`) sets
        // the width so the loop var composes with same-width arithmetic; default
        // u32 when unsuffixed.
        let var_ty = hi_ty.unwrap_or(Ty {
            width: Some(32),
            signed: false,
            is_size: false,
        });
        let var_ty_tok = var_ty.to_tokens();
        self.push_scope();
        self.declare(&var, var_ty);
        let body = self.lower_block(&forloop.body)?;
        self.pop_scope();
        Ok(quote! {
            axeyum_verify::ast::Stmt::For {
                var: #var.into(),
                var_ty: #var_ty_tok,
                bound: #bound,
                body: vec![ #(#body),* ],
            }
        })
    }

    /// `#[axeyum::unwind(K)] while cond { body }` — bounded model checking by
    /// unrolling up to `K` iterations (the function-level unwind bound, or a
    /// per-loop one). The guard is re-evaluated each iteration; panic classes in
    /// the body are checked on every feasible iteration. The result is a
    /// **bounded** guarantee (no bug within `K` iterations).
    fn lower_while(&mut self, w: &syn::ExprWhile) -> syn::Result<TokenStream> {
        if w.label.is_some() {
            return Err(syn::Error::new(
                w.span(),
                "axeyum::verify: labeled `while` loops are not supported",
            ));
        }
        let bound = extract_unwind(&w.attrs)?.or(self.unwind).ok_or_else(|| {
            syn::Error::new(
                w.span(),
                "axeyum::verify: a `while` loop needs an unwind bound — put \
                 `#[axeyum::unwind(K)]` on the function (alongside `#[axeyum::verify]`)",
            )
        })?;
        let bound = u128::from(bound);
        // `while let` desugars to a different node; only a boolean guard is in
        // fragment.
        let (cond, cty) = self.lower_expr(&w.cond)?;
        if cty != Ty::bool() {
            return Err(syn::Error::new(
                w.cond.span(),
                "axeyum::verify: `while` guard must be a boolean expression",
            ));
        }
        self.push_scope();
        let body = self.lower_block(&w.body)?;
        self.pop_scope();
        Ok(quote! {
            axeyum_verify::ast::Stmt::While {
                cond: #cond,
                bound: #bound,
                body: vec![ #(#body),* ],
            }
        })
    }

    fn lower_else(&mut self, expr: &Expr) -> syn::Result<Vec<TokenStream>> {
        match expr {
            Expr::Block(b) => self.lower_block(&b.block),
            Expr::If(_) => {
                let mut out = Vec::new();
                if let Some(s) = self.try_lower_stmt_expr(expr)? {
                    out.push(s);
                }
                Ok(out)
            }
            _ => Err(syn::Error::new(
                expr.span(),
                "axeyum::verify: unsupported else branch",
            )),
        }
    }

    /// Statement-form macros: `assert!`, `assert_eq!`, `panic!`, `unreachable!`,
    /// and the `axeyum_unwind!(K, for ..)` loop form.
    fn lower_macro_stmt(&mut self, mac: &syn::Macro) -> syn::Result<TokenStream> {
        let name = mac
            .path
            .get_ident()
            .map(ToString::to_string)
            .unwrap_or_default();
        match name.as_str() {
            "assert" => {
                let cond: Expr = mac.parse_body()?;
                let (c, _) = self.lower_expr(&cond)?;
                Ok(quote! { axeyum_verify::ast::Stmt::Assert(#c) })
            }
            "assert_eq" => {
                let args: AssertEqArgs = mac.parse_body()?;
                let (l, _) = self.lower_expr(&args.left)?;
                let (r, _) = self.lower_expr(&args.right)?;
                Ok(quote! {
                    axeyum_verify::ast::Stmt::Assert(axeyum_verify::ast::Expr::Binary {
                        op: axeyum_verify::ast::BinOp::Eq,
                        lhs: Box::new(#l),
                        rhs: Box::new(#r),
                    })
                })
            }
            "panic" | "unreachable" => Ok(quote! { axeyum_verify::ast::Stmt::Panic }),
            other => Err(syn::Error::new(
                mac.span(),
                format!("axeyum::verify: unsupported macro `{other}!`"),
            )),
        }
    }

    /// Lower a value expression into (tokens building `ast::Expr`, its Ty).
    #[allow(clippy::too_many_lines)]
    fn lower_expr(&mut self, expr: &Expr) -> syn::Result<(TokenStream, Ty)> {
        match expr {
            Expr::Lit(el) => lower_lit(&el.lit, expr.span()),
            Expr::Path(p) => {
                let name = path_ident(p)?;
                if self.lookup_option(&name).is_some() {
                    return Err(syn::Error::new(
                        p.span(),
                        format!(
                            "axeyum::verify: `{name}` is an `Option` — consume it with \
                             `.unwrap()`/`.unwrap_or(..)`/`.is_some()` or `match`, not as a value"
                        ),
                    ));
                }
                let ty = self.lookup(&name).ok_or_else(|| {
                    syn::Error::new(
                        p.span(),
                        format!("axeyum::verify: unknown variable `{name}`"),
                    )
                })?;
                Ok((quote! { axeyum_verify::ast::Expr::Var(#name.into()) }, ty))
            }
            Expr::Paren(p) => self.lower_expr(&p.expr),
            Expr::Group(g) => self.lower_expr(&g.expr),
            Expr::Binary(b) => self.lower_binary(b),
            Expr::Unary(u) => self.lower_unary(u),
            Expr::Cast(c) => {
                // `expr as uN/iN` — re-type the inner expr (a narrowing cast is
                // modeled as the target width; Phase 1 supports same-or-narrower
                // integer casts by reinterpreting the literal/var at the new Ty).
                let target = parse_scalar_ty(&c.ty)?;
                let (inner, _) = self.lower_expr(&c.expr)?;
                // We cannot change a symbol's width mid-stream soundly without an
                // extract/extend; restrict casts to literals (constant-fold).
                if let Expr::Lit(_) = &*c.expr {
                    // Re-lower the literal at the target type.
                    if let Expr::Lit(el) = &*c.expr {
                        return lower_lit_as(&el.lit, target, c.span());
                    }
                }
                let _ = inner;
                Err(syn::Error::new(
                    c.span(),
                    "axeyum::verify: only literal `as` casts are supported in Phase 1",
                ))
            }
            Expr::If(eif) => {
                // if-expression (both arms produce a value).
                let (cond, _) = self.lower_expr(&eif.cond)?;
                let then = block_tail_expr(&eif.then_branch)?;
                let (t, tty) = self.lower_expr(then)?;
                let Some((_, els_expr)) = &eif.else_branch else {
                    return Err(syn::Error::new(
                        eif.span(),
                        "axeyum::verify: an `if` used as a value needs an `else`",
                    ));
                };
                let (e, _) = self.lower_else_expr(els_expr)?;
                Ok((
                    quote! {
                        axeyum_verify::ast::Expr::Ite {
                            cond: Box::new(#cond),
                            then: Box::new(#t),
                            els: Box::new(#e),
                        }
                    },
                    tty,
                ))
            }
            Expr::MethodCall(mc) => self.lower_method_call(mc),
            Expr::Index(idx) => self.lower_index(idx),
            other => Err(syn::Error::new(
                other.span(),
                "axeyum::verify: unsupported expression (out of the bounded fragment)",
            )),
        }
    }

    /// `a[i]` — a fixed-length array index. The array must be a declared array
    /// parameter; the index is any integer expression. Out-of-bounds (`i >= len`)
    /// is a checked panic class handled by the runtime lowering.
    fn lower_index(&mut self, idx: &syn::ExprIndex) -> syn::Result<(TokenStream, Ty)> {
        let Expr::Path(p) = &*idx.expr else {
            return Err(syn::Error::new(
                idx.expr.span(),
                "axeyum::verify: only a simple array variable can be indexed (`a[i]`)",
            ));
        };
        let name = path_ident(p)?;
        let (elem, _len) = self.lookup_array(&name).ok_or_else(|| {
            syn::Error::new(
                p.span(),
                format!("axeyum::verify: `{name}` is not a known array parameter"),
            )
        })?;
        let (index_tok, _idx_ty) = self.lower_expr(&idx.index)?;
        let elem_tok = elem.to_tokens();
        Ok((
            quote! {
                axeyum_verify::ast::Expr::Index {
                    array: #name.into(),
                    index: Box::new(#index_tok),
                    ty: #elem_tok,
                }
            },
            elem,
        ))
    }

    fn lower_else_expr(&mut self, expr: &Expr) -> syn::Result<(TokenStream, Ty)> {
        match expr {
            Expr::Block(b) => {
                let tail = block_tail_expr(&b.block)?;
                self.lower_expr(tail)
            }
            // An `else if` or a bare value expression both lower directly.
            _ => self.lower_expr(expr),
        }
    }

    /// `.unwrap()` / `.expect(..)` on an `Option` value. In Phase 1 we require
    /// the receiver to be a call of the form `some_if(cond, value)` shape is not
    /// available; instead we model `opt.unwrap()` where `opt` was bound to a
    /// symbolic `Option` is out of scope — so we support the direct form
    /// `<bool-expr>.then_some(<value>).unwrap()` is also out. Phase 1 supports
    /// the explicit helper `axeyum_verify::opt(is_some, value).unwrap()` via a
    /// method-call shape recognized here.
    #[allow(clippy::too_many_lines)]
    fn lower_method_call(&mut self, mc: &syn::ExprMethodCall) -> syn::Result<(TokenStream, Ty)> {
        let method = mc.method.to_string();
        // A method on a virtual `Option` binding (`let x = a.checked_*(b)`).
        if let Expr::Path(p) = &*mc.receiver {
            if let Ok(name) = path_ident(p) {
                if let Some(b) = self.lookup_option(&name) {
                    return self.lower_option_method(&method, mc, &b);
                }
            }
        }
        if method == "unwrap" || method == "expect" {
            // Receiver must be `opt(is_some, value)` — our recognized Option ctor.
            if let Expr::Call(call) = &*mc.receiver {
                if let Expr::Path(p) = &*call.func {
                    let fname = p.path.segments.last().map(|s| s.ident.to_string());
                    if fname.as_deref() == Some("opt") && call.args.len() == 2 {
                        let mut it = call.args.iter();
                        let is_some = it.next().unwrap();
                        let value = it.next().unwrap();
                        let (cond, _) = self.lower_expr(is_some)?;
                        let (val, vty) = self.lower_expr(value)?;
                        return Ok((
                            quote! {
                                axeyum_verify::ast::Expr::UnwrapOption {
                                    is_some: Box::new(#cond),
                                    value: Box::new(#val),
                                }
                            },
                            vty,
                        ));
                    }
                }
            }
            // `recv.checked_{add,sub,mul}(arg).unwrap()` (or `.expect(..)`) is
            // exactly the plain panicking op: checked-then-unwrap panics iff the
            // op overflows, which is what `BinOp::{Add,Sub,Mul}` already records.
            if let Expr::MethodCall(inner) = &*mc.receiver {
                if let Some(op) = match inner.method.to_string().as_str() {
                    "checked_add" => Some("Add"),
                    "checked_sub" => Some("Sub"),
                    "checked_mul" => Some("Mul"),
                    _ => None,
                } {
                    if inner.args.len() != 1 {
                        return Err(syn::Error::new(
                            inner.span(),
                            "axeyum::verify: `checked_*` takes exactly one argument",
                        ));
                    }
                    let (lhs, lty) = self.lower_expr(&inner.receiver)?;
                    let arg = inner.args.first().unwrap();
                    let (rhs, _rty) = if is_untyped_int_lit(arg) && lty.width.is_some() {
                        if let Expr::Lit(el) = arg {
                            lower_lit_as(&el.lit, lty, el.span())?
                        } else {
                            self.lower_expr(arg)?
                        }
                    } else {
                        self.lower_expr(arg)?
                    };
                    let op_ident = format_ident!("{}", op);
                    return Ok((
                        quote! {
                            axeyum_verify::ast::Expr::Binary {
                                op: axeyum_verify::ast::BinOp::#op_ident,
                                lhs: Box::new(#lhs),
                                rhs: Box::new(#rhs),
                            }
                        },
                        lty,
                    ));
                }
            }
            return Err(syn::Error::new(
                mc.span(),
                "axeyum::verify: `unwrap`/`expect` is supported only on the modeled \
                 `opt(is_some, value)` Option or a `checked_{add,sub,mul}(..)` chain \
                 in Phase 1 (see STATUS.md)",
            ));
        }
        // Wrapping arithmetic `recv.wrapping_{add,sub,mul}(arg)` → a modular
        // (never-panicking) binary op. Both operands must share an integer type.
        if let Some(variant) = match method.as_str() {
            "wrapping_add" => Some("WrappingAdd"),
            "wrapping_sub" => Some("WrappingSub"),
            "wrapping_mul" => Some("WrappingMul"),
            "saturating_add" => Some("SaturatingAdd"),
            "saturating_sub" => Some("SaturatingSub"),
            "saturating_mul" => Some("SaturatingMul"),
            "min" => Some("Min"),
            "max" => Some("Max"),
            _ => None,
        } {
            if mc.args.len() != 1 {
                return Err(syn::Error::new(
                    mc.span(),
                    format!("axeyum::verify: `.{method}()` takes exactly one argument"),
                ));
            }
            let (lhs, lty) = self.lower_expr(&mc.receiver)?;
            let arg = mc.args.first().unwrap();
            // Coerce an untyped int literal argument to the receiver's type.
            let (rhs, _rty) = if is_untyped_int_lit(arg) && lty.width.is_some() {
                if let Expr::Lit(el) = arg {
                    lower_lit_as(&el.lit, lty, el.span())?
                } else {
                    self.lower_expr(arg)?
                }
            } else {
                self.lower_expr(arg)?
            };
            let op_ident = format_ident!("{}", variant);
            return Ok((
                quote! {
                    axeyum_verify::ast::Expr::Binary {
                        op: axeyum_verify::ast::BinOp::#op_ident,
                        lhs: Box::new(#lhs),
                        rhs: Box::new(#rhs),
                    }
                },
                lty,
            ));
        }
        // `recv.checked_{add,sub,mul}(arg).unwrap_or(default)` — Option-flow with a
        // fallback. Desugar to `ite(!overflows, wrapping_op(a, arg), default)`: on
        // no overflow the value is the (wrapping == real) result, else the default.
        // Uses the never-panicking `WrappingOp` + the boolean `Overflows` node, so
        // no spurious overflow panic is recorded.
        if method == "unwrap_or" {
            if mc.args.len() != 1 {
                return Err(syn::Error::new(
                    mc.span(),
                    "axeyum::verify: `.unwrap_or()` takes exactly one argument",
                ));
            }
            if let Expr::MethodCall(inner) = &*mc.receiver {
                if let Some((ovf_op, wrap_op)) = match inner.method.to_string().as_str() {
                    "checked_add" => Some(("Add", "WrappingAdd")),
                    "checked_sub" => Some(("Sub", "WrappingSub")),
                    "checked_mul" => Some(("Mul", "WrappingMul")),
                    _ => None,
                } {
                    if inner.args.len() != 1 {
                        return Err(syn::Error::new(
                            inner.span(),
                            "axeyum::verify: `checked_*` takes exactly one argument",
                        ));
                    }
                    let (lhs, lty) = self.lower_expr(&inner.receiver)?;
                    let coerce = |s: &mut Self, e: &Expr| -> syn::Result<TokenStream> {
                        Ok(if is_untyped_int_lit(e) && lty.width.is_some() {
                            if let Expr::Lit(el) = e {
                                lower_lit_as(&el.lit, lty, el.span())?.0
                            } else {
                                s.lower_expr(e)?.0
                            }
                        } else {
                            s.lower_expr(e)?.0
                        })
                    };
                    let arg = coerce(self, inner.args.first().unwrap())?;
                    let default = coerce(self, mc.args.first().unwrap())?;
                    let ovf_ident = format_ident!("{}", ovf_op);
                    let wrap_ident = format_ident!("{}", wrap_op);
                    return Ok((
                        quote! {
                            axeyum_verify::ast::Expr::Ite {
                                cond: Box::new(axeyum_verify::ast::Expr::Unary {
                                    op: axeyum_verify::ast::UnOp::Not,
                                    operand: Box::new(axeyum_verify::ast::Expr::Overflows {
                                        op: axeyum_verify::ast::BinOp::#ovf_ident,
                                        lhs: Box::new(#lhs),
                                        rhs: Box::new(#arg),
                                    }),
                                }),
                                then: Box::new(axeyum_verify::ast::Expr::Binary {
                                    op: axeyum_verify::ast::BinOp::#wrap_ident,
                                    lhs: Box::new(#lhs),
                                    rhs: Box::new(#arg),
                                }),
                                els: Box::new(#default),
                            }
                        },
                        lty,
                    ));
                }
            }
            return Err(syn::Error::new(
                mc.span(),
                "axeyum::verify: `.unwrap_or()` is supported only on a \
                 `checked_{add,sub,mul}(..)` chain in Phase 1",
            ));
        }
        // `recv.rotate_left(N)` / `recv.rotate_right(N)` by a *constant* amount.
        if let Some(left) = match method.as_str() {
            "rotate_left" => Some(true),
            "rotate_right" => Some(false),
            _ => None,
        } {
            if mc.args.len() != 1 {
                return Err(syn::Error::new(
                    mc.span(),
                    format!("axeyum::verify: `.{method}()` takes exactly one argument"),
                ));
            }
            let arg = mc.args.first().unwrap();
            let Expr::Lit(el) = arg else {
                return Err(syn::Error::new(
                    arg.span(),
                    "axeyum::verify: rotate amount must be a constant integer literal",
                ));
            };
            let Lit::Int(li) = &el.lit else {
                return Err(syn::Error::new(
                    arg.span(),
                    "axeyum::verify: rotate amount must be an integer literal",
                ));
            };
            let by: u32 = li.base10_parse()?;
            let (operand, oty) = self.lower_expr(&mc.receiver)?;
            return Ok((
                quote! {
                    axeyum_verify::ast::Expr::Rotate {
                        left: #left,
                        by: #by,
                        operand: Box::new(#operand),
                    }
                },
                oty,
            ));
        }
        // `recv.pow(N)` with a *constant* exponent N — fold to N-1 nested checked
        // `Mul`s (N==0 ⇒ 1), exactly matching Rust's `pow` overflow-panic at each
        // step. A symbolic exponent is out of the bounded fragment.
        if method == "pow" {
            if mc.args.len() != 1 {
                return Err(syn::Error::new(
                    mc.span(),
                    "axeyum::verify: `.pow()` takes exactly one argument",
                ));
            }
            let arg = mc.args.first().unwrap();
            let Expr::Lit(el) = arg else {
                return Err(syn::Error::new(
                    arg.span(),
                    "axeyum::verify: `.pow()` exponent must be a constant integer literal",
                ));
            };
            let Lit::Int(li) = &el.lit else {
                return Err(syn::Error::new(
                    arg.span(),
                    "axeyum::verify: `.pow()` exponent must be an integer literal",
                ));
            };
            let n: u32 = li.base10_parse()?;
            if n > 64 {
                return Err(syn::Error::new(
                    arg.span(),
                    "axeyum::verify: `.pow()` exponent is bounded to ≤ 64 in this fragment",
                ));
            }
            let (base, bty) = self.lower_expr(&mc.receiver)?;
            if n == 0 {
                let one = syn::LitInt::new("1", mc.span());
                let (one_tok, _) = lower_lit_as(&Lit::Int(one), bty, mc.span())?;
                return Ok((one_tok, bty));
            }
            let mut acc = base.clone();
            for _ in 1..n {
                acc = quote! {
                    axeyum_verify::ast::Expr::Binary {
                        op: axeyum_verify::ast::BinOp::Mul,
                        lhs: Box::new(#acc),
                        rhs: Box::new(#base),
                    }
                };
            }
            return Ok((acc, bty));
        }
        // `recv.abs()` (signed) — desugar to `ite(a < 0, -a, a)`. The `-a` arm
        // records the `iN::MIN` negation-overflow panic, which is *exactly* the
        // condition under which `abs` panics, so this is sound and precise.
        if method == "abs" {
            if !mc.args.is_empty() {
                return Err(syn::Error::new(
                    mc.span(),
                    "axeyum::verify: `.abs()` takes no arguments",
                ));
            }
            let (recv, lty) = self.lower_expr(&mc.receiver)?;
            let zero_lit = syn::LitInt::new("0", mc.span());
            let (zero, _) = lower_lit_as(&Lit::Int(zero_lit), lty, mc.span())?;
            return Ok((
                quote! {
                    axeyum_verify::ast::Expr::Ite {
                        cond: Box::new(axeyum_verify::ast::Expr::Binary {
                            op: axeyum_verify::ast::BinOp::Lt,
                            lhs: Box::new(#recv),
                            rhs: Box::new(#zero),
                        }),
                        then: Box::new(axeyum_verify::ast::Expr::Unary {
                            op: axeyum_verify::ast::UnOp::Neg,
                            operand: Box::new(#recv),
                        }),
                        els: Box::new(#recv),
                    }
                },
                lty,
            ));
        }
        Err(syn::Error::new(
            mc.span(),
            format!("axeyum::verify: unsupported method `.{method}()`"),
        ))
    }

    fn lower_binary(&mut self, b: &ExprBinary) -> syn::Result<(TokenStream, Ty)> {
        let (mut l, mut lty) = self.lower_expr(&b.left)?;
        let (mut r, mut rty) = self.lower_expr(&b.right)?;
        // Coerce an unsuffixed integer literal operand to the other operand's
        // integer type (Rust's literal-inference, restricted to the direct
        // operand). This makes `r <= 15` type-check when `r: u8`.
        if lty != rty {
            if is_untyped_int_lit(&b.right) && lty.width.is_some() {
                if let Expr::Lit(el) = &*b.right {
                    let (nr, nrty) = lower_lit_as(&el.lit, lty, el.span())?;
                    r = nr;
                    rty = nrty;
                }
            } else if is_untyped_int_lit(&b.left) && rty.width.is_some() {
                if let Expr::Lit(el) = &*b.left {
                    let (nl, nlty) = lower_lit_as(&el.lit, rty, el.span())?;
                    l = nl;
                    lty = nlty;
                }
            }
        }
        let (op_tok, result_ty) =
            bin_op(&b.op, lty, rty).map_err(|m| syn::Error::new(b.span(), m))?;
        Ok((
            quote! {
                axeyum_verify::ast::Expr::Binary {
                    op: #op_tok,
                    lhs: Box::new(#l),
                    rhs: Box::new(#r),
                }
            },
            result_ty,
        ))
    }

    fn lower_unary(&mut self, u: &ExprUnary) -> syn::Result<(TokenStream, Ty)> {
        let (inner, ty) = self.lower_expr(&u.expr)?;
        let op_tok = match u.op {
            SynUnOp::Not(_) => quote! { axeyum_verify::ast::UnOp::Not },
            SynUnOp::Neg(_) => quote! { axeyum_verify::ast::UnOp::Neg },
            _ => {
                return Err(syn::Error::new(
                    u.span(),
                    "axeyum::verify: unsupported unary operator",
                ));
            }
        };
        Ok((
            quote! {
                axeyum_verify::ast::Expr::Unary { op: #op_tok, operand: Box::new(#inner) }
            },
            ty,
        ))
    }
}

fn lower_lit(lit: &Lit, span: proc_macro2::Span) -> syn::Result<(TokenStream, Ty)> {
    match lit {
        Lit::Bool(b) => {
            let v = b.value;
            Ok((quote! { axeyum_verify::ast::Expr::BoolLit(#v) }, Ty::bool()))
        }
        Lit::Int(li) => {
            // Default integer literal type: i32 unless suffixed (uN/iN).
            let suffix = li.suffix();
            let ty = if suffix.is_empty() {
                Ty {
                    width: Some(32),
                    signed: true,
                    is_size: false,
                }
            } else {
                parse_suffix_ty(suffix)
                    .ok_or_else(|| syn::Error::new(span, "axeyum::verify: bad literal suffix"))?
            };
            lower_lit_as(lit, ty, span)
        }
        _ => Err(syn::Error::new(
            span,
            "axeyum::verify: unsupported literal (only integer/bool)",
        )),
    }
}

fn lower_lit_as(lit: &Lit, ty: Ty, span: proc_macro2::Span) -> syn::Result<(TokenStream, Ty)> {
    let Lit::Int(li) = lit else {
        return Err(syn::Error::new(
            span,
            "axeyum::verify: expected an integer literal",
        ));
    };
    let value: u128 = li
        .base10_parse()
        .map_err(|_| syn::Error::new(span, "axeyum::verify: integer literal out of range"))?;
    let ty_tok = ty.to_tokens();
    Ok((
        quote! { axeyum_verify::ast::Expr::IntLit { value: #value, ty: #ty_tok } },
        ty,
    ))
}

/// Map a syn binary op + operand types to (runtime `BinOp` tokens, result `Ty`).
fn bin_op(op: &SynBinOp, lty: Ty, _rty: Ty) -> Result<(TokenStream, Ty), String> {
    use SynBinOp::{
        Add, And, BitAnd, BitOr, BitXor, Div, Eq, Ge, Gt, Le, Lt, Mul, Ne, Or, Rem, Shl, Shr, Sub,
    };
    let bool_ty = Ty::bool();
    let (variant, result) = match op {
        Add(_) => ("Add", lty),
        Sub(_) => ("Sub", lty),
        Mul(_) => ("Mul", lty),
        Div(_) => ("Div", lty),
        Rem(_) => ("Rem", lty),
        BitAnd(_) => ("BitAnd", lty),
        BitOr(_) => ("BitOr", lty),
        BitXor(_) => ("BitXor", lty),
        Shl(_) => ("Shl", lty),
        Shr(_) => ("Shr", lty),
        Eq(_) => ("Eq", bool_ty),
        Ne(_) => ("Ne", bool_ty),
        Lt(_) => ("Lt", bool_ty),
        Le(_) => ("Le", bool_ty),
        Gt(_) => ("Gt", bool_ty),
        Ge(_) => ("Ge", bool_ty),
        And(_) => ("And", bool_ty),
        Or(_) => ("Or", bool_ty),
        _ => return Err("axeyum::verify: unsupported binary operator".into()),
    };
    let ident = format_ident!("{}", variant);
    Ok((quote! { axeyum_verify::ast::BinOp::#ident }, result))
}

fn parse_suffix_ty(suffix: &str) -> Option<Ty> {
    if suffix == "bool" {
        return Some(Ty::bool());
    }
    if suffix == "usize" {
        return Some(Ty {
            width: Some(USIZE_WIDTH),
            signed: false,
            is_size: true,
        });
    }
    if suffix == "isize" {
        return Some(Ty {
            width: Some(USIZE_WIDTH),
            signed: true,
            is_size: true,
        });
    }
    let (signed, rest) = if let Some(r) = suffix.strip_prefix('u') {
        (false, r)
    } else if let Some(r) = suffix.strip_prefix('i') {
        (true, r)
    } else {
        return None;
    };
    let width: u32 = rest.parse().ok()?;
    if (1..=128).contains(&width) {
        Some(Ty {
            width: Some(width),
            signed,
            is_size: false,
        })
    } else {
        None
    }
}

/// Whether `expr` is an integer literal with no type suffix (so it can adopt the
/// type of its sibling operand, like Rust's literal inference).
fn is_untyped_int_lit(expr: &Expr) -> bool {
    matches!(expr, Expr::Lit(el) if matches!(&el.lit, Lit::Int(li) if li.suffix().is_empty()))
}

fn path_ident(p: &syn::ExprPath) -> syn::Result<String> {
    p.path
        .get_ident()
        .map(ToString::to_string)
        .ok_or_else(|| syn::Error::new(p.span(), "axeyum::verify: expected a simple identifier"))
}

/// The tail (return) expression of a block, requiring exactly one trailing expr.
fn block_tail_expr(block: &Block) -> syn::Result<&Expr> {
    match block.stmts.last() {
        Some(Stmt::Expr(e, None)) => Ok(e),
        _ => Err(syn::Error::new(
            block.span(),
            "axeyum::verify: an `if`-expression branch must end in a value expression",
        )),
    }
}

/// Maps a `checked_*` method name to its (overflow-predicate op, wrapping-value
/// op) `BinOp` variant names, or `None` if it is not a modeled checked op.
fn checked_ops(method: &str) -> Option<(&'static str, &'static str)> {
    match method {
        "checked_add" => Some(("Add", "WrappingAdd")),
        "checked_sub" => Some(("Sub", "WrappingSub")),
        "checked_mul" => Some(("Mul", "WrappingMul")),
        _ => None,
    }
}

/// Reads the unwind bound `K` from an `#[axeyum::unwind(K)]` (or `#[unwind(K)]`)
/// attribute, if present. Errors on a malformed attribute.
fn extract_unwind(attrs: &[syn::Attribute]) -> syn::Result<Option<u64>> {
    for attr in attrs {
        let last = attr.path().segments.last().map(|s| s.ident.to_string());
        if last.as_deref() == Some("unwind") {
            let k: syn::LitInt = attr.parse_args()?;
            return Ok(Some(k.base10_parse()?));
        }
    }
    Ok(None)
}

/// Parses a `lo..hi` range with integer-literal bounds; returns
/// `(lo, hi, hi_type)` where `hi_type` is the suffix type of `hi` (e.g. `u16`
/// in `0..4u16`).
fn parse_simple_range(expr: &Expr) -> syn::Result<(u128, u128, Option<Ty>)> {
    let Expr::Range(r) = expr else {
        return Err(syn::Error::new(
            expr.span(),
            "axeyum::verify: loop must iterate a literal range `0..N`",
        ));
    };
    let lo = match r.start.as_deref() {
        Some(Expr::Lit(el)) => lit_u128(&el.lit, el.span())?,
        None => 0,
        Some(other) => {
            return Err(syn::Error::new(
                other.span(),
                "axeyum::verify: range start must be a literal",
            ));
        }
    };
    let (hi, hi_ty) = match r.end.as_deref() {
        Some(Expr::Lit(el)) => {
            let v = lit_u128(&el.lit, el.span())?;
            let ty = if let Lit::Int(li) = &el.lit {
                if li.suffix().is_empty() {
                    None
                } else {
                    parse_suffix_ty(li.suffix())
                }
            } else {
                None
            };
            (v, ty)
        }
        _ => {
            return Err(syn::Error::new(
                expr.span(),
                "axeyum::verify: range end must be an integer literal",
            ));
        }
    };
    // `..=` is inclusive.
    let hi = if matches!(r.limits, syn::RangeLimits::Closed(_)) {
        hi + 1
    } else {
        hi
    };
    Ok((lo, hi, hi_ty))
}

fn lit_u128(lit: &Lit, span: proc_macro2::Span) -> syn::Result<u128> {
    match lit {
        Lit::Int(li) => li
            .base10_parse()
            .map_err(|_| syn::Error::new(span, "axeyum::verify: integer literal out of range")),
        _ => Err(syn::Error::new(
            span,
            "axeyum::verify: expected an integer literal",
        )),
    }
}

/// `assert_eq!(a, b)` argument parser.
struct AssertEqArgs {
    left: Expr,
    right: Expr,
}

impl syn::parse::Parse for AssertEqArgs {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let left: Expr = input.parse()?;
        let _: syn::Token![,] = input.parse()?;
        let right: Expr = input.parse()?;
        // ignore any trailing format args
        while !input.is_empty() {
            let _: proc_macro2::TokenTree = input.parse()?;
        }
        Ok(AssertEqArgs { left, right })
    }
}
