//! Check that a `String` literal in a **real** `lean4export` stream is not
//! merely admitted but *computes*, in the environment Lean itself exported.
//!
//! The census answers "did the trusted gate refuse anything"; it does not answer
//! "does the literal mean what Lean means by it". This probe does, against
//! Lean's own `String`, `String.ofList`, `Char.ofNat` and `List` rather than a
//! test fixture shaped like them:
//!
//! 1. reduce the named definition to a weak head normal form and require a
//!    string literal;
//! 2. build `String.ofList (List.cons Char (Char.ofNat c₀) … (List.nil Char))`
//!    from the **imported** declarations, for the payload's Unicode scalars; and
//! 3. require the kernel to identify the two, and to *refuse* a reordered list.
//!
//! ```text
//! cargo run --release -p axeyum-lean-import --example string_literal_reduction_probe -- \
//!     stream.ndjson importStringLiteral
//! ```

use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::PathBuf;

use axeyum_lean_import::{ImportLimits, import_ndjson};
use axeyum_lean_kernel::{ExprId, Kernel, Lit, NameId};

fn child(kernel: &mut Kernel, parent: NameId, component: &str) -> NameId {
    kernel.name_str(parent, component)
}

/// `String.ofList (List.cons Char c₀ … (List.nil Char))` over the given scalars.
fn of_list_of_scalars(kernel: &mut Kernel, scalars: &[u32]) -> ExprId {
    let anon = kernel.anon();
    let string = child(kernel, anon, "String");
    let of_list = child(kernel, string, "ofList");
    let char_name = child(kernel, anon, "Char");
    let char_of_nat = child(kernel, char_name, "ofNat");
    let list = child(kernel, anon, "List");
    let list_nil = child(kernel, list, "nil");
    let list_cons = child(kernel, list, "cons");
    let zero = kernel.level_zero();
    let char_type = kernel.const_(char_name, vec![]);

    let nil = kernel.const_(list_nil, vec![zero]);
    let mut acc = kernel.app(nil, char_type);
    let cons = kernel.const_(list_cons, vec![zero]);
    let cons = kernel.app(cons, char_type);
    let of_nat = kernel.const_(char_of_nat, vec![]);
    for &scalar in scalars.iter().rev() {
        let code = kernel.lit(Lit::nat(scalar));
        let character = kernel.app(of_nat, code);
        let step = kernel.app(cons, character);
        acc = kernel.app(step, acc);
    }
    let head = kernel.const_(of_list, vec![]);
    kernel.app(head, acc)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut arguments = std::env::args_os().skip(1);
    let path = arguments
        .next()
        .map(PathBuf::from)
        .ok_or("usage: string_literal_reduction_probe <export.ndjson|-> [declaration]")?;
    let target = arguments.next().map_or_else(
        || "importStringLiteral".to_owned(),
        |raw| raw.to_string_lossy().into_owned(),
    );

    let reader: Box<dyn BufRead> = if path.as_os_str() == "-" {
        Box::new(BufReader::new(std::io::stdin()))
    } else {
        Box::new(BufReader::new(File::open(&path)?))
    };
    let (mut kernel, report) = import_ndjson(reader, ImportLimits::default())?.into_parts();

    let value = kernel
        .environment()
        .iter()
        .find_map(|(_, declaration)| {
            (kernel.display_name(declaration.name()).to_string() == target)
                .then(|| declaration.value())
                .flatten()
        })
        .ok_or_else(|| format!("{target}: not a definition in this stream"))?;

    let normal = kernel.whnf(value);
    let payload = match kernel.expr_node(normal) {
        axeyum_lean_kernel::ExprNode::Lit(Lit::Str(payload)) => payload.clone(),
        other => {
            return Err(format!("{target}: did not reduce to a string literal: {other:?}").into());
        }
    };
    let scalars: Vec<u32> = payload.chars().map(u32::from).collect();

    let inferred = kernel
        .infer(normal)
        .map_err(|error| format!("{target}: the literal has no type: {error:?}"))?;
    let expansion = of_list_of_scalars(&mut kernel, &scalars);
    let agrees = kernel.def_eq(normal, expansion);

    // A control in the same run: the same scalars in the wrong order must NOT be
    // identified with the literal, or the agreement above measures nothing.
    let mut reordered: Vec<u32> = scalars.clone();
    reordered.reverse();
    let refuses_reordered = if reordered == scalars {
        true
    } else {
        let wrong = of_list_of_scalars(&mut kernel, &reordered);
        !kernel.def_eq(normal, wrong)
    };

    let rendered: Vec<String> = scalars.iter().map(u32::to_string).collect();
    println!(
        "STRING-LITERAL|declaration={target}|decl_records={}|admitted={}|type={}|scalars={}|of_list_agrees={agrees}|reordered_refused={refuses_reordered}",
        report.declaration_records,
        report.admitted_declarations,
        kernel.render_lean(inferred),
        rendered.join(","),
    );
    if !(agrees && refuses_reordered) {
        return Err("the imported literal did not compute as Lean's String".into());
    }
    Ok(())
}
