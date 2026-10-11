//! Writes the typed `.pyi` package for `axeyum._native` from the Rust signatures.
//!
//! Run it as
//!
//! ```sh
//! cargo run -p axeyum-py --features stub-gen --bin stub_gen
//! ```
//!
//! and it rewrites `python/axeyum/_native/**/__init__.pyi` in place. The
//! `stub-gen` feature is required (`required-features` in `Cargo.toml`), because
//! without it nothing has been submitted to the inventory and this binary would
//! cheerfully write an EMPTY stub package over the real one. That is the
//! repository's standing failure mode -- a tool pointed at nothing reports a
//! clean result -- so the count is printed and a zero is a hard failure.
//!
//! # Errors
//!
//! Fails when the workspace `pyproject.toml` cannot be read, when the inventory
//! is empty, or when a stub file cannot be written.

fn main() -> pyo3_stub_gen::Result<()> {
    let mut info = _native::stub_info()?;
    let qualified_int_annotations = qualify_shadowed_int_annotations(&mut info);

    let modules = info.modules.len();
    let items: usize = info
        .modules
        .values()
        .map(|module| {
            module.class.len() + module.enum_.len() + module.function.len() + module.variables.len()
        })
        .sum();

    if items == 0 {
        anyhow::bail!(
            "STUB_GEN|FAIL the inventory is empty -- nothing was written. Either the \
             `stub-gen` feature is off (so no `#[gen_stub_*]` expanded), or the \
             gatherer was linked without the library."
        );
    }

    info.generate()?;
    println!(
        "STUB_GEN|modules={modules}|items={items}|qualified_int_annotations={qualified_int_annotations}"
    );
    Ok(())
}

// Bound<PyInt> is rendered as unqualified `int` by the gatherer. A class with
// an `int` method shadows that name in annotations (notably Expr.rat/pow).
// Qualify the structured type metadata before rendering rather than patching
// generated text or silencing mypy's valid-type check.
fn qualify_shadowed_int_annotations(info: &mut pyo3_stub_gen::StubInfo) -> usize {
    let mut changed = 0;
    for module in info.modules.values_mut() {
        for class in module.class.values_mut() {
            if !class.methods.contains_key("int") {
                continue;
            }
            for methods in class.methods.values_mut() {
                for method in methods {
                    let params = &mut method.parameters;
                    for param in params
                        .positional_only
                        .iter_mut()
                        .chain(params.positional_or_keyword.iter_mut())
                        .chain(params.keyword_only.iter_mut())
                        .chain(params.varargs.iter_mut())
                        .chain(params.varkw.iter_mut())
                    {
                        changed += usize::from(qualify_int_type(&mut param.type_info));
                    }
                    changed += usize::from(qualify_int_type(&mut method.r#return));
                }
            }
        }
    }
    changed
}

fn qualify_int_type(info: &mut pyo3_stub_gen::TypeInfo) -> bool {
    let qualified = match info.name.as_str() {
        "int" => "builtins.int",
        "typing.Optional[int]" => "typing.Optional[builtins.int]",
        _ => return false,
    };
    qualified.clone_into(&mut info.name);
    info.import.insert("builtins".into());
    true
}
