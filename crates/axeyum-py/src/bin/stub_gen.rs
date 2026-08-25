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
    let info = _native::stub_info()?;

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
    println!("STUB_GEN|modules={modules}|items={items}");
    Ok(())
}
