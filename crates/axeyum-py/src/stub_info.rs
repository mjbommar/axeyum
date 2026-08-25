//! The `pyo3-stub-gen` inventory gatherer (feature `stub-gen` only).
//!
//! `pyo3_stub_gen::define_stub_info_gatherer!` looks for `pyproject.toml` beside
//! `Cargo.toml`. Ours is at the WORKSPACE root, two directories up, because
//! `[tool.maturin] manifest-path` points down at this crate rather than the
//! other way round. So the gatherer is written out rather than generated: the
//! macro would compile and then fail at run time with a file-not-found on a path
//! nobody would think to look at.
//!
//! It has to live in THIS crate, not in `src/bin/stub_gen.rs`: `inventory`
//! collects the submitted records per linked library, and a binary that only
//! depends on the library sees an empty inventory unless the gathering function
//! is itself compiled into that library.

use std::path::Path;

use pyo3_stub_gen::{Result, StubInfo};

/// Every `#[gen_stub_*]`-annotated item in this crate, resolved against the
/// workspace `pyproject.toml`.
///
/// # Errors
///
/// Fails when the workspace `pyproject.toml` is missing or does not parse.
pub fn stub_info() -> Result<StubInfo> {
    let manifest_dir: &Path = env!("CARGO_MANIFEST_DIR").as_ref();
    let workspace_root = manifest_dir
        .parent()
        .and_then(Path::parent)
        .ok_or_else(|| {
            anyhow::anyhow!(
                "CARGO_MANIFEST_DIR ({}) has fewer than two ancestors; the workspace \
             pyproject.toml cannot be located",
                manifest_dir.display()
            )
        })?;
    StubInfo::from_pyproject_toml(workspace_root.join("pyproject.toml"))
}

/// Registers an exception created by `pyo3::create_exception!` with the stub
/// inventory.
///
/// `pyo3_stub_gen::create_exception!` exists for this, but adopting it would
/// make `pyo3-stub-gen` a **mandatory** dependency of the default build: the
/// macro invocation *is* the exception's definition, so it cannot sit behind
/// `#[cfg(feature = "stub-gen")]`. This submits the same `PyClassInfo` from a
/// separate, fully feature-gated block, leaving `create_exception!` as `PyO3`
/// wrote it.
///
/// `$base` is the Rust type of the base exception, which must itself have been
/// registered here or be one of `PyO3`'s (`pyo3-stub-gen` covers those).
/// `$members` are attributes the exception carries that no generator can see --
/// an exception's payload is attached with `setattr` at the raise site, so it
/// exists in no signature and in no `#[pyclass]`.
macro_rules! stub_exception {
    ($module:literal, $name:ident, $base:ty, $doc:literal $(, $member:literal : $member_ty:ty = $member_doc:literal)* $(,)?) => {
        impl ::pyo3_stub_gen::PyStubType for $name {
            fn type_output() -> ::pyo3_stub_gen::TypeInfo {
                ::pyo3_stub_gen::TypeInfo::with_module(
                    stringify!($name),
                    ::pyo3_stub_gen::ModuleRef::Named($module.to_string()),
                )
            }
        }

        ::pyo3_stub_gen::inventory::submit! {
            ::pyo3_stub_gen::type_info::PyClassInfo {
                struct_id: ::std::any::TypeId::of::<$name>,
                pyclass_name: stringify!($name),
                module: Some($module),
                doc: $doc,
                getters: &[
                    $(::pyo3_stub_gen::type_info::MemberInfo {
                        name: $member,
                        r#type: <$member_ty as ::pyo3_stub_gen::PyStubType>::type_output,
                        doc: $member_doc,
                        default: None,
                        deprecated: None,
                    },)*
                ],
                setters: &[],
                bases: &[|| <$base as ::pyo3_stub_gen::PyStubType>::type_output()],
                has_eq: false,
                has_ord: false,
                has_hash: false,
                has_str: false,
                subclass: true,
            }
        }
    };
}

pub(crate) use stub_exception;
