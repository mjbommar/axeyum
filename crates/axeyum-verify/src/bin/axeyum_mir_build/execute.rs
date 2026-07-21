use std::ffi::{OsStr, OsString};
use std::fs::{self, OpenOptions};
use std::io::Write as _;
use std::path::{Component, Path, PathBuf};
use std::process::Command;

use axeyum_ir::{Sort, TermArena, TermId, render};
use axeyum_verify::reflect::mir::checked::{
    CheckedMirMemory, CheckedMirScalar, MirMemoryConfig, MirScalarConfig,
    reflect_bounded_memory_checked, reflect_scalar_into_checked,
};
use axeyum_verify::reflect::mir::syntax::{Function, MirType, ParseErrorKind, parse_function};

use crate::ToolError;
use crate::args::{Config, Profile, Target};
use crate::json::{quote, string_array};

const SUMMARY_SCHEMA: &str = "axeyum.verify-mir-build.v1";
const SCALAR_SUMMARY_SCHEMA: &str = "axeyum.verify-mir-build-scalar-contract.v1";
const REGISTERED_RUSTC_VERBOSE: &[&str] = &[
    "rustc 1.97.0-nightly (f53b654a8 2026-04-30)",
    "binary: rustc",
    "commit-hash: f53b654a8882fd5fc036c4ca7a4ff41ce32497a6",
    "commit-date: 2026-04-30",
    "host: x86_64-unknown-linux-gnu",
    "release: 1.97.0-nightly",
    "LLVM version: 22.1.4",
];

struct Prepared {
    manifest: PathBuf,
    cargo: PathBuf,
    rustc: PathBuf,
    cargo_version: String,
    rustc_version: String,
}

struct SummaryInputs<'a> {
    config: &'a Config,
    prepared: &'a Prepared,
    cargo_args: &'a [OsString],
    rustc_args: &'a [OsString],
    capture: &'a std::process::Output,
    function: &'a Function,
    reflected: &'a CheckedMirMemory,
}

struct ScalarSummaryInputs<'a> {
    config: &'a Config,
    prepared: &'a Prepared,
    cargo_args: &'a [OsString],
    rustc_args: &'a [OsString],
    capture: &'a std::process::Output,
    function: &'a Function,
    arena: &'a TermArena,
    reflected: &'a CheckedMirScalar,
}

fn prepare(config: &Config) -> Result<Prepared, ToolError> {
    let manifest = canonical_file(&config.manifest_path, "manifest_path")?;
    if manifest.file_name() != Some(OsStr::new("Cargo.toml")) {
        return Err(ToolError::new(
            "manifest_path",
            "--manifest-path must name Cargo.toml",
        ));
    }
    let cargo = canonical_file(&config.cargo, "cargo_path")?;
    let rustc = canonical_file(&config.rustc, "rustc_path")?;
    let output_parent = canonical_parent(&config.output, "output_path")?;
    if config.output.exists() {
        return Err(ToolError::new(
            "output_exists",
            format!("output already exists: {}", config.output.display()),
        ));
    }
    let target_parent = canonical_parent(&config.target_dir, "target_dir")?;
    if config.target_dir.exists() {
        return Err(ToolError::new(
            "target_dir_exists",
            format!(
                "isolated target directory already exists: {}",
                config.target_dir.display()
            ),
        ));
    }
    ensure_direct_child(&target_parent, &config.target_dir, "target_dir")?;
    ensure_direct_child(&output_parent, &config.output, "output_path")?;

    let rustc_version = command_text(&rustc, [OsStr::new("-vV")], "compiler_execution")?;
    let rustc_lines = rustc_version.lines().collect::<Vec<_>>();
    if rustc_lines != REGISTERED_RUSTC_VERBOSE {
        return Err(ToolError::new(
            "compiler_identity",
            format!(
                "registered rustc identity required; found {}",
                rustc_version.trim_end().replace('\n', " | ")
            ),
        ));
    }
    let cargo_version = command_text(&cargo, [OsStr::new("-vV")], "cargo_identity")?;
    if !cargo_version.starts_with("cargo ") {
        return Err(ToolError::new(
            "cargo_identity",
            "cargo -vV did not return a Cargo identity",
        ));
    }

    Ok(Prepared {
        manifest,
        cargo,
        rustc,
        cargo_version,
        rustc_version,
    })
}

pub fn run(config: &Config) -> Result<String, ToolError> {
    let prepared = prepare(config)?;
    fs::create_dir(&config.target_dir).map_err(|error| {
        ToolError::new(
            "target_dir_create",
            format!("cannot create {}: {error}", config.target_dir.display()),
        )
    })?;
    let mut target_guard = CreatedTargetDir::new(config.target_dir.clone());
    let (cargo_args, rustc_args) = build_arguments(config, &prepared.manifest);
    let manifest_parent = prepared
        .manifest
        .parent()
        .ok_or_else(|| ToolError::new("manifest_path", "Cargo.toml has no parent"))?;
    let capture = Command::new(&prepared.cargo)
        .args(&cargo_args)
        .current_dir(manifest_parent)
        .env("RUSTC", &prepared.rustc)
        .env("LC_ALL", "C")
        .env("SOURCE_DATE_EPOCH", "0")
        .env("CARGO_TERM_COLOR", "never")
        .env_remove("RUSTC_WRAPPER")
        .env_remove("RUSTC_WORKSPACE_WRAPPER")
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS")
        .env_remove("RUSTC_BOOTSTRAP")
        .output()
        .map_err(|error| {
            ToolError::new("cargo_execution", format!("cannot execute Cargo: {error}"))
        })?;
    if !capture.status.success() {
        let stderr = String::from_utf8_lossy(&capture.stderr);
        return Err(ToolError::new(
            classify_cargo_failure(&stderr),
            format!("Cargo build failed: {}", stderr.trim()),
        ));
    }
    let mir = std::str::from_utf8(&capture.stdout).map_err(|error| {
        ToolError::new(
            "mir_encoding",
            format!("Cargo rustc stdout is not UTF-8: {error}"),
        )
    })?;
    let function = parse_function(mir, &config.function).map_err(|error| {
        let class = match error.kind() {
            ParseErrorKind::MissingFunction => "function_missing",
            ParseErrorKind::DuplicateFunction => "function_duplicate",
            _ => "mir_syntax",
        };
        ToolError::new(class, format!("{:?}: {error}", error.kind()))
    })?;
    let summary = match config.profile {
        Profile::CheckedMemory => {
            let reflected = reflect_bounded_memory_checked(
                mir,
                &MirMemoryConfig::new(&config.function, config.target_usize_width),
            )
            .map_err(|error| {
                ToolError::new("mir_reflection", format!("{:?}: {error}", error.kind()))
            })?;
            build_summary(&SummaryInputs {
                config,
                prepared: &prepared,
                cargo_args: &cargo_args,
                rustc_args: &rustc_args,
                capture: &capture,
                function: &function,
                reflected: &reflected,
            })?
        }
        Profile::ScalarContract => {
            let mut arena = TermArena::new();
            let parameters = scalar_parameters(&mut arena, &function, config.target_usize_width)?;
            let reflected = reflect_scalar_into_checked(
                &mut arena,
                &parameters,
                mir,
                &MirScalarConfig::new(&config.function, config.target_usize_width),
            )
            .map_err(|error| {
                ToolError::new("mir_reflection", format!("{:?}: {error}", error.kind()))
            })?;
            build_scalar_summary(&ScalarSummaryInputs {
                config,
                prepared: &prepared,
                cargo_args: &cargo_args,
                rustc_args: &rustc_args,
                capture: &capture,
                function: &function,
                arena: &arena,
                reflected: &reflected,
            })?
        }
    };
    atomic_create(&config.output, &capture.stdout)?;
    target_guard.keep();
    Ok(summary)
}

fn build_summary(inputs: &SummaryInputs<'_>) -> Result<String, ToolError> {
    let cargo_arg_strings = os_strings(inputs.cargo_args, "cargo_argument_encoding")?;
    let rustc_arg_strings = os_strings(inputs.rustc_args, "rustc_argument_encoding")?;
    let manifest_text = inputs.prepared.manifest.to_str().ok_or_else(|| {
        ToolError::new("manifest_encoding", "canonical manifest path is not UTF-8")
    })?;
    let parameter_types = inputs
        .function
        .params
        .iter()
        .map(|parameter| render_type(parameter.ty))
        .collect::<Vec<_>>();
    let final_memory = inputs
        .reflected
        .region
        .output
        .iter()
        .map(|term| render(&inputs.reflected.arena, *term))
        .collect::<Vec<_>>();
    let target_name = match &inputs.config.target {
        Target::Lib => None,
        Target::Bin(name) => Some(name.as_str()),
    };
    Ok(format!(
        concat!(
            "{{\"schema\":{},\"cargo_identity\":{},\"rustc_identity\":{},",
            "\"cargo_args\":{},\"rustc_args\":{},\"manifest\":{},",
            "\"package\":{},\"target_kind\":{},\"target_name\":{},",
            "\"function\":{},\"target_usize_width\":{},\"mir_bytes\":{},",
            "\"parameter_types\":{},\"blocks\":{},\"region_local\":{},",
            "\"region_bytes\":{},\"result_width\":{},\"result_signed\":{},",
            "\"result_term\":{},\"panic_term\":{},\"final_memory_terms\":{}}}"
        ),
        quote(SUMMARY_SCHEMA),
        string_array(inputs.prepared.cargo_version.lines()),
        string_array(inputs.prepared.rustc_version.lines()),
        string_array(cargo_arg_strings.iter().map(String::as_str)),
        string_array(rustc_arg_strings.iter().map(String::as_str)),
        quote(manifest_text),
        quote(&inputs.config.package),
        quote(match inputs.config.target {
            Target::Lib => "lib",
            Target::Bin(_) => "bin",
        }),
        target_name.map_or_else(|| "null".to_owned(), quote),
        quote(&inputs.config.function),
        inputs.config.target_usize_width,
        inputs.capture.stdout.len(),
        string_array(parameter_types.iter().map(String::as_str)),
        inputs.function.blocks.len(),
        inputs.reflected.region.local,
        inputs.reflected.region.input.len(),
        inputs.reflected.result.width,
        inputs.reflected.result.signed,
        quote(&render(
            &inputs.reflected.arena,
            inputs.reflected.result.value,
        )),
        quote(&render(&inputs.reflected.arena, inputs.reflected.panic,)),
        string_array(final_memory.iter().map(String::as_str)),
    ))
}

fn build_scalar_summary(inputs: &ScalarSummaryInputs<'_>) -> Result<String, ToolError> {
    let cargo_args = project_scalar_cargo_arguments(
        inputs.cargo_args,
        &inputs.prepared.manifest,
        &inputs.config.target_dir,
    )?;
    let rustc_args = os_strings(inputs.rustc_args, "rustc_argument_encoding")?;
    if rustc_args
        .iter()
        .any(|argument| Path::new(argument).is_absolute())
    {
        return Err(ToolError::new(
            "scalar_summary_path",
            "scalar-profile rustc argument projection contains an absolute path",
        ));
    }
    let parameter_types = inputs
        .function
        .params
        .iter()
        .map(|parameter| render_type(parameter.ty))
        .collect::<Vec<_>>();
    let target_name = match &inputs.config.target {
        Target::Lib => None,
        Target::Bin(name) => Some(name.as_str()),
    };
    Ok(format!(
        concat!(
            "{{\"schema\":{},\"profile\":{},\"cargo_identity\":{},",
            "\"rustc_identity\":{},\"cargo_executable\":{},",
            "\"rustc_executable\":{},\"cargo_args\":{},\"rustc_args\":{},",
            "\"manifest\":{},\"target_dir\":{},\"output\":{},",
            "\"package\":{},\"target_kind\":{},\"target_name\":{},",
            "\"function\":{},\"target_usize_width\":{},\"mir_bytes\":{},",
            "\"parameter_types\":{},\"blocks\":{},\"result_width\":{},",
            "\"result_signed\":{},\"result_term\":{},\"panic_term\":{}}}"
        ),
        quote(SCALAR_SUMMARY_SCHEMA),
        quote("scalar-contract"),
        string_array(inputs.prepared.cargo_version.lines()),
        string_array(inputs.prepared.rustc_version.lines()),
        quote("$CARGO"),
        quote("$RUSTC"),
        string_array(cargo_args.iter().map(String::as_str)),
        string_array(rustc_args.iter().map(String::as_str)),
        quote("$MANIFEST"),
        quote("$TARGET_DIR"),
        quote("$OUTPUT"),
        quote(&inputs.config.package),
        quote(match inputs.config.target {
            Target::Lib => "lib",
            Target::Bin(_) => "bin",
        }),
        target_name.map_or_else(|| "null".to_owned(), quote),
        quote(&inputs.config.function),
        inputs.config.target_usize_width,
        inputs.capture.stdout.len(),
        string_array(parameter_types.iter().map(String::as_str)),
        inputs.function.blocks.len(),
        inputs.reflected.result.width,
        inputs.reflected.result.signed,
        quote(&render(inputs.arena, inputs.reflected.result.value,)),
        quote(&render(inputs.arena, inputs.reflected.panic)),
    ))
}

fn project_scalar_cargo_arguments(
    arguments: &[OsString],
    manifest: &Path,
    target_dir: &Path,
) -> Result<Vec<String>, ToolError> {
    arguments
        .iter()
        .map(|argument| {
            if argument == manifest.as_os_str() {
                return Ok("$MANIFEST".to_owned());
            }
            if argument == target_dir.as_os_str() {
                return Ok("$TARGET_DIR".to_owned());
            }
            let value = argument.to_str().ok_or_else(|| {
                ToolError::new("cargo_argument_encoding", "command argument is not UTF-8")
            })?;
            if Path::new(value).is_absolute() {
                return Err(ToolError::new(
                    "scalar_summary_path",
                    format!("unregistered absolute Cargo argument `{value}`"),
                ));
            }
            Ok(value.to_owned())
        })
        .collect()
}

fn scalar_parameters(
    arena: &mut TermArena,
    function: &Function,
    target_width: u32,
) -> Result<Vec<TermId>, ToolError> {
    function
        .params
        .iter()
        .enumerate()
        .map(|(index, parameter)| {
            let sort = scalar_sort(parameter.ty, target_width)?;
            let symbol = arena
                .declare_internal(&format!("mir.build.{}.arg{index}", function.name), sort)
                .map_err(|error| {
                    ToolError::new(
                        "mir_reflection",
                        format!("cannot declare parameter: {error}"),
                    )
                })?;
            Ok(arena.var(symbol))
        })
        .collect()
}

fn scalar_sort(ty: MirType, target_width: u32) -> Result<Sort, ToolError> {
    match ty {
        MirType::Bool => Ok(Sort::Bool),
        MirType::Integer { width, .. } => Ok(Sort::BitVec(width)),
        MirType::Usize | MirType::Isize => Ok(Sort::BitVec(target_width)),
        MirType::ByteArray { .. } => Err(ToolError::new(
            "mir_reflection",
            "scalar-contract profile rejects array parameters",
        )),
    }
}

fn canonical_file(path: &Path, class: &'static str) -> Result<PathBuf, ToolError> {
    require_absolute_clean(path, class)?;
    let canonical = fs::canonicalize(path).map_err(|error| {
        ToolError::new(class, format!("cannot resolve {}: {error}", path.display()))
    })?;
    if canonical != path {
        return Err(ToolError::new(
            class,
            format!("path must already be canonical: {}", path.display()),
        ));
    }
    if !canonical.is_file() {
        return Err(ToolError::new(
            class,
            format!("path is not a regular file: {}", path.display()),
        ));
    }
    Ok(canonical)
}

fn canonical_parent(path: &Path, class: &'static str) -> Result<PathBuf, ToolError> {
    require_absolute_clean(path, class)?;
    let parent = path
        .parent()
        .ok_or_else(|| ToolError::new(class, format!("path has no parent: {}", path.display())))?;
    let canonical = fs::canonicalize(parent).map_err(|error| {
        ToolError::new(
            class,
            format!("cannot resolve parent {}: {error}", parent.display()),
        )
    })?;
    if canonical != parent {
        return Err(ToolError::new(
            class,
            format!("parent must already be canonical: {}", parent.display()),
        ));
    }
    Ok(canonical)
}

fn require_absolute_clean(path: &Path, class: &'static str) -> Result<(), ToolError> {
    if !path.is_absolute() {
        return Err(ToolError::new(
            class,
            format!("path must be absolute: {}", path.display()),
        ));
    }
    if path
        .components()
        .any(|component| matches!(component, Component::ParentDir | Component::CurDir))
    {
        return Err(ToolError::new(
            class,
            format!("path must not contain . or ..: {}", path.display()),
        ));
    }
    Ok(())
}

fn ensure_direct_child(parent: &Path, path: &Path, class: &'static str) -> Result<(), ToolError> {
    if path.parent() != Some(parent) {
        return Err(ToolError::new(
            class,
            format!(
                "path must be a direct child of its canonical parent: {}",
                path.display()
            ),
        ));
    }
    Ok(())
}

fn command_text<'a, I>(executable: &Path, args: I, class: &'static str) -> Result<String, ToolError>
where
    I: IntoIterator<Item = &'a OsStr>,
{
    let output = Command::new(executable)
        .args(args)
        .env("LC_ALL", "C")
        .output()
        .map_err(|error| ToolError::new(class, format!("cannot execute: {error}")))?;
    if !output.status.success() {
        return Err(ToolError::new(
            class,
            format!(
                "identity command failed: {}",
                String::from_utf8_lossy(&output.stderr).trim()
            ),
        ));
    }
    String::from_utf8(output.stdout)
        .map_err(|error| ToolError::new(class, format!("identity is not UTF-8: {error}")))
}

fn build_arguments(config: &Config, manifest: &Path) -> (Vec<OsString>, Vec<OsString>) {
    let mut cargo_args = vec![
        OsString::from("rustc"),
        OsString::from("--manifest-path"),
        manifest.as_os_str().to_owned(),
        OsString::from("--package"),
        OsString::from(&config.package),
    ];
    match &config.target {
        Target::Lib => cargo_args.push(OsString::from("--lib")),
        Target::Bin(name) => {
            cargo_args.push(OsString::from("--bin"));
            cargo_args.push(OsString::from(name));
        }
    }
    cargo_args.extend([
        OsString::from("--target-dir"),
        config.target_dir.as_os_str().to_owned(),
        OsString::from("--locked"),
        OsString::from("--quiet"),
        OsString::from("--"),
    ]);
    let rustc_args = vec![
        OsString::from("-C"),
        OsString::from("opt-level=0"),
        OsString::from("-C"),
        OsString::from("overflow-checks=yes"),
        OsString::from("-Zunpretty=mir"),
    ];
    cargo_args.extend(rustc_args.iter().cloned());
    (cargo_args, rustc_args)
}

fn os_strings(values: &[OsString], class: &'static str) -> Result<Vec<String>, ToolError> {
    values
        .iter()
        .map(|value| {
            value
                .to_str()
                .map(str::to_owned)
                .ok_or_else(|| ToolError::new(class, "command argument is not UTF-8"))
        })
        .collect()
}

fn classify_cargo_failure(stderr: &str) -> &'static str {
    if stderr.contains("did not match any packages")
        || stderr.contains("package ID specification") && stderr.contains("did not match")
    {
        "wrong_package"
    } else if stderr.contains("no bin target named")
        || stderr.contains("no library targets found")
        || stderr.contains("no targets specified")
    {
        "wrong_target"
    } else {
        "cargo_build"
    }
}

fn render_type(ty: MirType) -> String {
    match ty {
        MirType::Bool => "bool".to_owned(),
        MirType::Integer { width, signed } => {
            format!("{}{width}", if signed { 'i' } else { 'u' })
        }
        MirType::Usize => "usize".to_owned(),
        MirType::Isize => "isize".to_owned(),
        MirType::ByteArray { bytes } => format!("[u8;{bytes}]"),
    }
}

fn atomic_create(output: &Path, bytes: &[u8]) -> Result<(), ToolError> {
    let parent = output
        .parent()
        .ok_or_else(|| ToolError::new("output_write", "output has no parent"))?;
    let name = output
        .file_name()
        .and_then(OsStr::to_str)
        .ok_or_else(|| ToolError::new("output_write", "output filename is not UTF-8"))?;
    let temporary = parent.join(format!(".{name}.axeyum-tmp-{}", std::process::id()));
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&temporary)
        .map_err(|error| {
            ToolError::new(
                "output_write",
                format!(
                    "cannot create temporary output {}: {error}",
                    temporary.display()
                ),
            )
        })?;
    let result = (|| {
        file.write_all(bytes).map_err(|error| {
            ToolError::new(
                "output_write",
                format!("cannot write temporary output: {error}"),
            )
        })?;
        file.sync_all().map_err(|error| {
            ToolError::new(
                "output_write",
                format!("cannot sync temporary output: {error}"),
            )
        })?;
        fs::hard_link(&temporary, output).map_err(|error| {
            let class = if output.exists() {
                "output_exists"
            } else {
                "output_write"
            };
            ToolError::new(
                class,
                format!("cannot commit output {}: {error}", output.display()),
            )
        })?;
        Ok(())
    })();
    drop(file);
    let _ = fs::remove_file(&temporary);
    result
}

struct CreatedTargetDir {
    path: PathBuf,
    keep: bool,
}

impl CreatedTargetDir {
    fn new(path: PathBuf) -> Self {
        Self { path, keep: false }
    }

    fn keep(&mut self) {
        self.keep = true;
    }
}

impl Drop for CreatedTargetDir {
    fn drop(&mut self) {
        if !self.keep {
            let _ = fs::remove_dir_all(&self.path);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{classify_cargo_failure, project_scalar_cargo_arguments, render_type};
    use axeyum_verify::reflect::mir::syntax::MirType;
    use std::ffi::OsString;
    use std::path::Path;

    #[test]
    fn cargo_diagnostics_map_to_stable_selection_classes() {
        assert_eq!(
            classify_cargo_failure("package ID specification `missing` did not match any packages"),
            "wrong_package"
        );
        assert_eq!(
            classify_cargo_failure("error: no bin target named `missing`"),
            "wrong_target"
        );
        assert_eq!(classify_cargo_failure("could not compile"), "cargo_build");
    }

    #[test]
    fn typed_summary_names_are_unambiguous() {
        assert_eq!(render_type(MirType::Bool), "bool");
        assert_eq!(
            render_type(MirType::Integer {
                width: 128,
                signed: true
            }),
            "i128"
        );
        assert_eq!(render_type(MirType::ByteArray { bytes: 4 }), "[u8;4]");
    }

    #[test]
    fn scalar_argument_projection_is_root_independent_and_strict() {
        let project = |root: &str| {
            let manifest = format!("{root}/fixture/Cargo.toml");
            let target = format!("{root}/scratch/target");
            let arguments = vec![
                OsString::from("rustc"),
                OsString::from("--manifest-path"),
                OsString::from(&manifest),
                OsString::from("--target-dir"),
                OsString::from(&target),
                OsString::from("--locked"),
            ];
            project_scalar_cargo_arguments(&arguments, Path::new(&manifest), Path::new(&target))
                .unwrap()
        };
        let first = project("/workspace/one");
        let second = project("/different/root");
        assert_eq!(first, second);
        assert_eq!(
            first,
            vec![
                "rustc",
                "--manifest-path",
                "$MANIFEST",
                "--target-dir",
                "$TARGET_DIR",
                "--locked",
            ]
        );

        let error = project_scalar_cargo_arguments(
            &[OsString::from("/unregistered/path")],
            Path::new("/manifest"),
            Path::new("/target"),
        )
        .unwrap_err();
        assert_eq!(error.class, "scalar_summary_path");
    }
}
