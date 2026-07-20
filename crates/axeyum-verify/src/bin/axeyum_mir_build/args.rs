use std::ffi::{OsStr, OsString};
use std::path::PathBuf;

use crate::ToolError;

pub const HELP: &str = "\
Usage:
  axeyum-mir-build \\
    --manifest-path /absolute/canonical/Cargo.toml \\
    --package PACKAGE (--lib | --bin NAME) --function FUNCTION \\
    --target-usize-width 64 \\
    --cargo /absolute/path/to/cargo --rustc /absolute/path/to/rustc \\
    --target-dir /absolute/new/target-dir --output /absolute/new/output.mir

Builds exactly one locked Cargo package target with the registered rustc,
checks one named function through Axeyum's strict MIR parser and bounded-memory
reflector, then atomically retains raw compiler stdout. The selected Cargo
build may execute that target's build scripts; this command is not a sandbox
for hostile crates. Existing outputs and target directories are never reused.
";

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Target {
    Lib,
    Bin(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Config {
    pub manifest_path: PathBuf,
    pub package: String,
    pub target: Target,
    pub function: String,
    pub target_usize_width: u32,
    pub cargo: PathBuf,
    pub rustc: PathBuf,
    pub target_dir: PathBuf,
    pub output: PathBuf,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Action {
    Help,
    Run(Config),
}

#[derive(Default)]
struct PartialConfig {
    manifest_path: Option<PathBuf>,
    package: Option<String>,
    target: Option<Target>,
    function: Option<String>,
    target_usize_width: Option<u32>,
    cargo: Option<PathBuf>,
    rustc: Option<PathBuf>,
    target_dir: Option<PathBuf>,
    output: Option<PathBuf>,
}

pub fn parse<I>(arguments: I) -> Result<Action, ToolError>
where
    I: IntoIterator<Item = OsString>,
{
    let mut arguments = arguments.into_iter();
    let _program = arguments.next();
    let mut partial = PartialConfig::default();
    while let Some(flag) = arguments.next() {
        let Some(flag) = flag.to_str() else {
            return Err(ToolError::new(
                "argument_encoding",
                "option names must be valid UTF-8",
            ));
        };
        match flag {
            "-h" | "--help" => {
                if arguments.next().is_some() || !is_empty(&partial) {
                    return Err(ToolError::new(
                        "help_combination",
                        "--help must be the only option",
                    ));
                }
                return Ok(Action::Help);
            }
            "--manifest-path" => set_path(
                &mut partial.manifest_path,
                flag,
                next_value(&mut arguments, flag)?,
            )?,
            "--package" => set_string(
                &mut partial.package,
                flag,
                next_value(&mut arguments, flag)?,
            )?,
            "--lib" => set_target(&mut partial.target, Target::Lib)?,
            "--bin" => {
                let value = required_utf8(next_value(&mut arguments, flag)?, flag)?;
                set_target(&mut partial.target, Target::Bin(value))?;
            }
            "--function" => set_string(
                &mut partial.function,
                flag,
                next_value(&mut arguments, flag)?,
            )?,
            "--target-usize-width" => {
                if partial.target_usize_width.is_some() {
                    return Err(duplicate(flag));
                }
                let raw = required_utf8(next_value(&mut arguments, flag)?, flag)?;
                let width = raw.parse::<u32>().map_err(|_| {
                    ToolError::new("target_width", format!("invalid target width `{raw}`"))
                })?;
                if width != 64 {
                    return Err(ToolError::new(
                        "target_width",
                        format!("registered Cargo MIR profile requires width 64; found {width}"),
                    ));
                }
                partial.target_usize_width = Some(width);
            }
            "--cargo" => set_path(&mut partial.cargo, flag, next_value(&mut arguments, flag)?)?,
            "--rustc" => set_path(&mut partial.rustc, flag, next_value(&mut arguments, flag)?)?,
            "--target-dir" => set_path(
                &mut partial.target_dir,
                flag,
                next_value(&mut arguments, flag)?,
            )?,
            "--output" => set_path(&mut partial.output, flag, next_value(&mut arguments, flag)?)?,
            other => {
                return Err(ToolError::new(
                    "unknown_argument",
                    format!("unknown option `{other}`"),
                ));
            }
        }
    }

    Ok(Action::Run(Config {
        manifest_path: required(partial.manifest_path, "--manifest-path")?,
        package: required(partial.package, "--package")?,
        target: required(partial.target, "--lib or --bin")?,
        function: required(partial.function, "--function")?,
        target_usize_width: required(partial.target_usize_width, "--target-usize-width")?,
        cargo: required(partial.cargo, "--cargo")?,
        rustc: required(partial.rustc, "--rustc")?,
        target_dir: required(partial.target_dir, "--target-dir")?,
        output: required(partial.output, "--output")?,
    }))
}

fn is_empty(config: &PartialConfig) -> bool {
    config.manifest_path.is_none()
        && config.package.is_none()
        && config.target.is_none()
        && config.function.is_none()
        && config.target_usize_width.is_none()
        && config.cargo.is_none()
        && config.rustc.is_none()
        && config.target_dir.is_none()
        && config.output.is_none()
}

fn next_value<I>(arguments: &mut I, flag: &str) -> Result<OsString, ToolError>
where
    I: Iterator<Item = OsString>,
{
    arguments
        .next()
        .ok_or_else(|| ToolError::new("missing_value", format!("{flag} requires a value")))
}

fn required_utf8(value: OsString, flag: &str) -> Result<String, ToolError> {
    let value = value
        .into_string()
        .map_err(|_| ToolError::new("argument_encoding", format!("{flag} requires valid UTF-8")))?;
    if value.is_empty() {
        return Err(ToolError::new(
            "empty_argument",
            format!("{flag} cannot be empty"),
        ));
    }
    Ok(value)
}

fn set_string(slot: &mut Option<String>, flag: &str, value: OsString) -> Result<(), ToolError> {
    if slot.is_some() {
        return Err(duplicate(flag));
    }
    *slot = Some(required_utf8(value, flag)?);
    Ok(())
}

fn set_path(slot: &mut Option<PathBuf>, flag: &str, value: OsString) -> Result<(), ToolError> {
    if slot.is_some() {
        return Err(duplicate(flag));
    }
    if value == OsStr::new("") {
        return Err(ToolError::new(
            "empty_argument",
            format!("{flag} cannot be empty"),
        ));
    }
    *slot = Some(PathBuf::from(value));
    Ok(())
}

fn set_target(slot: &mut Option<Target>, value: Target) -> Result<(), ToolError> {
    if slot.is_some() {
        return Err(ToolError::new(
            "conflicting_target",
            "select exactly one of --lib or --bin NAME",
        ));
    }
    *slot = Some(value);
    Ok(())
}

fn required<T>(value: Option<T>, flag: &str) -> Result<T, ToolError> {
    value.ok_or_else(|| ToolError::new("missing_argument", format!("missing required {flag}")))
}

fn duplicate(flag: &str) -> ToolError {
    ToolError::new(
        "duplicate_argument",
        format!("{flag} was provided more than once"),
    )
}

#[cfg(test)]
mod tests {
    use super::{Action, Target, parse};
    use std::ffi::OsString;

    fn args(values: &[&str]) -> Vec<OsString> {
        std::iter::once(OsString::from("tool"))
            .chain(values.iter().map(OsString::from))
            .collect()
    }

    #[test]
    fn complete_selection_is_typed() {
        let action = parse(args(&[
            "--manifest-path",
            "/tmp/Cargo.toml",
            "--package",
            "fixture",
            "--lib",
            "--function",
            "f",
            "--target-usize-width",
            "64",
            "--cargo",
            "/bin/cargo",
            "--rustc",
            "/bin/rustc",
            "--target-dir",
            "/tmp/target",
            "--output",
            "/tmp/out.mir",
        ]))
        .unwrap();
        let Action::Run(config) = action else {
            panic!("expected run action");
        };
        assert_eq!(config.target, Target::Lib);
        assert_eq!(config.package, "fixture");
        assert_eq!(config.function, "f");
    }

    #[test]
    fn missing_duplicate_conflicting_and_width_errors_are_stable() {
        assert_eq!(parse(args(&[])).unwrap_err().class, "missing_argument");
        assert_eq!(
            parse(args(&["--lib", "--bin", "x"])).unwrap_err().class,
            "conflicting_target"
        );
        assert_eq!(
            parse(args(&["--package", "x", "--package", "y"]))
                .unwrap_err()
                .class,
            "duplicate_argument"
        );
        assert_eq!(
            parse(args(&["--target-usize-width", "32"]))
                .unwrap_err()
                .class,
            "target_width"
        );
        assert_eq!(
            parse(args(&["--unknown"])).unwrap_err().class,
            "unknown_argument"
        );
    }
}
