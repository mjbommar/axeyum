//! Local, deterministic scalar-admission probe for ADR-0323.

use std::env;
use std::fs;
use std::path::Path;
use std::process::ExitCode;

use axeyum_verify::reflect::llvm::{
    checked::reflect_scalar_checked,
    syntax::{TerminatorKind, parse_function, parse_scalar_cfg, render_scalar_cfg},
};

#[derive(Debug, Clone, PartialEq, Eq)]
struct Admission {
    function: String,
    parameter_widths: Vec<u32>,
    return_width: u32,
    blocks: usize,
    phis: usize,
    instructions: usize,
    canonical: String,
}

fn admit(llvm: &str) -> Result<Admission, String> {
    let function = parse_function(llvm).map_err(|error| format!("function_syntax:{error}"))?;
    let cfg = parse_scalar_cfg(&function).map_err(|error| format!("scalar_cfg:{error}"))?;
    if cfg.blocks.len() != 1 {
        return Err(format!(
            "profile:expected exactly one block, found {}",
            cfg.blocks.len()
        ));
    }
    let block = &cfg.blocks[0];
    let TerminatorKind::Return { width, .. } = block.terminator.kind else {
        return Err("profile:expected one scalar return".to_owned());
    };
    if width != cfg.return_width {
        return Err("profile:return width differs from function width".to_owned());
    }
    let reflected =
        reflect_scalar_checked(llvm).map_err(|error| format!("checked_reflection:{error}"))?;
    if reflected.result.width != cfg.return_width {
        return Err("profile:reflected result width differs from parsed width".to_owned());
    }

    let canonical = render_scalar_cfg(&cfg);
    let reparsed_function =
        parse_function(&canonical).map_err(|error| format!("canonical_function:{error}"))?;
    let reparsed = parse_scalar_cfg(&reparsed_function)
        .map_err(|error| format!("canonical_scalar_cfg:{error}"))?;
    if render_scalar_cfg(&reparsed) != canonical {
        return Err("canonical_fixpoint:second rendering changed bytes".to_owned());
    }
    let canonical_reflected = reflect_scalar_checked(&canonical)
        .map_err(|error| format!("canonical_reflection:{error}"))?;
    if canonical_reflected.params.len() != reflected.params.len()
        || canonical_reflected.result.width != reflected.result.width
    {
        return Err("canonical_reflection:typed projection changed".to_owned());
    }

    let parameter_widths = reflected
        .params
        .iter()
        .map(|(_, _, width)| *width)
        .collect::<Vec<_>>();
    Ok(Admission {
        function: cfg.name,
        parameter_widths,
        return_width: cfg.return_width,
        blocks: cfg.blocks.len(),
        phis: block.phis.len(),
        instructions: block.instructions.len(),
        canonical,
    })
}

fn run(input: &Path, canonical_output: &Path) -> Result<(), String> {
    let llvm = fs::read_to_string(input)
        .map_err(|error| format!("cannot read LLVM input {}: {error}", input.display()))?;
    let admission = admit(&llvm)?;
    fs::write(canonical_output, admission.canonical.as_bytes()).map_err(|error| {
        format!(
            "cannot write canonical LLVM {}: {error}",
            canonical_output.display()
        )
    })?;
    println!("stage=accepted");
    println!("kind=straight_line_scalar");
    println!("function={}", admission.function);
    println!(
        "parameter_widths={}",
        admission
            .parameter_widths
            .iter()
            .map(u32::to_string)
            .collect::<Vec<_>>()
            .join(",")
    );
    println!("return_width={}", admission.return_width);
    println!("blocks={}", admission.blocks);
    println!("phis={}", admission.phis);
    println!("instructions={}", admission.instructions);
    println!("canonical_bytes={}", admission.canonical.len());
    Ok(())
}

fn usage(program: &Path) {
    eprintln!(
        "usage: {} <single-function.ll> <canonical-output.ll>",
        program.display()
    );
}

fn main() -> ExitCode {
    let mut args = env::args_os();
    let program = args
        .next()
        .unwrap_or_else(|| "axeyum-llvm-scalar-admit".into());
    let Some(input) = args.next() else {
        usage(Path::new(&program));
        return ExitCode::from(2);
    };
    let Some(output) = args.next() else {
        usage(Path::new(&program));
        return ExitCode::from(2);
    };
    if args.next().is_some() {
        usage(Path::new(&program));
        return ExitCode::from(2);
    }
    match run(Path::new(&input), Path::new(&output)) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("scalar admission failed: {error}");
            ExitCode::from(1)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const MAJOR_SHAPE: &str = r#"
define hidden noundef i32 @major(i64 noundef %dev) {
start:
  %high = lshr i64 %dev, 32
  %masked = and i64 %high, 4294963200
  %out = trunc nuw i64 %masked to i32
  ret i32 %out
}
"#;

    #[test]
    fn admits_scalar_shape_and_reaches_a_canonical_fixpoint() {
        let admission = admit(MAJOR_SHAPE).unwrap();
        assert_eq!(admission.function, "major");
        assert_eq!(admission.parameter_widths, [64]);
        assert_eq!(admission.return_width, 32);
        assert_eq!(admission.blocks, 1);
        assert_eq!(admission.phis, 0);
        assert_eq!(admission.instructions, 3);
        assert_eq!(
            render_scalar_cfg(
                &parse_scalar_cfg(&parse_function(&admission.canonical).unwrap()).unwrap()
            ),
            admission.canonical
        );
    }

    #[test]
    fn rejects_memory_without_widening_the_profile() {
        let error =
            admit("define i8 @f(ptr %p) {\n  %x = load i8, ptr %p, align 1\n  ret i8 %x\n}\n")
                .unwrap_err();
        assert!(error.starts_with("checked_reflection:"));
        assert!(error.contains("does not support type `ptr`"));
    }
}
