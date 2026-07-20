//! Deterministic semantic-profile classifier for the ADR-0294 loop census.

use std::collections::BTreeSet;
use std::env;
use std::fs;
use std::path::Path;
use std::process::ExitCode;

use axeyum_verify::reflect::llvm::{
    loops::{
        LoopReflectError, LoopReflectErrorKind, UnsignedPhiUpperBound,
        reflect_single_latch_loop_checked,
    },
    syntax::{ParseError, ParseErrorKind, parse_function, parse_scalar_cfg},
};

#[derive(Debug, Clone, PartialEq, Eq)]
struct Classification {
    stage: &'static str,
    kind: &'static str,
    function: String,
    state_components: usize,
    iteration_paths: usize,
    diagnostic: String,
}

impl Classification {
    fn parse_error(stage: &'static str, function: String, error: &ParseError) -> Self {
        Self {
            stage,
            kind: parse_error_kind(error.kind()),
            function,
            state_components: 0,
            iteration_paths: 0,
            diagnostic: error.to_string(),
        }
    }

    fn loop_error(function: String, error: &LoopReflectError) -> Self {
        Self {
            stage: "loop_reflection",
            kind: loop_error_kind(error.kind()),
            function,
            state_components: 0,
            iteration_paths: 0,
            diagnostic: error.to_string(),
        }
    }

    fn emit(&self) {
        println!("stage={}", self.stage);
        println!("kind={}", self.kind);
        println!("function={}", self.function);
        println!("state_components={}", self.state_components);
        println!("iteration_paths={}", self.iteration_paths);
        if !self.diagnostic.is_empty() {
            eprintln!("{}", self.diagnostic);
        }
    }
}

fn classify(llvm: &str) -> Classification {
    let function = match parse_function(llvm) {
        Ok(function) => function,
        Err(error) => {
            return Classification::parse_error("function_syntax", String::new(), &error);
        }
    };
    let function_name = function.name.clone();
    let cfg = match parse_scalar_cfg(&function) {
        Ok(cfg) => cfg,
        Err(error) => {
            return Classification::parse_error("scalar_cfg", function_name, &error);
        }
    };

    let mut candidates = Vec::new();
    let mut seen = BTreeSet::new();
    for block in &cfg.blocks {
        for phi in &block.phis {
            if phi.width > 1 && seen.insert(phi.dest.clone()) {
                candidates.push(phi.dest.clone());
            }
        }
    }
    if candidates.is_empty() {
        candidates.push("__axeyum_missing_non_boolean_phi__".to_owned());
    }

    let mut first_error = None;
    let mut first_non_property_error = None;
    for phi in candidates {
        match reflect_single_latch_loop_checked(llvm, UnsignedPhiUpperBound::new(phi, 0)) {
            Ok(system) => {
                let kind = if system.loop_block() == system.latch_block() {
                    "self_loop"
                } else {
                    "single_latch"
                };
                return Classification {
                    stage: "accepted",
                    kind,
                    function: function_name,
                    state_components: system.state_components().len(),
                    iteration_paths: system.iteration_paths().len(),
                    diagnostic: String::new(),
                };
            }
            Err(error) => {
                if first_error.is_none() {
                    first_error = Some(error.clone());
                }
                if error.kind() != LoopReflectErrorKind::InvalidProperty
                    && first_non_property_error.is_none()
                {
                    first_non_property_error = Some(error);
                }
            }
        }
    }

    let error = first_non_property_error
        .or(first_error)
        .expect("at least one property candidate is always attempted");
    Classification::loop_error(function_name, &error)
}

fn parse_error_kind(kind: ParseErrorKind) -> &'static str {
    match kind {
        ParseErrorKind::MissingDefinition => "missing_definition",
        ParseErrorKind::MultipleDefinitions => "multiple_definitions",
        ParseErrorKind::MalformedHeader => "malformed_header",
        ParseErrorKind::MalformedParameter => "malformed_parameter",
        ParseErrorKind::UnterminatedQuotedToken => "unterminated_quoted_token",
        ParseErrorKind::MalformedIdentifierEscape => "malformed_identifier_escape",
        ParseErrorKind::UnbalancedDelimiter => "unbalanced_delimiter",
        ParseErrorKind::UnclosedBody => "unclosed_body",
        ParseErrorKind::DuplicateBlockLabel => "duplicate_block_label",
        ParseErrorKind::MalformedInstruction => "malformed_instruction",
        ParseErrorKind::UnsupportedInstruction => "unsupported_instruction",
        ParseErrorKind::UnsupportedSemantics => "unsupported_semantics",
        ParseErrorKind::MalformedControlFlow => "malformed_control_flow",
        ParseErrorKind::UndefinedBlockLabel => "undefined_block_label",
        ParseErrorKind::InvalidPhi => "invalid_phi",
    }
}

fn loop_error_kind(kind: LoopReflectErrorKind) -> &'static str {
    match kind {
        LoopReflectErrorKind::Syntax => "syntax",
        LoopReflectErrorKind::NoCycle => "no_cycle",
        LoopReflectErrorKind::MultipleCycles => "multiple_cycles",
        LoopReflectErrorKind::NonCanonicalCycle => "non_canonical_cycle",
        LoopReflectErrorKind::NonCanonicalLoopRegion => "non_canonical_loop_region",
        LoopReflectErrorKind::PathLimit => "path_limit",
        LoopReflectErrorKind::InvalidPhi => "invalid_phi",
        LoopReflectErrorKind::UnsupportedInitializer => "unsupported_initializer",
        LoopReflectErrorKind::UnsupportedBody => "unsupported_body",
        LoopReflectErrorKind::UnsupportedMemory => "unsupported_memory",
        LoopReflectErrorKind::UnsupportedCall => "unsupported_call",
        LoopReflectErrorKind::InvalidContract => "invalid_contract",
        LoopReflectErrorKind::ContractDisproved => "contract_disproved",
        LoopReflectErrorKind::ContractUnknown => "contract_unknown",
        LoopReflectErrorKind::ContractSolver => "contract_solver",
        LoopReflectErrorKind::ExternalSsaDependency => "external_ssa_dependency",
        LoopReflectErrorKind::InvalidProperty => "invalid_property",
        LoopReflectErrorKind::IrConstruction => "ir_construction",
    }
}

fn run(path: &Path) -> Result<(), String> {
    let llvm = fs::read_to_string(path)
        .map_err(|error| format!("cannot read LLVM input {}: {error}", path.display()))?;
    classify(&llvm).emit();
    Ok(())
}

fn main() -> ExitCode {
    let mut args = env::args_os();
    let program = args
        .next()
        .and_then(|value| {
            Path::new(&value)
                .file_name()
                .map(std::borrow::ToOwned::to_owned)
        })
        .unwrap_or_else(|| "axeyum-llvm-loop-classify".into());
    let Some(path) = args.next() else {
        eprintln!(
            "usage: {} <single-function.ll>",
            Path::new(&program).display()
        );
        return ExitCode::from(2);
    };
    if args.next().is_some() {
        eprintln!(
            "usage: {} <single-function.ll>",
            Path::new(&program).display()
        );
        return ExitCode::from(2);
    }
    match run(Path::new(&path)) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("loop classifier: {error}");
            ExitCode::from(2)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const CAPSUM: &str = include_str!("../../tests/fixtures/llvm/clang_capsum8.ll");
    const CAPDIV: &str = include_str!("../../tests/fixtures/llvm/clang21_capdiv_natural_loop.ll");

    #[test]
    fn classifies_both_accepted_profiles_without_property_name_bias() {
        let self_loop = classify(CAPSUM);
        assert_eq!(self_loop.stage, "accepted");
        assert_eq!(self_loop.kind, "self_loop");
        assert_eq!(self_loop.function, "capsum8");
        assert!(self_loop.state_components > 0);
        assert_eq!(self_loop.iteration_paths, 1);

        let natural = classify(CAPDIV);
        assert_eq!(natural.stage, "accepted");
        assert_eq!(natural.kind, "single_latch");
        assert_eq!(natural.function, "capdiv");
        assert_eq!(natural.iteration_paths, 2);
    }

    #[test]
    fn preserves_precise_parse_and_loop_rejections() {
        let syntax = classify("define i8 @bad(i8 %x) {\n  %y = frob i8 %x, 1\n  ret i8 %y\n}\n");
        assert_eq!(syntax.stage, "scalar_cfg");
        assert_eq!(syntax.kind, "unsupported_instruction");
        assert!(syntax.diagnostic.contains("unsupported scalar instruction"));

        let memory_input = CAPDIV.replace("%12 = udiv i8 %8, %1", "%12 = load i8, ptr %1");
        let memory = classify(&memory_input);
        assert_eq!(memory.stage, "loop_reflection");
        assert_eq!(memory.kind, "unsupported_memory");
        assert!(memory.diagnostic.contains("does not admit memory"));
    }
}
