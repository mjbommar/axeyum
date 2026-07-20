//! Capture and check one function from an explicitly selected Cargo target.

#[path = "axeyum_mir_build/args.rs"]
mod args;
#[path = "axeyum_mir_build/execute.rs"]
mod execute;
#[path = "axeyum_mir_build/json.rs"]
mod json;

use std::process::ExitCode;

use args::Action;

const ERROR_SCHEMA: &str = "axeyum.verify-mir-build-error.v1";

#[derive(Debug)]
struct ToolError {
    class: &'static str,
    detail: String,
}

impl ToolError {
    fn new(class: &'static str, detail: impl Into<String>) -> Self {
        Self {
            class,
            detail: detail.into(),
        }
    }
}

fn main() -> ExitCode {
    match args::parse(std::env::args_os()) {
        Ok(Action::Help) => {
            print!("{}", args::HELP);
            ExitCode::SUCCESS
        }
        Ok(Action::Run(config)) => match execute::run(&config) {
            Ok(summary) => {
                println!("{summary}");
                ExitCode::SUCCESS
            }
            Err(error) => report(&error),
        },
        Err(error) => report(&error),
    }
}

fn report(error: &ToolError) -> ExitCode {
    eprintln!(
        "{{\"schema\":{},\"class\":{},\"detail\":{}}}",
        json::quote(ERROR_SCHEMA),
        json::quote(error.class),
        json::quote(&error.detail)
    );
    ExitCode::from(2)
}
