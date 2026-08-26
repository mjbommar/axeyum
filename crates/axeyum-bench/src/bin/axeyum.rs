//! Named binary wrapper for the ADR-0541 general SMT-LIB session driver.

// Keep the historical checked example and the installable binary behaviorally
// identical. A path module is deliberate: two copied command walks would drift
// the first time SMT-LIB gained a response variant.
#[path = "../../examples/axeyum_cli.rs"]
mod cli;

fn main() -> std::process::ExitCode {
    cli::main()
}
