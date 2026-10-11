//! Produce a multi-step exact identity for separate-process replay.
use axeyum_cas::{
    CasExpr,
    rewrite_trace::{TraceLimits, normalize_with_trace},
};
use std::path::Path;

fn main() -> Result<(), String> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 2 {
        return Err("usage: cas_trace_export OUTPUT_DIRECTORY".to_owned());
    }
    let x = CasExpr::var("x");
    let input = (x.clone() + CasExpr::int(1) + CasExpr::int(2)) * (-(-(x + CasExpr::int(1))));
    let limits = TraceLimits::default();
    let trace = normalize_with_trace(&input, limits).map_err(|e| format!("{e:?}"))?;
    let statement = serde_json::json!({"input": trace.input, "result": trace.result});
    let directory = Path::new(&args[1]);
    std::fs::create_dir_all(directory).map_err(|e| e.to_string())?;
    std::fs::write(
        directory.join("trace.json"),
        trace.to_json(limits).map_err(|e| format!("{e:?}"))?,
    )
    .map_err(|e| e.to_string())?;
    std::fs::write(
        directory.join("statement.json"),
        serde_json::to_vec(&statement).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;
    println!("EXPORTED|steps={}", trace.steps.len());
    Ok(())
}
