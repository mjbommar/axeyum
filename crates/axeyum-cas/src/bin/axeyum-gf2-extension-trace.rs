//! Deterministic distributed binary extension-field long-cycle traces.

use std::fs;

use axeyum_cas::gf2_extension::{
    BinaryExtensionLongCycleTraceShardReport, BinaryExtensionTraceLimits,
    binary_extension_long_cycle_trace_shard, collapse_binary_extension_long_cycle_trace_subshards,
    combine_binary_extension_long_cycle_trace_shards, extension_trace_hankel_minor,
};

fn main() {
    if let Err(error) = run() {
        eprintln!("GF2_EXTENSION_TRACE|status=FAIL|error={error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let arguments = std::env::args().skip(1).collect::<Vec<_>>();
    if arguments
        .first()
        .is_some_and(|argument| argument == "--merge")
    {
        if arguments.len() < 2 {
            return Err("usage: axeyum-gf2-extension-trace --merge <shard.json>...".into());
        }
        let shards = arguments[1..]
            .iter()
            .map(|path| {
                let encoded = fs::read_to_string(path)?;
                Ok(serde_json::from_str::<
                    BinaryExtensionLongCycleTraceShardReport,
                >(&encoded)?)
            })
            .collect::<Result<Vec<_>, Box<dyn std::error::Error>>>()?;
        let report = combine_binary_extension_long_cycle_trace_shards(&shards)?;
        println!("{}", serde_json::to_string(&report)?);
        return Ok(());
    }
    if arguments
        .first()
        .is_some_and(|argument| argument == "--collapse")
    {
        if arguments.len() < 4 {
            return Err("usage: axeyum-gf2-extension-trace --collapse <parent-index> <parent-count> <subshard.json>...".into());
        }
        let parent_index = arguments[1].parse::<u64>()?;
        let parent_count = arguments[2].parse::<u64>()?;
        let subshards = arguments[3..]
            .iter()
            .map(|path| {
                let encoded = fs::read_to_string(path)?;
                Ok(serde_json::from_str::<
                    BinaryExtensionLongCycleTraceShardReport,
                >(&encoded)?)
            })
            .collect::<Result<Vec<_>, Box<dyn std::error::Error>>>()?;
        let report = collapse_binary_extension_long_cycle_trace_subshards(
            &subshards,
            parent_index,
            parent_count,
        )?;
        println!("{}", serde_json::to_string(&report)?);
        return Ok(());
    }
    if arguments
        .first()
        .is_some_and(|argument| argument == "--hankel")
    {
        if arguments.len() < 4 {
            return Err("usage: axeyum-gf2-extension-trace --hankel <first-power> <maximum-order> <trace>...".into());
        }
        let first_power = arguments[1].parse::<usize>()?;
        let maximum_order = arguments[2].parse::<usize>()?;
        let traces = arguments[3..]
            .iter()
            .map(|trace| trace.parse::<i128>())
            .collect::<Result<Vec<_>, _>>()?;
        let report = extension_trace_hankel_minor(&traces, first_power, maximum_order)?;
        println!(
            "{}",
            serde_json::json!({
                "first_power": report.first_power,
                "tested_maximum_recurrence_order": report.tested_maximum_recurrence_order,
                "determinant": report.determinant.to_string(),
                "excludes_tested_order": report.excludes_tested_order(),
            })
        );
        return Ok(());
    }
    if arguments.len() != 6 {
        return Err("usage: axeyum-gf2-extension-trace <field-modulus> <polynomial-degree> <fixed-leading-coefficients> <shard-index> <shard-count> <max-candidates>".into());
    }
    let field_modulus = parse_u64(&arguments[0])?;
    let polynomial_degree = arguments[1].parse::<usize>()?;
    let fixed_leading_coefficients = arguments[2].parse::<usize>()?;
    let shard_index = arguments[3].parse::<u64>()?;
    let shard_count = arguments[4].parse::<u64>()?;
    let max_candidates = arguments[5].parse::<u64>()?;
    let limits = BinaryExtensionTraceLimits {
        max_field_degree: 16,
        max_polynomial_degree: 32,
        max_candidates,
    };
    let report = binary_extension_long_cycle_trace_shard(
        field_modulus,
        polynomial_degree,
        fixed_leading_coefficients,
        shard_index,
        shard_count,
        limits,
    )?;
    println!("{}", serde_json::to_string(&report)?);
    Ok(())
}

fn parse_u64(value: &str) -> Result<u64, Box<dyn std::error::Error>> {
    if let Some(binary) = value.strip_prefix("0b") {
        Ok(u64::from_str_radix(binary, 2)?)
    } else if let Some(hexadecimal) = value.strip_prefix("0x") {
        Ok(u64::from_str_radix(hexadecimal, 16)?)
    } else {
        Ok(value.parse::<u64>()?)
    }
}
