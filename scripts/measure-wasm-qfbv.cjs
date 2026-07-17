#!/usr/bin/env node
"use strict";

const path = require("node:path");

function usage() {
  console.error(
    "usage: node scripts/measure-wasm-qfbv.cjs <generated-node-module.js> [iterations]",
  );
  process.exit(2);
}

const moduleArgument = process.argv[2];
if (!moduleArgument) {
  usage();
}

const iterations = Number.parseInt(process.argv[3] ?? "1000", 10);
if (!Number.isSafeInteger(iterations) || iterations < 1) {
  usage();
}

const repetition = Number.parseInt(
  process.env.AXEYUM_MEASUREMENT_REPETITION ?? "1",
  10,
);
if (!Number.isSafeInteger(repetition) || repetition < 1) {
  throw new Error("AXEYUM_MEASUREMENT_REPETITION must be a positive integer");
}

const modulePath = path.resolve(moduleArgument);
const loadStarted = process.hrtime.bigint();
const axeyum = require(modulePath);
const loadElapsed = process.hrtime.bigint() - loadStarted;

const cases = [
  {
    name: "sat-bv8-add",
    expected: "sat",
    smt2: `(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= (bvadd x #x01) #x2a))
(check-sat)`,
  },
  {
    name: "unsat-bv8-equalities",
    expected: "unsat",
    smt2: `(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x2a))
(assert (= x #x2b))
(check-sat)`,
  },
  {
    name: "sat-bv32-structure",
    expected: "sat",
    smt2: `(set-logic QF_BV)
(declare-const x (_ BitVec 16))
(declare-const y (_ BitVec 16))
(assert (= (concat x y) #x12345678))
(assert (= ((_ extract 15 8) y) #x56))
(assert (= (bvadd x y) #x68ac))
(check-sat)`,
  },
];

function solveAndCheck(testCase) {
  const result = JSON.parse(axeyum.solve_smtlib_json(testCase.smt2, 1000));
  if (result.status !== testCase.expected) {
    throw new Error(
      `${testCase.name}: expected ${testCase.expected}, got ${result.status}: ${JSON.stringify(result)}`,
    );
  }
}

function percentile(sorted, fraction) {
  const index = Math.min(
    sorted.length - 1,
    Math.max(0, Math.ceil(fraction * sorted.length) - 1),
  );
  return sorted[index];
}

function summarize(testCase) {
  for (let index = 0; index < 100; index += 1) {
    solveAndCheck(testCase);
  }

  const samplesNs = [];
  const totalStarted = process.hrtime.bigint();
  for (let index = 0; index < iterations; index += 1) {
    const started = process.hrtime.bigint();
    solveAndCheck(testCase);
    samplesNs.push(Number(process.hrtime.bigint() - started));
  }
  const totalNs = Number(process.hrtime.bigint() - totalStarted);
  samplesNs.sort((left, right) => left - right);
  const sumNs = samplesNs.reduce((sum, value) => sum + value, 0);

  return {
    name: testCase.name,
    expected_status: testCase.expected,
    warmup_iterations: 100,
    measured_iterations: iterations,
    timeout_ms: 1000,
    total_ns: totalNs,
    mean_ns: sumNs / samplesNs.length,
    p50_ns: percentile(samplesNs, 0.5),
    p90_ns: percentile(samplesNs, 0.9),
    p95_ns: percentile(samplesNs, 0.95),
    p99_ns: percentile(samplesNs, 0.99),
    min_ns: samplesNs[0],
    max_ns: samplesNs[samplesNs.length - 1],
  };
}

console.log(
  JSON.stringify(
    {
      schema: "axeyum.wasm-qfbv-latency.v1",
      runtime: "nodejs",
      node_version: process.version,
      platform: process.platform,
      architecture: process.arch,
      generated_module: modulePath,
      axeyum_version: axeyum.version(),
      source_revision: process.env.AXEYUM_SOURCE_REVISION ?? null,
      repetition,
      module_load_and_instantiation_ns: Number(loadElapsed),
      measurement_clock: "process.hrtime.bigint",
      build_profile: process.env.AXEYUM_WASM_BUILD_PROFILE ?? "unspecified",
      wasm_opt_applied: false,
      cases: cases.map(summarize),
    },
    null,
    2,
  ),
);
