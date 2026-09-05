//! **The `by axeyum` sidecar.**
//!
//! Reads one JSON request on stdin, writes one JSON response on stdout, exits.
//! That is the whole contract; `lean/axeyum-tactic/Axeyum/Tactic.lean` is the
//! only client and `lean/axeyum-tactic/Axeyum/Protocol.lean` is the shared
//! vocabulary.
//!
//! # It always answers
//!
//! A sidecar that hangs is a Lean session that hangs, so this one carries a
//! hard timeout (`AXEYUM_TACTIC_TIMEOUT_MS`, default 30 s): the work runs on a
//! worker thread, and if the budget expires the main thread prints
//! `declined: timeout` and exits. Nothing about that is a soundness mechanism
//! — the timeout can only turn a slow success into a decline, never a decline
//! into a success — it is there so the tactic fails in bounded time.
//!
//! Every other failure mode is also an answer: an unreadable request, an
//! unsupported goal, and a producer that found nothing all print a `declined`
//! response with a typed reason and exit 0. The sidecar exits nonzero only
//! when it could not write a response at all.
//!
//! # It is not trusted
//!
//! The response carries a proof **term** in Lean source. Lean parses it,
//! elaborates it at the goal's own type, and its kernel checks it. If this
//! binary lied — wrong term, wrong goal, mutated term, echoed environment
//! identity — the goal does not close. `lean/axeyum-tactic/Tests/Mutations.lean`
//! demonstrates each of those with a stub sidecar in place of this one.

use std::io::Read as _;
use std::io::Write as _;
use std::sync::mpsc;
use std::time::Duration;

use axeyum_lean_import::tactic_bridge::{Dev, Hypothesis, decode, prove_to_lean_term};
use axeyum_lean_kernel::on_a_deep_stack;
use serde_json::{Value, json};

/// The protocol tag; must match `Axeyum.Protocol.protocolId`.
const PROTOCOL_ID: &str = "axeyum-tactic-v1";

/// The default hard timeout, in milliseconds.
const DEFAULT_TIMEOUT_MS: u64 = 30_000;

/// A `declined` response with a typed reason. `detail` is advisory: the Lean
/// side reads only `protocol`, `status` and `reason`.
fn declined(reason: &str, detail: &str) -> Value {
    json!({
        "protocol": PROTOCOL_ID,
        "status": "declined",
        "reason": reason,
        "detail": detail,
    })
}

/// An `accepted` response carrying the environment identity the request
/// asserted and the proof term.
fn accepted(environment_id: &str, term: &str) -> Value {
    json!({
        "protocol": PROTOCOL_ID,
        "status": "accepted",
        "environment_id": environment_id,
        "term": term,
    })
}

/// Do the work for one request. Never panics on a malformed request: an
/// unreadable request is `unsupported`, because the Lean side's own
/// `malformed-response` category is about *responses* and inventing a request
/// category here would put a string on the wire Lean treats as malformed.
fn handle(raw: &str) -> Value {
    let request: Value = match serde_json::from_str(raw) {
        Ok(value) => value,
        Err(error) => return declined("unsupported", &format!("request is not JSON: {error}")),
    };
    let object = match request.as_object() {
        Some(object) => object,
        None => return declined("unsupported", "request is not a JSON object"),
    };
    match object.get("protocol").and_then(Value::as_str) {
        Some(tag) if tag == PROTOCOL_ID => {}
        Some(tag) => {
            return declined(
                "unsupported",
                &format!("request protocol is {tag}, this sidecar speaks {PROTOCOL_ID}"),
            );
        }
        None => return declined("unsupported", "request has no string \"protocol\""),
    }
    let Some(environment_id) = object.get("environment_id").and_then(Value::as_str) else {
        return declined("unsupported", "request has no string \"environment_id\"");
    };
    let Some(goal_json) = object.get("goal") else {
        return declined("unsupported", "request has no \"goal\"");
    };
    let goal = match decode(goal_json) {
        Ok(goal) => goal,
        Err(why) => return declined("unsupported", &format!("goal did not decode: {why}")),
    };

    let mut hypotheses = Vec::new();
    if let Some(items) = object.get("hypotheses").and_then(Value::as_array) {
        for item in items {
            let (Some(name), Some(ty_json)) = (
                item.get("name").and_then(Value::as_str),
                item.get("type"),
            ) else {
                continue;
            };
            // A hypothesis that does not decode is skipped, not fatal: it is a
            // fact the producers simply will not have.
            if let Ok(ty) = decode(ty_json) {
                hypotheses.push(Hypothesis {
                    name: name.to_owned(),
                    ty,
                });
            }
        }
    }

    let mut dev = match Dev::new() {
        Ok(dev) => dev,
        Err(error) => {
            return declined("unknown", &format!("the ℕ prelude did not build: {error:?}"));
        }
    };
    match prove_to_lean_term(&mut dev, &hypotheses, &goal) {
        Ok(term) => accepted(environment_id, &term),
        Err(decline) => {
            let reason = decline.reason();
            declined(reason, decline.detail())
        }
    }
}

fn main() {
    let timeout_ms = std::env::var("AXEYUM_TACTIC_TIMEOUT_MS")
        .ok()
        .and_then(|value| value.parse::<u64>().ok())
        .unwrap_or(DEFAULT_TIMEOUT_MS);

    let mut raw = String::new();
    if let Err(error) = std::io::stdin().read_to_string(&mut raw) {
        let response = declined("unsupported", &format!("could not read stdin: {error}"));
        println!("{response}");
        return;
    }

    let (sender, receiver) = mpsc::channel();
    // The worker is deliberately detached: the kernel's prelude build wants a
    // deep stack (`on_a_deep_stack`), and a timeout must not wait on it.
    std::thread::spawn(move || {
        let owned = raw;
        let response = on_a_deep_stack(move || handle(&owned));
        // A closed receiver means the timeout already answered; that is the
        // expected race, not an error.
        let _ = sender.send(response);
    });

    let response = receiver
        .recv_timeout(Duration::from_millis(timeout_ms))
        .unwrap_or_else(|_| {
            declined(
                "timeout",
                &format!("the sidecar's budget of {timeout_ms} ms expired"),
            )
        });

    let mut stdout = std::io::stdout();
    if writeln!(stdout, "{response}").is_err() || stdout.flush().is_err() {
        // Could not answer at all: this is the one nonzero exit.
        std::process::exit(1);
    }
    // The worker may still be running; the process is done either way.
    std::process::exit(0);
}
