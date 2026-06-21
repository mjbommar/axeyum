# WASM Solver Playground

Run Axeyum **in your browser** — paste an SMT-LIB query, press Solve, get a
verdict. The solver is compiled to WebAssembly and runs *client-side*: no server,
no install, nothing leaves the page.

This is our answer to "interactive, executable docs" (the Verso / Jupyter
inspiration). Instead of a notebook kernel, the reader runs the **actual solver**
— so a playground example can't silently drift from the code, because it *is* the
code. See the rationale in [internals/documentation.md](../internals/documentation.md).

## Try it

Open [`index.html`](index.html) from a built docs site (or any static server).
A starter query is pre-loaded:

```smt2
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= (bvadd x #x01) #x00))
(check-sat)
```

Expected: **`sat`** (`x = #xff`). Toggle to the contradictory variant for
**`unsat`**, and try a wide multiply for an honest **`unknown`**.

## Status

The playground UI ([`index.html`](index.html)) is complete and ships with a
graceful fallback: until the WASM bundle is built, it explains how to enable
live solving and still lets you read/edit examples. The binding crate
([`crates/axeyum-wasm`](../../crates/axeyum-wasm)) is written and ready; it is
**not yet in the workspace** (so it can't entangle the main build), and the
bundle build is gated on the `wasm32` toolchain plus a green workspace.

## Build the bundle (activation)

```sh
# one-time
rustup target add wasm32-unknown-unknown
cargo install wasm-pack

# add "crates/axeyum-wasm" to [workspace].members in the root Cargo.toml, then:
wasm-pack build crates/axeyum-wasm --target web --out-dir ../../docs/playground/pkg

# serve the docs (the page needs to be over http for ES-module imports)
python3 -m http.server -d docs/playground 8080   # → http://localhost:8080
```

`wasm-pack` emits `docs/playground/pkg/axeyum_wasm.js` + `.wasm`; the page
imports them automatically. (`pkg/` is generated — git-ignore it.)

## How it works

```mermaid
flowchart LR
    ta["SMT-LIB textarea"] --> js["index.html (JS)"]
    js -->|"solve_smtlib_json(text, timeout)"| wasm["axeyum_wasm.wasm<br/>(axeyum-solver compiled to WASM)"]
    wasm -->|"{status, logic, detail}"| js
    js --> out["verdict panel<br/>sat / unsat / unknown"]
    classDef a fill:#eef,stroke:#557;
    classDef w fill:#e7f6e7,stroke:#2e7d32;
    class ta,js,out a;
    class wasm w;
```

The same `solve_smtlib` you'd call from Rust runs in the browser, including model
replay — a `sat` is still verified against the original query before it's shown.

## Why this is the right interactivity for Axeyum

- **WASM over Jupyter** — no kernel server; the solver is Rust, so WebAssembly is
  the native fit, and it runs entirely client-side (great for static docs / CI).
- **Real engine over canned output** — examples execute the committed solver, so
  they stay correct by construction (the Verso spirit, solver-flavored).
- **Pure Rust** — the default solver build is already wasm-compatible (ADR-0017),
  so this adds no C/C++ dependency.
