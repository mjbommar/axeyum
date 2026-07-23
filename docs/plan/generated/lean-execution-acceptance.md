# TL0.7.4 Lean execution acceptance summary

Generated from [`lean-execution-acceptance-v1.json`](../lean-execution-acceptance-v1.json).

- Status: **accepted no-credit real controls**
- Implementation revision: `679f4b9d1941b166c86db652501f1ba7df417da0`
- Official exporter source: `a3e35a584f59b390667db7269cd37fca8575e4bf` / tree `e8b4adcea8445abbe0ae656eb6067d079e3efca8`
- Built exporter SHA-256: `8e763913b03762488571a93ced6ec1a4e04f7d8eebbe40bd1215ba41a6bd4449` (206,915,024 bytes)
- Observed process attempts / completed controls: **3 / 2**
- Retained failed compile attempts: **1**
- Retained evidence: **67 files / 142,523 bytes**
- U2 cases, official outcomes, Axeyum outcomes, paired cells, and performance rows: **0**
- Terminal Lean parity credit: **0**

| Control | Completion SHA-256 | Stable projection SHA-256 |
|---|---|---|
| `pinned-lean-compile-preflight-4g-tstack512m` | `412930affb456cf9b47970af0e886b96dfc370ddbd13abf8d5cba32c681dae5f` | `a3af6c24011d8eb524fed0c1fa8e45cfd2e2330e44adc193b2f1cbea9f54030f` |
| `official-lean4export-flat-export-8g` | `9be90a95ed7ade1015598114d43b182b193edbf6063765aee0eae7ce7e14f3a0` | `3585e2daed64c88806906c5921c15f1f1dd14a7e16c7150346a4fe7946cc9ff4` |

The compile and export processes are real, but both selections are empty. The
export stream is byte-equal to the preregistered 65-line reference. This result
does not run U2, import or check with Axeyum, form a pair, measure performance,
or qualify power/host/network/object durability.
