# 254 — Producer-evaluation result contract

The next producer run now has a fail-closed result schema and validator. A
result must bind the pre-registered protocol, account for every one of the 98
safe input facts exactly once, keep its funnel monotone, and reject any
must-decline control that reaches kernel acceptance, reproduction, or admission.
No result artifact has been created: this is only the checker that prevents a
future run from reporting an incomplete or unfalsifiable funnel.
