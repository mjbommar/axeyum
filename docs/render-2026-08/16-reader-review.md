# 16 -- Coordinator reader review (proxy for the owner's cold read)

Date: 2026-08-21. Method: headless Chromium screenshots (1280px and
420px) of certificate.html, facts-pilot-arith.html, facts-atlas.html,
reviewed visually by the coordinator. The OWNER's cold read remains the
binding P0 sign-off; this is the proxy pass that gates P1 launch.

VERDICT: PASS. From certificate.html alone a cold reader can state what
was proved (Theorems 1-4 as claim cards with statements), what checked
it (the evidence boxes: record id, exit status, checked-by line), and
how to replay (copy-button rustc command + artifact name). The atlas
leads with "Disagreements in our favour" -- the ledger's headline metric
as the opening table. The pilot page's 17-node dependency graph is
legible with a sensible legend and hover guidance.

GRIPES (queued to P1-CARDS polish):
1. Title duplication: page header h1 and the first section h1 repeat
   verbatim on pilot/atlas pages.
2. Badge duplication: claim-card header badge repeats inside the
   evidence box; one should be the compact form.
3. Atlas/pilot node links are dead affordances until per-fact card pages
   exist (already the top P1 item).
4. Certificate replay command needs a wrapping/scroll polish pass at
   420px width (verify during P1 against the narrow screenshot).
