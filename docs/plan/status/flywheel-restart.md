# Lane: flywheel-restart

Status: IN PROGRESS (stub; committed early per lane protocol)

## Scope

1. Dispatch the one `admissible_via_contract` fact the frontier selects
   (`F:ml430-nat-coprime-factorizationlcmleft-factorizationlcmright-e7db70ce`)
   through the `nat-coprime-family-v1` producer contract, and record the
   outcome — produced or declined — as an artifact the validators accept.
2. Land ADR-1510's two guards as checker changes:
   - `scripts/validate-producer-contracts.py`: a contract records the open
     population it was sized against and must retire when that empties.
   - `scripts/validate-producer-contract-declines.py`: a decline whose fact is
     now settled must carry a `resolution` block.
   Each guard mutation-verified to kill exactly one test.

## Landed changes

(none yet)
