#!/usr/bin/env python3
"""Validate that obstruction groups preserve, rather than invent, observations."""
from __future__ import annotations
import json, pathlib, sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PATH=ROOT/'artifacts/autogenesis/obstruction-projection-v1.json'
def validate(data):
    errors=[]
    if data.get('kind')!='axeyum-autogenesis-obstruction-projection': return ['invalid projection kind']
    episodes={e.get('id'):e for e in data.get('episodes',[])}
    for o in data.get('obstructions',[]):
        ids=o.get('affected_episodes',[]); known=o.get('complete_known_blocker_set',[])
        if not ids or any(i not in episodes for i in ids): errors.append(f"{o.get('id')}: missing episode")
        observed=sorted({episodes[i]['obstruction_category'] for i in ids if i in episodes})
        if known!=observed: errors.append(f"{o.get('id')}: blocker set does not match episodes")
        if o.get('first_observed_blocker')!=episodes[ids[0]]['obstruction_category']: errors.append(f"{o.get('id')}: first blocker is not first observed")
        if o.get('resolution_commit') is not None or o.get('measured_before_after') is not None: errors.append(f"{o.get('id')}: generator cannot claim unbound resolution")
        status=o.get('candidate_capability_internal_status')
        if status not in {'not-applicable','present-in-knowledge-overlay','not-present-in-knowledge-overlay'}: errors.append(f"{o.get('id')}: invalid candidate capability status")
        if (o.get('candidate_capability') is None)!=(status=='not-applicable'): errors.append(f"{o.get('id')}: candidate capability and status disagree")
    if data.get('census',{}).get('episodes')!=len(episodes): errors.append('episode census mismatch')
    expected={status:sum(o.get('candidate_capability_internal_status')==status for o in data.get('obstructions',[])) for status in sorted({o.get('candidate_capability_internal_status') for o in data.get('obstructions',[])})}
    if data.get('census',{}).get('candidate_capability_statuses')!=expected: errors.append('candidate capability census mismatch')
    return errors
def main():
    data=json.loads(PATH.read_text()); errors=validate(data)
    for e in errors: print('AUTOGENESIS_OBSTRUCTION_ERROR|'+e,file=sys.stderr)
    if errors:return 1
    print(f"AUTOGENESIS_OBSTRUCTION_OK|episodes={len(data['episodes'])}|obstructions={len(data['obstructions'])}");return 0
if __name__=='__main__':raise SystemExit(main())
