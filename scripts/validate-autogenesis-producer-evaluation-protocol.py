#!/usr/bin/env python3
"""Validate that a general producer's evaluation contract can falsify it."""
from __future__ import annotations
import json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1];P=ROOT/'artifacts/autogenesis/producer-evaluation-protocol-v1.json'
REQUIRED={'unsupported-statement-shape','missing-reusable-theorem','missing-algebraic-normalization','binder-or-generalization-failure','search-budget-exhausted','reconstruction-failure','nonempty-axiom-footprint'}
def validate(d):
 e=[]
 if d.get('kind')!='axeyum-autogenesis-producer-evaluation-protocol':return ['invalid protocol kind']
 if d.get('state')!='preregistered-before-general-producer-execution':e.append('protocol is not pre-registered')
 i=d.get('inputs',{});o=d.get('outcome_contract',{})
 if not isinstance(i,dict) or i.get('evaluation_partitions')!=['development','train'] or not isinstance(i.get('evaluation_frontier_sha256'),str) or len(i['evaluation_frontier_sha256'])!=64:e.append('missing safe evaluation frontier identity')
 if not isinstance(i,dict) or not isinstance(i.get('candidate_fact_count'),int) or i['candidate_fact_count']<=0 or not isinstance(i.get('must_decline_control_count'),int) or i['must_decline_control_count']<=0:e.append('candidate or must-decline control set is vacuous')
 stages=o.get('required_stages') if isinstance(o,dict) else None
 if stages!=['adapter','producer','reconstruction','checker']:e.append('outcome stages are incomplete')
 taxonomy=o.get('decline_taxonomy') if isinstance(o,dict) else None
 ids={x.get('id') for x in taxonomy if isinstance(x,dict)} if isinstance(taxonomy,list) else set()
 if ids!=REQUIRED:e.append('decline taxonomy is incomplete or altered')
 if not isinstance(o,dict) or 'voids the entire census' not in o.get('must_decline_policy',''):e.append('must-decline failure does not void census')
 if d.get('funnel')!=['eligible','proposals','kernel_accepted','cleanly_reproduced','admitted']:e.append('funnel is incomplete')
 forbidden=d.get('forbidden_inputs');
 if not isinstance(forbidden,list) or len(forbidden)<4:e.append('forbidden input boundary is incomplete')
 return e
def main():
 d=json.loads(P.read_text());e=validate(d)
 for x in e:print('AUTOGENESIS_EVALUATION_PROTOCOL_ERROR|'+x,file=sys.stderr)
 if e:return 1
 i=d['inputs'];print(f"AUTOGENESIS_EVALUATION_PROTOCOL_OK|candidates={i['candidate_fact_count']}|controls={i['must_decline_control_count']}|declines={len(REQUIRED)}");return 0
if __name__=='__main__':raise SystemExit(main())
