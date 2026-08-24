#!/usr/bin/env python3
"""Freeze the outcome contract before a general producer is executed."""
from __future__ import annotations
import argparse,hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1];AUTO=ROOT/'artifacts/autogenesis';FRONTIER=AUTO/'producer-evaluation-frontier-v1.json';OUT=AUTO/'producer-evaluation-protocol-v1.json'
TAXONOMY=['unsupported-statement-shape','missing-reusable-theorem','missing-algebraic-normalization','binder-or-generalization-failure','search-budget-exhausted','reconstruction-failure','nonempty-axiom-footprint']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def build():
 d=json.loads(FRONTIER.read_text());c=d['census'];controls=d['must_decline_control_fact_ids']
 if not controls or c['candidate_facts']+len(controls)!=c['evaluation_dependency_ready_facts']:raise ValueError('evaluation frontier lacks a non-vacuous candidate/control partition')
 return {'schema_version':1,'kind':'axeyum-autogenesis-producer-evaluation-protocol','state':'preregistered-before-general-producer-execution','inputs':{'evaluation_frontier_path':str(FRONTIER.relative_to(ROOT)),'evaluation_frontier_sha256':sha(FRONTIER),'candidate_fact_count':c['candidate_facts'],'must_decline_control_count':len(controls),'evaluation_partitions':d['derivation']['evaluation_partitions']},'outcome_contract':{'one_row_per_input_fact':True,'required_stages':['adapter','producer','reconstruction','checker'],'decline_taxonomy':[{'id':x,'status':'preregistered'} for x in TAXONOMY],'must_decline_policy':'every listed control must have a declined outcome; any admitted, kernel-accepted, reproduced, or admitted-to-ledger control voids the entire census','success_policy':'every kernel-accepted proposal requires independent checking and clean replay before it can count as reproduced; only an authorized fact transition can count as admitted'},'funnel':['eligible','proposals','kernel_accepted','cleanly_reproduced','admitted'],'forbidden_inputs':['held-out fact identifiers','target-name dispatch tables','manually supplied proof plans','upstream proof bodies'],'trust_boundary':'evaluation protocol only; it does not register an operation, authorize proof search, prove a fact, or admit a ledger transition'}
def main():
 a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');x=a.parse_args()
 try:r=json.dumps(build(),indent=2,sort_keys=True)+'\n'
 except (OSError,json.JSONDecodeError,KeyError,ValueError) as e:print(f'AUTOGENESIS_EVALUATION_PROTOCOL_ERROR|{e}',file=sys.stderr);return 1
 if x.check:
  if not OUT.is_file() or OUT.read_text()!=r:print('AUTOGENESIS_EVALUATION_PROTOCOL_ERROR|protocol is stale',file=sys.stderr);return 1
 else:OUT.write_text(r)
 d=json.loads(r);print(f"AUTOGENESIS_EVALUATION_PROTOCOL|candidates={d['inputs']['candidate_fact_count']}|controls={d['inputs']['must_decline_control_count']}|declines={len(TAXONOMY)}");return 0
if __name__=='__main__':raise SystemExit(main())
