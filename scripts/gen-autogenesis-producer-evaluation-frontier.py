#!/usr/bin/env python3
"""Derive the safe, dependency-ready train/development producer frontier."""
from __future__ import annotations
import argparse,hashlib,importlib.util,json,pathlib,sys
from collections import defaultdict
from typing import Any
ROOT=pathlib.Path(__file__).resolve().parents[1];AUTO=ROOT/'artifacts/autogenesis';OUT=AUTO/'producer-evaluation-frontier-v1.json';NURSERY=AUTO/'nursery-v1.json';CATALOG=AUTO/'mathlib-nat-int-fact-catalog-v1.json';MUST_DECLINE=AUTO/'must-decline-mutations-v1.json';FRONTIER=ROOT/'scripts/fact-frontier.py'
class Error(RuntimeError):pass
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def module():
 s=importlib.util.spec_from_file_location('evaluation_frontier',FRONTIER)
 if s is None or s.loader is None:raise Error('cannot load fact frontier')
 m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
def build():
 m=module()
 try:
  facts=m.load();machine=m.build_machine_frontier(facts);nursery=json.loads(NURSERY.read_text());catalog=json.loads(CATALOG.read_text());must_decline=json.loads(MUST_DECLINE.read_text())
 except (OSError,json.JSONDecodeError,KeyError,m.FrontierError) as e:raise Error(str(e)) from e
 partition={r['fact_id']:r['partition'] for r in nursery['entries'] if isinstance(r,dict) and isinstance(r.get('fact_id'),str) and isinstance(r.get('partition'),str)}
 reviewed={r['fact_id']:r for r in catalog['facts'] if isinstance(r,dict) and isinstance(r.get('fact_id'),str)}
 ready=machine['selection']['ready_fact_ids'];allowed={'train','development'};selected=[f for f in ready if partition.get(f) in allowed];held=[f for f in ready if partition.get(f)=='held-out'];outside=[f for f in ready if f not in partition]
 if any(f not in reviewed for f in selected):raise Error('evaluation-ready fact lacks reviewed catalog entry')
 controls=sorted(r['fact_id'] for r in must_decline['entries'] if isinstance(r,dict) and isinstance(r.get('fact_id'),str))
 if not controls or not set(controls).issubset(selected):raise Error('must-decline controls are absent from evaluation-ready frontier')
 grouped=defaultdict(list)
 for f in selected:
  r=reviewed[f];grouped[(partition[f],r['family'],r['statement_shape'],r['dependency_component_id'])].append(f)
 groups=[{'partition':p,'family':fam,'statement_shape':shape,'dependency_component_id':component,'fact_ids':sorted(ids),'fact_count':len(ids)} for (p,fam,shape,component),ids in sorted(grouped.items())]
 by_partition={p:sum(len(g['fact_ids']) for g in groups if g['partition']==p) for p in sorted(allowed)}
 return {'schema_version':1,'kind':'axeyum-autogenesis-producer-evaluation-frontier','derivation':{'source':'scripts/fact-frontier.py build_machine_frontier intersected with nursery train/development','frontier_sha256':machine['frontier_sha256'],'ledger_sha256':machine['ledger']['ledger_sha256'],'nursery_sha256':sha(NURSERY),'reviewed_fact_catalog_sha256':sha(CATALOG),'must_decline_controls_sha256':sha(MUST_DECLINE),'evaluation_partitions':['development','train'],'trust_boundary':'deterministic train/development producer input only; never held-out inspection, operation registration, proof, or admission authority'},'census':{'global_dependency_ready_facts':len(ready),'evaluation_dependency_ready_facts':len(selected),'candidate_facts':len(selected)-len(controls),'must_decline_controls':len(controls),'by_partition':by_partition,'excluded_held_out_ready_facts':len(held),'excluded_outside_evaluation_ready_facts':len(outside),'groups':len(groups)},'must_decline_control_fact_ids':controls,'groups':groups}
def main():
 a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');x=a.parse_args()
 try:rendered=json.dumps(build(),indent=2,sort_keys=True)+'\n'
 except Error as e:print(f'AUTOGENESIS_EVALUATION_FRONTIER_ERROR|{e}',file=sys.stderr);return 1
 if x.check:
  if not OUT.is_file() or OUT.read_text()!=rendered:print('AUTOGENESIS_EVALUATION_FRONTIER_ERROR|projection is stale',file=sys.stderr);return 1
 else:OUT.write_text(rendered)
 d=json.loads(rendered);print(f"AUTOGENESIS_EVALUATION_FRONTIER|ready={d['census']['evaluation_dependency_ready_facts']}|train={d['census']['by_partition']['train']}|development={d['census']['by_partition']['development']}|groups={d['census']['groups']}");return 0
if __name__=='__main__':raise SystemExit(main())
