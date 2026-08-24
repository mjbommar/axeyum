from __future__ import annotations
import copy,importlib.util,json,pathlib,unittest
ROOT=pathlib.Path(__file__).resolve().parents[2];s=importlib.util.spec_from_file_location('ef',ROOT/'scripts/validate-autogenesis-producer-evaluation-frontier.py');assert s and s.loader;EF=importlib.util.module_from_spec(s);s.loader.exec_module(EF)
class Controls(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.data=json.loads((ROOT/'artifacts/autogenesis/producer-evaluation-frontier-v1.json').read_text())
 def test_current_valid(self):self.assertEqual(EF.validate(self.data),[])
 def test_group_outside_partition_rejected(self):
  d=copy.deepcopy(self.data);d['groups'][0]['partition']='held-out';self.assertTrue(any('outside evaluation' in x for x in EF.validate(d)))
 def test_duplicate_fact_rejected(self):
  d=copy.deepcopy(self.data);d['groups'][1]['fact_ids'].append(d['groups'][0]['fact_ids'][0]);d['groups'][1]['fact_ids'].sort();d['groups'][1]['fact_count']+=1;self.assertTrue(any('more than one' in x for x in EF.validate(d)))
 def test_global_partition_accounting_rejected(self):
  d=copy.deepcopy(self.data);d['census']['excluded_held_out_ready_facts']+=1;self.assertTrue(any('does not partition' in x for x in EF.validate(d)))
 def test_frontier_never_names_held_out_fact(self):
  n=json.loads((ROOT/'artifacts/autogenesis/nursery-v1.json').read_text());held={r['fact_id'] for r in n['entries'] if r['partition']=='held-out'};ids={f for g in self.data['groups'] for f in g['fact_ids']};self.assertFalse(held.intersection(ids))
if __name__=='__main__':unittest.main()
