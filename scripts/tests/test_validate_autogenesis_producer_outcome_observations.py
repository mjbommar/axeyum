from __future__ import annotations
import copy,importlib.util,json,pathlib,unittest
ROOT=pathlib.Path(__file__).resolve().parents[2]
SPEC=importlib.util.spec_from_file_location('producer_outcomes',ROOT/'scripts/validate-autogenesis-producer-outcome-observations.py');assert SPEC and SPEC.loader
PO=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(PO)
class Controls(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.data=json.loads((ROOT/'artifacts/autogenesis/producer-outcome-observations-v1.json').read_text())
 def test_current_valid(self):self.assertEqual(PO.validate(self.data),[])
 def test_held_out_census_rejected(self):
  d=copy.deepcopy(self.data);d['census']['held_out_observed_facts']=1;self.assertTrue(any('held-out' in e for e in PO.validate(d)))
 def test_group_partition_outside_train_development_rejected(self):
  d=copy.deepcopy(self.data);d['groups'][0]['partition']='held-out';self.assertTrue(any('outside train/development' in e for e in PO.validate(d)))
 def test_duplicate_fact_rejected(self):
  d=copy.deepcopy(self.data);d['groups'][1]['observed_fact_ids'].append(d['groups'][0]['observed_fact_ids'][0]);d['groups'][1]['observed_fact_ids'].sort();d['groups'][1]['observed_fact_count']+=1;d['census']['observed_facts']+=1;self.assertTrue(any('more than one' in e for e in PO.validate(d)))
 def test_invented_outcome_count_rejected(self):
  d=copy.deepcopy(self.data);d['census']['outcomes']['admissible-proof']+=1;self.assertTrue(any('outcome census' in e for e in PO.validate(d)))
if __name__=='__main__':unittest.main()
