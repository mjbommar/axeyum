from __future__ import annotations
import copy,importlib.util,json,pathlib,unittest
ROOT=pathlib.Path(__file__).resolve().parents[2]
SPEC=importlib.util.spec_from_file_location('concept_coverage',ROOT/'scripts/validate-autogenesis-concept-coverage-projection.py');assert SPEC and SPEC.loader
CC=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(CC)
class Controls(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.data=json.loads((ROOT/'artifacts/autogenesis/concept-coverage-projection-v1.json').read_text())
 def test_current_valid(self):self.assertEqual(CC.validate(self.data),[])
 def test_invented_formal_count_rejected(self):
  d=copy.deepcopy(self.data);r=next(r for r in d['concepts'] if r['qualified_formalization_fact_ids']);r['qualified_formalization_fact_count']+=1;self.assertTrue(any('formalization count' in e for e in CC.validate(d)))
 def test_topic_only_cannot_claim_formalization(self):
  d=copy.deepcopy(self.data);r=next(r for r in d['concepts'] if not r['qualified_formalization_fact_ids']);r['coverage_state']='fact-formalization-present';self.assertTrue(any('conflates' in e for e in CC.validate(d)))
 def test_invented_kernel_anchor_count_rejected(self):
  d=copy.deepcopy(self.data);r=next(r for r in d['concepts'] if r['kernel_semantic_anchor_ids']);r['kernel_semantic_anchor_count']+=1;self.assertTrue(any('kernel anchor count' in e for e in CC.validate(d)))
 def test_invented_kernel_anchor_rejected(self):
  d=copy.deepcopy(self.data);r=next(r for r in d['concepts'] if r['kernel_semantic_anchor_ids']);r['kernel_semantic_anchor_ids'][0]='Kernel.invented';self.assertTrue(any('do not exactly match active overlay links' in e for e in CC.validate(d)))
 def test_projection_never_names_held_out_fact(self):
  nursery=json.loads((ROOT/'artifacts/autogenesis/nursery-v1.json').read_text());held={r['fact_id'] for r in nursery['entries'] if r['partition']=='held-out'}
  ids={i for r in self.data['concepts'] for k in ('family_topic_fact_ids','qualified_formalization_fact_ids') for i in r[k]}
  self.assertFalse(held.intersection(ids))
if __name__=='__main__':unittest.main()
