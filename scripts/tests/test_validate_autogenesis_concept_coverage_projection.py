"""Controls for the family-topic concept projection.

ADR-0553 removed the formalization and kernel-anchor dimensions, so the four
controls over them are gone. They are NOT replaced by weaker versions: a control
that asserts a field is absent, and one that asserts the projection still
matches the reviewed crosswalk, are what keep the removal from being reversed by
accident. `test_projection_never_names_held_out_fact` survives unchanged in
intent and is the one that must never be dropped -- it is the blind-population
guarantee.
"""
from __future__ import annotations
import copy,importlib.util,json,pathlib,unittest
ROOT=pathlib.Path(__file__).resolve().parents[2]
SPEC=importlib.util.spec_from_file_location('concept_coverage',ROOT/'scripts/validate-autogenesis-concept-coverage-projection.py');assert SPEC and SPEC.loader
CC=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(CC)
class Controls(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.data=json.loads((ROOT/'artifacts/autogenesis/concept-coverage-projection-v1.json').read_text())
 def test_current_valid(self):self.assertEqual(CC.validate(self.data),[])
 def test_invented_topic_count_rejected(self):
  d=copy.deepcopy(self.data);r=next(r for r in d['concepts'] if r['family_topic_fact_ids']);r['family_topic_fact_count']+=1;self.assertTrue(any('family-topic count' in e for e in CC.validate(d)))
 def test_coverage_state_other_than_family_topic_only_rejected(self):
  d=copy.deepcopy(self.data);d['concepts'][0]['coverage_state']='fact-formalization-present';self.assertTrue(any('only coverage state' in e for e in CC.validate(d)))
 def test_readded_formalization_dimension_rejected(self):
  """ADR-0553. The columns may not return without a local concept vocabulary."""
  d=copy.deepcopy(self.data);d['concepts'][0]['qualified_formalization_fact_ids']=['F:invented'];self.assertTrue(any('removed by ADR-0553' in e for e in CC.validate(d)))
 def test_readded_kernel_anchor_dimension_rejected(self):
  d=copy.deepcopy(self.data);d['concepts'][0]['kernel_semantic_anchor_ids']=['Kernel.invented'];self.assertTrue(any('removed by ADR-0553' in e for e in CC.validate(d)))
 def test_concept_absent_from_the_crosswalk_rejected(self):
  d=copy.deepcopy(self.data);d['concepts'][0]['concept_id']='C:invented';self.assertTrue(any('do not match the reviewed crosswalk' in e for e in CC.validate(d)))
 def test_projection_never_names_held_out_fact(self):
  nursery=json.loads((ROOT/'artifacts/autogenesis/nursery-v1.json').read_text());held={r['fact_id'] for r in nursery['entries'] if r['partition']=='held-out'}
  ids={i for r in self.data['concepts'] for i in r['family_topic_fact_ids']}
  self.assertTrue(ids,'vacuity guard: the projection names no facts at all')
  self.assertFalse(held.intersection(ids))
if __name__=='__main__':unittest.main()
