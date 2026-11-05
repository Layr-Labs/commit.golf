import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_submission import check
from artifact_fixture import manifest


class PolicyTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        (self.root / 'CommitGolfCandidate').mkdir()
        (self.root / 'Solution.lean').write_text('import CommitGolfCandidate.Helper\n')
        (self.root / 'CommitGolfCandidate' / 'Helper.lean').write_text(
            'import CommitGolf.Statements\nimport CommitGolf.Oracle\n')
        self.claim = {'proofBytes': 76800, 'commitCycles': 2400, 'openingCycles': 1600}
        self.write_claim()
        (self.root / 'programs.json').write_text(json.dumps(manifest()))

    def write_claim(self):
        (self.root / 'claim.json').write_text(json.dumps(self.claim))

    def tearDown(self):
        self.temp.cleanup()

    def test_valid_submission(self):
        value = check(self.root)
        self.assertTrue(value['ok'], value['errors'])
        self.assertEqual(value['claim'], self.claim)

    def test_submission_instructions_are_allowed(self):
        (self.root / 'README.md').write_text('Submission instructions, not proof code.\n')
        result = check(self.root)
        self.assertTrue(result['ok'], result['errors'])

    def test_preserved_baseline_cannot_be_imported(self):
        (self.root / 'Solution.lean').write_text('import CommitGolfBaseline\n')
        self.assertFalse(check(self.root)['ok'])

    def test_cross_import_is_rejected(self):
        (self.root / 'CommitGolfCandidate' / 'Helper.lean').write_text('import CommitGolfCandidateX.Helper\n')
        value = check(self.root)
        self.assertFalse(value['ok'])
        self.assertIn('outside the allowed modules', value['errors'][0])

    def test_challenge_import_is_rejected(self):
        (self.root / 'Solution.lean').write_text('import CommitGolf.Challenge\n')
        value = check(self.root)
        self.assertFalse(value['ok'])
        self.assertIn('outside the allowed modules', value['errors'][0])

    def test_generated_artifact_import_is_allowed(self):
        (self.root / 'Solution.lean').write_text('import CommitGolf.Artifact\n')
        self.assertTrue(check(self.root)['ok'])

    def test_resource_libraries_and_contract_imports_have_exact_namespace_boundaries(self):
        for module in ('CommitGolf.Resources', 'ArkLib.Interaction.Oracle.Source',
                       'CompPoly.Univariate.Raw.Size'):
            with self.subTest(module=module):
                (self.root / 'Solution.lean').write_text(f'import {module}\n')
                self.assertTrue(check(self.root)['ok'])
        for module in ('CommitGolf.ResourcesExtra', 'ArkLibExtra.Source', 'CompPolyExtra.Raw'):
            with self.subTest(module=module):
                (self.root / 'Solution.lean').write_text(f'import {module}\n')
                self.assertFalse(check(self.root)['ok'])

    def test_delivered_program_manifest_is_required(self):
        (self.root / 'programs.json').unlink()
        value = check(self.root)
        self.assertFalse(value['ok'])
        self.assertTrue(any('programs.json' in error for error in value['errors']))

    def test_candidate_cannot_supply_generated_artifact_module(self):
        (self.root / 'CommitGolf').mkdir()
        (self.root / 'CommitGolf' / 'Artifact.lean').write_text('axiom replacement : Nat\n')
        self.assertFalse(check(self.root)['ok'])

    def test_alternate_module_headers_are_rejected(self):
        for header in ('module\nimport Lake\n', 'prelude\n', 'public import Lake\n', 'meta import Lake\n'):
            (self.root / 'CommitGolfCandidate' / 'Helper.lean').write_text(header)
            value = check(self.root)
            self.assertFalse(value['ok'], header)
            self.assertIn('alternate module headers', value['errors'][0])

    def test_symlink_and_archive_file_are_rejected(self):
        (self.root / 'CommitGolfCandidate' / 'Alias.lean').symlink_to('Helper.lean')
        (self.root / 'notes.zip').write_bytes(b'irrelevant')
        value = check(self.root)
        self.assertFalse(value['ok'])
        self.assertGreaterEqual(len(value['errors']), 2)

    def test_claim_needs_exactly_the_three_bounds(self):
        self.claim['extra'] = 1
        self.write_claim()
        value = check(self.root)
        self.assertFalse(value['ok'])
        self.assertIn('exactly proofBytes, commitCycles and openingCycles', value['errors'][0])

    def test_scores_are_nonnegative_integers(self):
        for bad in (-1, 1.5, '7', True):
            self.claim['commitCycles'] = bad
            self.write_claim()
            value = check(self.root)
            self.assertFalse(value['ok'], bad)

    def test_score_uses_proof_bytes_and_both_cycle_bounds(self):
        result = check(self.root)
        self.assertEqual(result['score'], 76800 * (2400 + 1600))

    def test_scores_are_capped(self):
        self.claim = {'proofBytes': 2**53 - 1, 'commitCycles': 1, 'openingCycles': 0}
        self.write_claim()
        self.assertTrue(check(self.root)['ok'])
        self.claim['proofBytes'] += 1
        self.write_claim()
        self.assertFalse(check(self.root)['ok'])

    def test_product_overflow_is_rejected(self):
        self.claim = {'proofBytes': 2**30, 'commitCycles': 2**30, 'openingCycles': 1}
        self.write_claim()
        self.assertFalse(check(self.root)['ok'])

    def test_old_claim_and_solver_selected_commitment_size_are_rejected(self):
        for value in ({'proofBytes': 1, 'checkCalls': 1},
                      {**self.claim, 'commitmentBytes': 0}):
            self.claim = value
            self.write_claim()
            self.assertFalse(check(self.root)['ok'])


if __name__ == '__main__':
    unittest.main()
