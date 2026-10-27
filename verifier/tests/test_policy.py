import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_submission import check


class PolicyTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        (self.root / 'CommitGolfCandidate').mkdir()
        (self.root / 'Solution.lean').write_text('import CommitGolfCandidate.Helper\n')
        (self.root / 'CommitGolfCandidate' / 'Helper.lean').write_text(
            'import CommitGolf.Statements\nimport CommitGolf.BindingFinite\n')
        self.claim = {'proofBytes': 76800, 'checkCalls': 2400}
        self.write_claim()

    def write_claim(self):
        (self.root / 'claim.json').write_text(json.dumps(self.claim))

    def tearDown(self):
        self.temp.cleanup()

    def test_valid_submission(self):
        value = check(self.root)
        self.assertTrue(value['ok'], value['errors'])
        self.assertEqual(value['claim'], self.claim)

    def test_cross_import_is_rejected(self):
        (self.root / 'CommitGolfCandidate' / 'Helper.lean').write_text('import CommitGolfCandidateX.Helper\n')
        value = check(self.root)
        self.assertFalse(value['ok'])
        self.assertIn('outside the allowed modules', value['errors'][0])

    def test_shared_baseline_import_is_rejected(self):
        (self.root / 'Solution.lean').write_text('import CommitGolfBaseline.MerkleProof.Certificate\n')
        result = check(self.root)
        self.assertFalse(result['ok'])
        self.assertIn('outside the allowed modules', result['errors'][0])

    def test_challenge_import_is_rejected(self):
        (self.root / 'Solution.lean').write_text('import CommitGolf.Challenge\n')
        value = check(self.root)
        self.assertFalse(value['ok'])
        self.assertIn('outside the allowed modules', value['errors'][0])

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

    def test_claim_needs_exactly_the_two_scores(self):
        self.claim['extra'] = 1
        self.write_claim()
        value = check(self.root)
        self.assertFalse(value['ok'])
        self.assertIn('exactly proofBytes and checkCalls', value['errors'][0])

    def test_scores_are_nonnegative_integers(self):
        for bad in (-1, 1.5, '7', True):
            self.claim['checkCalls'] = bad
            self.write_claim()
            value = check(self.root)
            self.assertFalse(value['ok'], bad)

    def test_scores_are_capped(self):
        self.claim['proofBytes'] = 2**53 - 1
        self.write_claim()
        self.assertTrue(check(self.root)['ok'])
        self.claim['proofBytes'] = 2**53
        self.write_claim()
        value = check(self.root)
        self.assertFalse(value['ok'])
        self.assertIn('exceeds 2^53 - 1', value['errors'][0])


if __name__ == '__main__':
    unittest.main()
