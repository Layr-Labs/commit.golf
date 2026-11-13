import json
import hashlib
import os
import runpy
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'verifier'))
from scoring import score_claim


class RunnerTests(unittest.TestCase):
    def run_runner(self, report, code=0, track="product"):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            (root / 'scripts').mkdir()
            submission = root / ('submission-pareto' if track == 'pareto' else 'submission')
            submission.mkdir()
            (submission / 'programs.json').write_bytes(b'delivered program fixture')
            output = root / ('scripts/pareto/score.json' if track == 'pareto' else 'scripts/score.json')
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text('{"score": 1}')  # stale output must never survive a failure
            old = Path.cwd()
            try:
                os.chdir(root)
                with patch.object(sys, 'argv', ['run.py', '--track', track]), patch.object(sys, 'platform', 'linux'), \
                     patch('subprocess.run', return_value=SimpleNamespace(returncode=code, stdout=json.dumps(report))) as verify, \
                     patch('subprocess.check_output', return_value='contract\n'), patch('builtins.print'):
                    try:
                        runpy.run_path(str(ROOT / 'scripts/run.py'), run_name='__main__')
                    except SystemExit as exc:
                        return exc.code, output.exists(), None
                self.assertEqual(verify.call_args.args[0][3], submission.name)
                return 0, output.exists(), json.loads(output.read_text())
            finally:
                os.chdir(old)

    def report(self):
        claim = {'proofBytes': 8, 'commitCycles': 7, 'openingCycles': 6}
        return {'status': 'verified', 'claim': claim, 'score': score_claim(claim),
                'contract_commit': 'contract',
                'artifact_digest': hashlib.sha256(b'delivered program fixture').hexdigest()}

    def test_verified_certificate_emits_combined_score(self):
        status, exists, result = self.run_runner(self.report())
        self.assertEqual(status, 0)
        self.assertTrue(exists)
        self.assertEqual(result['score'], 104)
        self.assertEqual(result['metrics']['proofBytes'], 8)
        self.assertEqual(result['metrics']['proverCycles'], 13)
        self.assertEqual(result['metrics']['artifactDigest'], self.report()['artifact_digest'])

    def test_rejection_leaves_no_score(self):
        for code in (0, 1):
            report = self.report()
            report['status'] = 'rejected'
            _, exists, _ = self.run_runner(report, code)
            self.assertFalse(exists)

    def test_mismatched_score_or_contract_leaves_no_score(self):
        for field, value in [('score', 1), ('score', 104.0), ('contract_commit', 'other'),
                             ('artifact_digest', '0' * 64), ('artifact_digest', None)]:
            report = self.report()
            report[field] = value
            status, exists, _ = self.run_runner(report)
            self.assertNotEqual(status, 0)
            self.assertFalse(exists)

    def test_overflow_leaves_no_score(self):
        report = self.report()
        report['claim']['commitCycles'] = 2**53 - 1
        _, exists, _ = self.run_runner(report)
        self.assertFalse(exists)

    def test_pareto_certificate_emits_ordered_objectives(self):
        status, exists, result = self.run_runner(self.report(), track='pareto')
        self.assertEqual(status, 0)
        self.assertTrue(exists)
        self.assertEqual(result['scores'], [13, 8])
        self.assertIs(result['valid'], True)
        self.assertNotIn('score', result)

    def test_pareto_failure_clears_stale_score(self):
        for field, value in [('status', 'rejected'), ('score', 1),
                             ('contract_commit', 'wrong'), ('artifact_digest', 'wrong')]:
            report = self.report()
            report[field] = value
            status, exists, _ = self.run_runner(report, track='pareto')
            self.assertNotEqual(status, 0)
            self.assertFalse(exists)
