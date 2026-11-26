"""Guard the real regression harness against accepting incidental failures."""
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from artifact import parse_artifact
from check_depth_linkage import make_cases, case_passes
from depth_profiles import depth_profile
from tracks import TRACKS


class DepthLinkageHarnessTests(unittest.TestCase):
    def test_modes_and_bytes_change_only_the_delivered_artifact(self):
        cases = make_cases()
        self.assertEqual(len(cases), 8)
        for name in {c.track for c in cases}:
            selected = [c for c in cases if c.track == name]
            self.assertEqual(len(selected), 4)
            matching, mode, changed_bytes, partial = selected
            self.assertEqual(mode.source, matching.source)
            self.assertEqual(changed_bytes.source, matching.source)
            base = json.loads(matching.artifact)
            m = json.loads(mode.artifact)
            self.assertNotEqual(m.pop('executionModes'), base['executionModes'])
            self.assertEqual(m, {k: v for k, v in base.items() if k != 'executionModes'})
            self.assertNotEqual(changed_bytes.artifact, matching.artifact)
            self.assertEqual(partial.artifact, matching.artifact)
            self.assertTrue(partial.full_certificate)
            self.assertIn('theorem certificate : True := True.intro', partial.source)
            for case in selected:
                parse_artifact(case.artifact, resource_model=TRACKS[name].depth_model)
                self.assertIn(depth_profile(TRACKS[name].depth_model).namespace, case.source)

    def test_partial_certificate_requires_specific_statement_mismatch(self):
        case = next(c for c in make_cases() if c.full_certificate)
        marker = "Challenge and solution theorem statement do not match: 'CommitGolf.Challenge.certificate'"
        good = 'Build completed successfully (123 jobs).\nuncaught exception: ' + marker + '\n'
        self.assertTrue(case_passes(case, {'status': 'rejected'}, good))
        for status in ('timeout', 'failed', 'policy_rejected', 'verified', None):
            self.assertFalse(case_passes(case, {'status': status}, good))
        for bad in ('', good.replace('certificate', 'another_target'),
                    good.replace('Build completed successfully (123 jobs).', ''),
                    'OOM killed compiler\n' + good, 'error: other failure\n' + good,
                    'PANIC unrelated\n' + good):
            self.assertFalse(case_passes(case, {'status': 'rejected'}, bad))

    def test_mode_rejection_requires_exact_equality_diagnostic(self):
        case = next(c for c in make_cases() if c.name.endswith('_mode'))
        line, source = next((i, s) for i, s in enumerate(case.source.splitlines(), 1)
                            if s.startswith('theorem submission_matches_artifact '))
        header = f'error: Solution.lean:{line}:{source.index("rfl")}: Tactic `rfl` failed: The left-hand side'
        good = (header + '\n  submission\nis not definitionally equal to the right-hand side\n'
                '  Artifact.depthSubmission\n\n⊢ submission = Artifact.depthSubmission\n'
                'error: build failed\nuncaught exception: Child exited with 1\n')
        self.assertTrue(case_passes(case, {'status': 'rejected'}, good))
        for bad in (good.replace('depthSubmission', 'submission'),
                    good.replace('Child exited with 1', 'Child exited with 127'),
                    'error: missing dependency\n' + good, 'PANIC unrelated\n' + good,
                    good.replace('Tactic `rfl` failed', 'Another tactic failed')):
            self.assertFalse(case_passes(case, {'status': 'rejected'}, bad))


if __name__ == '__main__':
    unittest.main()
