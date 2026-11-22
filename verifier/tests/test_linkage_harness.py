import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_submission import check
from artifact_fixture import manifest
from check_artifact_linkage import case_passes, linkage_config, make_cases, remove_owned

ROOT = Path(__file__).resolve().parents[2]

# The diagnostic bodies come from Lean v4.36.0 `lake comparator` runs of these fixtures, with
# build paths and the backtrace elided. Coordinates follow the fixed generated fixture as its
# trusted representation evolves. The judge's buffered progress line can follow its exit report.
_direct_source = make_cases(json.dumps(manifest()).encode())[0].source.splitlines()
_proof_line = next(i for i, line in enumerate(_direct_source, 1)
                   if line.startswith('theorem submission_matches_artifact '))
_proof_column = _direct_source[_proof_line - 1].index('rfl')
RFL_FAILURE = f'''Building Solution
✖ [6520/6522] Building Solution (6.4s)
trace: .> LEAN_PATH=build-paths-placeholder
error: Solution.lean:{_proof_line}:{_proof_column}: Tactic `rfl` failed: The left-hand side
  submission
is not definitionally equal to the right-hand side
  Artifact.submission

⊢ submission = Artifact.submission
Some required targets logged failures:
- Solution
error: build failed
error: Child exited with 1
'''
MISSING_TARGET = '''Building Solution
Build completed successfully (6522 jobs).
PANIC at LeanExport.dumpConstant LeanExport.Basic:254:48: Constant CommitGolf.Challenge.submission_matches_artifact not found in environment.
backtrace:
exporter-backtrace-placeholder
error: Child exited with 139
Exporting #[CommitGolf.Challenge.submission_matches_artifact] from Solution
'''


class LinkageHarnessTests(unittest.TestCase):
    def test_test_only_config_preserves_production_config_and_definition_holes(self):
        path = ROOT / 'verifier/comparator.json'
        raw = path.read_bytes()
        production = json.loads(raw)
        original = copy.deepcopy(production)
        isolated = linkage_config(production)
        self.assertEqual(isolated['theorem_names'], ['CommitGolf.Challenge.submission_matches_artifact'])
        self.assertEqual(isolated['definition_names'], ['CommitGolf.Challenge.submission'])
        self.assertEqual(isolated['permitted_axioms'], production['permitted_axioms'])
        self.assertEqual(production, original)
        self.assertEqual(path.read_bytes(), raw)

    def test_all_linkage_cases_reach_proof_checking_with_small_fixed_sources(self):
        cases = make_cases(json.dumps(manifest()).encode())
        self.assertEqual(len(cases), 8)
        self.assertEqual(sum(case.expected == 'verified' for case in cases), 2)
        for case in cases:
            with self.subTest(case=case.name), tempfile.TemporaryDirectory() as directory:
                candidate = Path(directory)
                (candidate / 'programs.json').write_bytes(case.manifest)
                (candidate / 'Solution.lean').write_text(case.source)
                (candidate / 'claim.json').write_text(
                    '{"proofBytes":1,"commitCycles":1,"openingCycles":1}\n')
                result = check(candidate)
                self.assertTrue(result['ok'], result['errors'])
                self.assertNotIn('CommitGolfCandidate.', case.source)
                self.assertNotIn('theorem certificate', case.source)

    def test_infrastructure_failure_never_counts_as_successful_negative(self):
        cases = make_cases(json.dumps(manifest()).encode())
        positive, negative = cases[0], cases[2]
        self.assertTrue(case_passes(positive, {'status': 'verified'}, ''))
        self.assertTrue(case_passes(negative, {'status': 'rejected'}, RFL_FAILURE))
        for status in ('failed', 'policy_rejected', 'timeout', 'verified', None):
            self.assertFalse(case_passes(negative, {'status': status}, RFL_FAILURE))
        self.assertFalse(case_passes(positive, {'status': 'rejected'}, RFL_FAILURE))
        for diagnostic in ('OOM killed compiler', "error: object file 'Dependency.olean' does not exist",
                           'error: Child exited with 127',
                           'error: Solution.lean:1:0: unknown identifier unrelated', ''):
            self.assertFalse(case_passes(negative, {'status': 'rejected', 'reason': diagnostic}, diagnostic))

    def test_rfl_rejection_must_be_the_required_equality_without_other_failures(self):
        negative = make_cases(json.dumps(manifest()).encode())[2]
        for diagnostic in (RFL_FAILURE.replace(f'{_proof_line}:{_proof_column}',
                                               f'{_proof_line + 1}:{_proof_column}'),
                           RFL_FAILURE.replace('⊢ submission = Artifact.submission', '⊢ True'),
                           'error: Dependency.lean:1:0: missing declaration\n' + RFL_FAILURE,
                           'OOM killed unrelated job\n' + RFL_FAILURE,
                           RFL_FAILURE.replace('Child exited with 1', 'Child exited with 127'),
                           RFL_FAILURE.replace('Child exited with 1', 'Child exited with 2'),
                           RFL_FAILURE + 'Your solution is okay!\n',
                           'PANIC at unrelated location\n' + RFL_FAILURE):
            self.assertFalse(case_passes(negative, {'status': 'rejected'}, diagnostic))

    def test_missing_equality_requires_the_exact_missing_export_target(self):
        missing = make_cases(json.dumps(manifest()).encode())[-1]
        self.assertTrue(case_passes(missing, {'status': 'rejected'}, MISSING_TARGET))
        for diagnostic in ('PANIC at unrelated location\nerror: Child exited with 139\n',
                           MISSING_TARGET.replace('submission_matches_artifact', 'unrelated_target'),
                           MISSING_TARGET.replace('Child exited with 139', 'Child exited with 127'),
                           'error: Dependency.lean:1:0: failed to load dependency\n' + MISSING_TARGET,
                           MISSING_TARGET.replace('Build completed successfully (6522 jobs).\n', ''),
                           MISSING_TARGET + 'PANIC at unrelated location\n',
                           MISSING_TARGET + 'Your solution is okay!\n'):
            self.assertFalse(case_passes(missing, {'status': 'rejected'}, diagnostic))

    def test_missing_target_accepts_only_the_exporter_abort_codes(self):
        missing = make_cases(json.dumps(manifest()).encode())[-1]
        for code in ('134', '139'):
            with self.subTest(code=code):
                self.assertTrue(case_passes(missing, {'status': 'rejected'},
                                            MISSING_TARGET.replace('139', code)))
        for diagnostic in ('error: Child exited with 139\n',
                           MISSING_TARGET.replace('Child exited with 139', 'Child exited with 140'),
                           MISSING_TARGET.replace('error: Child exited with 139\n', ''),
                           MISSING_TARGET.replace('PANIC at LeanExport.dumpConstant LeanExport.Basic:254:48: '
                                                  'Constant CommitGolf.Challenge.submission_matches_artifact '
                                                  'not found in environment.\n', ''),
                           MISSING_TARGET + 'error: Child exited with 134\n',
                           'PANIC at unrelated location\n' + MISSING_TARGET):
            self.assertFalse(case_passes(missing, {'status': 'rejected'}, diagnostic))

    def test_cleanup_is_limited_to_owned_direct_children(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            owner, outside = root / 'owned', root / 'outside'
            owner.mkdir()
            outside.mkdir()
            child = owner / 'run'
            child.mkdir()
            (child / 'result').write_text('temporary')
            remove_owned(child, owner)
            self.assertFalse(child.exists())
            with self.assertRaises(ValueError):
                remove_owned(outside, owner)
            (owner / 'alias').symlink_to(outside, target_is_directory=True)
            with self.assertRaises(ValueError):
                remove_owned(owner / 'alias', owner)
            self.assertTrue(outside.is_dir())


if __name__ == '__main__':
    unittest.main()
