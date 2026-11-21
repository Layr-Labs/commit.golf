import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from artifact import parse_artifact
from artifact_fixture import manifest
from check_submission import check
import verify

ROOT = Path(__file__).resolve().parents[2]


class ArtifactPipelineTests(unittest.TestCase):
    def fixture(self, root):
        trusted, candidate = root / 'trusted', root / 'candidate'
        trusted.mkdir()
        candidate.mkdir()
        for name in ('lean-toolchain', 'lakefile.lean', 'lake-manifest.json', 'CommitGolf.lean'):
            shutil.copy2(ROOT / name, trusted / name)
        (trusted / 'CommitGolf').mkdir()
        (trusted / 'verifier').mkdir()
        shutil.copy2(ROOT / 'verifier/Challenge.lean.in', trusted / 'verifier/Challenge.lean.in')
        shutil.copy2(ROOT / 'verifier/comparator.json', trusted / 'verifier/comparator.json')
        (candidate / 'Solution.lean').write_text('import CommitGolf.Artifact\n')
        (candidate / 'claim.json').write_text(json.dumps(
            {'proofBytes': 8, 'commitCycles': 7, 'openingCycles': 6}))
        raw = json.dumps(manifest()).encode()
        (candidate / 'programs.json').write_bytes(raw)
        for folder in ('lib/lean', 'ir'):
            cache = trusted / '.lake/build' / folder / 'CommitGolf'
            cache.mkdir(parents=True)
            (cache / 'Artifact.olean').write_bytes(b'previous manifest')
        args = SimpleNamespace(work=root / 'work', commit=None, trusted=trusted,
                               local=candidate, hide=[])
        return args, raw

    def execute(self, args, checked, policy=check):
        tools = {'COMPARATOR_BWRAP': '/unused/bwrap'}
        with patch('verify.platform.system', return_value='Darwin'), \
             patch('verify.tools_env', return_value=tools), \
             patch('verify.subprocess.run', return_value=SimpleNamespace(stdout='a' * 40)), \
             patch('verify.clone_tree', side_effect=lambda source, target: shutil.copytree(source, target)), \
             patch('verify.check', side_effect=policy), \
             patch('verify.run_checked', side_effect=checked) as comparator:
            return verify.verify(args), comparator

    def test_frozen_manifest_module_and_digest_reach_comparator(self):
        with tempfile.TemporaryDirectory() as directory:
            args, raw = self.fixture(Path(directory))

            def inspect(command, project, env, log):
                # Outside Linux, the development mode runs the judge without its sandbox.
                self.assertEqual(command[:3], ['lake', 'comparator', '--inadvisably-no-sandbox'])
                self.assertEqual(command[-2], '--config')
                config = json.loads(Path(command[-1]).read_text())
                self.assertIn('CommitGolf.Challenge.submission_matches_artifact', config['theorem_names'])
                self.assertEqual(config['definition_names'], ['CommitGolf.Challenge.submission'])
                artifact = project / 'CommitGolf/Artifact.lean'
                self.assertEqual(artifact.read_text(), parse_artifact(raw).lean_source())
                self.assertEqual(artifact.stat().st_mode & 0o222, 0)
                for folder in ('lib/lean', 'ir'):
                    self.assertFalse((project / '.lake/build' / folder / 'CommitGolf/Artifact.olean').exists())
                self.assertIn('submission_matches_artifact',
                              (project / 'CommitGolf/Challenge.lean').read_text())
                log.write_text('Your solution is okay!\n')
                return 0, False

            result, comparator = self.execute(args, inspect)
            self.assertEqual(comparator.call_count, 1)
            self.assertEqual(result['status'], 'verified')
            self.assertEqual(result['artifact_digest'], hashlib.sha256(raw).hexdigest())

    def test_change_after_policy_validation_is_rejected_before_compilation(self):
        with tempfile.TemporaryDirectory() as directory:
            args, _ = self.fixture(Path(directory))

            def mutate_after_check(source):
                result = check(source)
                changed = manifest()
                changed['steps']['commit'] += 1
                (source / 'programs.json').write_text(json.dumps(changed))
                return result

            result, comparator = self.execute(args, lambda *args: self.fail('must not compile'),
                                              policy=mutate_after_check)
            comparator.assert_not_called()
            self.assertEqual(result['status'], 'failed')
            self.assertIn('changed after policy validation', result['reason'])

    def test_local_generated_module_is_replaced_by_the_delivered_manifest(self):
        with tempfile.TemporaryDirectory() as directory:
            args, raw = self.fixture(Path(directory))
            (args.trusted / 'scripts').mkdir()
            (args.trusted / 'submission').mkdir()
            shutil.copy2(ROOT / 'scripts/generate_artifact.py',
                         args.trusted / 'scripts/generate_artifact.py')
            shutil.copy2(ROOT / 'verifier/artifact.py', args.trusted / 'verifier/artifact.py')
            local_manifest = manifest()
            local_manifest['steps']['check'] += 1
            (args.trusted / 'submission/programs.json').write_text(json.dumps(local_manifest))
            generated = subprocess.run([sys.executable,
                                       str(args.trusted / 'scripts/generate_artifact.py')],
                                      text=True, capture_output=True, timeout=10)
            self.assertEqual(generated.returncode, 0, generated.stderr)
            local_source = args.trusted / 'CommitGolf/Artifact.lean'
            self.assertEqual(local_source.stat().st_mode & 0o777, 0o644)
            for folder in ('lib/lean', 'ir'):
                (args.trusted / '.lake/build' / folder /
                 'CommitGolf/Artifact.olean').write_bytes(b'locally compiled artifact')

            def inspect(command, project, env, log):
                source = project / 'CommitGolf/Artifact.lean'
                self.assertEqual(source.read_text(), parse_artifact(raw).lean_source())
                self.assertNotEqual(source.read_text(), local_source.read_text())
                self.assertEqual(source.stat().st_mode & 0o222, 0)
                for folder in ('lib/lean', 'ir'):
                    self.assertFalse((project / '.lake/build' / folder /
                                      'CommitGolf/Artifact.olean').exists())
                log.write_text('Your solution is okay!\n')
                return 0, False

            result, comparator = self.execute(args, inspect)
            self.assertEqual(result['status'], 'verified')
            self.assertEqual(comparator.call_count, 1)

    def test_malformed_change_after_policy_validation_returns_structured_failure(self):
        for malformed in (b'{', b'\xff', b'{"schemaVersion": 2}'):
            with self.subTest(malformed=malformed), tempfile.TemporaryDirectory() as directory:
                args, _ = self.fixture(Path(directory))

                def mutate_after_check(source):
                    result = check(source)
                    (source / 'programs.json').write_bytes(malformed)
                    return result

                result, comparator = self.execute(args, lambda *args: self.fail('must not compile'),
                                                  policy=mutate_after_check)
                comparator.assert_not_called()
                self.assertEqual(result['status'], 'failed')
                self.assertTrue(result['reason'])
                self.assertNotIn('score', result)


if __name__ == '__main__':
    unittest.main()
