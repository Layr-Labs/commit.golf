"""Depth profile admission, artifact binding and full-certificate integration.

Pipeline/runner tests mock comparator execution; they do not certify the fixtures.
Supported-Linux certificate and kernel linkage tests run separately.
"""
import copy
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'verifier'))
from artifact import parse_artifact
from artifact_fixture import manifest
from check_submission import check, claim
from depth_profiles import DEPTH_PROFILES, depth_profile
from scoring import depth_objectives, MAX_SCORE, score_claim
from tracks import TRACKS
import test_artifact_pipeline as pipeline
import test_scoring as runner

DEPTH_TRACKS = {name: track for name, track in TRACKS.items() if track.depth_model is not None}


def depth_manifest(model, mode='legacy'):
    value = manifest()
    value['schemaVersion'] = 2
    value['executionModes'] = dict.fromkeys(('commit', 'opening', 'check'), mode)
    return value


def depth_claim(model):
    return dict(zip(depth_profile(model).claim_keys, (8, 7, 6, 2, 1)))


class DepthAdmissionTests(unittest.TestCase):
    def test_exact_fields_integer_types_and_aggregated_numeric_bounds(self):
        for model, profile in DEPTH_PROFILES.items():
            original = depth_claim(model)
            self.assertEqual(depth_objectives(original, model), [13, 8, 3])
            for field in profile.claim_keys:
                for bad in (-1, True, 1.0, '1', MAX_SCORE + 1, None):
                    value = {**original, field: bad}
                    with self.subTest(model=model, field=field, bad=bad):
                        with self.assertRaises(ValueError):
                            depth_objectives(value, model)
                with self.assertRaises(ValueError):
                    depth_objectives({k: v for k, v in original.items() if k != field}, model)
            for fields in (profile.work_fields, profile.depth_fields):
                value = {**original, **dict.fromkeys(fields, MAX_SCORE)}
                with self.assertRaises(ValueError):
                    depth_objectives(value, model)
            with self.assertRaises(ValueError):
                depth_objectives({**original, 'untrustedMetric': 0}, model)
            with self.assertRaises(ValueError):
                score_claim(original)

    def test_no_hidden_product_cap_for_three_independent_objectives(self):
        for model, profile in DEPTH_PROFILES.items():
            value = {**depth_claim(model), 'proofBytes': MAX_SCORE,
                     profile.work_fields[0]: MAX_SCORE - 6,
                     profile.depth_fields[0]: MAX_SCORE - 1}
            self.assertEqual(depth_objectives(value, model), [MAX_SCORE] * 3)
        # Preserve the older tracks' admission rule.
        with self.assertRaises(ValueError):
            score_claim(dict(proofBytes=MAX_SCORE, commitCycles=2, openingCycles=0))

    def test_profile_is_selected_by_trusted_track_not_candidate_text(self):
        for model in (None, '', 'other', [], {'namespace': 'Injected'}):
            with self.assertRaises(ValueError):
                depth_profile(model)
        for name, track in DEPTH_TRACKS.items():
            profile = depth_profile(track.depth_model)
            registration = next(item for item in json.loads((ROOT / 'benchmark.json').read_text())['tracks']
                                if item['name'] == name)
            self.assertEqual([o['name'] for o in registration['objectives']], list(profile.objectives))
            self.assertEqual(registration['paretoPolicies']['scoring']['version'], profile.version)

    def test_mode_and_manifest_schema_are_exactly_bound_to_generated_submission(self):
        for model, profile in DEPTH_PROFILES.items():
            legacy = parse_artifact(json.dumps(depth_manifest(model)).encode(), resource_model=model)
            parallel = parse_artifact(json.dumps(depth_manifest(model, profile.execution_modes[1])).encode(),
                                      resource_model=model)
            self.assertNotEqual(legacy.digest, parallel.digest)
            self.assertNotEqual(legacy.lean_source(), parallel.lean_source())
            self.assertIn(f'def depthSubmission : {profile.namespace}.Submission where', parallel.lean_source())
            self.assertIn('core := submission', parallel.lean_source())
            self.assertEqual(parallel.lean_source().count('=> .' + profile.execution_modes[1]), 3)
            with self.assertRaises(ValueError):
                parse_artifact(json.dumps(depth_manifest(model)).encode())
            with self.assertRaises(ValueError):
                parse_artifact(json.dumps(manifest()).encode(), resource_model=model)
            for bad in ('forkJoin' if model == 'oracle-rounds' else 'batched',
                        'legacy\naxiom injected : False', True, 0, None):
                value = depth_manifest(model)
                value['executionModes']['check'] = bad
                with self.subTest(model=model, bad=bad), self.assertRaises(ValueError):
                    parse_artifact(json.dumps(value).encode(), resource_model=model)
            for bad in ({'commit': 'legacy'}, {**legacy_modes(), 'unknown': 'legacy'}):
                value = depth_manifest(model)
                value['executionModes'] = bad
                with self.assertRaises(ValueError):
                    parse_artifact(json.dumps(value).encode(), resource_model=model)

    def test_claim_duplicates_and_nonfinite_constants_rejected(self):
        for model in DEPTH_PROFILES:
            value = depth_claim(model)
            with tempfile.TemporaryDirectory() as folder:
                path = Path(folder) / 'claim.json'
                raw = json.dumps(value)
                for bad in (raw[:-1] + ', "proofBytes": 8}', raw.replace('8', 'NaN', 1)):
                    path.write_text(bad)
                    with self.assertRaises(ValueError):
                        claim(path, resource_model=model)

    def test_old_manifest_renderer_contains_no_depth_namespace_or_modes(self):
        source = parse_artifact(json.dumps(manifest()).encode()).lean_source()
        self.assertNotIn('CommitGolfDepth', source)
        self.assertNotIn('depthSubmission', source)
        self.assertNotIn('modes', source)


def legacy_modes():
    return dict.fromkeys(('commit', 'opening', 'check'), 'legacy')


class DepthPipelineTests(unittest.TestCase):
    def fixture(self, folder, name):
        helper = pipeline.ArtifactPipelineTests()
        args, _ = helper.fixture(folder)
        track = TRACKS[name]
        args.track = name
        profile = depth_profile(track.depth_model)
        for relative in ('CommitGolfDepth.lean', 'verifier/' + profile.template):
            shutil.copy2(ROOT / relative, args.trusted / relative)
        shutil.copytree(ROOT / 'CommitGolfDepth', args.trusted / 'CommitGolfDepth')
        (args.local / 'claim.json').write_text(json.dumps(depth_claim(track.depth_model)))
        (args.local / 'programs.json').write_text(json.dumps(depth_manifest(track.depth_model)))
        return helper, args, profile

    def test_full_selected_certificate_and_modes_reach_comparator(self):
        for name, track in DEPTH_TRACKS.items():
            with self.subTest(track=name), tempfile.TemporaryDirectory() as folder:
                helper, args, profile = self.fixture(Path(folder), name)

                def inspect(command, project, env, log):
                    source = (project / 'CommitGolf/Challenge.lean').read_text()
                    self.assertIn(f'{profile.namespace}.Certificate submission', source)
                    self.assertIn(f'noncomputable def submission : {profile.namespace}.Submission', source)
                    self.assertIn('submission = CommitGolf.Artifact.depthSubmission', source)
                    self.assertNotIn('{{', source)
                    self.assertIn('8 7 6 2 1', source)
                    artifact = project / 'CommitGolf/Artifact.lean'
                    self.assertIn('modes', artifact.read_text())
                    self.assertEqual(artifact.stat().st_mode & 0o222, 0)
                    config = json.loads(Path(command[-1]).read_text())
                    self.assertIn('CommitGolf.Challenge.certificate', config['theorem_names'])
                    self.assertNotIn('CommitGolf.Artifact.depthSubmission', config['definition_names'])
                    self.assertTrue((project / 'CommitGolfDepth').is_dir())
                    self.assertFalse((project / '.lake/build/lib/lean/CommitGolf/Artifact.olean').exists())
                    log.write_text('Your solution is okay!\n')
                    return 0, False

                result, comparator = helper.execute(args, inspect)
                self.assertEqual(comparator.call_count, 1)
                self.assertEqual(result['status'], 'verified', result)
                self.assertEqual(result['scores'], [13, 8, 3])
                self.assertIsNone(result['score'])
                self.assertEqual(result['resource_model'], profile.version)
                self.assertEqual(result['objective_names'], list(profile.objectives))

    def test_wrong_or_lookalike_namespace_cannot_enter_other_track(self):
        for name, track in DEPTH_TRACKS.items():
            with tempfile.TemporaryDirectory() as folder:
                _, args, profile = self.fixture(Path(folder), name)
                for imported, admitted in [(profile.namespace, True),
                    (profile.namespace + '.Certificate', True),
                    ('CommitGolfDepth', False), (profile.namespace + 'Evil', False),
                    ('CommitGolfDepth.Span' if track.depth_model == 'oracle-rounds'
                     else 'CommitGolfDepth.Rounds', False)]:
                    (args.local / 'Solution.lean').write_text('import ' + imported + '\n')
                    result = check(args.local, resource_model=track.depth_model)
                    self.assertEqual(result['ok'], admitted, result)
                    self.assertFalse(check(args.local)['ok'])

    def test_old_three_field_certificate_claim_cannot_downgrade_depth(self):
        for name in DEPTH_TRACKS:
            with tempfile.TemporaryDirectory() as folder:
                helper, args, _ = self.fixture(Path(folder), name)
                (args.local / 'claim.json').write_text(json.dumps(
                    dict(proofBytes=8, commitCycles=7, openingCycles=6)))
                result, comparator = helper.execute(args, lambda *_: (0, False))
                self.assertEqual(result['status'], 'policy_rejected')
                self.assertEqual(comparator.call_count, 0)


class DepthRunnerTests(unittest.TestCase):
    def test_three_objective_output_and_stale_score_rejection(self):
        helper = runner.RunnerTests()
        for name, track in DEPTH_TRACKS.items():
            original = helper.report(name)
            status, exists, value = helper.run_runner(original, track=name)
            self.assertEqual(status, 0)
            self.assertTrue(exists)
            self.assertEqual(value['scores'], [13, 8, 3])
            self.assertEqual(value['metrics']['resourceModel'], depth_profile(track.depth_model).version)
            for field, bad in [('scores', [8, 13, 3]), ('scores', [13, 8]),
                               ('scores', [13.0, 8, 3]), ('scores', [True, 8, 3]),
                               ('resource_model', None), ('resource_model', 'other'),
                               ('objective_names', ['work', 'bytes', 'depth']),
                               ('objective_names', None), ('score', 104)]:
                report = copy.deepcopy(original)
                report[field] = bad
                with self.subTest(track=name, field=field, bad=bad):
                    status, exists, _ = helper.run_runner(report, track=name)
                    self.assertNotEqual(status, 0)
                    self.assertFalse(exists)


if __name__ == '__main__':
    unittest.main()
