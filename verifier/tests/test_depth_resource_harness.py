"""Guard the resource-only clients' isolation and precise negative diagnostics."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import shutil
from unittest.mock import patch
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from artifact import parse_artifact
from check_submission import check
from depth_profiles import depth_profile
from check_depth_resources import (RESOURCE_TARGET, EQUALITY_TARGET, ADMISSION_TARGET,
                                  make_cases, resource_config, expected_template, case_passes,
                                  protected_snapshot)
from depth_resource_fixture import FIXTURES, RESOURCE_FIXTURES
import check_depth_resources as harness

ROOT = Path(__file__).resolve().parents[2]


class ResourceHarnessTests(unittest.TestCase):
    def test_actual_mode_images_and_precise_understatements_are_fixed(self):
        cases = make_cases()
        self.assertEqual(len(cases), 12)
        for fixture in RESOURCE_FIXTURES:
            selected = [c for c in cases if c.fixture == fixture]
            positive, work, depth, mode, image, security = selected
            value = json.loads(positive.manifest)
            self.assertEqual(value['executionModes']['commit'],
                             'batched' if fixture.model == 'oracle-rounds' else 'forkJoin')
            self.assertEqual(work.manifest, positive.manifest)
            self.assertEqual(depth.manifest, positive.manifest)
            self.assertEqual((work.work, work.depth), (fixture.work - 1, fixture.depth))
            self.assertEqual((depth.work, depth.depth), (fixture.work, fixture.depth - 1))
            changed = json.loads(mode.manifest)
            self.assertEqual(changed['executionModes'].pop('commit'), 'legacy')
            self.assertEqual(changed, {**value, 'executionModes': {
                k: v for k, v in value['executionModes'].items() if k != 'commit'}})
            changed = json.loads(image.manifest)
            old = bytes.fromhex(value['images']['commit']['code'])
            new = bytes.fromhex(changed['images']['commit']['code'])
            self.assertEqual(sum(a != b for a, b in zip(old, new)), 1)
            self.assertEqual(new[1:], old[1:])
            self.assertTrue(security.production_scope)
            self.assertEqual(security.manifest, positive.manifest)
            for case in selected:
                parse_artifact(case.manifest, resource_model=fixture.model)

    def test_rounds_alias_is_prestate_input_not_fresh_reply(self):
        fixture = RESOURCE_FIXTURES[0]
        self.assertEqual(fixture.data[3], 512)
        self.assertEqual(fixture.data[5], 512)
        self.assertEqual(fixture.data[7], 544)
        self.assertEqual((fixture.work, fixture.depth), (33, 1))

    def test_config_is_owned_resource_contract_and_preserves_axiom_policy(self):
        production = json.loads((ROOT / 'verifier/comparator.json').read_text())
        before = copy.deepcopy(production)
        resource = resource_config(production)
        self.assertEqual(production, before)
        self.assertEqual(resource['theorem_names'], [EQUALITY_TARGET, ADMISSION_TARGET, RESOURCE_TARGET])
        self.assertNotIn('CommitGolf.Challenge.certificate', resource['theorem_names'])
        for key in ('definition_names', 'permitted_axioms', 'enable_nanoda'):
            self.assertEqual(resource[key], production[key])
        with self.assertRaises(ValueError):
            resource_config(resource)

    def test_templates_name_universal_actual_runs_and_do_not_claim_security(self):
        for fixture in RESOURCE_FIXTURES:
            case = next(c for c in make_cases() if c.fixture == fixture)
            template = expected_template(case)
            self.assertNotIn('{{', template)
            self.assertIn('(oracle : Oracle)', template)
            self.assertNotIn('(message : Message)', template)
            self.assertIn('oracle.run (submission.run .commit (fun _ => 0))', template)
            self.assertIn('submission = Artifact.depthSubmission', template)
            self.assertIn('theorem admission : submission.core.Admission', template)
            self.assertIn(f'≤ {fixture.work}', template)
            self.assertIn(f'≤ {fixture.depth}', template)
            self.assertNotIn('theorem certificate', template)
            self.assertNotIn('Legacy', template)
            self.assertNotIn('observer', template)

    def test_under_bound_requires_specific_completed_comparator_failure(self):
        for case in make_cases():
            if not case.name.endswith(('_under_work', '_under_depth')):
                continue
            good = ('Build completed successfully (123 jobs).\nuncaught exception: '
                    "Challenge and solution theorem statement do not match: '" + RESOURCE_TARGET + "'\n")
            self.assertTrue(case_passes(case, {'status': 'rejected'}, good, ''))
            for bad in ('', good.replace(RESOURCE_TARGET, EQUALITY_TARGET),
                        'OOM killed compiler\n' + good, 'error: another failure\n' + good,
                        good.replace('Build completed successfully (123 jobs).', '')):
                self.assertFalse(case_passes(case, {'status': 'rejected'}, bad, ''))
            self.assertFalse(case_passes(case, {'status': 'timeout'}, good, ''))

    def test_missing_security_certificate_requires_exact_export_boundary(self):
        for case in make_cases():
            if not case.production_scope:
                continue
            good = ('Build completed successfully (123 jobs).\n'
                    'PANIC at dumpConstant Export:12:8: Constant CommitGolf.Challenge.certificate not found in environment.\n'
                    'uncaught exception: Child exited with 134\n')
            self.assertTrue(case_passes(case, {'status': 'rejected'}, good, ''))
            for bad in ('', good.replace('certificate', 'unrelated'),
                        good.replace('Child exited with 134', 'Child exited with 127'),
                        'error: unrelated\n' + good, 'OOM killed\n' + good,
                        good.replace('Build completed successfully (123 jobs).\n', '')):
                self.assertFalse(case_passes(case, {'status': 'rejected'}, bad, ''))

    def test_wrong_mode_image_require_the_artifact_equality_not_incidental_error(self):
        source = 'theorem submission_matches_artifact : submission = Artifact.depthSubmission := by rfl\n'
        header = f'error: Solution.lean:1:{source.index("rfl")}: Tactic `rfl` failed: The left-hand side'
        good = (header + '\n  submission\nis not definitionally equal to the right-hand side\n'
                '  Artifact.depthSubmission\n\n⊢ submission = Artifact.depthSubmission\n'
                'error: build failed\nuncaught exception: Child exited with 1\n')
        for case in make_cases():
            if not case.name.endswith(('_wrong_mode', '_wrong_image')):
                continue
            self.assertTrue(case_passes(case, {'status': 'rejected'}, good, source))
            for bad in ('', good.replace('depthSubmission', 'other'),
                        good.replace('Child exited with 1', 'Child exited with 127'),
                        'error: unrelated\n' + good, 'PANIC unrelated\n' + good):
                self.assertFalse(case_passes(case, {'status': 'rejected'}, bad, source))

    def test_snapshot_includes_all_production_templates_and_track_scores(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            (root / 'verifier').mkdir()
            for name in ('comparator.json', 'Challenge.lean.in', 'RoundsChallenge.lean.in', 'SpanChallenge.lean.in'):
                (root / 'verifier' / name).write_text(name)
            before = protected_snapshot(root)
            self.assertEqual(len(before), 12)
            (root / 'verifier/SpanChallenge.lean.in').write_text('changed')
            self.assertNotEqual(before, protected_snapshot(root))

    def test_owned_runner_restores_full_production_scope_for_security_negatives(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            (root / 'verifier').mkdir()
            for name in ('comparator.json', 'Challenge.lean.in', 'RoundsChallenge.lean.in', 'SpanChallenge.lean.in'):
                shutil.copy2(ROOT / 'verifier' / name, root / 'verifier' / name)
            shutil.copy2(ROOT / 'CommitGolfDepth.lean', root / 'CommitGolfDepth.lean')
            shutil.copytree(ROOT / 'CommitGolfDepth', root / 'CommitGolfDepth')
            production = json.loads((root / 'verifier/comparator.json').read_text())
            cases = {case.name: case for case in make_cases()}
            observed = []

            def prepare(_root, owner):
                trusted = owner / 'trusted'
                shutil.copytree(root / 'verifier', trusted / 'verifier')
                return trusted

            def verify_case(args):
                name = args.work.name.removeprefix('run-')
                case = cases[name]
                config = json.loads((args.trusted / 'verifier/comparator.json').read_text())
                profile = depth_profile(case.fixture.model)
                template = (args.trusted / 'verifier' / profile.template).read_text()
                self.assertEqual(config, production if case.production_scope else resource_config(production))
                self.assertEqual(template, (root / 'verifier' / profile.template).read_text()
                                 if case.production_scope else expected_template(case))
                claim = json.loads((args.local / 'claim.json').read_text())
                self.assertEqual(claim[profile.work_fields[0]], case.work)
                self.assertEqual(claim[profile.depth_fields[0]], case.depth)
                observed.append(name)
                args.work.mkdir()
                (args.work / 'verify.log').write_text('mocked comparator; no proof acceptance implied')
                return {'status': case.expected}

            with patch.object(harness.verify, 'tools_env', return_value={}), \
                 patch.object(harness.verify, 'linux_preflight'), \
                 patch.object(harness, 'prepare_trusted', side_effect=prepare), \
                 patch.object(harness.verify, 'verify', side_effect=verify_case), \
                 patch.object(harness, 'case_passes', return_value=True), patch('builtins.print'):
                self.assertEqual(harness.run(root), 0)
            self.assertEqual(set(observed), set(cases))
            self.assertEqual(len(observed), 12)

    def test_fixed_clients_pass_static_admission_but_export_no_full_certificate(self):
        # This is static policy validation; actual comparator proof checking is separate.
        for fixture in RESOURCE_FIXTURES:
            with tempfile.TemporaryDirectory() as folder:
                root = Path(folder)
                source = (FIXTURES / fixture.source).read_text()
                (root / 'Solution.lean').write_text(source)
                (root / 'programs.json').write_text(json.dumps(fixture.manifest()))
                profile = depth_profile(fixture.model)
                (root / 'claim.json').write_text(json.dumps(dict.fromkeys(profile.claim_keys, 1)))
                self.assertTrue(check(root, resource_model=fixture.model)['ok'])
                self.assertNotIn('theorem certificate', source)


if __name__ == '__main__':
    unittest.main()
