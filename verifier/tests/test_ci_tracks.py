"""Exercise the workflow's detector on real Git diffs, then its required-check gate."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

import test_ci_gate as ci_gate


DIRECTORIES = {
    suffix: 'submission-commit-golf-' + suffix.lower().replace('_', '-')
    for suffix in ci_gate.TRACKS
}


class TrackDetectionTests(unittest.TestCase):
    def detect(self, before, after, *, branch='feature/candidate', head_repo='101',
               base_repo='101'):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            repo = root / 'repo'
            repo.mkdir()

            def git(*args):
                return subprocess.check_output([
                    'git', '-c', 'user.name=CI Regression', '-c',
                    'user.email=ci-regression@example.invalid', '-c',
                    'commit.gpgsign=false', *args], cwd=repo, stderr=subprocess.PIPE,
                    text=True).strip()

            def write(files):
                for name, value in files.items():
                    path = repo / name
                    path.parent.mkdir(parents=True, exist_ok=True)
                    if isinstance(value, tuple):
                        path.symlink_to(value[0])
                    else:
                        path.write_text(value)

            git('init', '--quiet')
            write(before)
            git('add', '--all')
            git('commit', '--quiet', '--allow-empty', '-m', 'base')
            base = git('rev-parse', 'HEAD')
            for name in before:
                (repo / name).unlink()
            write(after)
            git('add', '--all')
            git('commit', '--quiet', '--allow-empty', '-m', 'candidate')
            head = git('rev-parse', 'HEAD')
            output = root / 'output'
            result = subprocess.run([
                'bash', '-euo', 'pipefail', '-c', ci_gate.workflow_shell('changes')],
                cwd=repo, env={**os.environ, 'BASE_SHA': base, 'HEAD_SHA': head,
                    'HEAD_REF': branch, 'HEAD_REPO_ID': head_repo,
                    'BASE_REPO_ID': base_repo, 'GITHUB_OUTPUT': str(output)},
                text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            return dict(line.split('=', 1) for line in output.read_text().splitlines())

    def assert_selection(self, detected, selected, *, contract='false', managed='false'):
        self.assertEqual(detected['contract'], contract)
        self.assertEqual(detected['solver_branch'], managed)
        for track in DIRECTORIES:
            self.assertEqual(detected['changed_' + track.lower()],
                             str(track in selected).lower(), track)

    def gate_inputs(self, detected):
        return {'CONTRACT_CHANGED': detected['contract'],
                'SOLVER_BRANCH': detected['solver_branch'],
                **{f'CHANGED_{track}': detected['changed_' + track.lower()]
                   for track in DIRECTORIES}}

    def test_each_new_track_addition_is_selected(self):
        for track, directory in DIRECTORIES.items():
            with self.subTest(track=track):
                detected = self.detect({}, {directory + '/Solution.lean': 'invalid candidate'})
                self.assert_selection(detected, {track})

    def test_missing_exports_cannot_pass_on_original_baseline_results(self):
        track = '96_32_PRODUCT'
        source = 'namespace CommitGolf.Challenge\ndef unrelated : Nat := 0\nend CommitGolf.Challenge\n'
        detected = self.detect({}, {DIRECTORIES[track] + '/Solution.lean': source})
        self.assert_selection(detected, {track})
        env = {**self.gate_inputs(detected), 'LINKAGE_RESULT': 'skipped',
               'SCALE_RESULT': 'skipped'}
        for status in ('skipped', 'failure', 'cancelled', ''):
            with self.subTest(status=status):
                result = ci_gate.run_gate(**{**env, f'TRACK_{track}_RESULT': status})
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        # The gate requires this track's full benchmark to report success, independently
        # of the two original baselines. This supplies a job outcome, not a proof result.
        result = ci_gate.run_gate(**{**env, f'TRACK_{track}_RESULT': 'success'})
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_deleted_track_still_requires_verification(self):
        track = '64_32_PARETO'
        before = {DIRECTORIES[track] + '/Solution.lean': 'certificate',
                  DIRECTORIES[track] + '/programs.json': '{}'}
        self.assert_selection(self.detect(before, {}), {track})

    def test_track_to_track_move_selects_both_sides(self):
        old, new = '64_32_PRODUCT', '96_32_PRODUCT'
        detected = self.detect({DIRECTORIES[old] + '/Solution.lean': 'same content'},
                               {DIRECTORIES[new] + '/Solution.lean': 'same content'})
        self.assert_selection(detected, {old, new})

    def test_contract_to_track_move_remains_a_contract_change(self):
        track = '96_32_PARETO'
        detected = self.detect({'CommitGolf/Example.lean': 'same content'},
                               {DIRECTORIES[track] + '/Example.lean': 'same content'})
        self.assert_selection(detected, {track}, contract='true')

    def test_root_file_and_symlink_are_selected(self):
        for value in ('invalid root file', ('elsewhere',)):
            with self.subTest(value=value):
                track = '64_32_PRODUCT'
                detected = self.detect({}, {DIRECTORIES[track]: value})
                self.assert_selection(detected, {track}, contract='true')

    def test_near_prefix_and_original_tracks_do_not_select_new_tracks(self):
        detected = self.detect({}, {'submission/Solution.lean': 'original',
            'submission-pareto/Solution.lean': 'original',
            DIRECTORIES['64_32_PRODUCT'] + '-lookalike/Solution.lean': 'unrelated'})
        self.assert_selection(detected, set(), contract='true')

    def test_large_diff_and_newline_path_select_every_changed_track(self):
        after = {'submission/' + f'proof_{index}.lean': 'proof' for index in range(350)}
        after.update({directory + '/line\nbreak.lean': 'candidate'
                      for directory in DIRECTORIES.values()})
        self.assert_selection(self.detect({}, after), set(DIRECTORIES))

    def test_fork_cannot_impersonate_a_managed_submission_branch(self):
        track = '64_32_PRODUCT'
        files = {DIRECTORIES[track] + '/Solution.lean': 'candidate'}
        managed = self.detect({}, files, branch='submissions/candidate')
        self.assert_selection(managed, {track}, managed='true')
        env = {**self.gate_inputs(managed), **dict.fromkeys(ci_gate.RESULTS, 'skipped')}
        self.assertEqual(ci_gate.run_gate(**env).returncode, 0)
        fork = self.detect({}, files, branch='submissions/candidate', head_repo='202')
        self.assert_selection(fork, {track})
        env = {**self.gate_inputs(fork), 'LINKAGE_RESULT': 'skipped', 'SCALE_RESULT': 'skipped'}
        self.assertNotEqual(ci_gate.run_gate(**env).returncode, 0)
        self.assertEqual(ci_gate.run_gate(
            **{**env, f'TRACK_{track}_RESULT': 'success'}).returncode, 0)

    def test_mixed_contract_and_candidate_change_overrides_yukon_delegation(self):
        track = '96_32_PARETO'
        detected = self.detect({}, {DIRECTORIES[track] + '/Solution.lean': 'candidate',
                                   'CommitGolf/Example.lean': 'contract'},
                               branch='submissions/candidate')
        self.assert_selection(detected, {track}, contract='true', managed='true')
        env = self.gate_inputs(detected)
        self.assertNotEqual(ci_gate.run_gate(**env).returncode, 0)
        self.assertEqual(ci_gate.run_gate(
            **{**env, f'TRACK_{track}_RESULT': 'success'}).returncode, 0)

    def test_configuration_only_rollout_selects_no_missing_candidates(self):
        self.assert_selection(self.detect({}, {'verifier/tracks.py': 'new configuration'}),
                              set(), contract='true')

    def test_contract_only_change_requires_every_existing_track(self):
        baselines = {directory + '/Solution.lean': 'unchanged certificate'
                     for directory in DIRECTORIES.values()}
        for branch in ('feature/contract', 'submissions/candidate'):
            detected = self.detect(
                {**baselines, 'verifier/tracks.py': 'before'},
                {**baselines, 'verifier/tracks.py': 'after'}, branch=branch)
            self.assert_selection(detected, set(DIRECTORIES), contract='true',
                                  managed=str(branch.startswith('submissions/')).lower())
            env = {**self.gate_inputs(detected),
                   **{f'TRACK_{track}_RESULT': 'success' for track in DIRECTORIES}}
            self.assertEqual(ci_gate.run_gate(**env).returncode, 0)
            for track in DIRECTORIES:
                for status in ('skipped', 'failure', 'cancelled', ''):
                    with self.subTest(branch=branch, track=track, status=status):
                        self.assertNotEqual(ci_gate.run_gate(
                            **{**env, f'TRACK_{track}_RESULT': status}).returncode, 0)

    def test_contract_change_requires_only_existing_or_changed_tracks(self):
        existing, removed = '64_32_PRODUCT', '96_32_PARETO'
        baseline = {DIRECTORIES[existing] + '/Solution.lean': 'unchanged certificate'}
        detected = self.detect(
            {**baseline, DIRECTORIES[removed] + '/Solution.lean': 'deleted certificate',
             'CommitGolf/Example.lean': 'before'},
            {**baseline, 'CommitGolf/Example.lean': 'after'})
        self.assert_selection(detected, {existing, removed}, contract='true')

    def test_submission_only_change_does_not_select_unchanged_tracks(self):
        baselines = {directory + '/Solution.lean': 'certificate'
                     for directory in DIRECTORIES.values()}
        selected = '64_32_PARETO'
        self.assert_selection(self.detect(baselines, {
            **baselines, DIRECTORIES[selected] + '/Solution.lean': 'updated certificate'}),
            {selected})

    def test_contract_change_does_not_silently_skip_invalid_existing_roots(self):
        selected = '96_32_PRODUCT'
        for value in ('invalid root file', ('missing-target',)):
            with self.subTest(value=value):
                baseline = {DIRECTORIES[selected]: value}
                detected = self.detect(
                    {**baseline, 'verifier/tracks.py': 'before'},
                    {**baseline, 'verifier/tracks.py': 'after'})
                self.assert_selection(detected, {selected}, contract='true')


if __name__ == '__main__':
    unittest.main()
