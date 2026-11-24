"""Exercise the actual required-check shell with GitHub job outcomes."""
import os
from pathlib import Path
import re
import subprocess
import textwrap
import unittest


WORKFLOW = Path(__file__).resolve().parents[2] / '.github/workflows/test-pr.yml'
RESULTS = ('BENCHMARK_RESULT', 'PARETO_RESULT', 'LINKAGE_RESULT', 'SCALE_RESULT')
TRACKS = ('64_32_PRODUCT', '64_32_PARETO', '96_32_PRODUCT', '96_32_PARETO')


def workflow_shell(job_name):
    # Read the literal shell block so tests cannot drift from the deployed workflow.
    # Workflow schema/expression validation remains actionlint's responsibility.
    job = WORKFLOW.read_text().split(f'  {job_name}:\n', 1)[1]
    job = re.split(r'(?m)^  [a-z][a-z0-9-]*:\n', job, maxsplit=1)[0]
    block = re.search(r'(?m)^        run: \|\n((?:          .*\n|\n)+)', job)
    if block is None:
        raise AssertionError(f'{job_name} shell block not found')
    return textwrap.dedent(block.group(1))


def run_gate(**overrides):
    env = {**os.environ, 'CHANGES_RESULT': 'success', 'CONTRACT_CHANGED': 'true',
           'SOLVER_BRANCH': 'false', **dict.fromkeys(RESULTS, 'success'),
           **{f'CHANGED_{track}': 'false' for track in TRACKS},
           **{f'TRACK_{track}_RESULT': 'skipped' for track in TRACKS}, **overrides}
    return subprocess.run(['bash', '-euo', 'pipefail', '-c',
                           workflow_shell('contract-regressions')],
                          env=env, text=True, capture_output=True)


class ContractGateTests(unittest.TestCase):
    gate = staticmethod(run_gate)

    def assert_gate(self, expected, **overrides):
        result = self.gate(**overrides)
        self.assertEqual(result.returncode == 0, expected, result.stdout + result.stderr)

    def test_contract_changes_require_all_four_successes(self):
        for managed in ('true', 'false'):
            self.assert_gate(True, SOLVER_BRANCH=managed)
            for worker in RESULTS:
                for status in ('failure', 'cancelled', 'skipped', ''):
                    with self.subTest(managed=managed, worker=worker, status=status):
                        self.assert_gate(False, SOLVER_BRANCH=managed, **{worker: status})

    def test_submission_only_prs_require_both_baselines(self):
        baseline_only = {'CONTRACT_CHANGED': 'false', 'LINKAGE_RESULT': 'skipped',
                         'SCALE_RESULT': 'skipped'}
        self.assert_gate(True, **baseline_only)
        for worker in ('BENCHMARK_RESULT', 'PARETO_RESULT'):
            for status in ('failure', 'cancelled', 'skipped', ''):
                with self.subTest(worker=worker, status=status):
                    self.assert_gate(False, **{**baseline_only, worker: status})

    def test_only_managed_submission_branches_may_skip_all_workloads(self):
        skipped = {'CONTRACT_CHANGED': 'false', **dict.fromkeys(RESULTS, 'skipped')}
        self.assert_gate(True, SOLVER_BRANCH='true', **skipped)
        self.assert_gate(False, SOLVER_BRANCH='false', **skipped)
        self.assert_gate(False, SOLVER_BRANCH='true',
                         **{**skipped, 'CONTRACT_CHANGED': 'true'})
        for worker in RESULTS:
            with self.subTest(worker=worker):
                self.assert_gate(False, SOLVER_BRANCH='true',
                                 **{**skipped, worker: 'success'})

    def test_change_detection_failure_and_unknown_outputs_fail_closed(self):
        for status in ('failure', 'cancelled', 'skipped', ''):
            self.assert_gate(False, CHANGES_RESULT=status)
        for value in ('', 'TRUE', 'unknown'):
            self.assert_gate(False, CONTRACT_CHANGED=value)
            self.assert_gate(False, SOLVER_BRANCH=value)

    def test_regression_failures_cannot_pass_as_a_submission_only_skip(self):
        for managed in ('true', 'false'):
            for worker in ('LINKAGE_RESULT', 'SCALE_RESULT'):
                for status in ('failure', 'cancelled', ''):
                    with self.subTest(managed=managed, worker=worker, status=status):
                        self.assert_gate(False, SOLVER_BRANCH=managed,
                            **{'CONTRACT_CHANGED': 'false', 'LINKAGE_RESULT': 'skipped',
                               'SCALE_RESULT': 'skipped', worker: status})

    def test_every_changed_track_subset_requires_its_selected_jobs(self):
        for mask in range(16):
            for contract in ('true', 'false'):
                for managed in ('true', 'false'):
                    env = {'CONTRACT_CHANGED': contract, 'SOLVER_BRANCH': managed}
                    if contract == 'false':
                        env.update(LINKAGE_RESULT='skipped', SCALE_RESULT='skipped')
                        if managed == 'true':
                            env.update(BENCHMARK_RESULT='skipped', PARETO_RESULT='skipped')
                    for index, track in enumerate(TRACKS):
                        changed = bool(mask & (1 << index))
                        env[f'CHANGED_{track}'] = str(changed).lower()
                        env[f'TRACK_{track}_RESULT'] = (
                            'success' if changed and (contract == 'true' or managed == 'false')
                            else 'skipped')
                    with self.subTest(mask=mask, contract=contract, managed=managed):
                        self.assert_gate(True, **env)

    def test_selected_new_track_failure_cancel_or_skip_fails_the_gate(self):
        for track in TRACKS:
            for managed in ('true', 'false'):
                for status in ('failure', 'cancelled', 'skipped', ''):
                    with self.subTest(track=track, managed=managed, status=status):
                        self.assert_gate(False, SOLVER_BRANCH=managed,
                            **{f'CHANGED_{track}': 'true', f'TRACK_{track}_RESULT': status})

    def test_new_track_flags_and_unexpected_job_results_fail_closed(self):
        for track in TRACKS:
            for value in ('', 'TRUE', 'unknown'):
                with self.subTest(track=track, value=value):
                    self.assert_gate(False, **{f'CHANGED_{track}': value})
            for status in ('success', 'failure', 'cancelled', ''):
                with self.subTest(track=track, status=status):
                    self.assert_gate(False, **{f'TRACK_{track}_RESULT': status})


if __name__ == '__main__':
    unittest.main()
