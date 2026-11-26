import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]

# Exported functions take precedence over setup.sh's PATH prefix, without changing HOME or
# touching the real toolchain. The fake installer matches elan 4.1.2: installing an existing
# toolchain returns an error, even when its compiler works.
HARNESS = r'''
elan() {
  printf 'elan %s\n' "$*" >> "$SETUP_TEST_LOG"
  if [[ "$1" == run ]]; then
    [[ -f "$SETUP_TEST_READY" ]]
  elif [[ "$1 $2" == 'toolchain install' ]]; then
    if [[ -f "$SETUP_TEST_INSTALLED" ]]; then return 1; fi
    if [[ "$SETUP_TEST_MODE" == install_failure ]]; then return 17; fi
    touch "$SETUP_TEST_INSTALLED"
    if [[ "$SETUP_TEST_MODE" != broken_install ]]; then touch "$SETUP_TEST_READY"; fi
  else
    return 90
  fi
}
lake() {
  printf 'lake %s\n' "$*" >> "$SETUP_TEST_LOG"
  if [[ "$SETUP_TEST_MODE" == cache_failure && "$*" == 'exe cache get' ]]; then return 19; fi
  if [[ "$SETUP_TEST_MODE" == build_failure && "$1" == build ]]; then return 23; fi
  return 0
}
python3() { printf 'preflight\n' >> "$SETUP_TEST_LOG"; }
export -f elan lake python3
exec bash scripts/setup.sh
'''


class SetupTests(unittest.TestCase):
    def run_setup(self, mode):
        with tempfile.TemporaryDirectory() as folder:
            project = Path(folder)
            (project / 'scripts').mkdir()
            (project / 'verifier').mkdir()
            shutil.copy2(ROOT / 'scripts/setup.sh', project / 'scripts/setup.sh')
            (project / 'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
            (project / 'verifier/setup_tools.sh').write_text(
                'printf "tools\\n" >> "$SETUP_TEST_LOG"\n')
            log, installed, ready = (project / name for name in ('calls', 'installed', 'ready'))
            if mode in ('existing', 'broken_existing'):
                installed.touch()
            if mode == 'existing':
                ready.touch()
            env = {**os.environ, 'SETUP_TEST_LOG': str(log),
                   'SETUP_TEST_INSTALLED': str(installed), 'SETUP_TEST_READY': str(ready),
                   'SETUP_TEST_MODE': mode}
            result = subprocess.run(['bash', '-c', HARNESS], cwd=project, env=env,
                                    text=True, capture_output=True)
            return result.returncode, log.read_text().splitlines()

    def assert_build_finished(self, calls):
        self.assertEqual(calls[-4:], ['tools', 'lake exe cache get',
                                     'lake build CommitGolf CommitGolfTests CommitGolfDepth.Rounds.Tests CommitGolfDepth.Span.Tests', 'preflight'])

    def assert_build_not_started(self, calls):
        self.assertFalse(any(call == 'tools' or call.startswith('lake ') or
                             call == 'preflight' for call in calls))

    def test_existing_working_toolchain_skips_install(self):
        status, calls = self.run_setup('existing')
        self.assertEqual(status, 0)
        self.assertFalse(any(call.startswith('elan toolchain install ') for call in calls))
        self.assert_build_finished(calls)

    def test_missing_toolchain_installs_and_checks_compiler(self):
        status, calls = self.run_setup('missing')
        self.assertEqual(status, 0)
        self.assertEqual(calls[:3], [
            'elan run leanprover/lean4:v4.35.0 lean --version',
            'elan toolchain install leanprover/lean4:v4.35.0',
            'elan run leanprover/lean4:v4.35.0 lean --version'])
        self.assert_build_finished(calls)

    def test_install_failure_stops_setup(self):
        status, calls = self.run_setup('install_failure')
        self.assertEqual(status, 17)
        self.assert_build_not_started(calls)

    def test_successful_install_with_broken_compiler_stops_setup(self):
        status, calls = self.run_setup('broken_install')
        self.assertNotEqual(status, 0)
        self.assert_build_not_started(calls)

    def test_existing_broken_toolchain_is_not_ignored(self):
        status, calls = self.run_setup('broken_existing')
        self.assertNotEqual(status, 0)
        self.assert_build_not_started(calls)

    def test_cache_failure_stops_before_build_and_preflight(self):
        status, calls = self.run_setup('cache_failure')
        self.assertEqual(status, 19)
        self.assertEqual(calls[-2:], ['tools', 'lake exe cache get'])
        self.assertFalse(any(call.startswith('lake build ') or call == 'preflight' for call in calls))

    def test_build_failure_stops_before_preflight(self):
        status, calls = self.run_setup('build_failure')
        self.assertEqual(status, 23)
        self.assertEqual(calls[-3:], ['tools', 'lake exe cache get',
                                     'lake build CommitGolf CommitGolfTests CommitGolfDepth.Rounds.Tests CommitGolfDepth.Span.Tests'])
        self.assertNotIn('preflight', calls)


if __name__ == '__main__':
    unittest.main()
