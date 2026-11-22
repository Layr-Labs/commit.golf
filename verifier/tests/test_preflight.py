import subprocess
import sys
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from verify import VerifyError, linux_command, linux_preflight, linux_systemd_preflight, main


class SystemdPreflightTests(unittest.TestCase):
    def probe(self, output):
        with patch('verify.shutil.which', return_value='/usr/bin/systemd-run'), \
                patch('verify.subprocess.run', return_value=SimpleNamespace(stdout=output)) as run:
            linux_systemd_preflight()
        run.assert_called_once_with(['systemd-run', '--version'], check=True, text=True,
                                    capture_output=True, timeout=10)

    def test_supported_versions(self):
        for version in (257, 258, 260):
            with self.subTest(version=version):
                self.probe(f'systemd {version} ({version}.1-1ubuntu1)\n+PAM +AUDIT\n')

    def test_older_versions_fail_with_required_feature(self):
        for version in (0, 255, 256):
            with self.subTest(version=version), self.assertRaisesRegex(
                    VerifyError, rf'257 or newer is required for PrivatePIDs .*found {version}'):
                self.probe(f'systemd {version} ({version}.1)\n')

    def test_unknown_version_fails_closed(self):
        for output in ('', 'systemd unknown', 'something else 257'):
            with self.subTest(output=output), self.assertRaisesRegex(VerifyError, 'unrecognized'):
                self.probe(output)

    def test_missing_services_fail_before_version_probe(self):
        with patch('verify.shutil.which', side_effect=[None]), \
                patch('verify.subprocess.run') as run, \
                self.assertRaisesRegex(VerifyError, 'systemd user services'):
            linux_systemd_preflight()
        run.assert_not_called()

    def test_failed_version_probe_fails_closed(self):
        for error in (OSError('not executable'), subprocess.CalledProcessError(1, 'systemd-run'),
                      subprocess.TimeoutExpired('systemd-run', 10)):
            with self.subTest(error=type(error).__name__), \
                    patch('verify.shutil.which', return_value='/usr/bin/systemd-run'), \
                    patch('verify.subprocess.run', side_effect=error), \
                    self.assertRaisesRegex(VerifyError, 'could not determine systemd version'):
                linux_systemd_preflight()

    def test_linux_preflight_applies_version_guard(self):
        with patch('verify.os.geteuid', return_value=1000), \
                patch('verify.linux_systemd_preflight', side_effect=VerifyError('version guard')), \
                self.assertRaisesRegex(VerifyError, 'version guard'):
            linux_preflight({})


class SandboxUnitTests(unittest.TestCase):
    def unit(self):
        with patch('verify.os.sched_getaffinity', return_value={0, 1, 2}):
            command, _ = linux_command(['lake', 'comparator', '--config', '/trusted/comparator.json'],
                                       Path('/work/project'), {'COMPARATOR_BWRAP': '/usr/bin/bwrap'},
                                       [Path('/work/source')])
        separator = command.index('--')
        properties = [command[i + 1] for i in range(separator) if command[i] == '-p']
        return properties, command[separator + 1:]

    def test_network_is_a_private_loopback_namespace_without_unix_sockets(self):
        properties, _ = self.unit()
        self.assertIn('PrivateNetwork=yes', properties)
        self.assertIn('RestrictAddressFamilies=AF_INET AF_NETLINK', properties)
        self.assertFalse(any(prop.startswith('RestrictAddressFamilies=') and 'AF_UNIX' in prop
                             for prop in properties))
        for blocked in ('ptrace', 'kill', 'tkill', 'tgkill', 'pidfd_send_signal', 'pidfd_getfd'):
            self.assertTrue(any(prop.startswith('SystemCallFilter=~') and blocked in prop.split()
                                for prop in properties), blocked)

    def test_proc_stays_complete_for_bwrap(self):
        properties, _ = self.unit()
        self.assertIn('PrivatePIDs=yes', properties)
        self.assertFalse(any(prop.startswith('ProcSubset=') for prop in properties))

    def test_judge_runs_through_the_isolation_check_with_the_pinned_sandbox(self):
        _, command = self.unit()
        self.assertEqual(command[:2], ['/usr/bin/env', '-i'])
        self.assertIn('COMPARATOR_BWRAP=/usr/bin/bwrap', command)
        self.assertTrue(any(arg.startswith('COMMIT_VERIFIER_HOST_NETNS=') for arg in command))
        launcher = next(i for i, arg in enumerate(command) if arg.endswith('linux_exec.py'))
        self.assertEqual(command[launcher + 1:],
                         ['lake', 'comparator', '--config', '/trusted/comparator.json'])


class WorkDirectoryTests(unittest.TestCase):
    def invoke(self, extra):
        with patch('verify.Path.cwd', return_value=Path('/srv/commit-benchmark')), \
                patch.object(sys, 'argv', ['verify.py', '--local', 'submission', *extra]), \
                patch('verify.verify', return_value={'status': 'verified'}) as run, \
                patch('builtins.print'):
            self.assertEqual(main(), 0)
        return run.call_args.args[0].work

    def test_default_work_stays_under_current_checkout(self):
        work = self.invoke([])
        self.assertEqual(work.parent, Path('/srv/commit-benchmark/.work'))
        self.assertRegex(work.name, r'^[0-9a-f]{32}$')
        self.assertNotEqual(work, self.invoke([]))

    def test_explicit_work_path_is_preserved(self):
        for path in ('custom-work', '/srv/other-work'):
            with self.subTest(path=path):
                self.assertEqual(self.invoke(['--work', path]), Path(path))


if __name__ == '__main__':
    unittest.main()
