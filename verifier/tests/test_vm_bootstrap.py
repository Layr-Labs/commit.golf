"""Offline failure-path checks: tiny pinned fixtures, real SHA-256, no VM/network."""
import base64
import hashlib
import shlex
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
PIN = '4908fb59ccd4e87ae4e8e973b7ef56f535448eacb24a87fd787270c0048987bc'
PAYLOAD = b'tiny offline image fixture\x00\xff\n'

CURL = r'''
curl() {
  printf 'download\n' >> "$BOOT_TEST_LOG"
  local destination=''
  while (($#)); do
    if [[ "$1" == -o ]]; then destination="$2"; break; fi
    shift
  done
  case "$BOOT_TEST_MODE" in
    valid) cp "$BOOT_TEST_IMAGE" "$destination" ;;
    partial) printf partial > "$destination"; return 18 ;;
    wrong_hash) printf untrusted > "$destination" ;;
    *) return 92 ;;
  esac
}
export -f curl
exec bash scripts/blacksmith.sh prepare-image
'''


class ImageBootstrapTests(unittest.TestCase):
    def setUp(self):
        self.folder = tempfile.TemporaryDirectory()
        self.addCleanup(self.folder.cleanup)
        self.project = Path(self.folder.name)
        (self.project / 'scripts').mkdir()
        # Only the copied fixture uses a tiny public test pin. Production keeps its
        # reviewed Ubuntu pin; the real sha256sum checks all fixture bytes.
        source = (ROOT / 'scripts/blacksmith.sh').read_text()
        self.assertEqual(source.count(PIN), 1)
        self.digest = hashlib.sha256(PAYLOAD).hexdigest()
        (self.project / 'scripts/blacksmith.sh').write_text(source.replace(PIN, self.digest))
        self.payload = self.project / 'fixture.img'
        self.payload.write_bytes(PAYLOAD)
        self.image = self.project / '.cache/vm-image' / f'{self.digest}.img'
        self.log = self.project / 'calls'

    def prepare(self, mode='valid'):
        result = subprocess.run(['bash', '-c', CURL], cwd=self.project,
            env={**os.environ, 'RUNNER_TEMP': str(self.project / 'runner'),
                 'BOOT_TEST_IMAGE': str(self.payload), 'BOOT_TEST_LOG': str(self.log),
                 'BOOT_TEST_MODE': mode}, capture_output=True, text=True, timeout=10)
        calls = self.log.read_text().splitlines() if self.log.exists() else []
        return result, calls

    def seed(self, value):
        self.image.parent.mkdir(parents=True)
        self.image.write_bytes(value)

    def test_cold_download_is_checked_and_published_atomically(self):
        result, calls = self.prepare()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(calls, ['download'])
        self.assertEqual(self.image.read_bytes(), PAYLOAD)
        self.assertFalse(self.image.with_suffix('.img.part').exists())

    def test_verified_cache_hit_needs_no_download(self):
        self.seed(PAYLOAD)
        result, calls = self.prepare('partial')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(calls, [])
        self.assertEqual(self.image.read_bytes(), PAYLOAD)

    def test_corrupt_cache_is_replaced_by_verified_download(self):
        self.seed(b'corrupt cached data')
        result, calls = self.prepare()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(calls, ['download'])
        self.assertEqual(self.image.read_bytes(), PAYLOAD)

    def test_partial_download_fails_without_final_image_then_recovers(self):
        self.seed(b'corrupt cached data')
        result, _ = self.prepare('partial')
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(self.image.exists())
        self.assertEqual(self.image.with_suffix('.img.part').read_bytes(), b'partial')
        result, calls = self.prepare()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(calls, ['download', 'download'])
        self.assertEqual(self.image.read_bytes(), PAYLOAD)

    def test_successful_transfer_with_wrong_hash_cannot_publish_then_recovers(self):
        result, _ = self.prepare('wrong_hash')
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(self.image.exists())
        result, _ = self.prepare()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.image.read_bytes(), PAYLOAD)

    def test_abandoned_partial_is_never_used_as_cache(self):
        self.image.parent.mkdir(parents=True)
        self.image.with_suffix('.img.part').write_bytes(PAYLOAD)
        result, calls = self.prepare()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(calls, ['download'])
        self.assertEqual(self.image.read_bytes(), PAYLOAD)


    def test_cloud_init_failure_stops_before_candidate_copy(self):
        self.seed(PAYLOAD)
        shutil.copy2(ROOT / 'scripts/vm-packages.sh', self.project / 'scripts/vm-packages.sh')
        harness = r"""
test() { if [[ "$*" == '-c /dev/kvm' ]]; then return 0; fi; builtin test "$@"; }
sudo() { return 0; }
qemu-img() { return 0; }
cloud-localds() { return 0; }
ssh-keygen() { mkdir -p "$RUNNER_TEMP/commit-verifier-vm"; echo fixture > "$RUNNER_TEMP/commit-verifier-vm/key.pub"; }
ssh() {
  printf '%s\n' "${*: -1}" >> "$BOOT_TEST_LOG"
  if [[ "${*: -1}" == 'sudo cloud-init status --wait' ]]; then return 2; fi
  return 0
}
export -f test sudo qemu-img cloud-localds ssh-keygen ssh
mkdir -p "$RUNNER_TEMP"
exec bash scripts/blacksmith.sh start
"""
        result = subprocess.run(['bash', '-c', harness], cwd=self.project,
            env={**os.environ, 'RUNNER_TEMP': str(self.project / 'runner'),
                 'BOOT_TEST_LOG': str(self.log)}, capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertEqual(self.log.read_text().splitlines(), ['true', 'sudo cloud-init status --wait'])


APT = r"""#!/usr/bin/env bash
set -eu
printf '%s\n' "$*" >> "$BOOT_TEST_LOG"
count=0
if [[ -f "$BOOT_TEST_COUNT" ]]; then read -r count < "$BOOT_TEST_COUNT"; fi
count=$((count+1)); echo "$count" > "$BOOT_TEST_COUNT"
if [[ "$BOOT_TEST_MODE" == hung_update ||
      ( "$BOOT_TEST_MODE" == hung_install && " $* " == *' install '* ) ]]; then exec /bin/sleep 5; fi
if [[ "$BOOT_TEST_MODE" == failed_update ||
      ( "$BOOT_TEST_MODE" == recovered_update && "$count" == 1 ) ]]; then
  echo 'File has unexpected size / Hash Sum mismatch' >&2; exit 100
fi
if [[ "$BOOT_TEST_MODE" == failed_install && " $* " == *' install '* ]]; then exit 100; fi
exit 0
"""


class PackageBootstrapTests(unittest.TestCase):
    def run_packages(self, mode):
        with tempfile.TemporaryDirectory() as folder:
            project = Path(folder)
            binaries = project / 'bin'
            binaries.mkdir()
            for name, source in [('apt-get', APT), ('sleep', '#!/bin/sh\nexit 0\n')]:
                command = binaries / name
                command.write_text(source)
                command.chmod(0o755)
            script = (ROOT / 'scripts/vm-packages.sh').read_text()
            if mode in ('hung_update', 'hung_install'):
                # Exercise the actual timeout/exit path without waiting the production 300s.
                self.assertIn('timeout --kill-after=10s 300s apt-get', script)
                duration = '300s' if mode == 'hung_update' else '480s'
                script = script.replace(duration + ' apt-get', '0.05s apt-get')
            helper = project / 'packages.sh'
            helper.write_text(script)
            log = project / 'calls'
            result = subprocess.run(['bash', str(helper)], env={**os.environ,
                'PATH': str(binaries) + os.pathsep + os.environ['PATH'],
                'BOOT_TEST_LOG': str(log), 'BOOT_TEST_COUNT': str(project / 'count'),
                'BOOT_TEST_MODE': mode}, capture_output=True, text=True, timeout=10)
            return result, [shlex.split(line) for line in log.read_text().splitlines()]

    def assert_verified_update(self, call):
        self.assertEqual(call[-2:], ['--error-on=any', 'update'])
        self.assertEqual(call[:-2], ['-o', 'Acquire::Retries=0', '-o',
            'Acquire::http::Timeout=30', '-o', 'Acquire::https::Timeout=30'])

    def assert_same_packages(self, call):
        self.assertEqual(call[6:], ['-y', 'install', 'git', 'curl', 'build-essential',
            'python3', 'golang-go', 'dbus-user-session', 'apparmor', 'zstd'])
        self.assertEqual(call[:6], ['-o', 'Acquire::Retries=0', '-o',
            'Acquire::http::Timeout=30', '-o', 'Acquire::https::Timeout=30'])

    def test_first_pass_requires_verified_update_then_same_package_list(self):
        result, calls = self.run_packages('valid')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(calls), 2)
        self.assert_verified_update(calls[0])
        self.assert_same_packages(calls[1])

    def test_index_mismatch_retries_update_before_install(self):
        result, calls = self.run_packages('recovered_update')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(calls), 3)
        for call in calls[:2]: self.assert_verified_update(call)
        self.assert_same_packages(calls[2])

    def test_persistent_index_failure_never_installs_and_fails_closed(self):
        result, calls = self.run_packages('failed_update')
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(len(calls), 3)
        for call in calls: self.assert_verified_update(call)

    def test_install_failure_requires_fresh_update_each_retry_and_fails_closed(self):
        result, calls = self.run_packages('failed_install')
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(len(calls), 6)
        for call in calls[::2]: self.assert_verified_update(call)
        for call in calls[1::2]: self.assert_same_packages(call)

    def test_hung_update_times_out_and_never_installs(self):
        result, calls = self.run_packages('hung_update')
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(len(calls), 3)
        for call in calls: self.assert_verified_update(call)

    def test_hung_install_times_out_and_rechecks_indexes_before_retry(self):
        result, calls = self.run_packages('hung_install')
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(len(calls), 6)
        for call in calls[::2]: self.assert_verified_update(call)
        for call in calls[1::2]: self.assert_same_packages(call)

    def test_cloud_init_embeds_exact_helper_and_waits_before_copy(self):
        source = (ROOT / 'scripts/blacksmith.sh').read_text()
        # Expand the real heredoc only, without running VM setup. YAML literal
        # checks ensure one final-stage helper and no duplicate package module.
        content = source.split('<<CLOUD\n', 1)[1].split('\nCLOUD', 1)[0]
        with tempfile.TemporaryDirectory() as folder:
            vm = Path(folder)
            (vm / 'key.pub').write_text('ssh-ed25519 fixture')
            result = subprocess.run(['bash', '-c', 'vm="$1"; cat <<CLOUD\n' + content + '\nCLOUD',
                'cloud-fixture', str(vm)], cwd=ROOT, capture_output=True, text=True, check=True)
        config = result.stdout
        encoded = config.split('    content: ', 1)[1].splitlines()[0]
        self.assertEqual(base64.b64decode(encoded), (ROOT / 'scripts/vm-packages.sh').read_bytes())
        self.assertIn("permissions: '0700'", config)
        self.assertIn('owner: root:root', config)
        self.assertIn('runcmd:\n  - [/bin/bash, /usr/local/sbin/commit-verifier-packages]', config)
        self.assertNotIn('package_update:', config)
        self.assertNotIn('\npackages:', config)
        self.assertLess(source.index("guest 'sudo cloud-init status --wait'"),
                        source.index("tar --exclude='./.work'"))


if __name__ == '__main__':
    unittest.main()
