import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from artifact import parse_artifact
from artifact_fixture import manifest

ROOT = Path(__file__).resolve().parents[2]


class GenerateArtifactTests(unittest.TestCase):
    def fixture(self, root):
        for folder in ('scripts', 'verifier', 'submission', 'CommitGolf'):
            (root / folder).mkdir()
        shutil.copy2(ROOT / 'scripts/generate_artifact.py', root / 'scripts/generate_artifact.py')
        shutil.copy2(ROOT / 'verifier/artifact.py', root / 'verifier/artifact.py')
        raw = json.dumps(manifest()).encode()
        (root / 'submission/programs.json').write_bytes(raw)
        return raw

    def cli(self, root, *args):
        return subprocess.run([sys.executable, str(root / 'scripts/generate_artifact.py'), *args],
                              cwd=root.parent, text=True, capture_output=True, timeout=10)

    def caches(self, root):
        paths = []
        for folder in ('lib/lean', 'ir'):
            cache = root / '.lake/build' / folder / 'CommitGolf'
            cache.mkdir(parents=True, exist_ok=True)
            for suffix in ('olean', 'olean.private', 'olean.server', 'ilean', 'trace', 'c', 'o'):
                path = cache / ('Artifact.' + suffix)
                path.write_bytes(b'stale')
                paths.append(path)
            (cache / 'ArtifactEncoding.olean').write_bytes(b'preserve')
        return paths

    def test_defaults_work_outside_repository_and_use_exact_verifier_renderer(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            raw = self.fixture(root)
            result = self.cli(root)
            self.assertEqual(result.returncode, 0, result.stderr)
            destination = root / 'CommitGolf/Artifact.lean'
            self.assertTrue(destination.read_text().endswith(parse_artifact(raw).lean_source()))
            self.assertIn(hashlib.sha256(raw).hexdigest(), result.stdout)
            self.assertEqual(destination.stat().st_mode & 0o777, 0o644)
            before = destination.stat().st_mtime_ns
            caches = self.caches(root)
            again = self.cli(root)
            self.assertEqual(again.returncode, 0, again.stderr)
            self.assertIn('Already current', again.stdout)
            self.assertEqual(destination.stat().st_mtime_ns, before)
            self.assertTrue(all(path.exists() for path in caches))

    def test_changed_manifest_requires_refresh_and_purges_every_artifact_cache(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root)
            self.assertEqual(self.cli(root).returncode, 0)
            destination = root / 'CommitGolf/Artifact.lean'
            old = destination.read_bytes()
            inode = destination.stat().st_ino
            destination.chmod(0o444)
            caches = self.caches(root)
            changed = manifest()
            changed['images']['opening'] = {'code': '78563412', 'data': '00ff00'}
            raw = json.dumps(changed).encode()
            (root / 'submission/programs.json').write_bytes(raw)
            rejected = self.cli(root)
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('--refresh', rejected.stderr)
            self.assertEqual(destination.read_bytes(), old)
            self.assertTrue(all(path.exists() for path in caches))
            refreshed = self.cli(root, '--refresh')
            self.assertEqual(refreshed.returncode, 0, refreshed.stderr)
            self.assertNotEqual(destination.stat().st_ino, inode)
            self.assertEqual(destination.stat().st_mode & 0o777, 0o644)
            self.assertTrue(destination.read_text().endswith(parse_artifact(raw).lean_source()))
            self.assertTrue(all(not path.exists() for path in caches))
            for folder in ('lib/lean', 'ir'):
                self.assertEqual((root / '.lake/build' / folder /
                                  'CommitGolf/ArtifactEncoding.olean').read_bytes(), b'preserve')

    def test_current_readonly_module_is_atomically_repaired_without_chmodding_hardlinks(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root)
            self.assertEqual(self.cli(root).returncode, 0)
            destination = root / 'CommitGolf/Artifact.lean'
            old = destination.read_bytes()
            destination.chmod(0o444)
            outside = root / 'other-hardlink'
            os.link(destination, outside)
            caches = self.caches(root)
            result = self.cli(root)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn('Refreshed', result.stdout)
            self.assertEqual(destination.read_bytes(), old)
            self.assertEqual(destination.stat().st_mode & 0o777, 0o644)
            self.assertEqual(outside.stat().st_mode & 0o777, 0o444)
            self.assertNotEqual(destination.stat().st_ino, outside.stat().st_ino)
            self.assertTrue(all(not path.exists() for path in caches))

    def test_explicit_input_and_formatting_only_change_refresh_the_manifest_digest(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root)
            alternate = root / 'other.json'
            raw = json.dumps(manifest(), indent=2).encode()
            alternate.write_bytes(raw)
            result = self.cli(root, str(alternate))
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn(hashlib.sha256(raw).hexdigest(), result.stdout)
            self.assertNotEqual(self.cli(root).returncode, 0)
            self.assertEqual(self.cli(root, '--refresh').returncode, 0)

    def test_invalid_manifest_preserves_source_and_caches(self):
        for invalid in (b'{', b'\xff', b'{"schemaVersion":1,"schemaVersion":1}'):
            with self.subTest(raw=invalid), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                self.fixture(root)
                self.assertEqual(self.cli(root).returncode, 0)
                destination = root / 'CommitGolf/Artifact.lean'
                old = destination.read_bytes()
                caches = self.caches(root)
                (root / 'submission/programs.json').write_bytes(invalid)
                result = self.cli(root, '--refresh')
                self.assertNotEqual(result.returncode, 0)
                self.assertNotIn('Traceback', result.stderr)
                self.assertEqual(destination.read_bytes(), old)
                self.assertTrue(all(path.exists() for path in caches))

    def test_unmanaged_or_edited_output_is_never_overwritten_even_with_refresh(self):
        for edited in (False, True):
            with self.subTest(edited=edited), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                self.fixture(root)
                destination = root / 'CommitGolf/Artifact.lean'
                if edited:
                    self.assertEqual(self.cli(root).returncode, 0)
                    destination.write_text(destination.read_text() + '\naxiom changed : False\n')
                else:
                    destination.write_text('import CommitGolf.Programs\n')
                old = destination.read_bytes()
                caches = self.caches(root)
                result = self.cli(root, '--refresh')
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('move it aside', result.stderr)
                self.assertEqual(destination.read_bytes(), old)
                self.assertTrue(all(path.exists() for path in caches))

    def test_linked_destination_and_contract_directory_do_not_touch_external_files(self):
        for linked_directory in (False, True):
            with self.subTest(directory=linked_directory), tempfile.TemporaryDirectory() as directory:
                root = Path(directory) / 'project'
                root.mkdir()
                self.fixture(root)
                outside = Path(directory) / 'outside'
                outside.mkdir()
                sentinel = outside / 'Artifact.lean'
                sentinel.write_bytes(b'external source')
                if linked_directory:
                    (root / 'CommitGolf').rmdir()
                    (root / 'CommitGolf').symlink_to(outside, target_is_directory=True)
                else:
                    (root / 'CommitGolf/Artifact.lean').symlink_to(sentinel)
                self.assertNotEqual(self.cli(root, '--refresh').returncode, 0)
                self.assertEqual(sentinel.read_bytes(), b'external source')

    def test_every_cache_parent_symlink_is_rejected_before_creating_output(self):
        for relative in ('.lake', '.lake/build', '.lake/build/lib', '.lake/build/lib/lean',
                         '.lake/build/lib/lean/CommitGolf', '.lake/build/ir',
                         '.lake/build/ir/CommitGolf'):
            with self.subTest(parent=relative), tempfile.TemporaryDirectory() as directory:
                root = Path(directory) / 'project'
                root.mkdir()
                self.fixture(root)
                outside = Path(directory) / 'outside'
                outside.mkdir()
                sentinel = outside / 'Artifact.olean'
                sentinel.write_bytes(b'external cache')
                link = root / relative
                link.parent.mkdir(parents=True, exist_ok=True)
                link.symlink_to(outside, target_is_directory=True)
                result = self.cli(root)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(sentinel.read_bytes(), b'external cache')
                self.assertFalse((root / 'CommitGolf/Artifact.lean').exists())

    def test_cache_leaf_symlink_is_unlinked_without_following_it(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root)
            outside = root / 'outside'
            outside.write_bytes(b'external')
            cache = root / '.lake/build/lib/lean/CommitGolf'
            cache.mkdir(parents=True)
            leaf = cache / 'Artifact.olean'
            leaf.symlink_to(outside)
            result = self.cli(root)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertFalse(leaf.is_symlink())
            self.assertEqual(outside.read_bytes(), b'external')

    def test_non_file_cache_entry_blocks_generation_without_deleting_other_cache(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root)
            caches = self.caches(root)
            (root / '.lake/build/ir/CommitGolf/Artifact.unexpected').mkdir()
            self.assertNotEqual(self.cli(root).returncode, 0)
            self.assertFalse((root / 'CommitGolf/Artifact.lean').exists())
            self.assertTrue(all(path.exists() for path in caches))

    @unittest.skipUnless(hasattr(os, 'mkfifo'), 'requires FIFOs')
    def test_fifo_destination_is_rejected_without_blocking(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root)
            os.mkfifo(root / 'CommitGolf/Artifact.lean')
            self.assertNotEqual(self.cli(root, '--refresh').returncode, 0)

    def test_ignore_rule_covers_only_the_generated_root_module(self):
        paths = 'CommitGolf/Artifact.lean\nCommitGolf/ArtifactEncoding.lean\n' \
                'submission/CommitGolfCandidate/Artifact.lean\n'
        result = subprocess.run(['git', '-C', str(ROOT), 'check-ignore', '--no-index', '--stdin'],
                                input=paths, text=True, capture_output=True, check=True)
        self.assertEqual(result.stdout, 'CommitGolf/Artifact.lean\n')


if __name__ == '__main__':
    unittest.main()
