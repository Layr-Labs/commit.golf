"""Pre-sandbox admission reads must reject hostile file types without blocking or overreading."""
import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import check_submission as policy
import verify
from artifact_fixture import manifest

CHILD = '''import json, sys
from pathlib import Path
sys.path.insert(0, sys.argv[3])
import check_submission as policy
import verify
try:
    result = policy.check(Path(sys.argv[2])) if sys.argv[1] == 'check' else policy.claim(Path(sys.argv[2]))
except (OSError, ValueError) as exc:
    result = {'ok': False, 'error': str(exc)}
print(json.dumps(result))
'''


class PolicyReadTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.owner = Path(self.temp.name)
        self.root = self.owner / 'submission'
        self.root.mkdir()
        (self.root / 'Solution.lean').write_text('import Lean\n')
        self.raw_claim = json.dumps({'proofBytes': 1, 'commitCycles': 1, 'openingCycles': 1}).encode()
        (self.root / 'claim.json').write_bytes(self.raw_claim)
        (self.root / 'programs.json').write_text(json.dumps(manifest()))

    def tearDown(self):
        self.temp.cleanup()

    def child_rejects(self, mode, path):
        result = subprocess.run([sys.executable, '-c', CHILD, mode, str(path),
                                 str(Path(policy.__file__).resolve().parent)],
                                capture_output=True, text=True, timeout=5)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse(json.loads(result.stdout)['ok'])

    @unittest.skipUnless(hasattr(os, 'mkfifo'), 'requires owned POSIX FIFOs')
    def test_claim_fifo_and_symlink_to_fifo_reject_without_waiting(self):
        fifo = self.owner / 'owned.fifo'
        os.mkfifo(fifo)
        claim = self.root / 'claim.json'
        claim.unlink()
        claim.symlink_to(fifo)
        self.child_rejects('check', self.root)
        self.child_rejects('claim', claim)
        claim.unlink()
        os.mkfifo(claim)
        self.child_rejects('check', self.root)
        self.child_rejects('claim', claim)

    def test_claim_size_boundary_remains_512_bytes(self):
        path = self.root / 'claim.json'
        path.write_bytes(self.raw_claim + b' ' * (512 - len(self.raw_claim)))
        self.assertTrue(policy.check(self.root)['ok'])
        path.write_bytes(self.raw_claim + b' ' * (513 - len(self.raw_claim)))
        result = policy.check(self.root)
        self.assertFalse(result['ok'])
        self.assertTrue(any('512' in error for error in result['errors']))

    def assert_entry_not_opened(self, path):
        original_io, original_os = io.open, os.open
        def guard(function):
            def wrapped(file, *args, **kwargs):
                if not isinstance(file, int) and Path(file) == path:
                    raise AssertionError('an already rejected entry was opened')
                return function(file, *args, **kwargs)
            return wrapped
        with patch('io.open', side_effect=guard(original_io)), \
             patch('check_submission.os.open', side_effect=guard(original_os)):
            self.assertFalse(policy.check(self.root)['ok'])

    def test_flagged_lean_symlink_and_oversized_or_disallowed_source_are_not_read(self):
        solution = self.root / 'Solution.lean'
        external = self.owner / 'owned-source.lean'
        external.write_text('import Lean\n')
        solution.unlink()
        solution.symlink_to(external)
        self.assert_entry_not_opened(solution)
        solution.unlink()
        with solution.open('wb') as output:
            output.truncate(policy.MAX_FILE_BYTES + 1)
        self.assert_entry_not_opened(solution)
        solution.write_text('import Lean\n')
        disallowed = self.root / 'Other.lean'
        disallowed.write_text('import Lean\n')
        self.assert_entry_not_opened(disallowed)

    def test_bounded_reader_checks_regular_type_and_length_before_decoding(self):
        path = self.root / 'Solution.lean'
        path.write_bytes(b'import Lean\n' + b'--' + b' ' * (policy.MAX_FILE_BYTES - 14))
        self.assertTrue(policy.check(self.root)['ok'])
        path.write_bytes(b'\xff')
        self.assertFalse(policy.check(self.root)['ok'])
        path.write_bytes(b'123456')
        with self.assertRaisesRegex(ValueError, '5 bytes'):
            policy.regular_bytes(path, 5)

    def test_reader_requests_at_most_one_byte_past_its_limit(self):
        original = os.fdopen
        requested = []
        class GrowingRegularSource:
            def __init__(self, fd, *args): self.file = original(fd, *args)
            def __enter__(self): return self
            def __exit__(self, *args): self.file.close()
            def fileno(self): return self.file.fileno()
            def read(self, size=-1):
                requested.append(size)
                self_outer.assertGreaterEqual(size, 0)
                self_outer.assertLessEqual(size, 8)
                return b'x' * size
        self_outer = self
        with patch('check_submission.os.fdopen', side_effect=GrowingRegularSource):
            with self.assertRaises(ValueError):
                policy.regular_bytes(self.root / 'claim.json', 7)
        self.assertTrue(requested)

    def test_import_scanning_preserves_universal_newlines(self):
        source = self.root / 'Solution.lean'
        for newline in ('\n', '\r', '\r\n'):
            with self.subTest(newline=repr(newline)):
                source.write_bytes(('-- comment' + newline + 'import Lean' + newline).encode())
                self.assertTrue(policy.check(self.root)['ok'])
                source.write_bytes(('-- comment' + newline + 'import Lake' + newline).encode())
                result = policy.check(self.root)
                self.assertFalse(result['ok'])
                self.assertTrue(any('outside the allowed modules' in error for error in result['errors']))

    def test_total_size_rejection_precedes_content_reads(self):
        modules = self.root / 'CommitGolfCandidate'
        modules.mkdir()
        for path in [self.root / 'Solution.lean', *[modules / (name + '.lean') for name in 'ABC']]:
            with path.open('wb') as output:
                output.truncate(policy.MAX_FILE_BYTES)
        with patch('check_submission.regular_bytes', side_effect=AssertionError('must not read content')):
            result = policy.check(self.root)
        self.assertFalse(result['ok'])
        self.assertIn('submission exceeds 32 MiB', result['errors'])

    def test_inventory_stops_at_limit_before_reading_contents(self):
        consumed = 0
        class Entry:
            def __init__(self, path): self.path = str(path)
            def is_dir(self, *, follow_symlinks):
                self_outer.assertFalse(follow_symlinks)
                return False
        self_outer = self
        def entries():
            nonlocal consumed
            while True:
                consumed += 1
                if consumed > policy.MAX_FILES + 1:
                    raise AssertionError('inventory consumed beyond rejection boundary')
                yield Entry(self.root / ('entry' + str(consumed)))
        with patch('check_submission.os.scandir', return_value=contextlib.nullcontext(entries())), \
             patch('check_submission.regular_bytes', side_effect=AssertionError('must not read content')):
            result = policy.check(self.root)
        self.assertFalse(result['ok'])
        self.assertEqual(consumed, policy.MAX_FILES + 1)
        self.assertEqual(result['files'], policy.MAX_FILES + 1)

    def test_real_entry_count_boundary_and_directory_symlink(self):
        modules = self.root / 'CommitGolfCandidate'
        modules.mkdir()
        for i in range(policy.MAX_FILES - 4):
            (modules / f'M{i}.lean').write_text('import Lean\n')
        self.assertTrue(policy.check(self.root)['ok'])
        extra = modules / 'Extra.lean'
        extra.write_text('import Lean\n')
        self.assertFalse(policy.check(self.root)['ok'])
        extra.unlink()
        for path in modules.iterdir():
            path.unlink()
        modules.rmdir()
        outside = self.owner / 'outside'
        outside.mkdir()
        (self.root / 'linked-directory').symlink_to(outside, target_is_directory=True)
        original = os.scandir
        def guarded(path):
            self.assertNotEqual(Path(path), outside)
            self.assertNotEqual(Path(path), self.root / 'linked-directory')
            return original(path)
        with patch('check_submission.os.scandir', side_effect=guarded):
            self.assertFalse(policy.check(self.root)['ok'])


class LocalMaterializationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.owner = Path(self.temp.name)
        self.root, self.stage = self.owner / 'source', self.owner / 'stage'
        self.root.mkdir()

    def tearDown(self):
        self.temp.cleanup()

    def valid_source(self):
        (self.root / 'Solution.lean').write_bytes(b'import Lean\r\n')
        (self.root / 'claim.json').write_text('{"proofBytes":1,"commitCycles":1,"openingCycles":1}')
        (self.root / 'programs.json').write_text(json.dumps(manifest()))

    def test_regular_bytes_paths_and_executable_modes_are_preserved(self):
        self.valid_source()
        (self.root / 'Solution.lean').chmod(0o755)
        (self.root / 'README.md').write_bytes(b'\x00\xff\r\n')
        nested = self.root / 'CommitGolfCandidate'
        nested.mkdir(mode=0o750)
        (nested / 'Helper.lean').write_text('import Lean\n')
        verify.copy_local_submission(self.root, self.stage)
        self.assertTrue(policy.check(self.stage)['ok'])
        for source in self.root.rglob('*'):
            target = self.stage / source.relative_to(self.root)
            self.assertEqual(source.stat().st_mode & 0o7777, target.stat().st_mode & 0o7777)
            if source.is_file(): self.assertEqual(source.read_bytes(), target.read_bytes())

    def test_root_symlink_to_tiny_valid_source_is_rejected_before_copy(self):
        self.valid_source()
        alias = self.owner / 'alias'
        alias.symlink_to(self.root, target_is_directory=True)
        with self.assertRaises(OSError):
            verify.copy_local_submission(alias, self.stage)
        self.assertFalse(self.stage.exists())

    def test_oversized_file_is_rejected_without_copying_content(self):
        self.valid_source()
        with (self.root / 'README.md').open('wb') as file:
            file.truncate(policy.MAX_FILE_BYTES + 1)
        with patch('verify.regular_bytes', side_effect=AssertionError('must not read oversized source')):
            with self.assertRaises(ValueError):
                verify.copy_local_submission(self.root, self.stage)
        self.assertFalse(self.stage.exists())

    @unittest.skipUnless(hasattr(os, 'mkfifo'), 'requires owned POSIX FIFO')
    def test_entry_symlinks_and_fifos_are_rejected_without_reading(self):
        outside = self.owner / 'outside'
        outside.write_bytes(b'owned data')
        special = self.root / 'entry'
        special.symlink_to(outside)
        for kind in ('symlink', 'fifo'):
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                verify.copy_local_submission(self.root, self.stage)
            self.assertFalse(self.stage.exists())
            special.unlink()
            if kind == 'symlink': os.mkfifo(special)

    def test_metadata_count_and_total_caps_precede_stage_creation(self):
        for name in ('a', 'b'): (self.root / name).write_bytes(b'old')
        with patch('verify.MAX_TOTAL_BYTES', 5), \
             patch('verify.regular_bytes', side_effect=AssertionError('must not read content')):
            with self.assertRaises(ValueError):
                verify.copy_local_submission(self.root, self.stage)
        self.assertFalse(self.stage.exists())
        too_many = [self.root / 'unused'] * (policy.MAX_FILES + 1)
        with patch('verify.inventory', return_value=too_many), \
             patch('verify.regular_bytes', side_effect=AssertionError('must not read content')):
            with self.assertRaises(ValueError):
                verify.copy_local_submission(self.root, self.stage)
        self.assertFalse(self.stage.exists())

    def test_growing_file_cannot_exceed_read_quota_or_reach_stage(self):
        source = self.root / 'growing'
        source.write_bytes(b'old')
        original = verify.regular_bytes
        requested = []
        def grow(path, limit, *, dir_fd=None):
            self.assertIsNotNone(dir_fd)
            requested.append(limit)
            source.write_bytes(b'x' * 65)
            return original(path, limit, dir_fd=dir_fd)
        with patch('verify.MAX_FILE_BYTES', 64), patch('verify.regular_bytes', side_effect=grow):
            with self.assertRaises(ValueError):
                verify.copy_local_submission(self.root, self.stage)
        self.assertEqual(requested, [64])
        self.assertFalse((self.stage / 'growing').exists())

    def test_actual_bytes_not_metadata_enforce_aggregate_quota(self):
        for name in ('a', 'b'): (self.root / name).write_bytes(b'old')
        original = verify.regular_bytes
        first = None
        def grow_first(path, limit, *, dir_fd=None):
            nonlocal first
            if first is None:
                first = Path(path).name
                (self.root / path).write_bytes(b'12345678')
            return original(path, limit, dir_fd=dir_fd)
        with patch('verify.MAX_TOTAL_BYTES', 10), patch('verify.regular_bytes', side_effect=grow_first):
            with self.assertRaises(ValueError):
                verify.copy_local_submission(self.root, self.stage)
        copied = list(self.stage.iterdir())
        self.assertEqual(len(copied), 1)
        self.assertEqual(copied[0].read_bytes(), b'12345678')

    def test_actual_walk_rechecks_entry_count_after_preflight(self):
        for i in range(5): (self.root / str(i)).write_bytes(b'x')
        with patch('verify.inventory', return_value=[]), patch('verify.MAX_FILES', 3):
            with self.assertRaises(ValueError):
                verify.copy_local_submission(self.root, self.stage)
        self.assertLessEqual(len(list(self.stage.iterdir())), 3)

    def test_leaf_replacement_with_symlink_cannot_be_read(self):
        source = self.root / 'leaf'
        source.write_bytes(b'original')
        outside = self.owner / 'outside'
        outside.write_bytes(b'must not be copied')
        original = verify.regular_bytes
        def swap(path, limit, *, dir_fd=None):
            source.unlink()
            source.symlink_to(outside)
            return original(path, limit, dir_fd=dir_fd)
        with patch('verify.regular_bytes', side_effect=swap), self.assertRaises(OSError):
            verify.copy_local_submission(self.root, self.stage)
        self.assertFalse((self.stage / 'leaf').exists())

    def test_open_directory_anchor_survives_parent_path_replacement(self):
        nested = self.root / 'nested'
        nested.mkdir()
        (nested / 'payload').write_bytes(b'original')
        outside = self.owner / 'outside'
        outside.mkdir()
        (outside / 'payload').write_bytes(b'must not be copied')
        original = os.open
        swapped = False
        def open_and_swap(path, flags, *args, **kwargs):
            nonlocal swapped
            fd = original(path, flags, *args, **kwargs)
            if Path(path) == Path('nested') and kwargs.get('dir_fd') is not None and not swapped:
                swapped = True
                nested.rename(self.owner / 'moved')
                nested.symlink_to(outside, target_is_directory=True)
            return fd
        with patch('verify.os.open', side_effect=open_and_swap):
            try:
                verify.copy_local_submission(self.root, self.stage)
            except (OSError, ValueError):
                pass  # A newly observed symlink may instead cause a closed rejection.
        self.assertTrue(swapped)
        self.assertEqual((self.stage / 'nested/payload').read_bytes(), b'original')

    def test_open_descriptors_close_on_child_scan_failure(self):
        (self.root / 'nested').mkdir()
        original_open, original_scan = os.open, os.scandir
        opened = []
        def track(*args, **kwargs):
            fd = original_open(*args, **kwargs)
            opened.append(fd)
            return fd
        scans = 0
        def fail_child(path):
            nonlocal scans
            if isinstance(path, int):
                scans += 1
                if scans == 2: raise OSError('owned test scan failure')
            return original_scan(path)
        with patch('verify.os.open', side_effect=track), patch('verify.os.scandir', side_effect=fail_child):
            with self.assertRaises(OSError):
                verify.copy_local_submission(self.root, self.stage)
        self.assertGreaterEqual(len(opened), 2)
        for fd in opened:
            with self.assertRaises(OSError): os.fstat(fd)


if __name__ == '__main__':
    unittest.main()
