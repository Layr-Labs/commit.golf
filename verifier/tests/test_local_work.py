import sys
import tempfile
import unittest
from argparse import Namespace
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from verify import VerifyError, main, verify


class LocalWorkTests(unittest.TestCase):
    def check_rejected(self, source, work):
        args = Namespace(work=work, local=source, commit=None, trusted=Path('.'))
        existed = work.exists()
        with patch('verify.tools_env') as tools, patch('verify.shutil.copytree') as copy:
            report = verify(args)
        self.assertEqual(report['status'], 'failed')
        self.assertIn('outside the local submission directory', report['reason'])
        self.assertFalse(report['work_created'])
        self.assertEqual(work.exists(), existed)
        tools.assert_not_called()
        copy.assert_not_called()

    def test_work_inside_local_source_is_rejected_before_creation(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'submission'
            source.mkdir()
            self.check_rejected(source, source / '.work' / 'attempt')

    def test_work_equal_to_local_source_is_a_structured_rejection(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'submission'
            source.mkdir()
            self.check_rejected(source, source)

    def test_resolved_source_symlink_cannot_hide_containment(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / 'submission'
            source.mkdir()
            alias = root / 'alias'
            alias.symlink_to(source, target_is_directory=True)
            self.check_rejected(alias, source / '.work' / 'attempt')

    def test_resolved_work_parent_symlink_cannot_hide_containment(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / 'submission'
            source.mkdir()
            alias = root / 'alias'
            alias.symlink_to(source, target_is_directory=True)
            self.check_rejected(source, alias / 'attempt')

    def test_sibling_work_directory_reaches_normal_setup(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source, work = root / 'submission', root / '.work' / 'attempt'
            source.mkdir()
            args = Namespace(work=work, local=source, commit=None, trusted=Path('.'))
            with patch('verify.tools_env', side_effect=VerifyError('normal setup')) as tools:
                report = verify(args)
            self.assertEqual(report['reason'], 'normal setup')
            self.assertTrue(report['work_created'])
            self.assertTrue(work.is_dir())
            tools.assert_called_once_with(Path('.'))


class CleanupOwnershipTests(unittest.TestCase):
    def run_main(self, source, work, setup):
        with patch.object(sys, 'argv', ['verify.py', '--local', str(source),
                                       '--work', str(work), '--cleanup']), \
                patch('verify.tools_env', side_effect=setup) as tools, \
                patch('builtins.print'):
            self.assertEqual(main(), 1)
        return tools

    def test_cleanup_keeps_preexisting_work(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source, work = root / 'submission', root / 'existing-work'
            source.mkdir()
            work.mkdir()
            sentinel = work / 'keep'
            sentinel.write_text('preexisting')
            tools = self.run_main(source, work, VerifyError('unexpected setup'))
            tools.assert_not_called()
            self.assertEqual(sentinel.read_text(), 'preexisting')

    def test_cleanup_keeps_local_submission_when_work_equals_source(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'submission'
            source.mkdir()
            sentinel = source / 'keep'
            sentinel.write_text('submission')
            tools = self.run_main(source, source, VerifyError('unexpected setup'))
            tools.assert_not_called()
            self.assertEqual(sentinel.read_text(), 'submission')

    def test_cleanup_removes_work_created_by_this_invocation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source, work = root / 'submission', root / '.work' / 'new'
            source.mkdir()

            def setup(_):
                (work / 'owned').write_text('created by verifier')
                raise VerifyError('normal setup')

            tools = self.run_main(source, work, setup)
            tools.assert_called_once()
            self.assertFalse(work.exists())
            self.assertTrue(source.is_dir())


if __name__ == '__main__':
    unittest.main()
