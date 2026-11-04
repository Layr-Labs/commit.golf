import subprocess
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_submission import check
from fetch import FetchError, fetch_pr

ROOT = Path(__file__).resolve().parents[2]


class ChallengeTests(unittest.TestCase):
    def test_fixed_certificate(self):
        template = (ROOT / "verifier/Challenge.lean.in").read_text()
        self.assertIn("submission : CommitGolf.Submission", template)
        self.assertIn("CommitGolf.Certificate submission {{proofBytes}} {{commitCycles}} {{openingCycles}}", template)
        self.assertNotIn("{{certificate}}", template)
        self.assertIn('import CommitGolf.Artifact', template)
        self.assertIn('submission_matches_artifact : submission = CommitGolf.Artifact.submission', template)
        config = json.loads((ROOT / 'verifier/comparator.json').read_text())
        self.assertIn('CommitGolf.Challenge.submission_matches_artifact', config['theorem_names'])
        self.assertEqual(config['definition_names'], ['CommitGolf.Challenge.submission'])

    def test_runner_has_no_oracle_selector(self):
        result = subprocess.run([sys.executable, str(ROOT / "scripts/run.py"),
                                 "--track", "ideal-xof"], capture_output=True, text=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn("unrecognized arguments", result.stderr)

    def test_fetch_only_uses_submission_directory(self):
        commit = "a" * 40
        # Empty git tree ends the fetch before any files are written.
        with patch("fetch.bounded", side_effect=[b"", b"", b"", commit.encode(), b""]) as git:
            with self.assertRaisesRegex(FetchError, "submission directory is empty"):
                fetch_pr("Layr-Labs/commit.golf", 1, commit, ROOT / "unused-fetch-destination")
            self.assertEqual(git.call_args_list[-1].args[0][-1], commit + ":submission")

    def test_fetch_preserves_delivered_manifest_bytes(self):
        commit, blob = 'a' * 40, 'b' * 40
        raw = b'{"delivered": "bytes"}\n'
        entry = f'100644 blob {blob}\tprograms.json\0'.encode()
        replies = [b'', b'', b'', commit.encode(), entry, b'', str(len(raw)).encode(), raw]
        with tempfile.TemporaryDirectory() as directory:
            destination = Path(directory) / 'submission'
            with patch('fetch.bounded', side_effect=replies):
                fetch_pr('Layr-Labs/commit.golf', 1, commit, destination)
            self.assertEqual((destination / 'programs.json').read_bytes(), raw)

    def test_missing_starter_is_not_accepted(self):
        with tempfile.TemporaryDirectory() as directory:
            self.assertFalse(check(Path(directory))["ok"])


if __name__ == "__main__":
    unittest.main()
