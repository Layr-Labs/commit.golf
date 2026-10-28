import subprocess
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

    def test_missing_starter_is_not_accepted(self):
        with tempfile.TemporaryDirectory() as directory:
            self.assertFalse(check(Path(directory))["ok"])


if __name__ == "__main__":
    unittest.main()
