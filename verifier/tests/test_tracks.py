import sys
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from tracks import (TRACKS, HIDING_TRACKS, CERTIFICATES,
                    certificate_name, submission_path, track_constructor)
from check_submission import check
from fetch import fetch_pr

ROOT = Path(__file__).resolve().parents[2]


class TrackTests(unittest.TestCase):
    def test_baseline_directories_pass_intake(self):
        for track in ("ideal-permutation", "ideal-compression"):
            with self.subTest(track=track):
                result = check(ROOT / submission_path(track))
                self.assertTrue(result["ok"], result["errors"])
                self.assertEqual(result["claim"], {"proofBytes": 76800, "checkCalls": 2400})

    def test_closed_track_mapping(self):
        self.assertEqual(track_constructor("ideal-permutation"), "idealPermutation")
        self.assertEqual(track_constructor("ideal-compression"), "idealCompression")
        self.assertEqual(track_constructor("random-oracle-fixed-output"), "randomOracleFixedOutput")
        self.assertEqual(submission_path("random-oracle-fixed-output"), "submissions/random-oracle-fixed-output")
        self.assertEqual(track_constructor("ideal-xof"), "idealXof")
        self.assertEqual(submission_path("ideal-xof"), "submissions/ideal-xof")
        for value in ("", "../ideal-permutation", "mixed", "random-oracle-fixed-output,ideal-compression", "idealCompression", "x; import Evil"):
            with self.subTest(value=value), self.assertRaises(ValueError):
                submission_path(value)

    def test_bad_track_rejected_before_fetch(self):
        with patch("fetch.bounded") as git:
            with self.assertRaises(ValueError):
                fetch_pr("Layr-Labs/commit.golf", 1, "a" * 40, Path("unused"), "../outside")
            git.assert_not_called()

    def test_template_enforces_selected_track(self):
        template = (ROOT / "verifier/Challenge.lean.in").read_text()
        for track in TRACKS:
            text = template.replace("{{certificate}}", certificate_name(track))
            self.assertIn(f"CommitGolf.{CERTIFICATES[track]} submission", text)
            self.assertNotIn("{{certificate}}", text)

    def test_hiding_tracks_have_distinct_paths_and_certificates(self):
        self.assertEqual(len(HIDING_TRACKS), 4)
        for track in HIDING_TRACKS:
            self.assertEqual(submission_path(track), f"submissions/{track}")
            self.assertTrue(CERTIFICATES[track].endswith("HidingCertificate"))
            self.assertEqual(certificate_name(track), CERTIFICATES[track])
            self.assertNotEqual(certificate_name(track), certificate_name(track.removesuffix("-hiding")))



if __name__ == "__main__":
    unittest.main()
