"""Exercise the real score wrapper with a mocked verifier; these are not verifier runs."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "verifier"))
from tracks import TRACKS


class YukonTests(unittest.TestCase):
    def test_manifest_routing(self):
        manifest = json.loads((ROOT / "benchmark.json").read_text())
        self.assertEqual(manifest["schemaVersion"], 2)
        self.assertEqual({t["name"] for t in manifest["tracks"]}, set(TRACKS))
        for track in manifest["tracks"]:
            name = track["name"]
            self.assertEqual(track["editablePaths"], [f"submissions/{name}"])
            self.assertEqual(track["benchmarkCommand"], ["bash", "scripts/benchmark.sh", "--track", name])
            self.assertEqual(track["scorePath"], f"scripts/scores/{name}/score.json")
            self.assertEqual(track["direction"], "-")
            workflow = ROOT / ".github/workflows" / track["runner"]["workflow"]
            self.assertIn(f"track: {name}\n", workflow.read_text())
            self.assertIn("workflow_dispatch:", workflow.read_text())

    def invoke(self, track, *, status="verified", reported_track=None, commit="abc", size=76800,
               calls=2400, returncode=0, expect_failure=False, platform="linux"):
        report = {"status": status, "track": reported_track or track, "contract_commit": commit,
                  "claim": {"proofBytes": size, "checkCalls": calls}}
        with tempfile.TemporaryDirectory() as tmp:
            score = Path(tmp) / "scripts/scores" / track / "score.json"
            score.parent.mkdir(parents=True)
            score.write_text('{"score": 1}')  # A rejected run must remove stale results.
            root = Path(tmp)
            (root / "verifier").mkdir()
            (root / "verifier/verify.py").write_text(
                "import json, sys\nfrom pathlib import Path\n"
                "Path('arguments.json').write_text(json.dumps(sys.argv[1:]))\n"
                "work = Path(sys.argv[sys.argv.index('--work') + 1])\n"
                "assert not work.exists()\nwork.mkdir()\n"
                + f"print({json.dumps(report)!r})\nsys.exit({returncode})\n")
            bin_dir = root / "bin"
            bin_dir.mkdir()
            for name, output in [("uname", "Linux" if platform == "linux" else "Darwin"),
                                 ("git", "abc")]:
                stub = bin_dir / name
                stub.write_text(f"#!/bin/sh\necho {output}\n")
                stub.chmod(0o755)
            env = dict(os.environ, PATH=f"{bin_dir}:{os.environ['PATH']}")
            result = subprocess.run(
                ["bash", str(ROOT / "scripts/benchmark.sh"), "--track", track],
                cwd=root, env=env, capture_output=True, text=True)
            if expect_failure:
                self.assertNotEqual(result.returncode, 0)
                self.assertFalse(score.exists())
            else:
                self.assertEqual(result.returncode, 0, result.stderr)
                scored = json.loads(score.read_text())
                self.assertEqual(scored["score"], size * calls)
                self.assertEqual(scored["metrics"]["track"], track)
                self.assertEqual(scored["metrics"]["proofBytes"], size)
                self.assertEqual(scored["metrics"]["checkCalls"], calls)
                command = json.loads((root / "arguments.json").read_text())
                self.assertEqual(command[command.index("--local") + 1], f"submissions/{track}")
                self.assertEqual(command[command.index("--track") + 1], track)

    def test_all_track_scores(self):
        for track in TRACKS:
            with self.subTest(track=track):
                self.invoke(track)

    def test_rejected_runs_leave_no_score(self):
        cases = [dict(returncode=1), dict(status="rejected"), dict(commit="wrong"),
                 dict(reported_track="ideal-xof"), dict(size=True), dict(calls=-1),
                 dict(size=2**53), dict(size=2**40, calls=2**20), dict(platform="darwin")]
        for case in cases:
            with self.subTest(case=case):
                self.invoke("ideal-permutation", expect_failure=True, **case)


if __name__ == "__main__":
    unittest.main()
