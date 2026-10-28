"""Verify one track submission and record its two scores in scripts/score.json."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import uuid

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "verifier"))
from tracks import TRACKS, submission_path

parser = argparse.ArgumentParser()
parser.add_argument("--track", choices=TRACKS, default="ideal-permutation")
args = parser.parse_args()

score_path = Path("scripts/score.json")
score_path.unlink(missing_ok=True)
if sys.platform != "linux":
    raise SystemExit("Official verification requires Linux; the macOS mode is unsandboxed")
command = [sys.executable, "verifier/verify.py", "--local", submission_path(args.track), "--track", args.track,
           "--trusted", ".", "--work", f".work/{uuid.uuid4().hex}"]
result = subprocess.run(command, stdout=subprocess.PIPE, text=True)
print(result.stdout, end="")
if result.returncode:
    raise SystemExit(result.returncode)
report = json.loads(result.stdout)
if report["status"] != "verified" or report["track"] != args.track:
    raise SystemExit("Verifier did not accept the submission")
claim = report["claim"]
proof_bytes, check_calls = claim["proofBytes"], claim["checkCalls"]
if any(type(value) is not int or not 0 <= value <= 2**53 - 1 for value in (proof_bytes, check_calls)):
    raise SystemExit("Invalid verifier metrics")
contract = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
if report["contract_commit"] != contract:
    raise SystemExit("Verifier used a different contract from the repository commit")
# The leaderboard is the Pareto frontier of the two scores, so there is no single combined score.
metrics = {"track": args.track, "proofBytes": proof_bytes, "checkCalls": check_calls,
           "contractCommit": contract, "verified": True}
temporary = score_path.with_suffix(".tmp")
temporary.write_text(json.dumps({"metrics": metrics}) + "\n")
temporary.replace(score_path)
