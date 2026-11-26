"""Verify the machine certificate and record the selected track’s certified score."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import uuid

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "verifier"))
from scoring import score_claim, depth_objectives
from depth_profiles import depth_profile
from tracks import TRACKS

parser = argparse.ArgumentParser()
parser.add_argument("--track", choices=tuple(TRACKS), default="product")
args = parser.parse_args()
track = TRACKS[args.track]
submission = Path(track.submission)

score_path = Path(track.score_path)
score_path.parent.mkdir(parents=True, exist_ok=True)
score_path.unlink(missing_ok=True)
if sys.platform != "linux":
    raise SystemExit("Official verification requires Linux; the macOS mode is unsandboxed")
command = [sys.executable, "verifier/verify.py", "--local", str(submission),
           "--trusted", ".", "--work", f".work/{uuid.uuid4().hex}", "--track", args.track]
result = subprocess.run(command, stdout=subprocess.PIPE, text=True)
print(result.stdout, end="")
if result.returncode:
    raise SystemExit(result.returncode)
report = json.loads(result.stdout)
if report["status"] != "verified":
    raise SystemExit("Verifier did not accept the submission")
if (report.get("track") != args.track or type(report.get("permutation_cycles")) is not int
        or report["permutation_cycles"] != track.permutation_cycles
        or type(report.get("compression_input_bytes")) is not int
        or report["compression_input_bytes"] != track.compression_input_bytes):
    raise SystemExit("Verifier used a different track, permutation cost, or compression width")
claim = report["claim"]
profile = depth_profile(track.depth_model) if track.depth_model is not None else None
try:
    if profile is None:
        score = score_claim(claim)
        if type(report.get("score")) is not int or report["score"] != score:
            raise SystemExit("Verifier reported a different score")
    else:
        point = depth_objectives(claim, track.depth_model)
        actual = report.get("scores")
        if (type(actual) is not list or len(actual) != 3
                or any(type(value) is not int for value in actual) or actual != point
                or report.get("score") is not None
                or report.get("resource_model") != profile.version
                or report.get("objective_names") != list(profile.objectives)):
            raise SystemExit("Verifier reported a different depth contract or objective point")
except ValueError as exc:
    raise SystemExit(f"Invalid verifier metrics: {exc}")
contract = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
if report["contract_commit"] != contract:
    raise SystemExit("Verifier used a different contract from the repository commit")
artifact_digest = hashlib.sha256((submission / 'programs.json').read_bytes()).hexdigest()
if report.get('artifact_digest') != artifact_digest:
    raise SystemExit('Verifier used a different delivered program manifest')
metrics = {**claim, "track": args.track, "permutationCycles": track.permutation_cycles,
           "compressionInputBytes": track.compression_input_bytes,
           "contractCommit": contract, "artifactDigest": artifact_digest, "verified": True}
if profile is None:
    metrics["proverCycles"] = claim["commitCycles"] + claim["openingCycles"]
else:
    metrics.update({profile.work_metric: point[0], profile.depth_metric: point[2],
                    "resourceModel": profile.version})
temporary = score_path.with_suffix(".tmp")
if profile is not None:
    payload = {"valid": True, "scores": point, "metrics": metrics}
else:
    payload = ({"valid": True, "scores": [metrics["proverCycles"], claim["proofBytes"]],
                "metrics": metrics} if track.pareto else {"score": score, "metrics": metrics})
temporary.write_text(json.dumps(payload) + "\n")
temporary.replace(score_path)
