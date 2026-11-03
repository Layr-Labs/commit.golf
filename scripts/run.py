"""Verify the machine certificate and record its combined cycle-times-bytes score."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import uuid

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "verifier"))
from scoring import score_claim

parser = argparse.ArgumentParser()
parser.parse_args()

score_path = Path("scripts/score.json")
score_path.unlink(missing_ok=True)
if sys.platform != "linux":
    raise SystemExit("Official verification requires Linux; the macOS mode is unsandboxed")
command = [sys.executable, "verifier/verify.py", "--local", "submission",
           "--trusted", ".", "--work", f".work/{uuid.uuid4().hex}"]
result = subprocess.run(command, stdout=subprocess.PIPE, text=True)
print(result.stdout, end="")
if result.returncode:
    raise SystemExit(result.returncode)
report = json.loads(result.stdout)
if report["status"] != "verified":
    raise SystemExit("Verifier did not accept the submission")
claim = report["claim"]
try:
    score = score_claim(claim)
except ValueError as exc:
    raise SystemExit(f"Invalid verifier metrics: {exc}")
if type(report.get("score")) is not int or report["score"] != score:
    raise SystemExit("Verifier reported a different score")
contract = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
if report["contract_commit"] != contract:
    raise SystemExit("Verifier used a different contract from the repository commit")
metrics = {**claim,
           "proverCycles": claim["commitCycles"] + claim["openingCycles"],
           "contractCommit": contract, "verified": True}
temporary = score_path.with_suffix(".tmp")
temporary.write_text(json.dumps({"score": score, "metrics": metrics}) + "\n")
temporary.replace(score_path)
