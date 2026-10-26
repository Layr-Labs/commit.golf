#!/usr/bin/env bash
# Verify one track submission and record its product score and metrics for Yukon.
set -euo pipefail

track=ideal-permutation
if [[ $# -ne 0 ]]; then
  if [[ $# -ne 2 || "$1" != --track ]]; then
    echo "Usage: bash scripts/benchmark.sh [--track TRACK]" >&2
    exit 2
  fi
  track="$2"
fi
case "$track" in
  ideal-permutation|ideal-compression|random-oracle-fixed-output|ideal-xof) ;;
  *) echo "Unknown track: $track" >&2; exit 2 ;;
esac

score_path="scripts/scores/$track/score.json"
mkdir -p "$(dirname "$score_path")"
rm -f "$score_path"
if [[ "$(uname -s)" != Linux ]]; then
  echo "Official verification requires Linux; the macOS mode is unsandboxed" >&2
  exit 1
fi
mkdir -p .work
work="$(mktemp -d .work/benchmark.XXXXXXXX)"
python3 verifier/verify.py --local "submissions/$track" --track "$track" \
  --trusted . --work "$work/verifier" > "$work/report.json" || {
    status=$?
    cat "$work/report.json"
    exit "$status"
  }
cat "$work/report.json"

# Keep JSON validation and integer arithmetic exact, including Yukon's score limit.
python3 - "$work/report.json" "$track" "$score_path" <<'PYTHON'
import json
from pathlib import Path
import subprocess
import sys

report = json.loads(Path(sys.argv[1]).read_text())
track = sys.argv[2]
score_path = Path(sys.argv[3])
if report["status"] != "verified" or report["track"] != track:
    raise SystemExit("Verifier did not accept the submission")
claim = report["claim"]
proof_bytes, check_calls = claim["proofBytes"], claim["checkCalls"]
if any(type(value) is not int or not 0 <= value <= 2**53 - 1 for value in (proof_bytes, check_calls)):
    raise SystemExit("Invalid verifier metrics")
contract = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
if report["contract_commit"] != contract:
    raise SystemExit("Verifier used a different contract from the repository commit")
score = proof_bytes * check_calls
if score > 2**53 - 1:
    raise SystemExit("Product score exceeds Yukon's exact integer range")
metrics = {"track": track, "proofBytes": proof_bytes, "checkCalls": check_calls,
           "contractCommit": contract, "verified": True}
temporary = score_path.with_suffix(".tmp")
temporary.write_text(json.dumps({"score": score, "metrics": metrics}) + "\n")
temporary.replace(score_path)
PYTHON
