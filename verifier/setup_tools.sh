#!/usr/bin/env bash
# Prepare and test the judge: Lake's built-in `lake comparator` and, on Linux, its bwrap sandbox.
#
#   verifier/setup_tools.sh          # writes verifier/.tools/env.sh after an acceptance test
#
# Policy: the judge must come from the project's exact Lean release, because it replays the
# export through that release's kernel and the bundled exporter reads the project's .olean files.
# `lake comparator` ships with every Lean release from v4.35.0, so the toolchain in
# `lean-toolchain` supplies the judge, the exporter and the kernel checker together.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tools="${root}/verifier/.tools"
export PATH="${HOME}/.elan/bin:${PATH}"

if ! command -v elan >/dev/null 2>&1; then
  echo "elan is required; install and verify it before preparing the verification tools" >&2
  exit 1
fi
toolchain="$(tr -d '[:space:]' < "${root}/lean-toolchain")"
elan run "${toolchain}" lake comparator --help >/dev/null

if [[ "$(uname -s)" == Linux ]]; then
  bwrap_bin="$(command -v bwrap || true)"
  if [[ -z "${bwrap_bin}" ]]; then
    echo "bubblewrap (bwrap) is required to sandbox the comparator on Linux" >&2
    exit 1
  fi
  echo "sandbox: $("${bwrap_bin}" --version) at ${bwrap_bin}"
  sandbox_flags=()
else
  echo "non-Linux host: lake comparator runs WITHOUT a sandbox; this mode is for development only" >&2
  bwrap_bin=""
  sandbox_flags=(--inadvisably-no-sandbox)
fi

# Acceptance: the judge must accept a matching proof and reject a mismatched statement on this
# host, with the sandbox it will use for submissions.
fixture="$(mktemp -d)"
trap 'rm -rf "${fixture}"' EXIT
judge() {  # solution source; prints the judge's exit status
  rm -rf "${fixture}/project"
  mkdir -p "${fixture}/project"
  cp "${root}/lean-toolchain" "${fixture}/project/lean-toolchain"
  cat > "${fixture}/project/lakefile.toml" <<'TOML'
name = "fixture"

[[lean_lib]]
name = "Challenge"

[[lean_lib]]
name = "Solution"
TOML
  cat > "${fixture}/project/comparator.json" <<'JSON'
{"challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": ["fixture"],
 "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}
JSON
  echo 'theorem fixture : 2 + 2 = 4 := sorry' > "${fixture}/project/Challenge.lean"
  printf '%s\n' "$1" > "${fixture}/project/Solution.lean"
  # The comparator needs a manifest; this trusted fixture has no dependencies to resolve.
  ( cd "${fixture}/project" && lake build Challenge >/dev/null )
  local status=0
  ( cd "${fixture}/project" && COMPARATOR_BWRAP="${bwrap_bin}" \
      lake comparator "${sandbox_flags[@]}" --config comparator.json ) \
    > "${fixture}/log" 2>&1 || status=$?
  echo "${status}"
}
accepted="$(judge 'theorem fixture : 2 + 2 = 4 := rfl')"
if [[ "${accepted}" != 0 ]] || ! grep -qx 'Your solution is okay!' "${fixture}/log"; then
  cat "${fixture}/log" >&2
  echo "acceptance test failed: the comparator did not accept a matching proof" >&2
  exit 1
fi
reject() {  # solution source, expected diagnostic, description
  local status
  status="$(judge "$1")"
  if [[ "${status}" != 1 ]] || ! grep -qxF "error: $2" "${fixture}/log" ||
      grep -q 'Your solution is okay!' "${fixture}/log"; then
    cat "${fixture}/log" >&2
    echo "acceptance test failed: the comparator did not reject $3" >&2
    exit 1
  fi
}
reject 'theorem fixture : 2 + 2 = 4 ∨ False := .inl rfl' \
  "Challenge and solution theorem statement do not match: 'fixture'" 'a mismatched statement'
reject 'theorem fixture : 2 + 2 = 4 := sorry' \
  "Illegal axiom detected: 'sorryAx'" 'a proof that uses sorry'

mkdir -p "${tools}"
cat > "${tools}/env.sh" <<ENV
export COMPARATOR_BWRAP="${bwrap_bin}"
ENV
echo "tools ready; judge: lake comparator from ${toolchain}"
