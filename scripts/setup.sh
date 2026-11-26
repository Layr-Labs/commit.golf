#!/usr/bin/env bash
set -euo pipefail
unset BENCHMARK_INSECURE_LOCAL
export PATH="$HOME/.elan/bin:$PATH"
if ! command -v elan >/dev/null 2>&1; then
  curl --proto '=https' --tlsv1.2 -sSfL \
    https://raw.githubusercontent.com/leanprover/elan/464c9d28395000a2a0128e07081e4956d50eced2/elan-init.sh \
    | sh -s -- -y --default-toolchain none
fi
toolchain="$(tr -d '[:space:]' < lean-toolchain)"
if ! elan run "$toolchain" lean --version >/dev/null 2>&1; then
  elan toolchain install "$toolchain"
fi
# Confirm that installation supplied a runnable compiler before building the verifier.
elan run "$toolchain" lean --version
bash verifier/setup_tools.sh
lake exe cache get
lake build CommitGolf CommitGolfTests CommitGolfDepth.Rounds.Tests CommitGolfDepth.Span.Tests
python3 -c 'import sys; from pathlib import Path; sys.path.insert(0, "verifier"); from verify import linux_preflight, tools_env; linux_preflight(tools_env(Path(".").resolve()))'
