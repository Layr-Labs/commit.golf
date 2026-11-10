#!/usr/bin/env bash
# Trusted guest bootstrap, before candidate files enter the VM. Mirror index/hash
# mismatches can be transient; every retry still requires a fully verified update.
set -euo pipefail
export DEBIAN_FRONTEND=noninteractive
apt_options=(-o Acquire::Retries=0 -o Acquire::http::Timeout=30 -o Acquire::https::Timeout=30)
for ((attempt=1; attempt<=3; attempt++)); do
  echo "Verified guest package setup: attempt ${attempt}/3"
  # --error-on=any rejects partial updates instead of installing from stale indexes.
  # Bound both stages, including a wedged package process; signatures/hashes remain mandatory.
  if timeout --kill-after=10s 300s apt-get "${apt_options[@]}" --error-on=any update &&
     timeout --kill-after=10s 480s apt-get "${apt_options[@]}" -y install \
       git curl build-essential python3 golang-go dbus-user-session apparmor zstd; then
    exit 0
  fi
  if ((attempt < 3)); then sleep 10; fi
done
echo 'Verified guest package setup failed after three attempts' >&2
exit 1
