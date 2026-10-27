#!/usr/bin/env bash
# Trusted bootstrap in the fresh Ubuntu 26.04 guest, before any proof is compiled.
set -euo pipefail
cd /srv/commit-benchmark
systemctl --version
cat /sys/kernel/security/lsm
test "$(systemctl --version | head -1 | awk '{print $2}')" -ge 257
grep -qw landlock /sys/kernel/security/lsm
# ProtectSystem=strict excludes /home; keep the judge home under /srv, as upstream does.
useradd --create-home --home-dir /srv/golf --shell /bin/bash golf
chown -R golf:golf /srv/commit-benchmark
loginctl enable-linger golf
systemctl start "user@$(id -u golf).service"
cat > /etc/apparmor.d/golf-systemd-executor <<'APPARMOR'
abi <abi/4.0>,
include <tunables/global>
profile golf-systemd-executor /usr/lib/systemd/systemd-executor flags=(unconfined) {
  userns,
  include if exists <local/golf-systemd-executor>
}
APPARMOR
apparmor_parser -r /etc/apparmor.d/golf-systemd-executor
