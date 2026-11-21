#!/usr/bin/env bash
# Trusted bootstrap in the fresh Ubuntu 26.04 guest, before any proof is compiled.
set -euo pipefail
cd /srv/commit-benchmark
systemctl --version
cat /sys/kernel/security/lsm
test "$(systemctl --version | head -1 | awk '{print $2}')" -ge 257
command -v bwrap
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
# lake comparator sandboxes each step with bwrap, which needs an unprivileged user namespace.
# Grant one only if this image does not already, so a distribution profile for bwrap stays sole.
bwrap_probe() { sudo -u golf bwrap --ro-bind / / --dev /dev --proc /proc --unshare-all -- true; }
if ! bwrap_probe; then
  cat > /etc/apparmor.d/golf-bwrap <<'APPARMOR'
abi <abi/4.0>,
include <tunables/global>
profile golf-bwrap /usr/bin/bwrap flags=(unconfined) {
  userns,
  include if exists <local/golf-bwrap>
}
APPARMOR
  apparmor_parser -r /etc/apparmor.d/golf-bwrap
  bwrap_probe
fi
