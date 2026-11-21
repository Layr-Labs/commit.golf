#!/usr/bin/env python3
"""Refuse comparator startup if systemd did not apply the mandatory Linux isolation."""
from __future__ import annotations

import os
from pathlib import Path
import socket
import sys


def namespace(kind: str) -> str | None:
    """This process's namespace of the given kind, or None when /proc cannot tell."""
    try:
        return str(os.stat(f"/proc/self/ns/{kind}").st_ino)
    except OSError:
        return None


def isolation_check() -> None:
    if sys.platform != "linux" or os.geteuid() == 0:
        raise RuntimeError("sandbox launcher requires an unprivileged Linux process")
    host_dev = os.environ.get("COMMIT_VERIFIER_HOST_DEV")
    host_shm = os.environ.get("COMMIT_VERIFIER_HOST_SHM_DEV")
    if not host_dev or str(Path("/dev").stat().st_dev) == host_dev:
        raise RuntimeError("systemd failed to provide private devices; refusing to compile")
    if host_shm and Path("/dev/shm").exists() and str(Path("/dev/shm").stat().st_dev) == host_shm:
        raise RuntimeError("systemd failed to isolate shared memory; refusing to compile")
    for path in (Path.cwd(), Path(__file__).resolve(), Path.home()):
        if not os.statvfs(path).f_flag & os.ST_RDONLY:
            raise RuntimeError(f"systemd failed to mount {path} read-only; refusing to compile")
    host_pidns = os.environ.get("COMMIT_VERIFIER_HOST_PIDNS")
    if not host_pidns or namespace("pid") in (None, host_pidns):
        raise RuntimeError("systemd failed to give the job its own PID namespace; refusing to compile")
    try:
        list(Path("/sys/kernel").iterdir())
    except OSError:
        pass
    else:
        raise RuntimeError("systemd failed to hide /sys/kernel; refusing to compile")
    if Path("/etc/commit-golf").exists():
        try:
            list(Path("/etc/commit-golf").iterdir())
        except OSError:
            pass
        else:
            raise RuntimeError("systemd failed to hide /etc/commit-golf; refusing to compile")
    # The comparator's bwrap sandbox needs AF_INET and AF_NETLINK sockets to bring up loopback
    # devices. They are harmless only inside a private network namespace with no other device.
    host_netns = os.environ.get("COMMIT_VERIFIER_HOST_NETNS")
    if not host_netns or namespace("net") in (None, host_netns):
        raise RuntimeError("systemd failed to give the job its own network namespace; refusing to compile")
    try:
        devices = [name for _, name in socket.if_nameindex()]
    except OSError as exc:
        raise RuntimeError(f"cannot list network devices ({exc}); refusing to compile") from exc
    if devices != ["lo"]:
        raise RuntimeError("the job's network namespace has devices besides loopback; refusing to compile")
    probe = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        # Connecting a UDP socket only selects a route; it sends nothing.
        probe.connect(("192.0.2.1", 9))
    except OSError:
        pass
    else:
        raise RuntimeError("the job can route beyond loopback; refusing to compile")
    finally:
        probe.close()
    for family, kind in ((socket.AF_UNIX, socket.SOCK_STREAM),
                         (socket.AF_UNIX, socket.SOCK_DGRAM),
                         (socket.AF_INET6, socket.SOCK_STREAM)):
        try:
            sock = socket.socket(family, kind)
        except OSError:
            continue
        sock.close()
        raise RuntimeError("systemd failed to restrict socket families; refusing to compile")
    try:
        # A zero signal is harmless, but uses the same syscall that could terminate a
        # same-UID worker. The supervisor lives outside this filter and can still kill us.
        os.kill(os.getpid(), 0)
    except OSError:
        pass
    else:
        raise RuntimeError("systemd failed to disable process signals; refusing to compile")


def main() -> int:
    try:
        isolation_check()
        if len(sys.argv) < 2:
            raise RuntimeError("sandbox launcher needs a command")
        os.execvpe(sys.argv[1], sys.argv[1:], os.environ)
    except (OSError, RuntimeError) as exc:
        print(f"sandbox launch refused: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
