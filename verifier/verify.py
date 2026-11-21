#!/usr/bin/env python3
"""Check one frozen submission using a trusted challenge and an isolated comparator.

Local mode is for development only. Linux refuses to compile untrusted code without the
systemd unit around `lake comparator` and the comparator's own bwrap sandbox inside it; the
checker is never given the GitHub token.
"""
from __future__ import annotations

import argparse
import json
import os
import platform
import re
import selectors
import shutil
import signal
import subprocess
import sys
import time
import uuid
from pathlib import Path

from check_submission import check
from artifact import load_artifact, purge_artifact_cache, write_artifact_module
from fetch import FetchError, fetch_pr

HERE = Path(__file__).resolve().parent
TRUSTED = HERE.parent
LOG_CAP = 4 * 1024 * 1024
WALL_SECONDS = 4 * 3600
MEMORY_BYTES = 24 * 1024**3
MIN_SYSTEMD_VERSION = 257  # PrivatePIDs, also required by scripts/vm-setup.sh


class VerifyError(ValueError):
    pass


def tools_env(root: Path) -> dict[str, str]:
    path = root / 'verifier' / '.tools' / 'env.sh'
    if not path.is_file():
        raise VerifyError('verification tools missing; run verifier/setup_tools.sh')
    values = {}
    for line in path.read_text().splitlines():
        if line.startswith('export ') and '=' in line:
            name, value = line[7:].split('=', 1)
            values[name] = value.strip().strip('"')
    if platform.system() == 'Linux':
        file = Path(values.get('COMPARATOR_BWRAP', ''))
        if not file.is_absolute() or not file.is_file() or not os.access(file, os.X_OK):
            raise VerifyError('COMPARATOR_BWRAP must point to an installed executable')
    return values


def clone_tree(src: Path, dst: Path) -> None:
    if platform.system() == 'Darwin':
        cmd = ['cp', '-c', '-R', str(src), str(dst)]
    else:
        cmd = ['cp', '-a', '--reflink=auto', str(src), str(dst)]
    subprocess.run(cmd, check=True, timeout=600, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)


def linux_systemd_preflight() -> None:
    if not shutil.which('systemd-run') or not shutil.which('systemctl'):
        raise VerifyError('systemd user services are required on Linux')
    try:
        result = subprocess.run(['systemd-run', '--version'], check=True, text=True,
                                capture_output=True, timeout=10)
    except (OSError, subprocess.SubprocessError) as exc:
        raise VerifyError('could not determine systemd version; systemd 257 or newer is required') from exc
    version = re.match(r'systemd\s+([0-9]+)\b', result.stdout)
    if version is None:
        raise VerifyError('unrecognized systemd version; systemd 257 or newer is required')
    if int(version[1]) < MIN_SYSTEMD_VERSION:
        raise VerifyError(f'systemd {MIN_SYSTEMD_VERSION} or newer is required for PrivatePIDs '
                          f'(found {version[1]})')


def linux_preflight(env: dict[str, str]) -> None:
    if os.geteuid() == 0:
        raise VerifyError('refusing to compile candidate code as root')
    linux_systemd_preflight()
    if Path(env['COMPARATOR_BWRAP']).open('rb').read(4) != b'\x7fELF':
        raise VerifyError('a compiled bwrap binary is required on Linux')
    if platform.machine() not in {'x86_64', 'aarch64', 'riscv64'}:
        raise VerifyError('unsupported Linux architecture')


def linux_command(cmd: list[str], project: Path, env: dict[str, str], hidden: list[Path]) -> tuple[list[str], dict[str, str]]:
    unit = 'commit-verify-' + uuid.uuid4().hex[:12]
    # Lake scales its parallel builds to visible CPUs; the host has eight CPUs but the
    # verification cgroup has only 24 GiB. Keep large independent Lean modules from
    # collectively exhausting that memory limit.
    cpus = sorted(os.sched_getaffinity(0))[:2]
    # The comparator's bwrap sandbox gives each step a new network namespace and brings up its
    # loopback device, which needs an AF_INET socket (glibc's interface lookup) and an AF_NETLINK
    # socket. The unit therefore runs in its own network namespace, with only a loopback device,
    # and AF_UNIX stays unavailable, so no host socket is reachable.
    properties = [f'MemoryMax={MEMORY_BYTES}', 'MemorySwapMax=0', f'RuntimeMaxSec={WALL_SECONDS}',
                  f'CPUAffinity={" ".join(map(str, cpus))}',
                  'KillMode=control-group', 'TimeoutStopSec=5', 'SendSIGKILL=yes', 'TasksMax=512',
                  'PrivateNetwork=yes', 'RestrictAddressFamilies=AF_INET AF_NETLINK',
                  'NoNewPrivileges=yes', 'ProtectSystem=strict',
                  f'ReadWritePaths={project / ".lake"}', 'PrivateTmp=yes', 'PrivatePIDs=yes', 'ProcSubset=pid',
                  'InaccessiblePaths=/sys',
                  'InaccessiblePaths=' + ' '.join(f'-{p}' for p in ['/etc/commit-golf', *hidden]),
                  'PrivateDevices=yes', 'TemporaryFileSystem=/dev/shm', 'PrivateIPC=yes',
                  'SystemCallErrorNumber=EPERM',
                  'SystemCallFilter=~@debug ptrace process_vm_readv process_vm_writev '
                  'pidfd_getfd kill tkill tgkill pidfd_send_signal']
    clean = {'PATH': f'{Path.home() / ".elan/bin"}:{os.environ.get("PATH", "/usr/bin:/bin")}',
             'HOME': str(Path.home()), 'LANG': 'C.UTF-8',
             'COMPARATOR_BWRAP': env['COMPARATOR_BWRAP'],
             'COMMIT_VERIFIER_HOST_DEV': str(Path('/dev').stat().st_dev),
             'COMMIT_VERIFIER_HOST_NETNS': str(Path('/proc/self/ns/net').stat().st_ino),
             'COMMIT_VERIFIER_HOST_PIDNS': str(Path('/proc/self/ns/pid').stat().st_ino),
             'COMMIT_VERIFIER_HOST_SHM_DEV': str(Path('/dev/shm').stat().st_dev)}
    command = ['/usr/bin/env', '-i', *[f'{k}={v}' for k, v in clean.items()],
               sys.executable, str(HERE / 'linux_exec.py'), *cmd]
    runtime = os.environ.get('XDG_RUNTIME_DIR', f'/run/user/{os.getuid()}')
    bus_env = {'PATH': clean['PATH'], 'HOME': clean['HOME'], 'XDG_RUNTIME_DIR': runtime,
               'DBUS_SESSION_BUS_ADDRESS': os.environ.get('DBUS_SESSION_BUS_ADDRESS', f'unix:path={runtime}/bus')}
    return (['systemd-run', '--user', '--wait', '--collect', '--pipe', '--quiet', f'--unit={unit}',
             f'--working-directory={project}',
             *[arg for prop in properties for arg in ('-p', prop)], '--', *command], bus_env)


def run_checked(cmd: list[str], cwd: Path, env: dict[str, str], log: Path) -> tuple[int, bool]:
    """Capture at most 4 MiB; keep draining; kill the process group at the outer deadline."""
    proc = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            start_new_session=True, bufsize=0)
    deadline = time.monotonic() + WALL_SECONDS + 120
    truncated = False
    timed_out = False
    try:
        os.set_blocking(proc.stdout.fileno(), False)
        with selectors.DefaultSelector() as selector, log.open('wb') as output:
            selector.register(proc.stdout, selectors.EVENT_READ)
            kept = 0
            while True:
                remain = deadline - time.monotonic()
                if remain <= 0:
                    timed_out = True
                    break
                if not selector.select(remain):
                    continue
                try:
                    chunk = os.read(proc.stdout.fileno(), 65536)
                except BlockingIOError:
                    continue
                if not chunk:
                    break
                if kept < LOG_CAP:
                    output.write(chunk[:LOG_CAP - kept])
                    kept += min(len(chunk), LOG_CAP - kept)
                if kept >= LOG_CAP:
                    truncated = True
            if truncated:
                output.write(b'\n[output truncated]\n')
        if not timed_out:
            proc.wait(timeout=max(.1, deadline - time.monotonic()))
    except subprocess.TimeoutExpired:
        timed_out = True
    finally:
        if timed_out:
            try:
                os.killpg(proc.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                proc.wait()
        proc.stdout.close()
    return proc.returncode, timed_out


def verify(args: argparse.Namespace) -> dict:
    work = args.work.resolve()
    log = work / 'verify.log'
    result = {'status': 'failed', 'commit': args.commit, 'contract_commit': None,
              'log': str(log), 'claim': None, 'artifact_digest': None, 'work_created': False}
    try:
        if args.local and work.is_relative_to(args.local.resolve()):
            raise VerifyError('work directory must be outside the local submission directory')
        if work.exists():
            raise VerifyError('work directory must not exist')
        work.mkdir(parents=True)
        result['work_created'] = True
        env = tools_env(args.trusted)
        if platform.system() == 'Linux':
            linux_preflight(env)
        contract = subprocess.run(['git', '-C', str(args.trusted), 'rev-parse', 'HEAD'],
                                  check=True, text=True, capture_output=True, timeout=10).stdout.strip()
        result['contract_commit'] = contract
        if not re.fullmatch(r'[0-9a-f]{40}|[0-9a-f]{64}', contract):
            raise VerifyError('trusted checkout has no canonical commit')
        source = work / 'source'
        if args.local:
            shutil.copytree(args.local, source, symlinks=True)
        else:
            fetch_pr(args.repository, args.pr, args.commit, source)
        policy = check(source)
        result['claim'] = policy['claim']
        if not policy['ok']:
            result.update(status='policy_rejected', errors=policy['errors'])
            log.write_text('\n'.join(policy['errors']) + '\n')
            return result
        artifact = load_artifact(source / 'programs.json')
        if artifact.digest != policy['artifactDigest']:
            raise VerifyError('programs.json changed after policy validation')
        result['artifact_digest'] = artifact.digest
        project = work / 'project'
        project.mkdir()
        for name in ('lean-toolchain', 'lakefile.lean', 'lake-manifest.json', 'CommitGolf.lean'):
            shutil.copy2(args.trusted / name, project / name)
        for name in ('CommitGolf',):
            shutil.copytree(args.trusted / name, project / name)
        write_artifact_module(artifact, project)
        with (project / 'lakefile.lean').open('a') as out:
            out.write('\nlean_lib Solution\n')
        if (source / 'CommitGolfCandidate').is_dir():  # optional: Solution.lean may stand alone
            shutil.copytree(source / 'CommitGolfCandidate', project / 'CommitGolfCandidate')
        shutil.copy2(source / 'Solution.lean', project / 'Solution.lean')
        challenge = (args.trusted / 'verifier' / 'Challenge.lean.in').read_text()
        for key, value in policy['claim'].items():
            challenge = challenge.replace('{{' + key + '}}', str(value))
        (project / 'CommitGolf' / 'Challenge.lean').write_text(challenge)
        clone_tree(args.trusted / '.lake', project / '.lake')
        purge_artifact_cache(project)
        # Drop every cached artifact of candidate, solution, and challenge modules: the module
        # directories and the root-module files (.olean, .ilean, .trace, .hash, .c) beside them.
        for folder in (project / '.lake' / 'build' / 'lib' / 'lean', project / '.lake' / 'build' / 'ir'):
            for name in ('CommitGolfCandidate', 'Solution'):
                if (folder / name).is_dir():
                    shutil.rmtree(folder / name)
                for stale in folder.glob(f'{name}.*'):
                    stale.unlink()
            for stale in (folder / 'CommitGolf').glob('Challenge.*'):
                stale.unlink()
        config = ['--config', str(args.trusted / 'verifier' / 'comparator.json')]
        clean_env = {'PATH': f'{Path.home() / ".elan/bin"}:{os.environ.get("PATH", "/usr/bin:/bin")}',
                     'HOME': str(Path.home()), 'LANG': 'C.UTF-8'}
        if platform.system() == 'Linux':
            command, clean_env = linux_command(['lake', 'comparator', *config], project, env,
                                               [work / 'source', *args.hide])
        else:
            # bwrap needs Linux namespaces. This development mode is not a sandbox.
            command = ['lake', 'comparator', '--inadvisably-no-sandbox', *config]
        exit_code, timeout = run_checked(command, project, clean_env, log)
        if timeout:
            result['status'] = 'timeout'
        elif exit_code == 0 and 'Your solution is okay!' in log.read_text(errors='replace'):
            result.update(status='verified', score=policy['score'])
        else:
            result.update(status='rejected', reason=log.read_text(errors='replace')[-1200:])
        return result
    except (FetchError, ValueError, OSError, subprocess.SubprocessError) as exc:
        result.update(status='failed', reason=str(exc)[:1200])
        return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--repository', default='Layr-Labs/commit.golf')
    parser.add_argument('--pr', type=int)
    parser.add_argument('--commit')
    parser.add_argument('--local', type=Path)
    parser.add_argument('--trusted', type=Path, default=TRUSTED)
    parser.add_argument('--work', type=Path)
    parser.add_argument('--hide', type=Path, action='append', default=[])
    parser.add_argument('--cleanup', action='store_true')
    args = parser.parse_args()
    if bool(args.local) == bool(args.pr and args.commit):
        parser.error('provide either --local or both --pr and --commit')
    args.trusted = args.trusted.resolve()
    if args.work is None:
        args.work = Path.cwd() / '.work' / uuid.uuid4().hex
    result = verify(args)
    cleanup_work = Path(result['log']).parent if result.get('work_created') is True else None
    if args.cleanup and cleanup_work is not None and cleanup_work.exists():
        try:
            # Candidate code can change permissions inside its writable build tree.
            for directory, children, _ in os.walk(cleanup_work, followlinks=False):
                os.chmod(directory, os.stat(directory).st_mode | 0o700)
                for child in children:
                    path = Path(directory) / child
                    if not path.is_symlink():
                        os.chmod(path, path.stat().st_mode | 0o700)
            shutil.rmtree(cleanup_work)
        except OSError as exc:
            result.update(status='failed', reason=f'workspace cleanup failed: {exc}')
    print(json.dumps(result, sort_keys=True))
    return 0 if result['status'] == 'verified' else 1


if __name__ == '__main__':
    raise SystemExit(main())
