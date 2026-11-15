#!/usr/bin/env python3
"""Enforce conservative aggregate limits on trusted, unmeasured Lean build trees."""
from __future__ import annotations

import argparse
from contextlib import contextmanager
import fcntl
import json
import math
import os
from pathlib import Path
import subprocess
import stat
import sys
import uuid
import tempfile

try:
    from . import resources
except ImportError:
    import resources

BUILD_MEMORY_BYTES = 8 * 1024**3
BUILD_TASKS = 128
BUILD_CPUS = 2
STOP_SECONDS = 5


def current_cgroup() -> Path:
    return resources._resolve_current_cgroup(resources.PROC_ROOT).directory


def already_bounded() -> bool:
    """Do not alter the existing measured 4-core/16-GiB condition contract."""
    try:
        directory = current_cgroup()
        memory = (directory / 'memory.max').read_text().strip()
        swap = (directory / 'memory.swap.max').read_text().strip()
        if not (memory.isdecimal() and 0 < int(memory) <= 16 * 1024**3 and swap == '0'):
            return False
        cores = set()
        for cpu in os.sched_getaffinity(0):
            topology = Path('/sys/devices/system/cpu') / f'cpu{cpu}' / 'topology'
            cores.add(((topology / 'physical_package_id').read_text().strip(),
                       (topology / 'die_id').read_text().strip(),
                       (topology / 'core_id').read_text().strip()))
        return 0 < len(cores) <= 4
    except (OSError, RuntimeError, ValueError):
        return False


def verify_build_limits(cpus: list[int]) -> dict:
    directory = current_cgroup()
    values = {name: (directory / name).read_text().strip() for name in
              ['memory.max', 'memory.swap.max', 'memory.oom.group', 'pids.max', 'cpu.max']}
    quota, period = values['cpu.max'].split()
    if (values['memory.max'] != str(BUILD_MEMORY_BYTES)
            or values['memory.swap.max'] != '0'
            or values['memory.oom.group'] != '1'
            or values['pids.max'] != str(BUILD_TASKS)
            or quota == 'max' or int(quota) > BUILD_CPUS * int(period)
            or int(quota) <= 0 or int(period) <= 0
            or sorted(os.sched_getaffinity(0)) != cpus
            or not 0 < len(cpus) <= BUILD_CPUS):
        raise RuntimeError('build cgroup limits or CPU affinity were not enforced')
    return dict(kind='highambench-build-resource-proof', verified=True,
                cgroup=str(directory), logical_cpus=cpus, controls=values)


def build_command(argv: list[str], *, timeout: float, cwd: Path | None = None,
                  environment: dict[str, str] | None = None) -> tuple[list[str], str]:
    if not argv or not math.isfinite(timeout) or timeout <= 0:
        raise ValueError('bounded build needs a command and a finite positive timeout')
    cpus = sorted(os.sched_getaffinity(0))[:BUILD_CPUS]
    if not cpus:
        raise RuntimeError('no CPU is available for bounded preparation')
    unit = 'highambench-build-' + uuid.uuid4().hex + '.service'
    runtime = '/run/user/' + str(os.getuid())
    command = ['/usr/bin/env', 'XDG_RUNTIME_DIR=' + runtime,
               'systemd-run', '--user', '--wait', '--pipe', '--collect', '--quiet',
               '--service-type=exec', '--unit=' + unit,
               '--property=MemoryAccounting=yes', '--property=CPUAccounting=yes',
               '--property=TasksAccounting=yes', '--property=CPUQuota=200%',
               '--property=MemoryMax=' + str(BUILD_MEMORY_BYTES),
               '--property=MemorySwapMax=0', '--property=MemoryHigh=infinity',
               '--property=TasksMax=' + str(BUILD_TASKS),
               '--property=CPUAffinity=' + ' '.join(map(str, cpus)),
               '--property=KillMode=control-group', '--property=OOMPolicy=kill',
               '--property=SendSIGKILL=yes', '--property=TimeoutStopSec=' + str(STOP_SECONDS),
               '--property=RuntimeMaxSec=' + str(math.ceil(timeout)),
               '--property=NoNewPrivileges=yes', '--property=SystemCallArchitectures=native',
               '--property=SystemCallFilter=~sched_setaffinity',
               '--property=SystemCallErrorNumber=EPERM']
    if cwd is not None:
        command.append('--working-directory=' + str(cwd.resolve()))
    # systemd services do not inherit the caller's environment. Pass the exact
    # trusted build environment explicitly; never load credentials or auth files.
    safe_keys = {'PATH', 'LANG', 'LC_ALL', 'LEAN_PATH', 'TMPDIR'}
    for key, value in sorted((environment or {}).items()):
        if key in safe_keys:
            command.append('--setenv=' + key + '=' + value)
    command.extend(['--', sys.executable, str(Path(__file__).resolve()),
                    '--cpus', ','.join(map(str, cpus)), '--', *argv])
    return command, unit


@contextmanager
def command_scope(argv: list[str], *, timeout: float, cwd: Path | None = None,
                  environment: dict[str, str] | None = None):
    lock_path = Path(tempfile.gettempdir()) / f'highambench-build-{os.getuid()}.lock'
    descriptor = os.open(lock_path, os.O_CREAT | os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW, 0o600)
    try:
        info = os.fstat(descriptor)
        if (info.st_uid != os.getuid() or not stat.S_ISREG(info.st_mode)
                or stat.S_IMODE(info.st_mode) != 0o600 or info.st_nlink != 1):
            raise RuntimeError('build serialization lock is not private and user-owned')
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise RuntimeError('another bounded preparation/build is already running') from error
        command, unit = build_command(argv, timeout=timeout, cwd=cwd, environment=environment)
        try:
            yield command
        finally:
            # Stop only this generated unit, including surviving descendants after
            # a timeout, interrupted coordinator, or failed launcher. Its native
            # RuntimeMaxSec also applies if the coordinator is killed outright.
            stopped = subprocess.run(['systemctl', '--user', 'stop', unit],
                                     capture_output=True, text=True, timeout=STOP_SECONDS + 10,
                                     env=dict(os.environ, XDG_RUNTIME_DIR='/run/user/' + str(os.getuid())))
            if stopped.returncode and 'not loaded' not in stopped.stderr and 'not found' not in stopped.stderr:
                raise RuntimeError('cannot clean up bounded build unit: ' + stopped.stderr.strip())
    finally:
        os.close(descriptor)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cpus', required=True)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    try:
        cpus = [int(cpu) for cpu in args.cpus.split(',')]
        if not command:
            raise RuntimeError('no build command')
        proof = verify_build_limits(cpus)
        print('HIGHAMBENCH_BUILD_RESOURCE_PROOF=' + json.dumps(proof, sort_keys=True),
              file=sys.stderr, flush=True)
        environment = dict(os.environ, LEAN_NUM_THREADS='1', OMP_NUM_THREADS='1',
                           OPENBLAS_NUM_THREADS='1', MKL_NUM_THREADS='1')
        os.execvpe(command[0], command, environment)
    except (OSError, RuntimeError, ValueError) as error:
        print('bounded build error: ' + str(error), file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
