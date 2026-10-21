#!/usr/bin/env python3
"""Nonprivileged deployment observations; no containment acceptance."""
import ctypes
import fcntl
import hashlib
import json
import os
import platform
from pathlib import Path
import shutil
import subprocess
import sys


def status():
    keys = {"Uid", "Gid", "Groups", "CapInh", "CapPrm", "CapEff", "CapBnd", "CapAmb", "NoNewPrivs", "Seccomp"}
    return {k: v.strip() for line in Path('/proc/self/status').read_text().splitlines()
            for k, sep, v in [line.partition(':')] if sep and k in keys}


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


if len(sys.argv) > 1:
    if sys.argv[1] == 'set-nnp':
        libc = ctypes.CDLL(None, use_errno=True)
        if libc.prctl(38, 1, 0, 0, 0) != 0:
            raise OSError(ctypes.get_errno(), 'PR_SET_NO_NEW_PRIVS')
        os.execv(sys.executable, [sys.executable, __file__, 'exec-once'])
    elif sys.argv[1] == 'exec-once':
        first = json.dumps(status(), sort_keys=True)
        os.execv(sys.executable, [sys.executable, __file__, 'exec-twice', first])
    elif sys.argv[1] == 'exec-twice':
        print(json.dumps({'after_exec': json.loads(sys.argv[2]), 'after_reexec': status()}))
    else:
        raise SystemExit('unknown mode')
    raise SystemExit(0)

result = {'scope': 'Stage A observations only; isolated profile not established',
          'kernel': platform.uname()._asdict(), 'python': sys.version,
          'python_path': sys.executable, 'python_sha256': digest(sys.executable),
          'probe_sha256': digest(__file__), 'initial_status': status()}
try:
    fd = os.memfd_create('ash-profile-probe', os.MFD_ALLOW_SEALING)
    os.write(fd, b'trusted probe bytes')
    seals = fcntl.F_SEAL_WRITE | fcntl.F_SEAL_GROW | fcntl.F_SEAL_SHRINK | fcntl.F_SEAL_SEAL
    fcntl.fcntl(fd, fcntl.F_ADD_SEALS, seals)
    try:
        os.write(fd, b'X')
        mutation = 'unexpected success'
    except OSError as exc:
        mutation = {'errno': exc.errno, 'message': str(exc)}
    result['memfd'] = {'seals': fcntl.fcntl(fd, fcntl.F_GET_SEALS), 'write_after_seal': mutation,
                       'execution': 'not tested'}
    os.close(fd)
except (OSError, AttributeError) as exc:
    result['memfd'] = {'error': str(exc)}
for name, argv in [('nnp_exec_reexec', [sys.executable, __file__, 'set-nnp']),
                   ('user_namespace', [shutil.which('unshare') or 'unshare', '--user', '--', 'true'])]:
    try:
        run = subprocess.run(argv, capture_output=True, text=True, timeout=5)
        result[name] = {'argv': argv, 'exit': run.returncode, 'stdout': run.stdout, 'stderr': run.stderr}
    except (OSError, subprocess.TimeoutExpired) as exc:
        result[name] = {'error': str(exc)}
result['cgroup'] = {'membership': Path('/proc/self/cgroup').read_text(), 'observations': {}}
for name in ['cgroup.controllers', 'cgroup.subtree_control', 'cgroup.procs', 'memory.max', 'memory.swap.max', 'cpu.max', 'pids.max']:
    path = Path('/sys/fs/cgroup') / name
    result['cgroup']['observations'][str(path)] = {'exists': path.exists(), 'writable_as_observed': os.access(path, os.W_OK)}
result['stage_b'] = 'not executed; no launcher, approved static images, delegated limits or prepared storage'
print(json.dumps(result, indent=2, sort_keys=True))
