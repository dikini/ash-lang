"""Disposable Linux trusted-build monitor. No shell, native admission or containment."""
import ctypes
import hashlib
import json
import math
import os
from pathlib import Path, PurePosixPath
import selectors
import signal
import stat
import subprocess
import sys
import tempfile
import time

MAX_LOG = 16 * 1024 * 1024
MAX_MAP = 128 * 1024 * 1024
MAX_IMAGE = 128 * 1024 * 1024
MAX_CONFIG = 256 * 1024
MAX_RECORD = 4 * 1024 * 1024
MAX_ENTRIES = 4096
DEADLINE = 1200
INTERVAL = .01

class Refusal(Exception):
    pass

class Interrupted(Exception):
    pass

def digest_file(path, limit, *, prefix=False, copy_to=None):
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC)
    retained = None
    try:
        before = os.fstat(fd)
        if not stat.S_ISREG(before.st_mode):
            raise Refusal('not a regular file: ' + str(path))
        if before.st_size > limit and not prefix:
            raise Refusal('hash input exceeds bound: ' + str(path))
        digest = hashlib.sha256(); size = 0
        retained = open(copy_to, 'xb') if copy_to is not None else None
        while size < limit:
            block = os.read(fd, min(65536, limit-size))
            if not block:
                break
            digest.update(block); size += len(block)
            if retained is not None:
                retained.write(block)
        if retained is not None:
            retained.close()
        after = os.fstat(fd)
        return {'path': str(path), 'size_before': before.st_size, 'size_after': after.st_size,
                'hashed_bytes': size, 'sha256': digest.hexdigest(),
                'hash_is_prefix': max(before.st_size, after.st_size) > size,
                'device': before.st_dev, 'inode': before.st_ino}
    finally:
        if retained is not None:
            retained.close()
        os.close(fd)

def private_directory(path):
    path = Path(path)
    if not path.is_absolute() or str(path.resolve()) != str(path):
        raise Refusal('directory must be absolute without symlink components')
    info = path.stat()
    if not stat.S_ISDIR(info.st_mode) or info.st_uid != os.geteuid() or info.st_mode & 0o077:
        raise Refusal('directory must be owned by monitor UID and private (0700)')
    return path

def children():
    text = Path(f'/proc/self/task/{os.getpid()}/children').read_text()
    return [int(part) for part in text.split()]

def subreaper():
    if sys.platform != 'linux' or not hasattr(os, 'waitid') or not hasattr(os, 'WNOWAIT'):
        raise Refusal('Linux waitid/WNOWAIT required')
    if children():
        raise Refusal('dedicated monitor must start with no existing children')
    libc = ctypes.CDLL(None, use_errno=True)
    current = ctypes.c_int()
    if libc.prctl(37, ctypes.byref(current), 0, 0, 0) != 0:
        raise Refusal('GET_CHILD_SUBREAPER failed')
    if current.value != 0:
        raise Refusal('dedicated monitor unexpectedly already a subreaper')
    if libc.prctl(36, 1, 0, 0, 0) != 0:
        raise Refusal('SET_CHILD_SUBREAPER failed')
    if libc.prctl(37, ctypes.byref(current), 0, 0, 0) != 0 or current.value != 1:
        raise Refusal('subreaper readback failed')
    return {'enabled': True, 'process_local': True, 'initial_children': []}

def map_path(config):
    if 'map_relative_path' not in config:
        return None
    value = config['map_relative_path']
    if (not isinstance(value, str) or not value or len(value) > 4096
            or any(ord(c) < 32 for c in value) or any(c in value for c in '\\*?[]')
            or PurePosixPath(value).is_absolute()
            or str(PurePosixPath(value)) != value
            or '..' in PurePosixPath(value).parts
            or PurePosixPath(value).name != 'whole-static.map'):
        raise Refusal('map_relative_path must be one exact canonical relative whole-static.map path')
    return value

def watched(root, excluded, records, limit, map_relative_path=None, map_limit=MAX_MAP):
    pending = [root]; count = 0
    while pending:
        directory = pending.pop()
        with os.scandir(directory) as entries:
            for entry in entries:
                count += 1
                if count > MAX_ENTRIES:
                    return 'watch_entry_limit'
                path = Path(entry.path)
                if path == excluded:
                    continue
                if entry.is_symlink():
                    return 'unsupported_watch_symlink'
                if entry.is_dir(follow_symlinks=False):
                    if str(path.relative_to(root)) == map_relative_path:
                        return 'unsupported_watch_file'
                    pending.append(path)
                elif entry.name in ('native-build.log', 'whole-static.map'):
                    info = entry.stat(follow_symlinks=False)
                    if not stat.S_ISREG(info.st_mode):
                        return 'unsupported_watch_file'
                    relative = str(path.relative_to(root))
                    if relative not in records and len(records) >= MAX_ENTRIES:
                        return 'watch_record_limit'
                    is_map = relative == map_relative_path
                    cap = map_limit if is_map else limit
                    old = records.setdefault(relative, {'relative_path': relative, 'observed_peak_bytes': 0,
                                                        'file_class': 'link_map' if is_map else 'sidefile_log',
                                                        'limit_bytes': cap})
                    old['observed_peak_bytes'] = max(old['observed_peak_bytes'], info.st_size)
                    if info.st_size > cap:
                        return 'watched_file_limit'
    return None

def reap_owned(child, record, checkpoint):
    # The leader has never been reaped. Its PID pins this owned PGID until this
    # one group signal; never signal that numeric group again after reaping it.
    for number in (signal.SIGINT, signal.SIGTERM):
        signal.signal(number, signal.SIG_IGN)
    try:
        os.killpg(child.pid, signal.SIGKILL)
        record['group_sigkill_sent'] = True
    except ProcessLookupError:
        record['group_sigkill_sent'] = False
    last_checkpoint = 0
    while True:
        owned = children()
        record['remaining_children'] = owned
        if not owned:
            record['all_children_reaped'] = True
            record['reaping_pending'] = False
            return
        for pid in owned:
            # Every direct/adopted child belongs to this dedicated monitor's
            # single spawn. No unrelated child/group can enter this set.
            try:
                if os.getpgid(pid) != child.pid:
                    record['escaped_group_detected'] = True
                os.kill(pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        progress = False
        while True:
            try:
                pid, status = os.waitpid(-1, os.WNOHANG)
            except ChildProcessError:
                break
            if pid == 0:
                break
            progress = True
            code = os.waitstatus_to_exitcode(status)
            record['reaped_count'] += 1
            if len(record['reaped']) < MAX_ENTRIES:
                record['reaped'].append({'pid': pid, 'wait_status': status, 'exit_code': code})
            else:
                record['reaped_records_truncated'] = True
            if pid == child.pid:
                child.returncode = code
        if not progress:
            now = time.monotonic()
            if now - last_checkpoint >= 1:
                # SIGKILL cannot guarantee finite kernel termination. Keep this
                # monitor alive owning/reaping; persist pending, never claim done.
                record['reaping_pending'] = True
                record['pending_observed'] = True
                try:
                    checkpoint()
                except Exception as error:
                    record['checkpoint_error'] = str(error)[:1024]
                last_checkpoint = now
            time.sleep(INTERVAL)

def read_config(config_path):
    # Bound allocation before decoding or parsing, including the oversize sentinel.
    with open(config_path, 'rb') as stream:
        raw = stream.read(MAX_CONFIG + 1)
    if len(raw) > MAX_CONFIG:
        raise Refusal('config exceeds 256 KiB')
    return raw

def run(config_path):
    raw = read_config(config_path)
    config = json.loads(raw)
    parent = private_directory(config['output_parent'])
    directory = Path(tempfile.mkdtemp(prefix='build-run-', dir=parent))
    output_path = directory / 'output.log'; receipt = directory / 'receipt.json'
    record = {'schema': 2, 'kind': 'trusted-build-tool-observation',
              'config_sha256': hashlib.sha256(raw).hexdigest(),
              'monitor': digest_file(Path(__file__).resolve(), MAX_CONFIG),
              'run_directory': str(directory), 'output_path': str(output_path),
              'argv': config.get('argv'), 'child_pid': None, 'child_exit': None,
              'reason': 'setup_refusal', 'error': None, 'sample_interval_seconds': INTERVAL,
              'hard_storage_containment': False, 'observed_output_bytes': 0,
              'retained_output_bytes': 0, 'output_truncated': False, 'watched_files': [],
              'inputs': [], 'artifacts': [], 'cleanup': {
                  'all_children_reaped': True, 'remaining_children': [], 'reaped': [],
                  'reaped_count': 0, 'reaped_records_truncated': False,
                  'group_sigkill_sent': False, 'escaped_group_detected': False,
                  'reaping_pending': False, 'pending_observed': False}}
    def checkpoint():
        encoded = (json.dumps(record, indent=2) + '\n').encode()
        if len(encoded) > MAX_RECORD:
            raise Refusal('receipt exceeds 4 MiB')
        temporary = directory / 'receipt.pending'
        temporary.write_bytes(encoded); temporary.replace(receipt)
    child = None; selector = None; output = output_path.open('wb')
    observed_hash = hashlib.sha256(); watched_records = {}
    start = time.monotonic()
    def consume():
        if child is None or child.stdout is None:
            return
        while True:
            try:
                block = os.read(child.stdout.fileno(), 65536)
            except BlockingIOError:
                return
            if not block:
                return
            observed_hash.update(block); record['observed_output_bytes'] += len(block)
            remaining = max(0, limits['output_bytes'] - record['retained_output_bytes'])
            retained = block[:remaining]; output.write(retained)
            record['retained_output_bytes'] += len(retained)
            record['output_truncated'] |= len(retained) != len(block)
            if record['observed_output_bytes'] > limits['output_bytes']:
                return
    limits = {'deadline_seconds': DEADLINE, 'output_bytes': MAX_LOG, 'sidefile_bytes': MAX_LOG, 'map_bytes': MAX_MAP}
    selected_map = None
    try:
        known = {'argv','executable_pin','cwd','output_parent','watch_root','environment','self_test_limits','input_files','artifact_files','map_relative_path'}
        if set(config) - known:
            raise Refusal('unknown monitor configuration field')
        selected_map = map_path(config)
        record['map_relative_path'] = selected_map
        if config.get('self_test_limits') is not None:
            override = config['self_test_limits']
            required = {'deadline_seconds', 'output_bytes', 'sidefile_bytes'}
            if not isinstance(override, dict) or not required <= set(override) or set(override) - required - {'map_bytes'}:
                raise Refusal('invalid self-test limit schema')
            if 'map_bytes' in override and selected_map is None:
                raise Refusal('map self-test cap requires an exact map_relative_path')
            for key, upper in [('deadline_seconds', DEADLINE), ('output_bytes', MAX_LOG), ('sidefile_bytes', MAX_LOG), ('map_bytes', MAX_MAP)]:
                if key not in override:
                    continue
                value = override[key]
                if isinstance(value, bool) or not isinstance(value, (int, float)) or not math.isfinite(value) or value <= 0 or value > upper:
                    raise Refusal('self-test bounds may only tighten contract bounds')
                if key != 'deadline_seconds' and not isinstance(value, int):
                    raise Refusal('byte bounds must be integers')
                limits[key] = value
        record['limits'] = limits
        watch_root = private_directory(config['watch_root'])
        if watch_root != parent:
            raise Refusal('watch root must be the private experiment/output parent')
        cwd = Path(config['cwd'])
        if not cwd.is_absolute() or not cwd.is_dir():
            raise Refusal('missing or nonabsolute command cwd')
        argv = config['argv']; environment = config['environment']
        if not isinstance(argv, list) or not argv or not all(isinstance(x, str) and '\0' not in x for x in argv):
            raise Refusal('argv must be exact string array')
        if not Path(argv[0]).is_absolute() or str(Path(argv[0]).resolve()) != argv[0]:
            raise Refusal('executable must be canonical absolute path')
        if not isinstance(environment, dict) or not all(isinstance(k, str) and isinstance(v, str) and '\0' not in k+v and '=' not in k for k,v in environment.items()):
            raise Refusal('environment must be an explicit exact string map')
        record['environment_keys'] = sorted(environment)
        pin = config['executable_pin']
        expected_size = pin['size']
        if isinstance(expected_size, bool) or not isinstance(expected_size, int) or expected_size <= 0:
            raise Refusal('executable pin requires an explicit positive expected size')
        record['executable'] = digest_file(argv[0], expected_size)
        if (record['executable']['size_before'] != expected_size
                or record['executable']['size_after'] != expected_size
                or record['executable']['sha256'] != pin['sha256']):
            raise Refusal('executable pin mismatch')
        if len(config.get('input_files', [])) + len(config.get('artifact_files', [])) > MAX_ENTRIES:
            raise Refusal('input/artifact record count exceeds 4096')
        for item in config.get('input_files', []):
            expected = item['size']
            if isinstance(expected, bool) or not isinstance(expected, int) or expected < 0:
                raise Refusal('input pin requires exact nonnegative expected size')
            observation = digest_file(item['path'], expected)
            if observation['size_before'] != expected or observation['size_after'] != expected or observation['sha256'] != item['sha256']:
                raise Refusal('input pin mismatch: ' + item['path'])
            record['inputs'].append(observation)
        record['subreaper'] = subreaper()
        def interrupted(number, frame):
            raise Interrupted('monitor received signal ' + str(number))
        signal.signal(signal.SIGINT, interrupted); signal.signal(signal.SIGTERM, interrupted)
        child = subprocess.Popen(argv, cwd=cwd, env=environment, stdin=subprocess.DEVNULL,
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                 start_new_session=True, close_fds=True)
        record['child_pid'] = child.pid
        record['cleanup']['all_children_reaped'] = False
        record['child_pgid'] = os.getpgid(child.pid)
        record['child_session'] = os.getsid(child.pid)
        if record['child_pgid'] != child.pid or record['child_session'] != child.pid:
            raise Refusal('owned child did not establish its private session/process group')
        os.set_blocking(child.stdout.fileno(), False)
        selector = selectors.DefaultSelector(); selector.register(child.stdout, selectors.EVENT_READ)
        record['reason'] = 'running'; checkpoint()
        while True:
            selector.select(INTERVAL); consume()
            if record['observed_output_bytes'] > limits['output_bytes']:
                record['reason'] = 'output_limit'; break
            failure = watched(watch_root, directory, watched_records, limits['sidefile_bytes'], selected_map, limits['map_bytes'])
            if failure:
                record['reason'] = failure; break
            if time.monotonic() - start >= limits['deadline_seconds']:
                record['reason'] = 'deadline'; break
            status = os.waitid(os.P_PID, child.pid, os.WEXITED | os.WNOHANG | os.WNOWAIT)
            if status is not None:
                record['reason'] = 'leader_exit_with_descendants' if any(pid != child.pid for pid in children()) else 'exit'
                break
    except BaseException as error:
        record['reason'] = 'setup_refusal' if child is None else 'monitor_error'
        record['error'] = (type(error).__name__ + ': ' + str(error))[:1024]
    finally:
        if child is not None:
            reap_owned(child, record['cleanup'], checkpoint)
            # Also covers an exception before set_blocking/register succeeded.
            os.set_blocking(child.stdout.fileno(), False)
            while True:
                previous = record['observed_output_bytes']; consume()
                if record['observed_output_bytes'] == previous:
                    break
            record['child_exit'] = child.returncode
            child.stdout.close()
            # The child can write after the last loop sample but before waitid.
            # All descendants are now reaped: drain/sample the settled outputs.
            final_failures = []
            if record['observed_output_bytes'] > limits['output_bytes']:
                final_failures.append('output_limit')
            try:
                final_watch = watched(watch_root, directory, watched_records, limits['sidefile_bytes'], selected_map, limits['map_bytes'])
                if final_watch:
                    final_failures.append(final_watch)
            except (OSError, Refusal) as error:
                final_failures.append('final_watch_error')
                record['final_watch_error'] = str(error)[:1024]
            record['final_limit_failures'] = final_failures
            # Do not replace an earlier deadline/setup/group/limit refusal.
            if record['reason'] == 'exit' and final_failures:
                record['reason'] = final_failures[0]
        if selector is not None:
            selector.close()
        output.close()
        record['elapsed_seconds'] = time.monotonic() - start
        record['observed_output_sha256'] = observed_hash.hexdigest()
        record['output_file'] = digest_file(output_path, MAX_LOG)
        for relative, observation in watched_records.items():
            try:
                retained_path = directory / ('watched-' + str(len(record['watched_files'])) + '.log')
                observation.update(digest_file(parent / relative, observation['limit_bytes'], prefix=True, copy_to=retained_path))
                observation['retained_path'] = str(retained_path)
            except (OSError, Refusal) as error:
                observation['final_hash_error'] = str(error)[:1024]
            record['watched_files'].append(observation)
        for path in config.get('artifact_files', []):
            try:
                candidate = Path(path)
                if not candidate.is_absolute() or not candidate.is_relative_to(parent):
                    raise Refusal('artifact must be inside private experiment directory')
                record['artifacts'].append(digest_file(candidate, MAX_IMAGE))
            except (OSError, Refusal) as error:
                record['artifacts'].append({'path': path, 'error': str(error)[:1024]})
                if record['reason'] == 'exit': record['reason'] = 'artifact_refusal'
        if record['cleanup']['escaped_group_detected']:
            record['reason_before_group_refusal'] = record['reason']; record['reason'] = 'unsupported_group_escape'
        checkpoint()
    print(json.dumps({'receipt': str(receipt), 'reason': record['reason']}), flush=True)
    if child is None: return 78
    return 0 if record['reason'] == 'exit' and record['child_exit'] == 0 else 1

if __name__ == '__main__':
    try:
        if len(sys.argv) != 2: raise Refusal('usage: build_monitor.py CONFIG.json')
        raise SystemExit(run(sys.argv[1]))
    except (Refusal, OSError, ValueError, KeyError) as error:
        print(json.dumps({'receipt': None, 'reason': 'pre_run_refusal', 'error': str(error)[:1024]}), flush=True)
        raise SystemExit(78)
