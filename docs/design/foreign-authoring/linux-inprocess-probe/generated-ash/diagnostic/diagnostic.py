#!/usr/bin/python3
"""Trusted diagnostic only. No strict static-closure or product authority."""
import argparse
import ctypes
import errno
import fcntl
import hashlib
import json
import os
from pathlib import Path
import selectors
import signal
import stat
import struct
import tempfile
import time

ROOT = Path(__file__).resolve().parent
CONTROL_LIMIT = 256 * 1024
IMAGE_LIMIT = 96 * 1024 * 1024
OUTPUT_LIMIT = 16 * 1024
DEADLINE = 30
CHUNK = 64 * 1024
IMAGE_HASH = "45417a6db6fc41bd17b372b47423e06c57ecf55973a0a848c51a14f456537405"
RECEIPT_HASH = "4de5fe79b42c88fd3dc269a1438a0d5c24f190f199021c76ea3337178ff77d4c"
IMAGE_SIZE = 70880176
REPLACEMENT_HASH = "c338f484f853f1f8706ace538269a68c51cd5625c6cfc189f36211e534b76798"
SEALS = fcntl.F_SEAL_WRITE | fcntl.F_SEAL_GROW | fcntl.F_SEAL_SHRINK | fcntl.F_SEAL_SEAL


class Refused(Exception):
    pass


def sha(data):
    return hashlib.sha256(data).hexdigest()


def open_regular(path, cap):
    fd = os.open(path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW | os.O_NONBLOCK)
    try:
        info = os.fstat(fd)
        if not stat.S_ISREG(info.st_mode) or not 0 <= info.st_size <= cap:
            raise Refused("not a bounded regular file")
        return fd
    except BaseException:
        os.close(fd)
        raise


def bounded_read(path, cap):
    fd = open_regular(path, cap)
    try:
        parts = bytearray()
        while True:
            chunk = os.read(fd, min(CHUNK, cap - len(parts) + 1))
            if not chunk:
                return bytes(parts)
            if len(parts) + len(chunk) > cap:
                raise Refused("input grew beyond bound")
            parts.extend(chunk)
    finally:
        os.close(fd)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise Refused("duplicate JSON key")
        result[key] = value
    return result


def decode(data):
    if len(data) > CONTROL_LIMIT:
        raise Refused("control data bound")
    return json.loads(data, object_pairs_hook=unique_object,
                      parse_constant=lambda value: (_ for _ in ()).throw(Refused("nonfinite JSON")))


def load_policy(data):
    policy = decode(data)
    if policy.get("version") != 1 or policy.get("kind") != "trusted-generated-static-diagnostic":
        raise Refused("unsupported diagnostic policy")
    if policy["limits"] != {"image_bytes": IMAGE_LIMIT, "receipt_bytes": CONTROL_LIMIT,
                            "program_headers": 64, "combined_output_bytes": OUTPUT_LIMIT,
                            "child_deadline_seconds": DEADLINE}:
        raise Refused("unexpected diagnostic bounds")
    if (policy["image"]["sha256"] != IMAGE_HASH or policy["image"]["size_bytes"] != IMAGE_SIZE
            or policy["receipt"]["sha256"] != RECEIPT_HASH
            or policy["replacement"]["sha256"] != REPLACEMENT_HASH
            or policy["replacement"]["size_bytes"] != 821296
            or policy["argv"] != ["ash-generated-scalar-diagnostic"] or policy["environment"] != {}
            or policy["memfd"] != {"create_flags": 19, "required_seals": 15, "mode_octal": "0500"}
            or policy["strict_no_runtime_loading_profile_accepted"] is not False
            or policy["architecture_accepted"] is not False
            or policy["checked_runtime_authority"] is not False):
        raise Refused("policy scope mismatch")
    return policy


def authorize(policy_bytes, receipt_bytes, approval_bytes, harness_bytes):
    policy = load_policy(policy_bytes)
    receipt = decode(receipt_bytes)
    if receipt.get("version") != 1:
        raise Refused("unsupported receipt version")
    if approval_bytes is None:
        raise Refused("exact diagnostic approval absent")
    approval = decode(approval_bytes)
    required = {"version": 1, "authorized": True,
                "kind": "trusted-generated-static-diagnostic",
                "policy_sha256": sha(policy_bytes), "harness_sha256": sha(harness_bytes),
                "receipt_sha256": RECEIPT_HASH, "image_sha256": IMAGE_HASH,
                "image_size_bytes": IMAGE_SIZE, "replacement_sha256": REPLACEMENT_HASH,
                "known_runtime_loading_premise_accepted": True}
    if any(approval.get(key) != value for key, value in required.items()):
        raise Refused("diagnostic approval mismatch")
    if sha(receipt_bytes) != RECEIPT_HASH:
        raise Refused("receipt digest mismatch")
    if (receipt.get("kind") != "experimental-existing-profile-generated-ash-packaging"
            or receipt.get("source_commit") != policy["source_commit"]
            or receipt["artifacts"]["static-host"] != {"sha256": IMAGE_HASH, "size_bytes": IMAGE_SIZE}):
        raise Refused("receipt image association mismatch")
    return policy


def bounded_copy(source, destination, expected_size, expected_hash):
    source_fd = open_regular(source, IMAGE_LIMIT)
    destination_fd = -1
    try:
        if os.fstat(source_fd).st_size != expected_size:
            raise Refused("candidate size mismatch")
        destination_fd = os.open(destination, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC, 0o600)
        count = 0
        digest = hashlib.sha256()
        while True:
            chunk = os.read(source_fd, min(CHUNK, IMAGE_LIMIT - count + 1))
            if not chunk:
                break
            count += len(chunk)
            if count > IMAGE_LIMIT or count > expected_size:
                raise Refused("candidate copy bound")
            digest.update(chunk)
            view = memoryview(chunk)
            while view:
                written = os.write(destination_fd, view)
                if written <= 0:
                    raise Refused("short candidate copy")
                view = view[written:]
        if count != expected_size or digest.hexdigest() != expected_hash:
            raise Refused("candidate copy digest mismatch")
    finally:
        os.close(source_fd)
        if destination_fd >= 0:
            os.close(destination_fd)


def hash_fd(fd):
    size = os.fstat(fd).st_size
    if not 0 <= size <= IMAGE_LIMIT:
        raise Refused("pinned object size bound")
    digest = hashlib.sha256()
    offset = 0
    while offset < size:
        chunk = os.pread(fd, min(CHUNK, size - offset), offset)
        if not chunk:
            raise Refused("short pinned object read")
        offset += len(chunk)
        digest.update(chunk)
    return digest.hexdigest()


def inspect_elf(fd):
    header = os.pread(fd, 64, 0)
    if len(header) != 64:
        raise Refused("short ELF")
    fields = struct.unpack("<16sHHIQQQIHHHHHH", header)
    ident, kind, machine, version, entry, offset, _, _, size, stride, count, *_ = fields
    if ident[:7] != b"\x7fELF\x02\x01\x01" or (kind, machine, version, size) != (2, 62, 1, 64):
        raise Refused("unsupported ELF target")
    length = os.fstat(fd).st_size
    if stride != 56 or not 0 < count <= 64 or offset + count * stride > length:
        raise Refused("ELF program-header bound")
    types = []
    for index in range(count):
        raw = os.pread(fd, stride, offset + index * stride)
        if len(raw) != stride:
            raise Refused("short program header")
        ptype, flags, position, virtual, physical, filesz, memsz, alignment = struct.unpack("<IIQQQQQQ", raw)
        if position + filesz > length or filesz > memsz and ptype == 1:
            raise Refused("invalid segment bounds")
        types.append(ptype)
    if 3 in types or 2 in types or 1 not in types:
        raise Refused("unexpected structural ELF metadata")
    return {"type": "ET_EXEC", "machine": "EM_X86_64", "program_headers": count,
            "pt_interp": False, "pt_dynamic": False,
            "runtime_loading_excluded": False}


def pin_image(path):
    source_fd = open_regular(path, IMAGE_LIMIT)
    pinned = -1
    try:
        if os.fstat(source_fd).st_size != IMAGE_SIZE:
            raise Refused("image size mismatch")
        pinned = os.memfd_create("ash-generated-scalar-diagnostic", 19)
        count = 0
        while True:
            chunk = os.read(source_fd, min(CHUNK, IMAGE_LIMIT - count + 1))
            if not chunk:
                break
            count += len(chunk)
            if count > IMAGE_SIZE:
                raise Refused("image copy bound")
            view = memoryview(chunk)
            while view:
                written = os.write(pinned, view)
                if written <= 0:
                    raise Refused("short memfd write")
                view = view[written:]
        if count != IMAGE_SIZE:
            raise Refused("short image copy")
        os.fchmod(pinned, 0o500)
        fcntl.fcntl(pinned, fcntl.F_ADD_SEALS, SEALS)
        if fcntl.fcntl(pinned, fcntl.F_GET_SEALS) & SEALS != SEALS or hash_fd(pinned) != IMAGE_HASH:
            raise Refused("final sealed image mismatch")
        facts = inspect_elf(pinned)
        result, pinned = pinned, -1
        return result, facts
    finally:
        os.close(source_fd)
        if pinned >= 0:
            os.close(pinned)


def record_state(path, state):
    data = json.dumps(state, sort_keys=True, indent=2).encode() + b"\n"
    if len(data) > CONTROL_LIMIT:
        raise Refused("lifecycle record bound")
    temporary = path.with_suffix(".tmp")
    fd = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_TRUNC | os.O_CLOEXEC, 0o600)
    try:
        view = memoryview(data)
        while view:
            written = os.write(fd, view)
            if written <= 0:
                raise Refused("short lifecycle write")
            view = view[written:]
    finally:
        os.close(fd)
    os.replace(temporary, path)


def child_exec(image_fd, write_fd, null_fd, close_range):
    try:
        os.dup2(image_fd, 3, inheritable=False)
        os.dup2(null_fd, 0, inheritable=True)
        os.dup2(write_fd, 1, inheritable=True)
        os.dup2(write_fd, 2, inheritable=True)
        if close_range(4, 0xffffffff, 0) != 0:
            raise OSError(ctypes.get_errno(), "close_range")
        os.execve(3, ["ash-generated-scalar-diagnostic"], {})
        raise Refused("exec unexpectedly returned")
    except BaseException as error:
        message = ("trusted child setup/exec refusal errno=" + str(getattr(error, "errno", 0)) + "\n").encode()[:256]
        for target in [write_fd, 2]:
            try:
                os.write(target, message)
                break
            except OSError:
                pass
        os._exit(125)


def execute_once(image_fd, lifecycle):
    state = {"stage": "pre-fork", "child_created": False, "reaped": False}
    owned = set()
    selector = None
    pid = None
    waited = False
    output = bytearray()
    failure = None
    exit_code = None
    started = None
    try:
        if signal.getsignal(signal.SIGCHLD) == signal.SIG_IGN:
            raise Refused("SIGCHLD ignored; reaping association unavailable")
        libc = ctypes.CDLL(None, use_errno=True)
        close_range = getattr(libc, "close_range", None)
        if close_range is None:
            raise Refused("close_range unavailable")
        close_range.argtypes = [ctypes.c_uint, ctypes.c_uint, ctypes.c_int]
        close_range.restype = ctypes.c_int

        def keep_high(fd, close_original=True):
            duplicate = fcntl.fcntl(fd, fcntl.F_DUPFD_CLOEXEC, 10)
            owned.add(duplicate)
            if close_original:
                os.close(fd)
            return duplicate

        exec_fd = keep_high(image_fd, False)
        raw_read, raw_write = os.pipe2(os.O_CLOEXEC)
        # Raw descriptors become owned immediately; every later failure closes them.
        owned.update([raw_read, raw_write])
        read_fd = keep_high(raw_read)
        owned.discard(raw_read)
        write_fd = keep_high(raw_write)
        owned.discard(raw_write)
        raw_null = os.open("/dev/null", os.O_RDONLY | os.O_CLOEXEC)
        owned.add(raw_null)
        null_fd = keep_high(raw_null)
        owned.discard(raw_null)
        os.set_blocking(read_fd, False)
        selector = selectors.DefaultSelector()
        selector.register(read_fd, selectors.EVENT_READ)
        record_state(lifecycle, state)
        started = time.monotonic()
        pid = os.fork()
        if pid == 0:
            child_exec(exec_fd, write_fd, null_fd, close_range)
        # All post-fork parent setup remains in this try/finally cleanup region.
        state.update(stage="child-created", child_created=True, pid=pid)
        record_state(lifecycle, state)
        for fd in [write_fd, null_fd, exec_fd]:
            os.close(fd)
            owned.remove(fd)
        eof = False
        while not waited or not eof:
            if time.monotonic() - started >= DEADLINE:
                raise Refused("child deadline reached")
            for key, _ in selector.select(0.05):
                chunk = os.read(key.fd, min(4096, OUTPUT_LIMIT - len(output) + 1))
                if not chunk:
                    selector.unregister(key.fd)
                    eof = True
                elif len(output) + len(chunk) > OUTPUT_LIMIT:
                    output.extend(chunk[:OUTPUT_LIMIT - len(output)])
                    raise Refused("combined child output bound")
                else:
                    output.extend(chunk)
            if not waited:
                done, status = os.waitpid(pid, os.WNOHANG)
                if done:
                    waited = True
                    exit_code = os.waitstatus_to_exitcode(status)
                    state.update(stage="child-reaped", reaped=True, exit_code=exit_code)
                    record_state(lifecycle, state)
    except BaseException as error:
        failure = type(error).__name__ + ": " + str(error)[:1024]
    finally:
        if pid is not None and pid > 0:
            state["child_created"] = True
        if pid is not None and pid > 0 and not waited:
            state.update(stage="termination-requested-reaping-pending", pid=pid)
            try:
                record_state(lifecycle, state)
            except BaseException:
                pass
            try:
                os.kill(pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            except BaseException as error:
                failure = (failure or "") + "; termination request: " + str(error)[:256]
            # Kernel delays can delay reaping; pending state precedes this wait.
            while True:
                try:
                    done, status = os.waitpid(pid, 0)
                    waited = done == pid
                    exit_code = os.waitstatus_to_exitcode(status)
                    break
                except InterruptedError:
                    continue
                except BaseException as error:
                    failure = (failure or "") + "; reaping: " + str(error)[:512]
                    break
            state.update(stage="cleanup-complete" if waited else "reaping-unconfirmed",
                         reaped=waited, exit_code=exit_code)
        if selector is not None:
            try:
                selector.close()
            except BaseException as error:
                failure = (failure or "") + "; selector cleanup: " + str(error)[:256]
        for fd in owned:
            try:
                os.close(fd)
            except OSError:
                pass
        state.update(failure=failure, output_utf8=output.decode("utf-8", "replace"),
                     output_bytes=len(output), elapsed_seconds=None if started is None else round(time.monotonic() - started, 6))
        try:
            record_state(lifecycle, state)
        except BaseException as error:
            state["failure"] = (failure or "") + "; final lifecycle write: " + str(error)[:256]
    return state


def sealed_mutation_refusals(fd):
    outcomes = {}
    for name, operation in [("write", lambda: os.pwrite(fd, b"X", 0)),
                            ("shrink", lambda: os.ftruncate(fd, IMAGE_SIZE - 1)),
                            ("grow", lambda: os.ftruncate(fd, IMAGE_SIZE + 1))]:
        try:
            operation()
        except OSError as error:
            if error.errno != errno.EPERM:
                raise Refused("unexpected sealed mutation errno") from error
            outcomes[name] = {"errno": error.errno, "refused": True}
        else:
            raise Refused("sealed mutation unexpectedly succeeded")
    if hash_fd(fd) != IMAGE_HASH or os.fstat(fd).st_size != IMAGE_SIZE:
        raise Refused("sealed mutation comparison changed image")
    return outcomes


def expected_refusal(operation):
    try:
        value = operation()
    except Refused as error:
        return {"reason": str(error), "child_created": False}
    if isinstance(value, tuple) and isinstance(value[0], int):
        os.close(value[0])
    raise Refused("negative comparison unexpectedly accepted")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--approval", type=Path, required=True)
    args = parser.parse_args()
    case = Path(tempfile.mkdtemp(prefix="case-", dir=ROOT))
    result = {"kind": "trusted-generated-static-diagnostic", "strict_profile_success": False,
              "architecture_accepted": False, "diagnostic_success": False, "child_created": False}
    fd = -1
    try:
        policy_bytes = bounded_read(ROOT / "policy.json", CONTROL_LIMIT)
        policy = load_policy(policy_bytes)
        receipt_bytes = bounded_read(policy["receipt"]["path"], CONTROL_LIMIT)
        approval_bytes = bounded_read(args.approval, CONTROL_LIMIT)
        harness_bytes = bounded_read(__file__, CONTROL_LIMIT)
        authorize(policy_bytes, receipt_bytes, approval_bytes, harness_bytes)
        result.update(policy_sha256=sha(policy_bytes), receipt_sha256=sha(receipt_bytes),
                      approval_sha256=sha(approval_bytes), harness_sha256=sha(harness_bytes),
                      trusted_runtime_loading_premise=policy["diagnostic_premises"])
        negatives = {"missing_approval": expected_refusal(lambda: authorize(policy_bytes, receipt_bytes, None, harness_bytes))}
        for field, value in [("receipt_sha256", "0" * 64), ("image_sha256", "0" * 64)]:
            changed = decode(approval_bytes)
            changed[field] = value
            negatives[field] = expected_refusal(lambda changed=changed: authorize(policy_bytes, receipt_bytes, json.dumps(changed).encode(), harness_bytes))
        changed_receipt = decode(receipt_bytes)
        changed_receipt["version"] = 2
        negatives["unsupported_receipt"] = expected_refusal(lambda: authorize(policy_bytes, json.dumps(changed_receipt).encode(), approval_bytes, harness_bytes))
        changed_receipt["version"] = 1
        changed_receipt["status"] = "changed"
        negatives["changed_receipt"] = expected_refusal(lambda: authorize(policy_bytes, json.dumps(changed_receipt).encode(), approval_bytes, harness_bytes))
        candidate = case / "candidate"
        bounded_copy(policy["image"]["path"], candidate, IMAGE_SIZE, IMAGE_HASH)
        fd, facts = pin_image(candidate)
        result["elf"] = facts
        result["sealed_object"] = {"size_bytes": os.fstat(fd).st_size, "sha256": hash_fd(fd),
                                   "seals": fcntl.fcntl(fd, fcntl.F_GET_SEALS), "mode_octal": oct(stat.S_IMODE(os.fstat(fd).st_mode)), "create_flags": 19}
        with open(candidate, "r+b", buffering=0) as stream:
            stream.seek(IMAGE_SIZE - 1)
            old = stream.read(1)
            stream.seek(IMAGE_SIZE - 1)
            stream.write(bytes([old[0] ^ 1]))
        negatives["changed_image"] = expected_refusal(lambda: pin_image(candidate))
        replacement = case / "replacement"
        bounded_copy(policy["replacement"]["path"], replacement,
                     policy["replacement"]["size_bytes"], REPLACEMENT_HASH)
        os.replace(replacement, candidate)
        negatives["replacement_before_pin"] = expected_refusal(lambda: pin_image(candidate))
        result["sealed_mutation_refusals"] = sealed_mutation_refusals(fd)
        result["pre_execution_negatives"] = negatives
        result["candidate_path_now_sha256"] = REPLACEMENT_HASH
        if hash_fd(fd) != IMAGE_HASH or fcntl.fcntl(fd, fcntl.F_GET_SEALS) & SEALS != SEALS:
            raise Refused("pinned object changed before child creation")
        child = execute_once(fd, case / "lifecycle.json")
        result["child"] = child
        result["child_created"] = child["child_created"]
        result["diagnostic_success"] = (child["reaped"] and child["failure"] is None
                                        and child["exit_code"] == 0
                                        and child["output_utf8"] == policy["expected_output_utf8"])
    except BaseException as error:
        result["failure"] = type(error).__name__ + ": " + str(error)[:2048]
    finally:
        if fd >= 0:
            os.close(fd)
        if not result["child_created"] or result.get("child", {}).get("reaped"):
            for name in ["candidate", "replacement"]:
                (case / name).unlink(missing_ok=True)
        record_state(case / "result.json", result)
        print(json.dumps({"case": str(case), **result}, sort_keys=True, indent=2))
    return 0 if result["diagnostic_success"] else 78


if __name__ == "__main__":
    raise SystemExit(main())
