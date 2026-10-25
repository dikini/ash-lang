"""Read-only GDB probe; source only, not assigned for execution.

One exact two-owner startup; only final-Core capture inside restore_effect.
No inferior calls, source changes, meter writes, retries or runtime invocation.
"""
import gdb
import json
from pathlib import Path

TEST = "ash::build::image::source_resource_image::tests::imported_buffer_two_owner_discard_has_normal_startup_budget"
MAX_ROWS = 80
MAX_FRAMES = 24
sequence = 0
armed = False
restoring = False
window = 0
restore_count = 0
failed = False
counts = {}


def emit(row):
    global sequence
    sequence += 1
    if sequence > MAX_ROWS:
        print("CODE_INVENTORY " + json.dumps({"error": "row bound exceeded"}))
        gdb.execute("quit 77")
        return
    print("CODE_INVENTORY " + json.dumps(dict(sequence=sequence, **row), sort_keys=True))


def snapshot(ptr):
    obj = ptr.dereference()
    return {"meter": int(ptr), "used": int(obj["used"]), "limit": int(obj["limit"])}


def final_core_ancestor():
    frame = gdb.newest_frame()
    for _ in range(MAX_FRAMES):
        if frame is None:
            return False
        if (frame.name() or "").startswith("ash::core::validate::validate_effect_modules_with_work"):
            return True
        frame = frame.older()
    raise RuntimeError("ancestor bound exceeded")


class End(gdb.FinishBreakpoint):
    def __init__(self, frame, meter, row, kind):
        super().__init__(frame, internal=True)
        self.meter, self.row, self.kind = meter, row, kind

    def stop(self):
        global restoring, window
        try:
            after = snapshot(self.meter)
            emit(dict(self.row, event="return", after=after["used"],
                      inclusive=after["used"] - self.row["used"]))
        except Exception as error:
            emit({"event": "observer_error", "kind": self.kind, "error": str(error)[:400]})
        if self.kind == "root_gate":
            window -= 1
        if self.kind == "restore":
            restoring = False
        return False


class Arm(gdb.Breakpoint):
    def stop(self):
        global armed
        armed = True
        emit({"event": "exact_test", "name": TEST})
        return False


class Start(gdb.Breakpoint):
    def __init__(self, symbol, kind, graph_expr=None):
        super().__init__(symbol, internal=True)
        self.kind, self.graph_expr = kind, graph_expr

    def stop(self):
        global restoring, restore_count, window
        if not armed:
            return False
        if self.kind == "restore":
            restore_count += 1
            if restore_count > 1:
                emit({"event": "observer_error", "error": "second restore not covered"})
                gdb.execute("quit 77")
                return False
            restoring = True
        elif not restoring:
            return False
        if self.kind == "root_gate":
            try:
                if not final_core_ancestor():
                    return False
            except Exception as error:
                emit({"event": "observer_error", "error": str(error)[:400]})
                return False
            window += 1
        elif self.kind != "restore" and not window:
            return False
        try:
            meter = gdb.parse_and_eval("work" if self.kind == "restore" else "budget")
            row = dict(snapshot(meter), kind=self.kind)
            frame = gdb.newest_frame()
            row["caller"] = (frame.older().name() or "")[:300] if frame.older() else None
            if self.graph_expr:
                graph = gdb.parse_and_eval(self.graph_expr)
                code_len = int(graph.dereference()["code"]["len"])
                if not 0 <= code_len <= 65536:
                    raise RuntimeError("code length outside probe bound")
                row.update(graph=int(graph), code_len=code_len)
            if self.kind == "candidates":
                obj = gdb.parse_and_eval("self").dereference()
                row.update(value_analysis=int(gdb.parse_and_eval("self")),
                           value_graph=int(obj["graph"]), slots=int(obj["slots"]["len"]))
            counts[self.kind] = counts.get(self.kind, 0) + 1
            emit(dict(row, event="entry"))
            End(frame, meter, row, self.kind)
        except Exception as error:
            emit({"event": "observer_error", "kind": self.kind, "error": str(error)[:400]})
        return False


Arm(TEST, internal=True)
Start("ash::build::image::PureImage::restore_effect", "restore")
Start("ash::core::capture::check_control_roots_with_rows", "root_gate", "graph")
Start("ash::core::capture::control::ControlCodeInventory::prepare", "prepare", "graph")
Start("ash::core::capture::control::Analysis::from_code_inventory", "from_inventory", "inventory.graph")
Start("ash::core::capture::value::Analysis::resource_candidates", "candidates")


# Exact refused branches only, resolved from current source before run. The
# operator must pin this current source and its binary externally before launch.
def refusal_line(path, marker):
    with Path(path).open("rb") as source:
        raw = source.read(4 * 1024 * 1024 + 1)
    if len(raw) > 4 * 1024 * 1024:
        raise RuntimeError("source pin reader bound exceeded")
    lines = raw.decode("utf-8").splitlines()
    hits = [index for index, line in enumerate(lines) if marker in line]
    if len(hits) != 1 or "return Err(" not in lines[hits[0] + 1]:
        raise RuntimeError("refused branch source association is not exact")
    return hits[0] + 2


class Refused(gdb.Breakpoint):
    def __init__(self, location, validator=False):
        super().__init__(location, internal=True)
        self.validator = validator

    def stop(self):
        global failed
        if not restoring or not window or failed:
            return False
        try:
            obj = gdb.parse_and_eval("self").dereference()
            used = int(obj["type_work"]["value"]["value"]) if self.validator else int(obj["used"])
            limit = int(obj["type_work_limit"]) if self.validator else int(obj["limit"])
            cells = int(gdb.parse_and_eval("cells"))
            if not cells > limit - used:
                raise RuntimeError("selected branch is not a refused charge")
            stack = []
            frame = gdb.newest_frame()
            for _ in range(12):
                if frame is None:
                    break
                stack.append((frame.name() or "")[:300])
                frame = frame.older()
            failed = True
            emit({"event": "failed_charge", "used": used, "limit": limit,
                  "requested": cells, "stack": stack})
        except Exception as error:
            emit({"event": "observer_error", "kind": "failed_charge", "error": str(error)[:400]})
        return False


Refused("src/types.rs:" + str(refusal_line("src/types.rs", "if next > self.limit {")))
Refused("src/core/validate.rs:" + str(refusal_line("src/core/validate.rs", "if attempted > self.type_work_limit {")), True)


def exited(event):
    emit({"event": "inferior_exit", "exit_code": getattr(event, "exit_code", None),
          "calls": counts, "restore_count": restore_count, "open_root_windows": window,
          "limit": "inclusive phase costs overlap; same graph pointer establishes only immutable topology identity"})


gdb.events.exited.connect(exited)
