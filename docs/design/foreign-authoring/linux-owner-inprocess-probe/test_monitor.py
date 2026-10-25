import json
import hashlib
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
import importlib.util
import io
from unittest.mock import patch
PYTHON = os.path.realpath('/usr/bin/python3')
MONITOR = Path(__file__).with_name('build_monitor.py')
EVIDENCE = Path(tempfile.mkdtemp(prefix='safe-test-evidence-', dir=Path(__file__).parent))

class MonitorTests(unittest.TestCase):
    def run_case(self, code, *, deadline=2, output=16384, side=16384, invalid_cwd=False, inject=False, unsupported=False, bad_pin=False, late=False):
        with tempfile.TemporaryDirectory(prefix='ash-build-monitor-test-') as directory:
            root = Path(directory)
            config = {'argv': [PYTHON, '-B', '-c', code], 'cwd': str(root / 'missing') if invalid_cwd else str(root), 'output_parent': str(root), 'watch_root': str(root), 'environment': {}, 'self_test_limits': {'deadline_seconds': deadline, 'output_bytes': output, 'sidefile_bytes': side}, 'input_files': [], 'artifact_files': []}
            tool_bytes = Path(PYTHON).read_bytes()
            config['executable_pin'] = {'size': len(tool_bytes), 'sha256': '0'*64 if bad_pin else hashlib.sha256(tool_bytes).hexdigest()}
            path = root / 'config.json'; path.write_text(json.dumps(config))
            if late:
                wrapper = 'import runpy,sys,os,time; from pathlib import Path; from unittest.mock import patch\noriginal=os.waitid\ndef late_waitid(*args):\n Path(__import__("json").loads(Path(sys.argv[1]).read_text())["cwd"]).joinpath("late-ready").touch()\n until=time.monotonic()+2\n while True:\n  result=original(*args)\n  if result is not None or time.monotonic()>until: return result\n  time.sleep(.001)\nsys.argv=[sys.argv[1],sys.argv[2]]\nwith patch("os.waitid",side_effect=late_waitid):\n runpy.run_path(sys.argv[0],run_name="__main__")\n'
                argv = [PYTHON, '-B', '-c', wrapper, str(MONITOR), str(path)]
            elif unsupported:
                wrapper = 'import runpy,sys; from unittest.mock import patch,MagicMock; sys.argv=[sys.argv[1],sys.argv[2]]; fake=MagicMock(); fake.prctl.return_value=-1; \nwith patch("ctypes.CDLL",return_value=fake):\n runpy.run_path(sys.argv[0],run_name="__main__")\n'
                argv = [PYTHON, '-B', '-c', wrapper, str(MONITOR), str(path)]
            elif inject:
                wrapper = 'import runpy,sys; from unittest.mock import patch; sys.argv=[sys.argv[1],sys.argv[2]]; \nwith patch("selectors.EpollSelector.register",side_effect=OSError("injected setup failure")):\n runpy.run_path(sys.argv[0],run_name="__main__")\n'
                argv = [PYTHON, '-B', '-c', wrapper, str(MONITOR), str(path)]
            else:
                argv = [PYTHON, '-B', str(MONITOR), str(path)]
            completed = subprocess.run(argv, capture_output=True, text=True, timeout=10, check=False)
            self.assertNotEqual(completed.returncode, -9, completed.stderr)
            response = json.loads(completed.stdout)
            receipt = json.loads(Path(response['receipt']).read_text())
            retained = Path(receipt['output_path']).read_bytes()
            case = EVIDENCE / (self._testMethodName + '-' + str(len(list(EVIDENCE.iterdir()))))
            case.mkdir(mode=0o700)
            (case / 'config.json').write_bytes(path.read_bytes())
            (case / 'receipt.json').write_bytes(Path(response['receipt']).read_bytes())
            (case / 'output.log').write_bytes(retained)
            for item in receipt['watched_files']:
                if 'retained_path' in item:
                    (case / Path(item['retained_path']).name).write_bytes(Path(item['retained_path']).read_bytes())
            (case / 'monitor-stdout.log').write_text(completed.stdout)
            (case / 'monitor-stderr.log').write_text(completed.stderr)
        self.assertFalse(Path(directory).exists(), 'private test fixture disposed after actual reaping')
        (case / 'test-outcome.json').write_text(json.dumps({'returncode': completed.returncode, 'private_fixture_disposed': True}))
        return completed.returncode, receipt, retained
    def assert_reaped(self, receipt):
        self.assertTrue(receipt['cleanup']['all_children_reaped'], receipt)
        self.assertEqual(receipt['child_pgid'], receipt['child_pid'])
        self.assertEqual(receipt['child_session'], receipt['child_pid'])
        self.assertEqual(receipt['cleanup']['remaining_children'], [])
        self.assertTrue(any(item['pid'] == receipt['child_pid'] for item in receipt['cleanup']['reaped']))
    def test_normal_and_nonzero_exit(self):
        for status in (0, 7):
            with self.subTest(status=status):
                rc, receipt, output = self.run_case(f'import sys; print("trusted-child"); sys.exit({status})')
                self.assertEqual(receipt['reason'], 'exit'); self.assertEqual(receipt['child_exit'], status)
                self.assertEqual(output, b'trusted-child\n'); self.assertEqual(rc, 0 if status == 0 else 1)
                self.assert_reaped(receipt)
    def test_output_bound(self):
        rc, receipt, retained = self.run_case('import os,time; os.write(1,b"x"*65536); time.sleep(1)', output=1024)
        self.assertEqual(rc, 1); self.assertEqual(receipt['reason'], 'output_limit')
        self.assertEqual(len(retained), 1024); self.assertTrue(receipt['output_truncated'])
        self.assertGreater(receipt['observed_output_bytes'], len(retained)); self.assert_reaped(receipt)
    def test_direct_sidefile_bound_observes_overshoot(self):
        rc, receipt, _ = self.run_case('from pathlib import Path; import time; Path("native-build.log").write_bytes(b"x"*32768); time.sleep(1)', side=1024)
        self.assertEqual(rc, 1); self.assertEqual(receipt['reason'], 'watched_file_limit')
        record = next(x for x in receipt['watched_files'] if x['relative_path'] == 'native-build.log')
        self.assertGreater(record['observed_peak_bytes'], 1024); self.assertTrue(record['hash_is_prefix'])
        self.assertFalse(receipt['hard_storage_containment']); self.assert_reaped(receipt)
    def test_timeout_reaps_descendant(self):
        rc, receipt, _ = self.run_case('import os,time; child=os.fork(); time.sleep(60)', deadline=.2)
        self.assertEqual(rc, 1); self.assertEqual(receipt['reason'], 'deadline')
        self.assertGreaterEqual(len(receipt['cleanup']['reaped']), 2); self.assert_reaped(receipt)
    def test_setup_refusal_starts_no_child(self):
        rc, receipt, _ = self.run_case('raise AssertionError("must not start")', invalid_cwd=True)
        self.assertEqual(rc, 78); self.assertIsNone(receipt['child_pid']); self.assertEqual(receipt['reason'], 'setup_refusal')
        self.assertTrue(receipt['cleanup']['all_children_reaped'])
    def test_postspawn_setup_failure_reaps(self):
        rc, receipt, _ = self.run_case('import time; time.sleep(60)', inject=True)
        self.assertEqual(rc, 1); self.assertEqual(receipt['reason'], 'monitor_error'); self.assert_reaped(receipt)
    def test_successful_leader_cannot_leave_descendants(self):
        code = 'import os,time; child=os.fork(); time.sleep(60) if child==0 else os._exit(0)'
        rc, receipt, _ = self.run_case(code)
        self.assertEqual(rc, 1)
        self.assertEqual(receipt['reason'], 'leader_exit_with_descendants')
        self.assertEqual(receipt['child_exit'], 0)
        self.assertGreaterEqual(len(receipt['cleanup']['reaped']), 2)
        self.assert_reaped(receipt)
    def test_owned_escaped_descendant_is_refused_and_reaped(self):
        code = 'import os,time; child=os.fork();\nif child==0: os.setsid()\ntime.sleep(60)'
        rc, receipt, _ = self.run_case(code, deadline=.2)
        self.assertEqual(rc, 1)
        self.assertEqual(receipt['reason'], 'unsupported_group_escape')
        self.assertTrue(receipt['cleanup']['escaped_group_detected'])
        self.assertGreaterEqual(len(receipt['cleanup']['reaped']), 2)
        self.assert_reaped(receipt)
    def test_wrong_tool_pin_refuses_before_spawn(self):
        rc, receipt, _ = self.run_case('raise AssertionError("must not execute")', bad_pin=True)
        self.assertEqual(rc, 78)
        self.assertEqual(receipt['reason'], 'setup_refusal')
        self.assertIn('executable pin mismatch', receipt['error'])
        self.assertIsNone(receipt['child_pid'])
    def test_unsupported_subreaper_refuses_before_spawn(self):
        rc, receipt, _ = self.run_case('raise AssertionError("must not execute")', unsupported=True)
        self.assertEqual(rc, 78)
        self.assertEqual(receipt['reason'], 'setup_refusal')
        self.assertIn('GET_CHILD_SUBREAPER failed', receipt['error'])
        self.assertIsNone(receipt['child_pid'])
        self.assertTrue(receipt['cleanup']['all_children_reaped'])
    def test_unrelated_owned_control_group_is_not_signalled(self):
        control = subprocess.Popen([PYTHON, '-B', '-c', 'import time; time.sleep(60)'], start_new_session=True,
                                   stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        try:
            _, receipt, _ = self.run_case('import time; time.sleep(60)', deadline=.2)
            self.assertIsNone(control.poll(), 'monitor must not signal the sibling control group')
            self.assertNotIn(control.pid, [item['pid'] for item in receipt['cleanup']['reaped']])
            self.assert_reaped(receipt)
        finally:
            control.kill(); control.wait()

    def test_late_output_after_last_sample_is_refused(self):
        code = 'from pathlib import Path; import os,time\nwhile not Path("late-ready").exists(): time.sleep(.001)\nos.write(1,b"x"*2048)'
        rc, receipt, retained = self.run_case(code, output=1024, late=True)
        self.assert_reaped(receipt)
        self.assertEqual(rc, 1); self.assertEqual(receipt['reason'], 'output_limit')
        self.assertEqual(len(retained), 1024)
        self.assertEqual(receipt['observed_output_bytes'], 2048)

    def test_late_sidefile_after_last_sample_is_refused(self):
        code = 'from pathlib import Path; import time\nwhile not Path("late-ready").exists(): time.sleep(.001)\nPath("whole-static.map").write_bytes(b"x"*32768)'
        rc, receipt, _ = self.run_case(code, side=1024, late=True)
        self.assert_reaped(receipt)
        self.assertEqual(rc, 1); self.assertEqual(receipt['reason'], 'watched_file_limit')
        item = next(x for x in receipt['watched_files'] if x['relative_path']=='whole-static.map')
        self.assertEqual(item['observed_peak_bytes'], 32768)
        self.assertTrue(item['hash_is_prefix'])

    def test_cumulative_watch_records_are_bounded(self):
        spec = importlib.util.spec_from_file_location('monitor_for_test', MONITOR)
        monitor = importlib.util.module_from_spec(spec); spec.loader.exec_module(monitor)
        records = {}
        with tempfile.TemporaryDirectory() as directory, patch.object(monitor, 'MAX_ENTRIES', 2):
            root = Path(directory)
            for index in range(3):
                sub = root / str(index); sub.mkdir(); log = sub/'native-build.log'; log.write_bytes(b'x')
                result = monitor.watched(root, root/'excluded', records, 1024)
                self.assertEqual(result, None if index<2 else 'watch_record_limit')
                log.unlink(); sub.rmdir()
            self.assertEqual(len(records), 2)

    def test_config_read_is_bounded_before_decode(self):
        spec = importlib.util.spec_from_file_location('monitor_config_test', MONITOR)
        monitor = importlib.util.module_from_spec(spec); spec.loader.exec_module(monitor)
        requested = []
        class Tracked(io.BytesIO):
            def read(self, size=-1):
                requested.append(size)
                return super().read(size)
        stream = Tracked(b'x' * (monitor.MAX_CONFIG+100))
        with patch('builtins.open', return_value=stream):
            with self.assertRaisesRegex(monitor.Refusal, 'config exceeds'):
                monitor.read_config('unused-mocked-path')
        self.assertEqual(requested, [monitor.MAX_CONFIG+1])
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'large.json'; path.write_bytes(b'x'*(monitor.MAX_CONFIG+100))
            result = subprocess.run([PYTHON,'-B',str(MONITOR),str(path)],capture_output=True,text=True,timeout=5)
            self.assertEqual(result.returncode,78)
            self.assertEqual(json.loads(result.stdout)['reason'],'pre_run_refusal')
            self.assertEqual(list(Path(directory).iterdir()), [path])

if __name__ == '__main__':
    print('Retained safe-test evidence: ' + str(EVIDENCE), flush=True)
    unittest.main(verbosity=2)

