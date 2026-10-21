"""No child/image execution: fork, kill and waitpid are mocked in lifecycle tests."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, call, patch
import diagnostic as d


class DiagnosticTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.lifecycle = Path(self.directory.name) / 'lifecycle.json'
        self.image = tempfile.TemporaryFile()
        self.addCleanup(self.image.close)
        self.policy = d.bounded_read(d.ROOT / 'policy.json', d.CONTROL_LIMIT)
        self.receipt = d.bounded_read('/tmp/ash-generated-scalar.d771qtm9/producer-receipt.json', d.CONTROL_LIMIT)
        self.harness = d.bounded_read(d.__file__, d.CONTROL_LIMIT)
        self.approval = {'version': 1, 'authorized': True, 'kind': 'trusted-generated-static-diagnostic',
                         'policy_sha256': d.sha(self.policy), 'harness_sha256': d.sha(self.harness),
                         'receipt_sha256': d.RECEIPT_HASH, 'image_sha256': d.IMAGE_HASH,
                         'image_size_bytes': d.IMAGE_SIZE, 'replacement_sha256': d.REPLACEMENT_HASH,
                         'known_runtime_loading_premise_accepted': True}

    def test_pure_approval_bindings_and_refusals_never_fork(self):
        # This approval is an in-memory validator fixture, never a persisted authority.
        with patch.object(d.os, 'fork', side_effect=AssertionError('no fork in validator tests')):
            d.authorize(self.policy, self.receipt, json.dumps(self.approval).encode(), self.harness)
            for field in ['authorized', 'policy_sha256', 'harness_sha256', 'receipt_sha256', 'image_sha256',
                          'image_size_bytes', 'replacement_sha256', 'known_runtime_loading_premise_accepted']:
                changed = dict(self.approval)
                changed[field] = None
                with self.assertRaises(d.Refused):
                    d.authorize(self.policy, self.receipt, json.dumps(changed).encode(), self.harness)
            with self.assertRaises(d.Refused):
                d.authorize(self.policy, self.receipt, None, self.harness)
            changed = json.loads(self.receipt)
            changed['version'] = 2
            with self.assertRaises(d.Refused):
                d.authorize(self.policy, json.dumps(changed).encode(), json.dumps(self.approval).encode(), self.harness)

    def test_bounded_input_and_duplicate_json(self):
        path = Path(self.directory.name) / 'oversize'
        path.write_bytes(b'12345')
        with self.assertRaises(d.Refused):
            d.bounded_read(path, 4)
        with self.assertRaises(d.Refused):
            d.decode(b'{"version":1,"version":2}')

    def test_fifo_refuses_without_fork_or_blocking_open(self):
        path = Path(self.directory.name) / 'fifo'
        d.os.mkfifo(path)
        with patch.object(d.os, 'fork') as fork:
            with self.assertRaises(d.Refused):
                d.bounded_read(path, d.CONTROL_LIMIT)
        fork.assert_not_called()

    def test_child_descriptor_and_exec_contract_is_mocked(self):
        class ExitObserved(BaseException):
            pass
        close_range = Mock(return_value=0)
        with patch.object(d.os, 'dup2') as duplicate, \
                patch.object(d.os, 'execve') as execute, \
                patch.object(d.os, 'write') as write, \
                patch.object(d.os, '_exit', side_effect=ExitObserved) as leave:
            with self.assertRaises(ExitObserved):
                d.child_exec(10, 11, 12, close_range)
        self.assertEqual(duplicate.call_args_list, [
            call(10, 3, inheritable=False), call(12, 0, inheritable=True),
            call(11, 1, inheritable=True), call(11, 2, inheritable=True)])
        close_range.assert_called_once_with(4, 0xffffffff, 0)
        execute.assert_called_once_with(3, ['ash-generated-scalar-diagnostic'], {})
        # Mock exec returns; real exec cannot return successfully, so this refuses.
        leave.assert_called_once_with(125)
        write.assert_called_once()
        close_range = Mock(return_value=-1)
        with patch.object(d.os, 'dup2'), patch.object(d.os, 'execve') as execute, \
                patch.object(d.os, 'write'), patch.object(d.ctypes, 'get_errno', return_value=1), \
                patch.object(d.os, '_exit', side_effect=ExitObserved) as leave:
            with self.assertRaises(ExitObserved):
                d.child_exec(10, 11, 12, close_range)
        execute.assert_not_called()
        leave.assert_called_once_with(125)

    def test_selector_failure_precedes_fork(self):
        with patch.object(d.selectors, 'DefaultSelector', side_effect=OSError('selector setup')), \
                patch.object(d.os, 'fork') as fork, patch.object(d.os, 'kill') as kill:
            state = d.execute_once(self.image.fileno(), self.lifecycle)
        fork.assert_not_called()
        kill.assert_not_called()
        self.assertFalse(state['child_created'])
        self.assertIn('selector setup', state['failure'])

    def test_postfork_parent_setup_failure_is_killed_and_reaped(self):
        original = d.record_state
        calls = 0
        def record(path, state):
            nonlocal calls
            calls += 1
            if calls == 2:
                raise OSError('postfork record failure')
            original(path, state)
        with patch.object(d.os, 'fork', return_value=42424242), \
                patch.object(d.os, 'kill') as kill, \
                patch.object(d.os, 'waitpid', return_value=(42424242, 9)) as wait, \
                patch.object(d, 'record_state', side_effect=record):
            state = d.execute_once(self.image.fileno(), self.lifecycle)
        kill.assert_called_once_with(42424242, d.signal.SIGKILL)
        wait.assert_called_once_with(42424242, 0)
        self.assertTrue(state['child_created'])
        self.assertTrue(state['reaped'])
        self.assertIn('postfork record failure', state['failure'])

    def test_deadline_requests_kill_and_reaps_with_interrupted_wait(self):
        with patch.object(d.os, 'fork', return_value=42424242), \
                patch.object(d.os, 'kill') as kill, \
                patch.object(d.os, 'waitpid', side_effect=[InterruptedError(), (42424242, 9)]) as wait, \
                patch.object(d.time, 'monotonic', side_effect=[0, 31, 31]):
            state = d.execute_once(self.image.fileno(), self.lifecycle)
        kill.assert_called_once_with(42424242, d.signal.SIGKILL)
        self.assertEqual(wait.call_count, 2)
        self.assertTrue(state['reaped'])
        self.assertIn('deadline', state['failure'])

    def test_exec_refusal_status_is_reaped_without_kill(self):
        with patch.object(d.os, 'fork', return_value=42424242), \
                patch.object(d.os, 'kill') as kill, \
                patch.object(d.os, 'waitpid', return_value=(42424242, 125 << 8)):
            state = d.execute_once(self.image.fileno(), self.lifecycle)
        kill.assert_not_called()
        self.assertEqual(state['exit_code'], 125)
        self.assertTrue(state['reaped'])

    def test_combined_output_overflow_never_stores_more_than_limit(self):
        class Ready:
            fd = 123
        class Selector:
            def register(self, *args): pass
            def select(self, *args): return [(Ready(), None)]
            def close(self): pass
        with patch.object(d.os, 'fork', return_value=42424242), \
                patch.object(d.os, 'kill') as kill, \
                patch.object(d.os, 'waitpid', return_value=(42424242, 9)), \
                patch.object(d.os, 'read', return_value=b'x' * (d.OUTPUT_LIMIT + 1)), \
                patch.object(d.selectors, 'DefaultSelector', return_value=Selector()):
            state = d.execute_once(self.image.fileno(), self.lifecycle)
        self.assertEqual(state['output_bytes'], d.OUTPUT_LIMIT)
        self.assertIn('output bound', state['failure'])
        self.assertTrue(state['reaped'])
        kill.assert_called_once()


if __name__ == '__main__':
    unittest.main()
