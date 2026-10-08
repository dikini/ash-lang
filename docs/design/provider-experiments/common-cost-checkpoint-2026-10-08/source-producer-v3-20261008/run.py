from pathlib import Path
import datetime, hashlib, importlib.util, json, os, re, subprocess, time

E = Path(__file__).resolve().parent
P = Path('/home/dikini/.codex/ash-provider-evidence/algebraic-resource-analysis-2026-10-07/f1-root-correspondence/source-producer-connected-candidate-v3')
H = Path('/home/dikini/.codex/ash-provider-evidence/sqlite-2026-10-05/handoff/post282-private-forwarding-admission-test')
BASE = Path('/home/dikini/.codex/ash-provider-evidence/common-resource-support-2026-10-04/requested-root-metadata-160')

def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result

g = module('guards', BASE / 'author/f2-candidate-only-measurement-runner/run.py')
h = module('harness', BASE / 'author/connected-quality-260/harness.py')
R = g.R
sha = g.sha
pins = json.loads((P / 'pins.json').read_text())
save = lambda name, value: (E / name).write_text(json.dumps(value, indent=2) + '\n')
stamp = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat()
snapshots = lambda: [g.snap(root) for root in g.ROOTS]

assert not (E / 'start.json').exists(), 'preserve prior attempt'
assert sha(P / 'pins.json') == 'cc1b9e387ec6925f0b9c6c871ab412c7f43fef83d0a57ad7a97eac3f53f63896'
assert not g.engines(), g.engines()
for name, digest in pins['patches'].items():
    assert sha(P / name) == digest, name
before = snapshots()
assert before[0] == json.loads((E / 'before.json').read_text())
assert before[0]['head'] == pins['common_base_ref']
for rel, digest in pins['base'].items():
    assert before[0]['files'].get(rel) == digest, rel
fixture = 'tests/fixtures/provider-experiments/sqlite-copying/forwarding-chain.ash'
test = 'tests/provider_sqlite_copying.rs'
assert before[0]['files'][test] == '22aa0ca6387727fe668e6af630336ca85067c17cd31105f4338bed605e8b323f'
assert fixture not in before[0]['files']
assert sha(H / 'after' / test) == '717551a4f5bf4ee18c9ae7cf1ee27d9db4016ca72d0b96db0774e03a240fba56'
assert sha(H / 'after' / fixture) == '5d7405ee44fe147fd138c2b9e5a692c61b0c0746be2ecad49954f513cd4d88b0'
owned = [*pins['base'], test, fixture]
backup = {rel: ((R / rel).read_bytes() if (R / rel).exists() else None) for rel in owned}
rows = []
expected = {rel: before[0]['files'].get(rel) for rel in owned}
applied = None
failure = None
restoration_error = None
began = time.monotonic()
save('start.json', {'utc': stamp(), 'pins_sha256': sha(P / 'pins.json'), 'jobs': 1,
                    'max_seconds': 600, 'normal_limits': True, 'coverage_overlay': True,
                    'roots': before, 'runner_sha256': sha(Path(__file__))})

def apply(root, patch):
    subprocess.run(['git', 'apply', '--check', str(patch)], cwd=root, check=True)
    subprocess.run(['git', 'apply', str(patch)], cwd=root, check=True)

try:
    proof = E / 'direction-proof'
    proof.mkdir()
    subprocess.run(['git', 'init', '-q'], cwd=proof, check=True)
    for rel, data in backup.items():
        if data is not None:
            path = proof / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
    for patch in ['forward.patch', 'connected-coverage.patch', 'connected-coverage-inverse.patch', 'inverse.patch']:
        apply(proof, P / patch)
    for rel, data in backup.items():
        assert ((proof / rel).read_bytes() if (proof / rel).exists() else None) == data, rel
    apply(R, P / 'forward.patch')
    expected.update(pins['candidate'])
    for rel, digest in pins['candidate'].items():
        assert sha(R / rel) == digest, rel
    for rel in [test, fixture]:
        path = R / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes((H / 'after' / rel).read_bytes())
        expected[rel] = sha(path)
    apply(R, P / 'connected-coverage.patch')
    expected['src/core/capture/value/source_producer.rs'] = sha(R / 'src/core/capture/value/source_producer.rs')
    applied = {rel: sha(R / rel) for rel in owned}
    save('applied.json', {'source': applied, 'roots': snapshots()})
    env = {key: value for key, value in os.environ.items() if not key.startswith('ASH_')}
    env['CARGO_BUILD_JOBS'] = '1'
    commands = [
        ('value', ['cargo', 'test', '--locked', '-p', 'ash', '--lib',
                   'core::capture::value::tests::', '--', '--test-threads=1', '--nocapture']),
        ('native', ['cargo', 'test', '--locked', '-p', 'ash', '--test', 'provider_sqlite_copying',
                    'qualified_forwarding_chain_preserves_integer_and_source_completion',
                    '--', '--exact', '--test-threads=1', '--nocapture']),
    ]
    for name, command in commands:
        remaining = int(600 - (time.monotonic() - began) - 5)
        assert remaining > 5, 'bounded feedback window exhausted'
        print(json.dumps({'start': name, 'utc': stamp(), 'argv': command}), flush=True)
        log = E / (name + '.log')
        begin = time.monotonic()
        with log.open('wb') as stream:
            result = subprocess.run(['timeout', '--signal=TERM', '--kill-after=3s', str(remaining), *command],
                                    cwd=R, env=env, stdout=stream, stderr=subprocess.STDOUT)
        row = {'name': name, 'argv': command, 'exit': result.returncode,
               'seconds': time.monotonic() - begin, 'log_sha256': sha(log)}
        rows.append(row)
        save('results.json', rows)
        print(json.dumps(row), flush=True)
        assert result.returncode == 0, (name, result.returncode)
        raw = log.read_text()
        coverage = h.validate(raw, {'name': 'connected-' + name, 'argv': command,
            'summary_count': 1, 'exact_passed': 1 if name == 'native' else None,
            'require_nonempty_tests': True, 'unfiltered': False})
        row['harness'] = coverage
        if name == 'value':
            required = [
                'connected_nonleaf_producer_preserves_original_evidence_tuple_roots_and_control',
                'symbolic_returned_root_keeps_both_full_specializations_and_original_typecall',
                'recursive_callee_contexts_join_calls_but_keep_distinct_entries',
                'canonical_context_prefixes_preserve_source_order_and_atomic_cold_publication',
                'immutable_setup_keeps_late_real_owners_closure_dependencies_and_direct_readers',
                'evidence_input_phase_keeps_late_live_atoms_and_other_direct_readers',
                'evidence_completion_refusals_never_publish_attempted_transfers',
                'call_transfer_completion_has_prefilled_refusal_and_fresh_exact_retry_boundaries',
                'evidence_coalesces_complementary_empty_capture_ports_before_provider_validity',
            ]
            for test_name in required:
                assert re.search(r'^test core::capture::value::tests::' + re.escape(test_name) + r' \.\.\.(?: |$)', raw, re.M), test_name
            row['required_tests'] = required
        if name == 'native':
            hits = [tuple(map(int, match)) for match in re.findall(
                r'ash-fusion-connected-installed expression=(\d+) slot=(\d+) context=(\d+) total_raw=(\d+) total_evidence=(\d+) new_raw=(\d+) new_evidence=(\d+) root_reused=(\d+)', raw)]
            row['connected_hits'] = hits
            assert any(hit[2] == 0 and hit[5] > 0 and hit[6] > 0 for hit in hits), 'no new connected Raw/E native publication'
        save('results.json', rows)
except BaseException as error:
    failure = repr(error)
finally:
    try:
        assert not g.engines(), g.engines()
        assert all((sha(R / rel) if (R / rel).exists() else None) == digest for rel, digest in expected.items()), 'unexpected owned input mutation'
        for rel, data in backup.items():
            path = R / rel
            if data is None:
                if path.exists(): path.unlink()
            else:
                path.write_bytes(data)
        after = snapshots()
        save('after.json', after)
        assert after == before, 'guards not restored'
    except BaseException as error:
        restoration_error = repr(error)
    returned = {'utc': stamp(), 'elapsed_seconds': time.monotonic() - began,
                'failure': failure, 'restoration_error': restoration_error,
                'engines': g.engines(), 'results': rows, 'explicit_return': restoration_error is None,
                'all_three_guards_restored': restoration_error is None,
                'normal_limits_unchanged': True, 'pass': failure is None and restoration_error is None}
    save('return.json', returned)
    print(json.dumps(returned), flush=True)

raise SystemExit(0 if returned['pass'] else 1)
