from pathlib import Path
import datetime, hashlib, importlib.util, json, os, re, subprocess, time

E = Path(__file__).resolve().parent
P = Path('/home/dikini/.codex/ash-provider-evidence/algebraic-resource-analysis-2026-10-07/f1-root-correspondence/source-producer-connected-candidate-v3')
B = Path('/home/dikini/.codex/ash-provider-evidence/common-resource-support-2026-10-04')
A = B / 'requested-root-metadata-160'
H = Path('/home/dikini/.codex/ash-provider-evidence/sqlite-2026-10-05/handoff/post282-private-forwarding-admission-test')
D = B / 'cursor-method-connected-242/diagnostic-forward.patch'

def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result

g = module('guards', A / 'author/f2-candidate-only-measurement-runner/run.py')
h = module('harness', A / 'author/connected-quality-260/harness.py')
R, sha = g.R, g.sha
save = lambda name, value: (E / name).write_text(json.dumps(value, indent=2) + '\n')
pins = json.loads((P / 'pins.json').read_text())
cases = json.loads((A / 'author/context-extension-hit-candidate-only-measurement-runner-v1/cases.json').read_text())
cases = [case for case in cases if case['case_id'] in ['copying', 'bound_nul']]
fixture = 'tests/fixtures/provider-experiments/sqlite-copying/forwarding-chain.ash'
test = 'tests/provider_sqlite_copying.rs'
diag = ['src/core/validate.rs', 'src/types.rs', 'src/driver.rs', 'src/elaborate.rs', 'tests/support/sqlite_copying.rs']
owned = list(dict.fromkeys([*pins['base'], test, fixture, *diag]))
assert not (E / 'start.json').exists(), 'preserve prior attempt'
assert not g.engines(), g.engines()
assert sha(P / 'pins.json') == 'cc1b9e387ec6925f0b9c6c871ab412c7f43fef83d0a57ad7a97eac3f53f63896'
for name, digest in pins['patches'].items(): assert sha(P / name) == digest, name
before = [g.snap(root) for root in g.ROOTS]
assert before[0]['head'] == pins['common_base_ref']
for rel, digest in pins['base'].items(): assert before[0]['files'].get(rel) == digest, rel
assert before[0]['files'][test] == '22aa0ca6387727fe668e6af630336ca85067c17cd31105f4338bed605e8b323f'
assert fixture not in before[0]['files']
assert sha(H / 'after' / test) == '717551a4f5bf4ee18c9ae7cf1ee27d9db4016ca72d0b96db0774e03a240fba56'
assert sha(H / 'after' / fixture) == '5d7405ee44fe147fd138c2b9e5a692c61b0c0746be2ecad49954f513cd4d88b0'
backup = {rel: ((R / rel).read_bytes() if (R / rel).exists() else None) for rel in owned}
expected = {rel: before[0]['files'].get(rel) for rel in owned}
save('before.json', before)
save('start.json', {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'runner_sha256': sha(__file__), 'pins_sha256': sha(P / 'pins.json'),
    'diagnostic_patch_sha256': sha(D), 'jobs': 1, 'temporary_completion_ceiling': 268435456,
    'normal_source_limit': 327680, 'normal_Core_limit': 983040,
    'cases': cases, 'fresh_baseline': False, 'acceptance': False})

def apply(root, patch):
    subprocess.run(['git', 'apply', '--check', str(patch)], cwd=root, check=True)
    subprocess.run(['git', 'apply', str(patch)], cwd=root, check=True)

def write(root, rel, data):
    path = root / rel
    if data is None:
        if path.exists(): path.unlink()
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)

# Validate both exact compositions privately before changing shared sources.
proofs = {}
for lane in ['candidate']:
    proof = E / ('proof-' + lane)
    proof.mkdir()
    subprocess.run(['git', 'init', '-q'], cwd=proof, check=True)
    for rel, data in backup.items(): write(proof, rel, data)
    if lane == 'candidate':
        apply(proof, P / 'forward.patch')
        for rel, digest in pins['candidate'].items(): assert sha(proof / rel) == digest, rel
        apply(proof, P / 'connected-coverage.patch')
    for rel in [test, fixture]: write(proof, rel, (H / 'after' / rel).read_bytes())
    apply(proof, D)
    types = proof / 'src/types.rs'
    source = types.read_text()
    assert source.count('20_971_520; // temporary diagnostic ceiling214') == 1
    source = source.replace('20_971_520; // temporary diagnostic ceiling214', '268_435_456; // temporary diagnostic completion ceiling')
    old = '        if next > self.limit {\n            return Err(());\n        }'
    assert source.count(old) == 1
    source = source.replace(old, '        if next > self.limit {\n            eprintln!(\"ASH_COST_REFUSAL used={} requested={} limit={}\", self.used, cells, self.limit);\n            return Err(());\n        }')
    types.write_text(source)
    proofs[lane] = {rel: ((proof / rel).read_bytes() if (proof / rel).exists() else None) for rel in owned}
save('compositions.json', {lane: {rel: hashlib.sha256(data).hexdigest() if data is not None else None
                                for rel, data in values.items()} for lane, values in proofs.items()})

rows = []
failure = None
restoration_error = None
began = time.monotonic()
env = {key: value for key, value in os.environ.items() if not key.startswith('ASH_')}
env['CARGO_BUILD_JOBS'] = '1'
try:
    assert [g.snap(root) for root in g.ROOTS] == before
    for lane in ['candidate']:
        assert not g.engines(), g.engines()
        assert all((sha(R / rel) if (R / rel).exists() else None) == digest for rel, digest in expected.items())
        for rel, data in proofs[lane].items(): write(R, rel, data)
        expected = {rel: sha(R / rel) if (R / rel).exists() else None for rel in owned}
        save(lane + '-applied.json', expected)
        for case in cases:
            key = case['case_id']
            command = ['cargo', 'test', '--locked', '-p', 'ash', '--test', case['test_binary'],
                       case['test_name'], '--', '--exact', '--test-threads=1', '--nocapture']
            remaining = int(600 - (time.monotonic() - began) - 10)
            assert remaining > 5, 'bounded window exhausted'
            print(json.dumps({'start': lane + '-' + key, 'argv': command}), flush=True)
            log = E / (lane + '-' + key + '.log')
            start = time.monotonic()
            with log.open('wb') as stream:
                result = subprocess.run(['timeout', '--signal=TERM', '--kill-after=3s', str(min(300, remaining)), *command],
                                        cwd=R, env=env, stdout=stream, stderr=subprocess.STDOUT)
            text = log.read_text()
            row = {'lane': lane, 'case': key, 'argv': command, 'exit': result.returncode,
                   'seconds': time.monotonic() - start, 'log_sha256': sha(log),
                   'owners': {name: int(total) for name, total in re.findall(r'DEFICIT214 owner=(\S+) total=(\d+)', text)},
                   'connected_hits': [list(map(int, values)) for values in re.findall(
                       r'ash-fusion-connected-installed expression=(\d+) slot=(\d+) context=(\d+) total_raw=(\d+) total_evidence=(\d+) new_raw=(\d+) new_evidence=(\d+) root_reused=(\d+)', text)]}
            if result.returncode == 0:
                row['harness'] = h.validate(text, {'name': lane + '-' + key, 'argv': command,
                    'summary_count': 1, 'exact_passed': 1, 'require_nonempty_tests': True, 'unfiltered': False})
                assert set(row['owners']) == {'resolution', 'source-checking', 'module-linking',
                    'linked-interface', 'final-elaboration', 'independent-effect-core'}, row
            else:
                row['diagnostic_failure'] = text[-16000:]
            rows.append(row)
            save('results.json', rows)
            print(json.dumps({k: v for k, v in row.items() if k not in ['diagnostic_failure', 'harness', 'connected_hits']}), flush=True)
            assert not g.engines(), g.engines()
except BaseException as error:
    failure = repr(error)
finally:
    try:
        assert not g.engines(), g.engines()
        assert all((sha(R / rel) if (R / rel).exists() else None) == digest for rel, digest in expected.items()), 'unexpected owned mutation'
        for rel, data in backup.items(): write(R, rel, data)
        after = [g.snap(root) for root in g.ROOTS]
        save('after.json', after)
        assert after == before, 'full guards not restored'
    except BaseException as error:
        restoration_error = repr(error)
    returned = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'seconds': time.monotonic() - began, 'failure': failure,
        'restoration_error': restoration_error, 'all_three_guards_restored': restoration_error is None,
        'normal_limits_restored': restoration_error is None, 'engines': g.engines(),
        'completed_cases': len(rows), 'required_cases': 2,
        'all_diagnostic_programs_passed': len(rows) == 2 and all(row['exit'] == 0 for row in rows),
        'acceptance': False, 'explicit_return': restoration_error is None}
    save('return.json', returned)
    print(json.dumps(returned), flush=True)
raise SystemExit(0 if failure is None and restoration_error is None else 1)
