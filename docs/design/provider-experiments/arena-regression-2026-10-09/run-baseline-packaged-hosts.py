#!/usr/bin/env python3
"""Capture the six established packaged-host receipts; run engines only when invoked."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import time

P = argparse.ArgumentParser(description=__doc__)
P.add_argument('--repo', type=Path, default=Path('/home/dikini/Projects/ash-lang'))
P.add_argument('--target-dir', type=Path, required=True)
P.add_argument('--evidence', type=Path, required=True)
P.add_argument('--build-timeout', type=int, default=600)
P.add_argument('--host-timeout', type=int, default=300)
A = P.parse_args()
repo, target, evidence = A.repo.resolve(), A.target_dir.resolve(), A.evidence.resolve()
evidence.mkdir(parents=True, exist_ok=False)
sys.path.insert(0, str(repo / 'docs/design/provider-experiments/main-delivery-2026-10-08/evidence'))
from phase_report import parse_phase_lines

BUDGETS = {'SourceChecking': 1245184, 'FinalElaboration': 393216, 'IndependentCore': 1638400}
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def source_pins():
    paths = subprocess.check_output(['git', '-C', str(repo), 'ls-files', '-co', '--exclude-standard', '-z']).decode().split('\0')
    return {p: sha(repo / p) for p in sorted(set(paths)) if p and (repo / p).is_file()
            and ((repo / p).suffix in {'.rs', '.ash', '.toml', '.lock'} or p == 'Cargo.lock')}

def git_head():
    return subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()

receipt = {'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
           'repo': str(repo), 'target_dir': str(target), 'head': git_head(),
           'source_before': source_pins(), 'expected_budgets': BUDGETS,
           'runner_sha256': sha(Path(__file__)), 'runs': [], 'completed': False}
def save():
    (evidence / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')

def capture(name, command, cwd, timeout, env=None):
    begun = time.monotonic()
    row = {'name': name, 'command': command, 'shell_display': shlex.join(command), 'cwd': str(cwd)}
    try:
        done = subprocess.run(command, cwd=cwd, env=env, capture_output=True, text=True, timeout=timeout)
        stdout, stderr, code = done.stdout, done.stderr, done.returncode
    except subprocess.TimeoutExpired as failure:
        def decoded(s): return s.decode(errors='replace') if isinstance(s, bytes) else (s or '')
        stdout, stderr, code = decoded(failure.stdout), decoded(failure.stderr), None
        row['timeout_seconds'] = timeout
    except OSError as failure:
        stdout, stderr, code = '', str(failure), None
        row['execution_error'] = str(failure)
    row.update(exit_code=code, elapsed_seconds=time.monotonic()-begun)
    for stream, content in [('stdout', stdout), ('stderr', stderr)]:
        path = evidence / (name + '.' + stream)
        path.write_text(content)
        row[stream + '_file'] = path.name
        row[stream + '_sha256'] = sha(path)
    return row, stdout, stderr

unit = 'Completed(Ok(()), Closed)'
rows = 'Cons(Stored(1, TextValue("héllo 世界"), BlobBytes([0, 255])), Cons(Stored(2, TextValue("héllo 世界"), BlobBytes([0, 255])), Cons(Stored(3, TextValue("third"), BlobBytes([])), Nil)))'
query = f'Completed(Ok({rows}), Closed)'
sqlite = {
    'text-entry.ash': ('Completed(Completed(Ok(TextValue("héllo 世界")), Closed), Closed)',
                       'Scope<OpenError, CloseError, Scope<PrepareError, FinalizeError, Result<TextOrNull>>>', [13], [13], 1, 1),
    'copying-entry.ash': ('CopySession(Completed(Completed(Ok(Copied(42, TextValue("héllo 世界"), BlobBytes([0, 255]), TextValue(""), BlobBytes([]), NullText, NullBytes, TextValue("世界\\0tail"))), Closed), Closed))',
                         'CopyOutcome', [13, 2, 0, 0], [13, 2, 0, 0, 11], 1, 1),
    'session-entry.ash': (f'SessionReports(Completed(({unit}, {unit}, {unit}, {unit}, {query}), Closed), Completed({query}, Closed))',
                         'SessionOutcome', [13, 2, 5, 0], [13, 2, 13, 2, 5, 0, 13, 2, 13, 2, 5, 0], 2, 6),
    'control-resume.ash': ('Completed(Completed(Ok(CopiedRow(TextValue("héllo 世界"), BlobBytes([0, 255]))), Closed), Closed)',
                          'Scope<OpenError, CloseError, Scope<PrepareError, FinalizeError, Result<CopiedRow>>>', [], [13, 2], 1, 1),
    'control-discard.ash': ('42', 'Int', [], [], 1, 1),
}
# These are native event expectations already asserted by the public suites.
# Store(owner, bytes, alignment, used); Load indexes chronological publications.
arena = {
    'allocation-entry.ash': ('Completed(41, Closed)', 'Scope<ArenaInitError, ArenaFinishError, Int>', [
        ('Acquire',8,1), ('Store',0,8,8,8), ('Load',0), ('Release',0)]),
}

def checked(condition, issues, message):
    if not condition: issues.append(message)

def arena_trace(lines):
    normalized, owners, published, issue = [], [], [], []
    usage_pattern = r'Usage \{ used_payload_bytes: (\d+), payload_capacity: (\d+), object_count: (\d+), object_capacity: (\d+) \}'
    active = []
    for line in lines:
        try:
            activation = int(re.search(r'activation: (\d+)', line).group(1))
            if line.startswith('Acquired {'):
                used, capacity, count, slots = map(int, re.search(usage_pattern, line).groups())
                assert used == count == 0 and activation not in [o['activation'] for o in owners]
                owner = len(owners)
                owners.append({'activation': activation, 'usage': (used,capacity,count,slots), 'live': True, 'key': None})
                active.append(owner)
                normalized.append(('Acquire',capacity,slots))
                continue
            owner = next(i for i,o in enumerate(owners) if o['activation'] == activation)
            state = owners[owner]
            assert state['live']
            if line.startswith(('Stored {','Loaded {')):
                key = tuple(map(int,re.search(r'AllocationKey \{ owner: (\d+), object: (\d+) \}', line).groups()))
                usage = tuple(map(int,re.search(usage_pattern,line).groups()))
                if line.startswith('Stored {'):
                    tag, size, alignment = map(int,re.search(r'PayloadLayout \{ tag: LayoutTag\((\d+)\), size: (\d+), alignment: (\d+) \}',line).groups())
                    assert key not in [p['key'] for p in published]
                    assert usage[1] == state['usage'][1] and usage[3] == state['usage'][3]
                    assert usage[2] == state['usage'][2]+1 and key[1] == usage[2]
                    assert usage[0] <= usage[1] and usage[2] <= usage[3]
                    if state['key'] is None:
                        assert key[0] not in [o['key'] for o in owners if o['key'] is not None]
                        state['key'] = key[0]
                    assert key[0] == state['key']
                    state['usage'] = usage
                    published.append({'key':key,'owner':owner,'tag':tag,'size':size})
                    normalized.append(('Store',owner,size,alignment,usage[0]))
                else:
                    publication = next(i for i,p in enumerate(published) if p['key'] == key)
                    p = published[publication]
                    tag, size = map(int,re.search(r'layout: LayoutTag\((\d+)\), bytes_read: (\d+)',line).groups())
                    assert p['owner'] == owner and (tag,size) == (p['tag'],p['size']) and usage == state['usage']
                    normalized.append(('Load',publication))
            elif line.startswith('Released {'):
                assert 'host_teardown: false' in line and active.pop() == owner
                state['live'] = False
                normalized.append(('Release',owner))
            else:
                raise AssertionError('Unexpected native event')
        except (AssertionError, AttributeError, StopIteration, IndexError, ValueError) as failure:
            issue.append(f'Native event invariant mismatch: {line}: {failure}')
    checked(not active and all(not o['live'] for o in owners),issue,'Live owner after final native event')
    return normalized, issue

save()
build_env = os.environ.copy()
build_env.update(CARGO_BUILD_JOBS='1', RUSTC_WRAPPER='', CARGO_TARGET_DIR=str(target))
build, _, _ = capture('build-examples', ['cargo','build','--locked','-p','ash-foreign-adapter','--example','sqlite_session','--example','arena_typed'], repo, A.build_timeout, build_env)
receipt['build'] = build
receipt['build_environment'] = {key: build_env[key] for key in ['CARGO_BUILD_JOBS','RUSTC_WRAPPER','CARGO_TARGET_DIR']}
save()
if build['exit_code'] == 0:
    owned = evidence / 'sqlite-owned-package'
    owned.mkdir()
    source_package = repo / 'docs/design/provider-experiments/examples/sqlite-copying'
    for source in source_package.glob('*.ash'):
        shutil.copyfile(source, owned / source.name)
    receipt['sqlite_owned_directory'] = str(owned)
    for entry, (value, ty, inputs, outputs, connections, statements) in sqlite.items():
        name = 'sqlite-' + entry
        binary = target / 'debug/examples/sqlite_session'
        run, stdout, stderr = capture(name,[str(binary),str(owned / entry)],owned,A.host_timeout)
        issues, lines = [], stdout.splitlines()
        checked(run['exit_code'] == 0,issues,'Host exit must be zero')
        checked([x for x in lines if x.startswith('value: ')] == ['value: '+value],issues,'Exact source value')
        checked([x for x in lines if x.startswith('type: ')] == ['type: '+ty],issues,'Exact returned type')
        checked([x for x in lines if x.startswith('retained owners: ')] == ['retained owners: 0'],issues,'Zero retained owners before runtime drop')
        events = [x.removeprefix('observation: ') for x in lines if x.startswith('observation: ')]
        copies = {label:[int(n) for n in re.findall(label+r'\((\d+)\)',stdout)] for label in ['InputCopied','OutputCopied']}
        checked(copies == {'InputCopied':inputs,'OutputCopied':outputs},issues,'Exact copied byte lengths')
        for operation, count in [('open',connections),('prepare',statements),('finalize',statements),('close',connections)]:
            calls = [i for i,e in enumerate(events) if e.startswith(f'Call {{ operation: "{operation}",')]
            checked(len(calls)==count,issues,f'Native {operation} count')
            checked(all(events[i]==f'Call {{ operation: "{operation}", code: 0 }}' for i in calls),issues,f'Native {operation} success status')
            if operation in ['finalize','close']:
                dispatches = [i for i,e in enumerate(events) if e==f'FinishDispatched {{ operation: "{operation}" }}']
                checked(len(dispatches)==count and all(a<b for a,b in zip(dispatches,calls)),issues,f'Source {operation} dispatch before native completion')
        checked(not any('FaultInjected' in e or 'operation: "close_v2"' in e for e in events),issues,'No injected fault or close_v2')
        steps = [int(n) for n in re.findall(r'Call \{ operation: "step", code: (\d+) \}',stdout)]
        expected_steps = {'text-entry.ash':[100], 'copying-entry.ash':[100,101], 'session-entry.ash':[101]*6+[100,100,100,101]*2, 'control-resume.ash':[100,101], 'control-discard.ash':[]}[entry]
        checked(steps==expected_steps,issues,'Exact native stepping trace')
        if entry=='control-discard.ash':
            for operation in ['errcode','errmsg']:
                positions = [i for i,e in enumerate(events) if e==f'Query {{ operation: "{operation}" }}']
                finals = [i for i,e in enumerate(events) if e.startswith('Call { operation: "finalize",')]
                checked(len(positions)==len(finals)==1 and positions[0]<finals[0],issues,f'{operation} owned cleanup before finalize')
            checked(not copies['OutputCopied'],issues,'No abandoned row copy')
        if entry=='session-entry.ash':
            opens = [i for i,e in enumerate(events) if e.startswith('Call { operation: "open",')]
            closes = [i for i,e in enumerate(events) if e.startswith('Call { operation: "close",')]
            checked(len(opens)==len(closes)==2 and closes[0]<opens[1],issues,'Fresh connection opened only after first close')
        phases, phase_issues = parse_phase_lines([x for x in lines if x.startswith('compiler work: ')])
        issues.extend(phase_issues)
        checked(all(phases.get(p,{}).get('budget')==b for p,b in BUDGETS.items()),issues,'Reviewed phase budgets unchanged')
        actual_values = [x.removeprefix('value: ') for x in lines if x.startswith('value: ')]
        actual_types = [x.removeprefix('type: ') for x in lines if x.startswith('type: ')]
        run.update(values=actual_values, types=actual_types, expected_value=value, expected_type=ty, events=events, copies=copies, phase_numbers=phases,
                   native_call_counts={op:len(re.findall(r'Call \{ operation: "'+re.escape(op)+r'",',stdout))
                                       for op in sorted(set(re.findall(r'Call \{ operation: "([^"]+)"',stdout)))},
                   binary_sha256=sha(binary), issues=issues)
        receipt['runs'].append(run)
        save()
        print(name, 'PASS' if not issues else issues, flush=True)
    checked((owned/'session.sqlite3').is_file(), receipt.setdefault('issues',[]),'Persistent source-created SQLite database exists')
    fixtures = repo / 'tests/fixtures/provider-experiments/arena-typed'
    for entry, (value,ty,expected_trace) in arena.items():
        name = 'arena-' + entry.replace('/','-')
        binary = target / 'debug/examples/arena_typed'
        command = [str(binary),str(fixtures/entry)]
        if entry.startswith('composition-cases/'):
            command += ['--root','arena_cases',str(fixtures)]
        run,stdout,stderr = capture(name,command,repo,A.host_timeout)
        issues = []
        checked(run['exit_code']==0,issues,'Host exit must be zero')
        stdout_lines, all_lines = stdout.splitlines(), stdout.splitlines()+stderr.splitlines()
        checked([x for x in stdout_lines if not x.startswith(('type: ','retained owners: '))]==[value],issues,'Exact source value')
        reported_types = [x for x in all_lines if x.startswith('type: ')]
        checked(not reported_types or reported_types==['type: '+ty],issues,'Optional type report must match')
        retained = [x for x in all_lines if x.startswith('retained owners: ')]
        if retained: checked(retained==['retained owners: 0'],issues,'Zero retained owners')
        events = [x for x in all_lines if re.match(r'^(Acquired|Stored|Loaded|Released|Usage|AllocationRefused) \{',x)]
        trace, trace_issues = arena_trace(events)
        issues.extend(trace_issues)
        checked(trace==expected_trace,issues,'Exact public-suite native trace')
        cost_lines = [x for x in all_lines if x.startswith('CompilationWork {')]
        checked(len(cost_lines)==1,issues,'Single complete compilation work report')
        matches = re.findall(r'PhaseCost \{ completed: (true|false), phase: (SourceChecking|FinalElaboration|IndependentCore), used: (\d+) \}', '\n'.join(cost_lines))
        phases = {}
        checked(len(matches)==3 and {p for _,p,_ in matches}==set(BUDGETS),issues,'Three distinct observed compilation phases')
        for completed,phase,used in matches:
            used, budget = int(used), BUDGETS[phase]
            deficit = max(0,used-budget)
            checked(completed=='true' and used<=budget+budget//10,issues,phase+' completion/allowance')
            classification = 'WithinBudget' if not deficit else ('AcceptedDeficit' if used<=budget+budget//10 else 'OutsideAllowance')
            phases[phase] = {'completed':completed=='true','used':used,'budget':budget,'hard_limit':budget+budget//10,
                             'deficit_units':deficit,'assessment':classification,
                             'optimization_target':classification=='AcceptedDeficit'}
        actual_values = [x for x in stdout_lines if not x.startswith(('type: ','retained owners: '))]
        actual_types = [x.removeprefix('type: ') for x in all_lines if x.startswith('type: ')]
        run.update(values=actual_values,types=actual_types,expected_value=value,expected_type=ty,events=events,normalized_trace=trace,
                   expected_trace=expected_trace,native_event_counts={kind:sum(x.startswith(kind+' {') for x in events)
                                                                    for kind in ['Acquired','Stored','Loaded','Released']},
                   phase_numbers=phases,phase_assessment_origin='Runner assessment of observed host completed phase costs against reviewed unchanged budgets',
                   binary_sha256=sha(binary),issues=issues)
        receipt['runs'].append(run)
        save()
        print(name,'PASS' if not issues else issues,flush=True)
else:
    receipt.setdefault('issues',[]).append('Final packaged hosts not run because example build failed')
receipt['source_after'] = source_pins()
receipt['post_head'] = git_head()
receipt['changed_source_paths'] = sorted(p for p in set(receipt['source_before'])|set(receipt['source_after'])
                                         if receipt['source_before'].get(p)!=receipt['source_after'].get(p))
checked(not receipt['changed_source_paths'],receipt.setdefault('issues',[]),'Source hashes changed during final host window')
checked(receipt['head']==receipt['post_head'],receipt['issues'],'HEAD changed during final host window')
checked(len(receipt['runs'])==6,receipt['issues'],'All six established packaged hosts must run')
receipt['completed'] = True
receipt['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
receipt['passed'] = not receipt['issues'] and all(not r['issues'] for r in receipt['runs'])
save()
raise SystemExit(0 if receipt['passed'] else 1)
