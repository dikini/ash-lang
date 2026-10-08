#!/usr/bin/env python3
"""Validate actual captured arena host output; never executes a host."""
import argparse, hashlib, json, pathlib, re
p = argparse.ArgumentParser()
p.add_argument('--evidence', type=pathlib.Path, required=True)
a = p.parse_args()
r = json.loads((a.evidence / 'receipt.json').read_text())
assert r['completed'] and r['exit_code'] == 0 and r['head'] == r['post_head']
assert not r['changed_source_paths'] and r['drafts_unchanged']
log = (a.evidence / 'output.log').read_text()
assert hashlib.sha256((a.evidence / 'output.log').read_bytes()).hexdigest() == r['output_sha256']
events = [x for x in log.splitlines() if x.startswith(('Acquired {', 'Stored {', 'Loaded {', 'Released {'))]
expected = [
 'Acquired { activation: 0, usage: Usage { used_payload_bytes: 0, payload_capacity: 8, object_count: 0, object_capacity: 1 } }',
 'Stored { activation: 0, allocation: AllocationKey { owner: 1, object: 1 }, layout: PayloadLayout { tag: LayoutTag(3), size: 8, alignment: 8 }, usage: Usage { used_payload_bytes: 8, payload_capacity: 8, object_count: 1, object_capacity: 1 } }',
 'Loaded { activation: 0, allocation: AllocationKey { owner: 1, object: 1 }, layout: LayoutTag(3), bytes_read: 8, usage: Usage { used_payload_bytes: 8, payload_capacity: 8, object_count: 1, object_capacity: 1 } }',
 'Released { activation: 0, host_teardown: false }',
]
assert events == expected, events
assert log.splitlines().count('Completed(41, Closed)') == 1
cost_lines = [x for x in log.splitlines() if x.startswith('CompilationWork {')]
assert len(cost_lines) == 1
matches = re.findall(r'PhaseCost \{ completed: (true|false), phase: (SourceChecking|FinalElaboration|IndependentCore), used: (\d+) \}', cost_lines[0])
budgets = {'SourceChecking': 1245184, 'FinalElaboration': 393216, 'IndependentCore': 1638400}
assert len(matches) == 3 and {x[1] for x in matches} == set(budgets)
costs = {}
for completed, phase, used in matches:
    used = int(used); budget = budgets[phase]; deficit = max(0, used-budget)
    assert completed == 'true' and used <= budget + budget//10
    costs[phase] = {'completed': True, 'used': used, 'budget': budget,
                    'hard_limit': budget+budget//10, 'deficit_units': deficit,
                    'assessment': 'AcceptedDeficit' if deficit else 'WithinBudget',
                    'optimization_target': bool(deficit)}
result = {'passed': True, 'head': r['head'], 'value': 'Completed(41, Closed)',
          'events': events, 'phase_numbers': costs,
          'assessment_origin': 'Root assessment of the host raw completed phase costs against reviewed source budgets; not an extra host observation'}
target = a.evidence / 'validated-native-and-costs.json'
with target.open('x') as f: json.dump(result, f, indent=2); f.write('\n')
print(json.dumps(result, indent=2))
