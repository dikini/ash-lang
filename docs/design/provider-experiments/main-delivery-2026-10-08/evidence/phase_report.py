"""Parse bounded compiler phase reports without running the compiler or host."""
import re
PHASES = {'SourceChecking', 'FinalElaboration', 'IndependentCore'}
ROW = re.compile(r'compiler work: (SourceChecking|FinalElaboration|IndependentCore) used=(\d+) budget=(\d+) hard_limit=(\d+) completed=(true|false) assessment=(WithinBudget|AcceptedDeficit \{ units: \d+ \}|OutsideAllowance \{ units: \d+ \}) optimization_target=(true|false)')
def parse_phase_lines(lines):
    records, issues = {}, []
    for line in lines:
        match = ROW.fullmatch(line)
        if not match:
            issues.append('Malformed or unobserved phase report: ' + line)
            continue
        phase, used, budget, hard, completed, assessment, target = match.groups()
        used, budget, hard = int(used), int(budget), int(hard)
        if phase in records: issues.append('Duplicate phase: ' + phase)
        deficit = max(0, used-budget)
        target = target == 'true'
        label = assessment.split(' ')[0]
        units = re.search(r'units: (\d+)', assessment)
        reported_units = int(units.group(1)) if units else 0
        if hard != budget + budget//10: issues.append('Invalid finite10% hard limit: ' + phase)
        if completed != 'true': issues.append('Incomplete phase: ' + phase)
        if label == 'WithinBudget':
            if used > budget or target: issues.append('Inconsistent WithinBudget report: ' + phase)
        elif label == 'AcceptedDeficit':
            if not (0 < deficit <= budget//10 and used <= hard and reported_units == deficit and target):
                issues.append('Inconsistent or excessive AcceptedDeficit: ' + phase)
        else:
            issues.append('OutsideAllowance: ' + phase)
        records[phase] = {'used':used,'budget':budget,'hard_limit':hard,'completed':completed=='true',
            'assessment':label,'deficit_units':deficit,'reported_deficit_units':reported_units,
            'optimization_target':target,'future_optimization_target':label=='AcceptedDeficit'}
    if len(lines) != 3 or set(records) != PHASES:
        issues.append('Three distinct completed phase reports required')
    return records, issues
