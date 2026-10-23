"""Verify retained evidence bytes; never imports product code or executes outputs."""
from pathlib import Path
import argparse, gzip, hashlib, json
ROOT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--external', action='store_true')
args = parser.parse_args()
sha = lambda b: hashlib.sha256(b).hexdigest()
full = lambda v: (json.dumps(v, indent=2) + '\n').encode()
index = json.loads((ROOT / 'map-index.json').read_text())
resolved = {}
active = set()
def source_map(key):
    if key not in resolved:
        assert key not in active
        active.add(key)
        meta = index[key]
        value = json.loads(gzip.decompress((ROOT / meta['blob']).read_bytes()))
        if meta['encoding'] == 'json-map-delta':
            base = source_map(meta['base']).copy()
            for name in value['removed']:
                del base[name]
            base.update(value['changed'])
            value = dict(sorted(base.items()))
        else:
            assert meta['encoding'] == 'gzip'
        data = full(value)
        assert len(data) == meta['bytes'] and sha(data) == key
        assert len(value) == meta['entries']
        resolved[key] = value
        active.remove(key)
    return resolved[key]
def restore(value):
    if isinstance(value, dict):
        if set(value) == {'$retained_map'}:
            return source_map(value['$retained_map'])
        return {name: restore(item) for name, item in value.items()}
    if isinstance(value, list):
        return [restore(item) for item in value]
    return value
records = json.loads((ROOT / 'provenance.json').read_text())
known = {}
for row in records:
    data = gzip.decompress((ROOT / row['retained_as']).read_bytes())
    if row['encoding'] == 'json-map-template':
        data = full(restore(json.loads(data)))
    else:
        assert row['encoding'] == 'gzip'
    assert len(data) == row['original']['bytes']
    assert sha(data) == row['original']['sha256']
    if args.external:
        assert data == Path(row['original_path']).read_bytes()
    known[(row['original']['sha256'], row['retained_as'])] = True
associations = json.loads((ROOT / 'execution-associations.json').read_text())
for row in associations:
    if row['retained_as']:
        assert (row['original']['sha256'], row['retained_as']) in known
    else:
        assert row.get('omission')
manifest = json.loads((ROOT / 'manifest.json').read_text())
actual = {str(path.relative_to(ROOT)) for path in ROOT.rglob('*') if path.is_file() and path.name != 'manifest.json'}
assert actual == {row['path'] for row in manifest['files']}
for row in manifest['files']:
    data = (ROOT / row['path']).read_bytes()
    assert len(data) == row['bytes'] and sha(data) == row['sha256']
print(json.dumps({'payload_files': len(actual), 'provenance': len(records), 'source_maps': len(resolved), 'execution_associations': len(associations), 'external': args.external}))
