"""Read-only selected-producer equality check; never builds or executes images."""
import hashlib
import json
from pathlib import Path
ROOT = Path('/tmp/ash-owner-build-snapshot-1a8ecef0')
manifest = json.loads((ROOT/'archive-manifest.json').read_text())
source = ROOT/'source'
actual = {str(p.relative_to(source)) for p in source.rglob('*') if p.is_file()}
expected = {item['path'] for item in manifest['entries']}
if actual != expected:
    raise SystemExit('source path set mismatch')
for item in manifest['entries']:
    path = source/item['path']
    digest = hashlib.sha256()
    git_digest = hashlib.sha1(b'blob '+str(path.stat().st_size).encode()+b'\0')
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(65536), b''):
            digest.update(block); git_digest.update(block)
    if path.stat().st_size != item['size'] or digest.hexdigest() != item['sha256'] or git_digest.hexdigest() != item['git_blob']:
        raise SystemExit('producer mismatch: '+item['path'])
print(json.dumps({'commit':manifest['commit'],'tree':manifest['tree'],'files':len(expected),'all_full_file_hashes_equal':True}))
