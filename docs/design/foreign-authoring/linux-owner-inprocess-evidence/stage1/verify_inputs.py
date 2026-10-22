"""Read-only phase verifier. Does not build, spawn children or execute images."""
import hashlib
import json
import os
from pathlib import Path
import stat
import sys
ROOT = Path(__file__).parent
spec = json.loads((ROOT/'preflight-inputs.json').read_text())
if not (sys.flags.isolated and sys.flags.no_site and sys.flags.ignore_environment):
    raise SystemExit('isolated Python startup required')
if dict(os.environ) != spec['outer_environment']:
    raise SystemExit('outer environment differs from reviewed exact map')
def digest(path, prefix=b''):
    value = hashlib.sha256(prefix)
    with path.open('rb') as stream:
        for block in iter(lambda:stream.read(65536), b''):
            value.update(block)
    return value.hexdigest()
def check_pin(pin):
    path = Path(pin['path'])
    if not path.is_file() or str(path.resolve()) != pin['resolved']:
        raise SystemExit('input path association mismatch: '+str(path))
    if path.stat().st_size != pin['size'] or digest(path) != pin['sha256']:
        raise SystemExit('input size/hash mismatch: '+str(path))
for pin in spec['pins']:
    check_pin(pin)
for pin in json.loads(Path(spec['tool_native_manifest']).read_text())['files']:
    check_pin(pin)
linker = json.loads((ROOT/'default-linker-inputs.json').read_text())
for pin in linker['files']:
    check_pin(pin)
    for link in pin['symlink_chain']:
        if not Path(link['path']).is_symlink() or os.readlink(link['path']) != link['target']:
            raise SystemExit('linker lookup chain mismatch: '+link['path'])
if Path(linker['absent_earlier_PATH_cc']).exists():
    raise SystemExit('earlier PATH cc appeared')
for text in spec['private_directories']:
    path = Path(text); info = path.stat()
    if str(path.resolve()) != str(path) or info.st_uid != os.geteuid() or not stat.S_ISDIR(info.st_mode) or info.st_mode & 0o077:
        raise SystemExit('private directory premise mismatch: '+text)
for text in spec['cargo_config_absence_paths']:
    if Path(text).exists() or Path(text).is_symlink():
        raise SystemExit('unfrozen Cargo configuration appeared: '+text)
if not Path(spec['shared_cache']).is_dir():
    raise SystemExit('existing shared cache absent')
manifest = json.loads(Path(spec['snapshot_manifest']).read_text())
source = Path(spec['source_root'])
files = {str(p.relative_to(source)):p for p in source.rglob('*') if p.is_file() or p.is_symlink()}
if set(files) != {item['path'] for item in manifest['entries']}:
    raise SystemExit('producer path-set mismatch')
for item in manifest['entries']:
    path = files[item['path']]
    if path.is_symlink() or path.stat().st_size != item['size'] or digest(path) != item['sha256']:
        raise SystemExit('producer bytes mismatch: '+item['path'])
    if bool(path.stat().st_mode & 0o111) != (item['git_mode']=='100755'):
        raise SystemExit('producer executable mode mismatch: '+item['path'])
    value = hashlib.sha1(b'blob '+str(item['size']).encode()+b'\0')
    with path.open('rb') as stream:
        for block in iter(lambda:stream.read(65536),b''):value.update(block)
    if value.hexdigest() != item['git_blob']:
        raise SystemExit('producer Git blob mismatch: '+item['path'])
phase = sys.argv[1] if len(sys.argv)==2 else 'preparation-readback'
if phase not in ('preparation-readback','before-compiler','after-compiler'):
    raise SystemExit('unknown readback phase')
print(json.dumps({'phase':phase,'source_files':len(files),'source_bytes':sum(x['size'] for x in manifest['entries']),'commit':manifest['commit'],'tree':manifest['tree'],'all_source_tool_native_config_pins_equal':True,'source_is_hash_frozen_not_hostile_writer_containment':True}))
