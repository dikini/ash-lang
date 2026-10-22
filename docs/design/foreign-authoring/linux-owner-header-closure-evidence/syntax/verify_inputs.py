"""Read-only known-input verification; all discovered header inputs are frozen for syntax-only."""
from pathlib import Path
import hashlib,json,os,stat,sys
R=Path(__file__).parent

def read(p,n):
    with p.open('rb') as f:b=f.read(n+1)
    if len(b)>n:raise SystemExit('record exceeds bound')
    return b
spec=json.loads(read(R/'preflight-inputs.json',262144))
if not(sys.flags.isolated and sys.flags.no_site and sys.flags.ignore_environment) or dict(os.environ)!=spec['outer_environment']:raise SystemExit('isolated exact environment required')
for row in spec['pins']:
    p=Path(row['path'])
    if not p.is_file() or str(p.resolve())!=row['resolved'] or p.stat().st_size!=row['size']:raise SystemExit('input association differs: '+str(p))
    h=hashlib.sha256();n=0
    with p.open('rb') as f:
        before=os.fstat(f.fileno())
        while b:=f.read(min(65536,row['size']-n+1)):
            n+=len(b)
            if n>row['size']:raise SystemExit('input grew')
            h.update(b)
        after=os.fstat(f.fileno())
    if n!=row['size'] or h.hexdigest()!=row['sha256'] or (before.st_dev,before.st_ino,before.st_size,before.st_mtime_ns)!=(after.st_dev,after.st_ino,after.st_size,after.st_mtime_ns):raise SystemExit('input bytes differ: '+str(p))
for p in map(Path,spec['absence_paths']):
    if p.exists() or p.is_symlink():raise SystemExit('unfrozen specs/helper/include path appeared: '+str(p))
for row in spec['directories']:
    p=Path(row['path']);s=p.stat()
    if str(p.resolve())!=row['resolved'] or not stat.S_ISDIR(s.st_mode) or (s.st_dev,s.st_ino,s.st_uid)!=(row['device'],row['inode'],row['uid']):raise SystemExit('directory association differs')
    if row['private'] and (s.st_uid!=os.geteuid() or s.st_mode&0o077):raise SystemExit('private query directory differs')
phase=sys.argv[1] if len(sys.argv)==2 else 'preparation-readback'
if phase not in ['preparation-readback','before-syntax','after-syntax']:raise SystemExit('unknown phase')
if phase in ['preparation-readback','before-syntax'] and any((R/n).exists() for n in ['native-build.log','syntax-manifest.json','syntax-receipt.json']):raise SystemExit('query outputs already exist')
print(json.dumps({'phase':phase,'known_pins_equal':True,'known_pin_count':len(spec['pins']),'frozen_dependency_count':len(spec['frozen_dependency_paths']),'all_frozen_headers_equal':True,'syntax_run_by_verifier':False}))
