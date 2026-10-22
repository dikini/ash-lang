"""Post-success Cargo/source association gate; never executes the compiler."""
import hashlib
import json
from pathlib import Path
import re
import stat
import sys
import os
ROOT=Path(__file__).parent
SOURCE=Path('/tmp/ash-owner-build-snapshot-1a8ecef0/source')
CACHE=Path('/home/dikini/Projects/ash-lang/.worktree/generic-cells/target')
def bounded(path, limit):
    with path.open('rb') as stream:data=stream.read(limit+1)
    if len(data)>limit:raise SystemExit('correspondence record exceeds bound: '+str(path))
    return data
def sha(data):return hashlib.sha256(data).hexdigest()
def require(condition, reason):
    if not condition:raise SystemExit(reason)
require(len(sys.argv)==2,'monitor response path required')
response=json.loads(bounded(Path(sys.argv[1]),262144));receipt_path=Path(response['receipt'])
require(receipt_path.parent.parent==ROOT/'run-output','unexpected monitor receipt path')
receipt=json.loads(bounded(receipt_path,4194304))
require(receipt['config_sha256']==sha(bounded(ROOT/'compiler-build.monitor.json',262144)),'monitor config differs')
require(receipt['monitor']['sha256']=='14aae43130d74022568e849ca83b912aa63b9572fa971d0963a2a46c39347e60','monitor source differs')
require(receipt['reason']=='exit' and receipt['child_exit']==0 and receipt['cleanup']['all_children_reaped'] and not receipt['cleanup']['remaining_children'] and not receipt.get('final_limit_failures'),'compiler monitor did not succeed cleanly')
raw=bounded(Path(receipt['output_path']),16777216)
require(sha(raw)==receipt['output_file']['sha256'],'output association differs')
text=raw.decode('utf8'); messages=[]
for line in text.splitlines():
    try:item=json.loads(line)
    except ValueError:continue
    if isinstance(item,dict):messages.append(item)
require(any(m.get('reason')=='build-finished' and m.get('success') is True for m in messages),'Cargo success message missing')
selected=[m for m in messages if m.get('reason')=='compiler-artifact' and m.get('manifest_path')==str(SOURCE/'Cargo.toml')]
artifacts={}
for kind, src in [('bin','main.rs'),('lib','lib.rs')]:
    rows=[m for m in selected if m['target']['name']=='ash' and kind in m['target']['kind'] and m['target']['src_path']==str(SOURCE/'src'/src)]
    require(len(rows)==1,'unique selected-source '+kind+' artifact required')
    row=rows[0];require(row.get('fresh') is False,'selected-source '+kind+' unexpectedly fresh; stop for review')
    require(row['profile'].get('test') is False,'test artifact is not compiler')
    artifacts[kind]=row
require(artifacts['lib']['package_id']==artifacts['bin']['package_id'],'selected package identities differ')
require(artifacts['bin']['executable']==str(CACHE/'debug/ash'),'unexpected compiler executable')
package=artifacts['bin']['package_id']
builds=[m for m in messages if m.get('reason')=='build-script-executed' and m.get('package_id')==package]
require(len(builds)==1,'selected build-script record required')
build=builds[0];env=dict(build['env']);fingerprint=env.get('ASH_RUNTIME_FINGERPRINT','')
require(bool(re.fullmatch('[0-9a-f]{64}',fingerprint)),'actual runtime fingerprint missing')
require(env.get('ASH_RUNTIME_CARGO_PROFILE')=='debug' and env.get('ASH_RUNTIME_OPT_LEVEL')=='0','unexpected producer profile')
out_dir=Path(build['out_dir']);require(out_dir.is_relative_to(CACHE/'debug/build') and out_dir.name=='out','unexpected build-script outdir')
script_output=bounded(out_dir.parent/'output',1048576)
require(('cargo:rustc-env=ASH_RUNTIME_FINGERPRINT='+fingerprint).encode() in script_output,'build-script fingerprint output mismatch')
dep=bounded(CACHE/'debug/ash.d',1048576)
for path in [SOURCE/'Cargo.toml',SOURCE/'build.rs',SOURCE/'src/main.rs',SOURCE/'src/lib.rs']:
    require(str(path).encode() in dep,'selected dep-info missing '+str(path))
require(b'/home/dikini/Projects/ash-lang/.worktree/checked-ffi/' not in dep,'cached Borrow dep-info remains')
retain=ROOT/'compiler-correspondence';retain.mkdir(mode=0o700,exist_ok=False)
records=[]
def save(name,path,data):
    (retain/name).write_bytes(data);records.append({'original_path':str(path),'retained_path':str(retain/name),'size':len(data),'sha256':sha(data)})
save('compiler.d',CACHE/'debug/ash.d',dep);save('build-script-output.txt',out_dir.parent/'output',script_output)
for kind,source_name in [('bin','main.rs'),('lib','lib.rs')]:
    lines=[line for line in text.splitlines() if 'Running `' in line and '--crate-name ash ' in line and ('src/'+source_name) in line]
    require(len(lines)==1,'unique selected '+kind+' rustc command required')
    match=re.search(r'extra-filename=-([0-9a-f]{16})',lines[0]);require(match is not None,'Cargo fingerprint directory association missing')
    path=CACHE/'debug/.fingerprint'/('ash-'+match.group(1))/(kind+'-ash.json')
    data=bounded(path,1048576);json.loads(data);save(kind+'-ash.json',path,data)
path=out_dir.parent/'output'
( retain/'cargo-selected-records.json').write_text(json.dumps({'artifacts':artifacts,'build_script':build,'fingerprint':fingerprint},indent=2)+'\n')
path=CACHE/'debug/ash';require(not path.is_symlink(),'unexpected compiler symlink')
with path.open('rb') as stream:
    before=os.fstat(stream.fileno());require(stat.S_ISREG(before.st_mode),'compiler not regular');digest=hashlib.sha256();size=0
    for block in iter(lambda:stream.read(65536),b''):size+=len(block);digest.update(block)
    after=os.fstat(stream.fileno())
require((before.st_dev,before.st_ino,before.st_size,before.st_mtime_ns)==(after.st_dev,after.st_ino,after.st_size,after.st_mtime_ns) and size==after.st_size,'compiler changed during observation')
print(json.dumps({'path':str(path),'size':size,'sha256':digest.hexdigest(),'selected_manifest':str(SOURCE/'Cargo.toml'),'package_id':package,'actual_runtime_fingerprint':fingerprint,'selected_cargo_artifacts':artifacts,'retained_correspondence':records,'qualification':'Trusted normal Cargo artifact/dep-info/fingerprint correspondence after fresh selected-source compilation; not formal compiler correctness or foreign startup approval.'}))
