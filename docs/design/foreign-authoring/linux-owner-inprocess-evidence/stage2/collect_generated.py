"""Passive post-build collector. Never executes generated host or native input."""
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import sys
import tomllib
ROOT=Path(__file__).parent
OUT=ROOT/'experiment'
SOURCE=Path('/tmp/ash-owner-build-snapshot-1a8ecef0/source')
EXPECTED='6ed612090a3fadfbcc982c0cf41b210cb02e2d01af7db5a5958e63a6fc527a47'
def require(ok,why):
    if not ok:raise SystemExit(why)
def bounded(path,limit):
    with path.open('rb') as f:data=f.read(limit+1)
    require(len(data)<=limit,'record exceeds bound: '+str(path));return data
def observe(path):
    require(not path.is_symlink(),'symlink output: '+str(path))
    with path.open('rb') as f:
        before=os.fstat(f.fileno());require(stat.S_ISREG(before.st_mode),'nonregular output')
        digest=hashlib.sha256();total=0
        while total<before.st_size:
            block=f.read(min(65536,before.st_size-total))
            if not block:break
            digest.update(block);total+=len(block)
        require(not f.read(1),'output grew during hash');after=os.fstat(f.fileno())
    require(total==before.st_size and (before.st_dev,before.st_ino,before.st_size,before.st_mtime_ns)==(after.st_dev,after.st_ino,after.st_size,after.st_mtime_ns),'output changed during hash')
    return {'path':str(path),'size':total,'sha256':digest.hexdigest(),'device':after.st_dev,'inode':after.st_ino}
spec=json.loads(bounded(ROOT/'preflight-inputs.json',262144))
require(sys.flags.isolated and sys.flags.no_site and dict(os.environ)==spec['outer_environment'],'isolated exact outer context required')
require(len(sys.argv)==2,'monitor response path required')
response=json.loads(bounded(Path(sys.argv[1]),262144));receipt_path=Path(response['receipt'])
require(receipt_path.parent.parent==OUT,'unexpected receipt location')
r=json.loads(bounded(receipt_path,4194304))
require(r['monitor']['sha256']=='14aae43130d74022568e849ca83b912aa63b9572fa971d0963a2a46c39347e60','monitor source differs')
require(r['config_sha256']==hashlib.sha256(bounded(ROOT/'generation.monitor.json',262144)).hexdigest(),'config association differs')
require(r['reason']=='exit' and r['child_exit']==0 and r['cleanup']['all_children_reaped'] and not r['cleanup']['remaining_children'] and not r.get('final_limit_failures'),'generation did not complete cleanly')
raw=bounded(Path(r['output_path']),16777216)
require(hashlib.sha256(raw).hexdigest()==r['output_file']['sha256'],'output association differs')
require(raw.decode().splitlines()==[str(OUT/'ordinary-host')],'unexpected successful build output')
projects=list((OUT/'.ash-build').iterdir());require(len(projects)==1 and projects[0].is_dir() and not projects[0].is_symlink(),'one genuine generated project required')
project=projects[0];data=tomllib.loads(bounded(project/'Cargo.toml',1048576).decode());name=data['package']['name']
require(name==project.name,'generated package/path differs')
require(data['dependencies']['ash']['path']==str(SOURCE),'generated runtime source differs')
require(data['dependencies']['ash'].get('features')==[],'unexpected runtime features')
require(bounded(project/'rust-toolchain.toml',1048576)==bounded(SOURCE/'rust-toolchain.toml',1048576),'toolchain seed differs')
main=bounded(project/'src/main.rs',1048576).decode();match=re.search(r'const RUNTIME_FINGERPRINT: \[u8; 32\] = \[([^]]+)\]',main)
require(match is not None,'generated runtime fingerprint missing')
values=re.findall(r'0x([0-9a-f]{2})',match.group(1));require(len(values)==32 and ''.join(values)==EXPECTED,'generated runtime fingerprint differs')
require('include_bytes!("program-image.bin")' in main and 'include_bytes!("expected-facts.bin")' in main,'private payload embedding differs')
require('malloc' in main and 'free' in main,'baseline native names missing; source mapping inspection required')
seed=tomllib.loads(bounded(ROOT/'selected-Cargo.lock.seed',1048576).decode());post=tomllib.loads(bounded(project/'Cargo.lock',1048576).decode())
def key(row):return (row['name'],row['version'],row.get('source'),row.get('checksum'))
seedkeys={key(row) for row in seed['package']}
for row in post['package']:
    require(key(row) in seedkeys or (row['name']==name and row['version']=='0.0.0' and 'source' not in row),'unfrozen resolved package: '+row['name'])
require((SOURCE/'Cargo.lock').read_bytes()==(ROOT/'selected-Cargo.lock.seed').read_bytes(),'selected lock seed changed')
files=[]
for path in sorted(project.rglob('*')):
    require(not path.is_symlink(),'generated symlink refused')
    if path.is_file():
        require(len(files)<4096,'generated manifest entry limit')
        if path.suffix in ('.rs','.toml','.lock'):require(path.stat().st_size<=1048576,'generated text exceeds1MiB')
        if path.name=='native-build.log':require(path.stat().st_size<=16777216,'generated build log exceeds16MiB')
        files.append(observe(path))
require({str(Path(row['path']).relative_to(project)) for row in files}=={'src/main.rs','src/program-image.bin','src/expected-facts.bin','Cargo.toml','Cargo.lock','rust-toolchain.toml','native-build.log'},'unknown generated project record set')
require(not (project/'linked-program').exists(),'generated staging output still present')
ordinary=observe(OUT/'ordinary-host')
require(not Path('/home/dikini/Projects/ash-lang/.worktree/generic-cells/target/x86_64-unknown-linux-gnu/debug',name).exists(),'generated root executable not retired')
manifest={'project':str(project),'package_name':name,'files':files,'ordinary_host':ordinary,'ordinary_host_is_not_final_static_image':True}
encoded=(json.dumps(manifest,indent=2)+'\n').encode();require(len(encoded)<=4194304,'manifest exceeds4MiB')
path=ROOT/'generated-manifest.json';require(not path.exists(),'refuse overwriting generation evidence');path.write_bytes(encoded)
compiler=observe(Path('/home/dikini/Projects/ash-lang/.worktree/generic-cells/target/debug/ash'))
require(compiler['sha256']=='5dca1b624bf206c44c6c4d3037675193800516eb936a0cf6420e67394e998d3e','compiler changed before receipt')
receipt={'kind':'existing-profile-owner-packaging-generation-only','selected_source_commit':'1a8ecef0b03ddc75a45254543bd8f6f0bb10969c','contract_retained_commit':'2ac8c393846715249de5a475a65e47bf1309bb54','contract_sha256':'27430b69ee44dcbcb835a83dc38ff2b034826b81dddae40b7bb9ba7b4377cc3e','compiler':compiler,'runtime_fingerprint':EXPECTED,'generated_manifest':observe(path),'monitor_receipt':observe(receipt_path),'lock_seed':observe(ROOT/'selected-Cargo.lock.seed'),'lock_seed_qualification':'Pinned selected compiler embedded-write input, NOT an independently captured generated pre-Cargo lock. Generated lock is observed post-resolution only.','post_resolution_lock':observe(project/'Cargo.lock'),'source_inputs':[observe(OUT/'owner.ash'),observe(OUT/'entry.ash')],'native_archive':observe(Path('/usr/lib/x86_64-linux-gnu/libc.a')),'whole_static_candidate':False,'owner_image_executed':False,'remaining':'Bridge/private payload/source mapping still needs independent inspection; no checked runtime/O-K/copy or ownerful architecture/startup approval. Stop before separately assigned static relink.'}
encoded=(json.dumps(receipt,indent=2)+'\n').encode();require(len(encoded)<=262144,'producer receipt exceeds256KiB');sys.stdout.buffer.write(encoded)
