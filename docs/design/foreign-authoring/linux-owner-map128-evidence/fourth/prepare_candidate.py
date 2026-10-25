"""Bounded passive static-image collection; no candidate is executed."""
import hashlib
import json
import os
from pathlib import Path
import stat
import struct
import sys
ROOT=Path(__file__).parent
CACHE=Path('/home/dikini/Projects/ash-lang/.worktree/generic-cells/target')
IMAGE_LIMIT=134217728
MONITOR=Path('/tmp/ash-owner-map-class-monitor/build_monitor.py')
def need(ok,why):
    if not ok:raise SystemExit(why)
def read(path,limit):
    with path.open('rb') as f:data=f.read(limit+1)
    need(len(data)<=limit,'record too large: '+str(path));return data
def digest(path):
    need(not path.is_symlink(),'symlink refused: '+str(path))
    with path.open('rb') as f:
        before=os.fstat(f.fileno());need(stat.S_ISREG(before.st_mode),'nonregular hash input')
        h=hashlib.sha256();total=0
        while total<before.st_size:
            block=f.read(min(65536,before.st_size-total))
            if not block:break
            h.update(block);total+=len(block)
        need(not f.read(1),'input grew while hashing');after=os.fstat(f.fileno())
    need(total==before.st_size and (before.st_dev,before.st_ino,before.st_size,before.st_mtime_ns)==(after.st_dev,after.st_ino,after.st_size,after.st_mtime_ns),'hash input changed')
    return {'path':str(path),'size':total,'sha256':h.hexdigest()}
spec=json.loads(read(ROOT/'preflight-inputs.json',262144));outer=spec['outer_environment']
need(sys.flags.isolated and sys.flags.no_site and dict(os.environ)==outer,'isolated exact environment required')
need(len(sys.argv)==2,'relink response required');response=json.loads(read(Path(sys.argv[1]),262144));receipt_path=Path(response['receipt']);need(receipt_path.parent.parent==ROOT,'unexpected relink receipt')
r=json.loads(read(receipt_path,4194304));need(r['config_sha256']==hashlib.sha256(read(ROOT/'relink.monitor.json',262144)).hexdigest(),'relink config association differs')
need(r['monitor']['sha256']=='b36fbefca8bdec200da79d01c36dc0c90039f948e6e0ca26c5d3d5cab17606a0','monitor differs')
need(r['schema']==2 and r['map_relative_path']=='whole-static.map','wrong map monitor schema/path')
need(r['limits']=={'deadline_seconds':1200,'output_bytes':16777216,'sidefile_bytes':16777216,'map_bytes':67108864},'map/log limit split differs')
need(r['reason']=='exit' and r['child_exit']==0 and r['cleanup']['all_children_reaped'] and not r['cleanup']['remaining_children'] and not r['cleanup']['escaped_group_detected'] and not r['cleanup']['reaping_pending'] and not r.get('final_limit_failures') and not r['output_truncated'],'relink did not succeed cleanly')
raw=read(Path(r['output_path']),16777216)
need(hashlib.sha256(raw).hexdigest()==r['output_file']['sha256'],'relink raw output differs')
messages=[]
for line in raw.decode('utf8').splitlines():
    try:row=json.loads(line)
    except ValueError:continue
    if isinstance(row,dict):messages.append(row)
need(any(x.get('reason')=='build-finished' and x.get('success') is True for x in messages),'Cargo build-finished success absent')
project=Path('/tmp/ash-owner-generation-stage2/experiment/.ash-build/ash-host-6-0')
artifacts=[x for x in messages if x.get('reason')=='compiler-artifact' and x.get('manifest_path')==str(project/'Cargo.toml') and x.get('target',{}).get('name')=='ash-host-6-0' and x.get('target',{}).get('src_path')==str(project/'src/main.rs') and 'bin' in x.get('target',{}).get('kind',[])]
need(len(artifacts)==1 and artifacts[0].get('fresh') is False,'fresh actual selected root Cargo artifact required')
need(artifacts[0]['executable']==str(CACHE/'x86_64-unknown-linux-gnu/debug/ash-host-6-0'),'root artifact output association differs')
linked=CACHE/'x86_64-unknown-linux-gnu/debug/ash-host-6-0'
need(linked.stat().st_size<=IMAGE_LIMIT,'final static image exceeds128MiB')
source=digest(linked);candidate=ROOT/'static-host';need(not candidate.exists(),'refuse existing candidate')
with linked.open('rb') as src,candidate.open('xb') as dst:
    total=0
    for block in iter(lambda:src.read(65536),b''):
        total+=len(block);need(total<=IMAGE_LIMIT,'candidate grew over128MiB');dst.write(block)
os.chmod(candidate,0o400)
final=digest(candidate);need(final['size']==source['size'] and final['sha256']==source['sha256'],'candidate copy differs')
with candidate.open('rb') as f:
    header=f.read(64);need(len(header)==64 and header[:7]==b'\x7fELF\x02\x01\x01','ELF64 LE version1 required')
    fields=struct.unpack('<16sHHIQQQIHHHHHH',header)
    _,kind,machine,version,entry,phoff,shoff,flags,ehsize,phsize,phnum,shsize,shnum,shstr=fields
    need(kind==2 and machine==62 and version==1 and ehsize==64,'x86-64 ET_EXEC required')
    need(phsize==56 and 0<phnum<=64 and phoff+phnum*56<=final['size'],'invalid/bounded program headers')
    f.seek(phoff);table=f.read(phnum*56);need(len(table)==phnum*56,'short program header table');headers=[]
    for row in struct.iter_unpack('<IIQQQQQQ',table):
        typ,pflags,offset,vaddr,paddr,filesz,memsz,align=row
        need(typ not in (2,3),'PT_DYNAMIC/PT_INTERP refused')
        need(offset+filesz<=final['size'],'segment outside image')
        if typ==1:need(filesz<=memsz,'LOAD file extent exceeds memory extent')
        headers.append({'type':typ,'flags':pflags,'offset':offset,'virtual_address':vaddr,'file_bytes':filesz,'memory_bytes':memsz,'alignment':align})
    need(any(h['type']==1 and h['flags']&1 and h['virtual_address']<=entry<h['virtual_address']+h['memory_bytes'] for h in headers),'entry outside executable LOAD')
state={'candidate':final,'linked_root':source,'entry':entry,'program_headers':headers,'Cargo_root_artifact':artifacts[0],'relink_monitor_receipt':digest(receipt_path)}
encoded=(json.dumps(state,indent=2)+'\n').encode();need(len(encoded)<=262144,'candidate record exceeds256KiB');sys.stdout.buffer.write(encoded)
