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
MONITOR=Path('/tmp/ash-owner-map128-monitor/build_monitor.py')
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
LIBC_PATH = '/usr/lib/x86_64-linux-gnu/libc.a'
LIBC_SIZE = 6238972
LIBC_SHA = '2a277b999268f100c5f838689704b7432e9b1fdac76bf0cbda83cdbbaecc89e2'
def map_load_lines(data):
    text=data.decode('utf8')
    lines=text.splitlines()
    need('Memory Configuration' in lines and 'Linker script and memory map' in lines,'unrecognized GNU/BFD map framing')
    need(lines.index('Memory Configuration') < lines.index('Linker script and memory map'),'invalid GNU/BFD map framing order')
    need(any(line.startswith('OUTPUT(') and line.rstrip().endswith(' elf64-x86-64)') for line in lines),'unsupported GNU/BFD map output format')
    loads=[line for line in lines if line.startswith('LOAD ')]
    need(loads,'empty GNU/BFD LOAD set')
    return loads

def require_explicit_libc(loads):
    rows=[item for item in loads if item['path']==LIBC_PATH]
    need(rows,'explicit pinned libc.a LOAD missing')
    need(any(row.get('observed',{}).get('size')==LIBC_SIZE and row.get('observed',{}).get('sha256')==LIBC_SHA for row in rows),'explicit libc.a LOAD size/hash differs')

spec=json.loads(read(ROOT/'preflight-inputs.json',262144));outer=spec['outer_environment']
need(sys.flags.isolated and sys.flags.no_site and dict(os.environ)==outer,'isolated exact environment required')
need(len(sys.argv)==3,'candidate record and inspection response required')
state=json.loads(read(Path(sys.argv[1]),262144));final=state['candidate'];source=state['linked_root'];entry=state['entry'];headers=state['program_headers'];artifacts=[state['Cargo_root_artifact']]
candidate=ROOT/'static-host';need(candidate.stat().st_size<=IMAGE_LIMIT and final['size']<=IMAGE_LIMIT,'candidate exceeds128MiB');need(final['path']==str(candidate) and digest(candidate)==final,'candidate record association differs')
receipt_path=Path(state['relink_monitor_receipt']['path']);need(digest(receipt_path)==state['relink_monitor_receipt'],'relink receipt changed')
response=json.loads(read(Path(sys.argv[2]),262144));inspection_path=Path(response['receipt']);ins=json.loads(read(inspection_path,4194304))
need(ins['config_sha256']==hashlib.sha256(read(ROOT/'inspection.monitor.json',262144)).hexdigest(),'inspection config association differs')
need(ins['monitor']['sha256']=='62adc0d5264b0d08835079174a19db49de954b0fa51e97ede216d036e549c914','inspection monitor source differs')
need(ins['reason']=='exit' and ins['child_exit']==0 and ins['cleanup']['all_children_reaped'] and not ins['cleanup']['remaining_children'] and not ins['cleanup']['escaped_group_detected'] and not ins['cleanup']['reaping_pending'] and not ins.get('final_limit_failures') and not ins['output_truncated'],'passive inspection did not succeed cleanly')
report=read(Path(ins['output_path']),16777216)
need(hashlib.sha256(report).hexdigest()==ins['output_file']['sha256'],'readelf output association differs')
need(b'There is no dynamic section in this file.' in report,'unsupported dynamic dependency metadata')
need(digest(candidate)==final,'candidate changed during inspection')
relink=json.loads(read(receipt_path,4194304))
need(relink['schema']==2 and relink['map_relative_path']=='whole-static.map','wrong relink map policy')
need(relink['limits']=={'deadline_seconds':1200,'output_bytes':16777216,'sidefile_bytes':16777216,'map_bytes':134217728},'relink class bounds differ')
map_rows=[row for row in relink['watched_files'] if row['relative_path']=='whole-static.map']
need(len(map_rows)==1,'exact map observation missing/duplicated')
map_record=map_rows[0]
need(map_record['file_class']=='link_map' and map_record['limit_bytes']==134217728 and not map_record['hash_is_prefix'] and map_record['observed_peak_bytes']<=134217728,'incomplete/oversize/noncanonical map observation')
map_path=ROOT/'whole-static.map';map_bytes=read(map_path,134217728);loads=[]
for line in map_load_lines(map_bytes):
    if line.startswith('LOAD '):
        need(len(loads)<4096,'LOAD manifest entry limit');name=line[5:].strip();path=Path(name)
        if not path.is_absolute():path=Path('/tmp/ash-owner-generation-stage2/experiment/.ash-build/ash-host-6-0')/path
        item={'load_line':line,'path':str(path)}
        if path.is_file() and not path.is_symlink():item['observed']=digest(path)
        else:item['unavailable']='Linker temporary/missing/nonregular input; correspondence remains a producer/build-trust premise, not a fully hashed closure claim.'
        loads.append(item)
require_explicit_libc(loads)
complete_map=digest(map_path)
need(complete_map['sha256']==map_record['sha256'] and complete_map['size']==map_record['hashed_bytes']==map_record['size_before']==map_record['size_after'],'complete map differs from settled monitored bytes')
manifest={'Cargo_root_artifact':artifacts[0],'candidate':final,'linked_root':source,'entry':entry,'program_headers':headers,'link_map':complete_map,'map_policy':{'exact_relative_path':'whole-static.map','map_bytes':134217728,'other_watched_log_bytes':16777216,'discarded_section_diagnostics_suppressed':True,'symbol_name_rendering':'mangled (--no-demangle); no additional active-map record removal','observed_peak_bytes':map_record['observed_peak_bytes'],'sampling_not_quota':True},'LOAD_records':loads,'qualification':'Structural static ELF facts plus recorded existing LOAD inputs. Retained or absent runtime loader routes, linker temporaries, producer/native correctness and no-loading premises require separate source review. No ownerful architecture or startup acceptance.'}
encoded=(json.dumps(manifest,indent=2)+'\n').encode();need(len(encoded)<=4194304,'static manifest exceeds4MiB');manifest_path=ROOT/'static-manifest.json';need(not manifest_path.exists(),'old static manifest');manifest_path.write_bytes(encoded)
receipt={'kind':'owner-existing-profile-whole-static-packaging-only','contract_retained_commit':'5cb93a9fd03d963377b0a79bc2e18404c54c2c47','contract_sha256':'c4aaeab72ca1d32971d4d12939828f6d56c69c600005ca57f586329e200f95bd','historical_generation_contract_sha256':'27430b69ee44dcbcb835a83dc38ff2b034826b81dddae40b7bb9ba7b4377cc3e','selected_source_commit':'1a8ecef0b03ddc75a45254543bd8f6f0bb10969c','stage2_generation_receipt':digest(Path('/tmp/ash-owner-generation-stage2/generation-receipt.json')),'relink_monitor_receipt':digest(receipt_path),'inspection_monitor_receipt':digest(inspection_path),'static_manifest':digest(manifest_path),'candidate':final,'image_executed':False,'mode_note':'Candidate copied with0400, hash-verified private file; this is not approved immutable-fd execution. Ownerful architecture/approval/store/context/native assumptions remain pending.'}
encoded=(json.dumps(receipt,indent=2)+'\n').encode();need(len(encoded)<=262144,'static receipt exceeds256KiB');sys.stdout.buffer.write(encoded)
