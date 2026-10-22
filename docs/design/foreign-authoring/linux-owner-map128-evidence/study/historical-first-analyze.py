"""Bounded read-only ELF metadata and fixed-prefix comparison; no native tools."""
from pathlib import Path
import collections,hashlib,json,os,re,stat,struct
R=Path('/tmp/ash-owner-map-budget-analysis');P=Path('/tmp/ash-owner-generation-stage2/experiment/ordinary-host');SIZE=475650552;SHA='d5799c76fbf3be8b06a473906b4e73ce82b1fdf90db4a1b1923d958816fe0a61'
def hash_stream(f):
 f.seek(0);h=hashlib.sha256();n=0
 while b:=f.read(65536):h.update(b);n+=len(b)
 return n,h.hexdigest()
def identity(s):return [s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns]
with P.open('rb') as f:
 before=os.fstat(f.fileno());assert stat.S_ISREG(before.st_mode) and before.st_size==SIZE and hash_stream(f)==(SIZE,SHA)
 def readat(offset,length,cap):
  assert 0<=length<=cap and 0<=offset<=SIZE and offset+length<=SIZE
  f.seek(offset);b=f.read(length);assert len(b)==length;return b
 eh=struct.unpack('<16sHHIQQQIHHHHHH',readat(0,64,64));assert eh[0][:7]==b'\x7fELF\x02\x01\x01' and eh[2]==62
 shoff,shsize,shnum,shstr=eh[6],eh[11],eh[12],eh[13];assert shsize==64 and 0<shnum<=4096 and shstr<shnum
 table=readat(shoff,shsize*shnum,64*4096);headers=[struct.unpack('<IIQQQQIIQQ',x) for x in struct.iter_unpack('64s',table) for x in [x[0]]]
 names=readat(headers[shstr][4],headers[shstr][5],65536)
 sections=[]
 for index,h in enumerate(headers):
  assert h[0]<len(names);end=names.index(0,h[0]);name=names[h[0]:end].decode()
  sections.append({'index':index,'name':name,'type':h[1],'flags':h[2],'address':h[3],'offset':h[4],'size':h[5],'link':h[6],'entry_bytes':h[9]})
 sym=next(x for x in sections if x['name']=='.symtab');strings=sections[sym['link']];textsec=next(x for x in sections if x['name']=='.text')
 assert sym['entry_bytes']==24 and sym['size']%24==0 and sym['size']<=16*1024*1024 and strings['type']==3
 strtab=readat(strings['offset'],strings['size'],64*1024*1024)
 kinds=collections.Counter();bindings=collections.Counter();symbols=0;text_functions={};text_function_rows=0;text_name_bytes_rows=0;top=[]
 for start in range(0,sym['size'],24*1024):
  chunk=readat(sym['offset']+start,min(24*1024,sym['size']-start),24*1024)
  for name,info,other,shndx,value,size in struct.iter_unpack('<IBBHQQ',chunk):
   assert name<len(strtab);end=strtab.index(0,name);n=strtab[name:end];symbols+=1;kinds[str(info&15)]+=1;bindings[str(info>>4)]+=1
   if shndx==textsec['index'] and info&15==2:
    text_function_rows+=1;text_name_bytes_rows+=len(n);text_functions[n]=len(n)
    if len(top)<5 or len(n)>top[-1]['bytes']:
     top.append({'bytes':len(n),'prefix':n[:200].decode('utf8',errors='replace')});top=sorted(top,key=lambda x:x['bytes'],reverse=True)[:5]
 assert hash_stream(f)==(SIZE,SHA);after=os.fstat(f.fileno());assert identity(before)==identity(after)
 producer={'path':str(P),'size':SIZE,'sha256_before':SHA,'sha256_after':SHA,'identity_before':identity(before),'identity_after':identity(after),'complete_producer_file_verified':True,'ELF_type':eh[1],'machine':eh[2],'sections':sections,'symtab':{'symbol_rows':symbols,'symbol_type_counts':dict(kinds),'symbol_binding_counts':dict(bindings),'defined_text_function_rows':text_function_rows,'defined_text_function_name_bytes_with_rows':text_name_bytes_rows,'unique_defined_text_function_names':len(text_functions),'unique_defined_text_function_name_bytes':sum(text_functions.values()),'largest_five_names':top},'qualification':'Complete ordinary producer input metadata, not a final static candidate; ordinary link is ET_DYN and includes DWARF. Different static linker/CRT/section ordering prevent treating it as a bijective inventory or bound for a future map.'}
inputs=[('third','/tmp/ash-owner-static-stage3-map64/build-run-5p6l8giw/watched-0.log','0e62a016e6bca947d2ce30ae523a0ff1e429eb45bffa7f85b477a1275dad94ab'),('fourth','/tmp/ash-owner-static-stage3-mangled/build-run-ppvqh10e/watched-0.log','af27c6e1f59f1d26c56d996989500bab10274e839702d0a3e9af0f11aca6d1d5')]
rows=[]
for label,path,sha in inputs:
 with open(path,'rb') as f:b=f.read(67108865)
 assert len(b)==67108864 and hashlib.sha256(b).hexdigest()==sha
 counts=collections.Counter();sizes=collections.Counter();matched=set();raw_names=set();pending=None;pairs=0;mangled=rendered=0;last_extent=None
 output_sections=[]
 for line in b.splitlines(keepends=True):
  l=line.rstrip(b'\r\n');cat='other'
  if m:=re.match(rb'^([.][^ \t\r\n]+)[ \t]+0x([0-9a-f]+)[ \t]+0x([0-9a-f]+)',l):output_sections.append({'name':m[1].decode(),'address':int(m[2],16),'planned_bytes':int(m[3],16)})
  if l.startswith(b' .text._R') or l.startswith(b' .text._ZN'):cat='mangled_text_section';pending=l.strip().split()[0][6:]
  elif m:=re.match(rb'^\s+0x([0-9a-f]+)\s+0x([0-9a-f]+)\s+(.+)',l):cat='address_extent_input';last_extent={'address':int(m[1],16),'bytes':int(m[2],16),'input_prefix':m[3][:200].decode('utf8',errors='replace')}
  elif m:=re.match(rb'^\s+0x[0-9a-f]+\s+(.+)',l):
   cat='address_symbol_name'
   if pending is not None:pairs+=1;mangled+=len(pending);rendered+=len(m[1]);pending=None
   if m[1].startswith((b'_R',b'_ZN')):
    raw_names.add(m[1])
    if m[1] in text_functions:matched.add(m[1])
  elif l.startswith(b' *fill*'):cat='fill'
  elif l.startswith(b'LOAD '):cat='load'
  elif not l.strip():cat='blank'
  counts[cat]+=1;sizes[cat]+=len(line)
 assert sum(sizes.values())==len(b)
 textplan=next(x for x in output_sections if x['name']=='.text')
 rows.append({'label':label,'path':path,'bytes':len(b),'sha256':sha,'markers':{x:b.find(x.encode()) for x in ['Memory Configuration','Linker script and memory map','OUTPUT(','Cross Reference Table','.debug_info']},'actual_rodata_output_header_count':len(re.findall(rb'^\.rodata(?:\s|$)',b,re.M)),'output_sections_observed':output_sections,'last_observed_extent':last_extent,'text_planned_address_progress_fraction':(last_extent['address']-textplan['address'])/textplan['planned_bytes'],'progress_qualification':'Address position within the partial linker-script planned .text extent only; not percent of completed map/file/link or a correspondence to ordinary ELF ordering.','category_lines':dict(counts),'category_bytes':dict(sizes),'paired_names':{'count':pairs,'raw_section_name_bytes':mangled,'symbol_name_bytes':rendered},'raw_Rust_addressed_symbol_names':len(raw_names),'raw_Rust_names_matching_ordinary_text_functions':len(matched),'matched_name_bytes':sum(text_functions[x] for x in matched),'near_end_1200bytes':b[-1200:].decode('utf8'),'full_map_hash_or_completeness_claimed':False})
spaces=[]
for p in [Path('/tmp'),Path('/home/dikini/Projects/ash-lang/.worktree/generic-cells/target')]:
 v=os.statvfs(p);spaces.append({'path':str(p),'canonical':str(p.resolve()),'device':p.stat().st_dev,'available_bytes':v.f_bavail*v.f_frsize,'observation_only_not_reservation':True})
ignore=Path('/home/dikini/Projects/ash-lang/.worktree/generic-cells/.gitignore');ib=ignore.read_bytes();assert b'/target/' in ib.splitlines()
result={'status':'READ_ONLY_COMPLETE_PRODUCER_METADATA_AND_PARTIAL_MAP_ANALYSIS','producer':producer,'prefixes':rows,'space_observations':spaces,'proposed_project_output_parent':'/home/dikini/Projects/ash-lang/.worktree/generic-cells/target/checked-ffi-owner-packaging','output_parent_created':False,'ignore_input':{'path':str(ignore),'size':len(ib),'sha256':hashlib.sha256(ib).hexdigest(),'matching_rule':'/target/'},'mutable_cache_files_read':False,'source_binary_or_cache_copies':False}
(R/'analysis.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'symtab':producer['symtab'],'prefixes':[{k:x[k] for k in ['label','category_bytes','paired_names','last_observed_extent','text_planned_address_progress_fraction','raw_Rust_names_matching_ordinary_text_functions','matched_name_bytes']} for x in rows],'space':spaces},indent=2))
