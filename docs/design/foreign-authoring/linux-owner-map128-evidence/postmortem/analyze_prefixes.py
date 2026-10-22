"""Read only three retained bounded prefixes and pinned installed BFD manual."""
from pathlib import Path
import collections,gzip,hashlib,json,re
R=Path('/tmp/ash-owner-map64-postmortem')
inputs=[('first16',Path('/tmp/ash-owner-static-stage3/build-run-mwoqlg55/watched-0.log'),16777216,'63767c4105e76634735b0ed1dabe4dc2fdc1236fb06f6e4c009e5f7946afb0f5'),('suppressed16',Path('/tmp/ash-owner-static-stage3-map-detail/build-run-gbjzjclf/watched-0.log'),16777216,'cb91bca15d2f3469175d7c1a2e9a6f67530a1ac7fb4028b68316823bc10453c9'),('suppressed64',Path('/tmp/ash-owner-static-stage3-map64/build-run-5p6l8giw/watched-0.log'),67108864,'0e62a016e6bca947d2ce30ae523a0ff1e429eb45bffa7f85b477a1275dad94ab')]
markers=['Discarded input sections','Memory Configuration','Linker script and memory map','LOAD ','OUTPUT(','Cross Reference Table','.debug_info','.rodata']
result={'status':'BOUNDED_PREFIX_ONLY_NOT_FULL_MAP_OR_RETRY_PERMISSION','inputs':[],'class_rule':'Disjoint line heuristics, precedence shown in script; categories describe retained text bytes, not executable/native size or complete map distribution.'}
for label,path,cap,expected in inputs:
 with path.open('rb') as f:b=f.read(cap+1)
 assert len(b)==cap and hashlib.sha256(b).hexdigest()==expected
 counts=collections.Counter();sizes=collections.Counter();pairs=[];pending=None;top=[]
 for line in b.splitlines(keepends=True):
  raw=line.rstrip(b'\r\n');cat='other'
  if raw.startswith(b' .text._R') or raw.startswith(b' .text._ZN'):
   cat='mangled_text_section';pending=raw.strip().split()[0][len(b'.text.'):]
  elif re.match(rb'^\s+0x[0-9a-f]+\s+0x[0-9a-f]+',raw):cat='address_extent_input'
  elif m:=re.match(rb'^\s+0x[0-9a-f]+\s+(.+)',raw):
   cat='address_symbol_rendering'
   if pending is not None:
    pairs.append((len(pending),len(m[1])))
    top.append({'mangled_bytes':len(pending),'rendered_bytes':len(m[1]),'mangled_prefix':pending[:120].decode(),'rendered_prefix':m[1][:200].decode()});pending=None
  elif raw.startswith(b' *fill*'):cat='fill'
  elif raw.startswith(b'LOAD '):cat='load'
  elif not raw.strip():cat='blank'
  counts[cat]+=1;sizes[cat]+=len(line)
 assert sum(sizes.values())==len(b)
 row={'label':label,'path':str(path),'retained_bytes':len(b),'sha256':expected,'markers':{m:b.find(m.encode()) for m in markers},'category_lines':dict(counts),'category_bytes':dict(sizes),'category_percent':{k:round(v*100/len(b),3) for k,v in sizes.items()},'LOAD_lines':len(re.findall(rb'^LOAD ',b,re.M)),'explicit_libc_LOAD_present':b'LOAD /usr/lib/x86_64-linux-gnu/libc.a\n' in b,'local_symbol_markers':b.count(b'(local)'),'last_text_section_offset':b.rfind(b' .text.'),'paired_names':{'count':len(pairs),'mangled_total_bytes':sum(x[0] for x in pairs),'rendered_total_bytes':sum(x[1] for x in pairs),'difference_bytes':sum(x[1]-x[0] for x in pairs),'qualification':'Adjacent-section/next-addressed-symbol pairing heuristic, not a simulated --no-demangle result or complete-map size estimate.'},'largest_three_observed_renderings':sorted(top,key=lambda x:x['rendered_bytes'],reverse=True)[:3],'near_end_last1600bytes':b[-1600:].decode('utf8'),'full_map_hashed_or_complete':False}
 if label=='suppressed64':row['first16_range_sha256']=hashlib.sha256(b[:16777216]).hexdigest()
 result['inputs'].append(row)
p=Path('/usr/share/man/man1/ld.bfd.1.gz');raw=p.read_bytes();assert len(raw)==49180 and hashlib.sha256(raw).hexdigest()=='2f7c363d588b25cf60ac64322f3cd30eb01c7807e6bddaa82580d256dbdd1e9e'
# Compressed input is already exact pinned; decompression still bounded before retention.
with gzip.open(p,'rb') as f:manual=f.read(262145)
assert len(manual)==174576 and hashlib.sha256(manual).hexdigest()=='d68694b33179394f19c779f3b3cf04272571c55f28cacf913fbf2bd85e2999ec'
text=manual.decode(); opts={}
for option,needle in [('no-demangle','.IP \\fB\\-\\-demangle'),('no-print-map-locals','.IP \\fB\\-\\-print\\-map\\-locals'),('reduce-memory-overheads','.IP \\fB\\-\\-reduce\\-memory\\-overheads')]:
 at=text.find(needle);assert at>=0;opts[option]={'manual_uncompressed_byte_offset':at,'interpretation':{'no-demangle':'Controls rendering of symbol names in errors and other output; default demangles unless COLLECT_NO_DEMANGLE is set. Proposed diagnostic-only option requires exact review/assignment; no fit/byte-identity claim.','no-print-map-locals':'Local map symbols disabled by default; none observed in retained prefixes. No evidenced benefit from restating this default.','reduce-memory-overheads':'Changes linker memory/speed tradeoffs including map generation algorithm and hash table size; not documented to omit the large symbol representations. Not recommended as this map-size remedy.'}[option]}
result['manual']={'path':str(p),'compressed_bytes':len(raw),'compressed_sha256':hashlib.sha256(raw).hexdigest(),'uncompressed_bytes':len(manual),'uncompressed_sha256':hashlib.sha256(manual).hexdigest(),'options':opts,'short_exact_quote':'These options control whether to demangle symbol names in error messages and other output.'}
(R/'prefix-analysis.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'category64':result['inputs'][2]['category_bytes'],'pair64':result['inputs'][2]['paired_names'],'manual_options':list(opts)},indent=2))
