from pathlib import Path
import hashlib,json,struct
root=Path('/home/dikini/Projects/ash-lang/.worktree/checked-owner-passive');target=Path('/home/dikini/Projects/ash-lang/.worktree/generic-cells/target');d=target/'checked-owner-producer-artifact-730-1792734011758332101';out=target/'checked-owner-producer-static-link-role-comment';project=d/'.ash-build/ash-host-730-0'
def pin(p,cap=128*1024*1024):
 before=p.stat();assert before.st_size<=cap;h=hashlib.sha256();n=0
 with p.open('rb') as f:
  for b in iter(lambda:f.read(65536),b''):n+=len(b);assert n<=cap;h.update(b)
 after=p.stat();identity=lambda s:[s.st_dev,s.st_ino,s.st_mode,s.st_size,s.st_mtime_ns,s.st_ctime_ns];assert identity(before)==identity(after)
 return {'path':str(p),'bytes':n,'sha256':h.hexdigest(),'identity':identity(after)}
pins={str(p.relative_to(d)):pin(p) for p in sorted(d.rglob('*')) if p.is_file()}
assert (d/'owner.c').read_bytes()==(root/'tests/fixtures/checked-owner-runtime/owner.c').read_bytes();assert (d/'owner.h').read_bytes()==(root/'tests/fixtures/checked-owner-runtime/owner.h').read_bytes()
with (d/'program').open('rb') as f:head=f.read(4096)
assert head[:7]==b'\x7fELF\x02\x01\x01';assert struct.unpack_from('<HHI',head,16)==(2,62,1);assert struct.unpack_from('<H',head,52)[0]==64
entry,phoff=struct.unpack_from('<QQ',head,24);phsize,phnum=struct.unpack_from('<HH',head,54);assert phsize==56 and 0<phnum<=64 and 64<=phoff and phoff+phsize*phnum<=len(head)
rows=[]
for i in range(phnum):
 kind,flags,offset,va,pa,filesz,memsz,align=struct.unpack_from('<IIQQQQQQ',head,phoff+i*56);assert kind not in [2,3]
 if kind==1:assert filesz<=memsz and offset+filesz<=pins['program']['bytes']
 rows.append(dict(type=kind,flags=flags,offset=offset,vaddr=va,filesz=filesz,memsz=memsz,align=align))
assert any(r['type']==1 and r['flags']&1 and r['vaddr']<=entry<r['vaddr']+r['memsz'] for r in rows)
raw=(project/'producer-receipt.bin').read_bytes();assert len(raw)<=4096 and raw[:8]==b'ASHRCP01' and struct.unpack_from('<I',raw,8)[0]==1 and raw[12:14]==bytes([1,0]);n=struct.unpack_from('<I',raw,14)[0];assert raw[18:18+n]==b'x86_64-unknown-linux-gnu';at=18+n;assert struct.unpack_from('<I',raw,at)[0]==16;at+=4;limits=struct.unpack_from('<QQQQ',raw,at);at+=32;assert at+16*42==len(raw) and limits[0]==128*1024*1024 and limits[1]>=len(raw) and limits[2]>=16
names=['ProgramImage','ExpectedFacts','GeneratedRust','OriginalMappings','RuntimeFingerprint','BuildConfiguration','DeclaredNativeInputs','FinalElf','CheckedContracts','RuntimeClosure','NativeClosure','HeaderClosure','ToolClosure','Policy','Premises','Context'];fields={}
for i,name in enumerate(names):
 tag,present,size=struct.unpack_from('<BBQ',raw,at);digest=raw[at+10:at+42].hex();assert tag==i and present in [0,1];assert present or (size==0 and digest=='00'*32);fields[name]={'bytes':size,'sha256':digest} if present else None;at+=42
for field,path in [('ProgramImage',project/'src/program-image.bin'),('ExpectedFacts',project/'src/expected-facts.bin'),('GeneratedRust',project/'src/main.rs'),('FinalElf',d/'program'),('Policy',project/'src/checked-policy.bin')]:
 actual=pin(path);assert fields[field]=={k:actual[k] for k in ['bytes','sha256']}
sha=hashlib.sha256();size=0
for path in [project/'src/program-image.bin',project/'src/expected-facts.bin']:
 b=path.read_bytes();sha.update(struct.pack('<Q',len(b)));sha.update(b);size+=8+len(b)
assert fields['CheckedContracts']=={'bytes':size,'sha256':sha.hexdigest()}
assert [n for n in names if fields[n] is None]==['RuntimeClosure','NativeClosure','HeaderClosure','ToolClosure','Premises','Context']
policy=(project/'src/checked-policy.bin').read_bytes();assert len(policy)==156 and policy[:8]==b'ASHPOL01' and struct.unpack_from('<I',policy,8)[0]==1
for at,name in [(12,'ProgramImage'),(52,'ExpectedFacts')]:assert struct.unpack_from('<Q',policy,at)[0]==fields[name]['bytes'] and policy[at+8:at+40].hex()==fields[name]['sha256']
capacities=struct.unpack_from('<8Q',policy,92);assert capacities[0]==0 and capacities[1]==5 and capacities[2:4]==(1,1) and capacities[5]>=capacities[1] and capacities[6]>=capacities[5]+1
result={'purpose':'independent passive post-link bytes/structure/data association; no startup/immutable execution/native closure authority','pins':pins,'elf':{'class':64,'endian':'little','machine':62,'type':2,'entry':entry,'program_headers':rows,'no_interpreter_or_dynamic_segment':True},'receipt':{'pin':pin(project/'producer-receipt.bin'),'role':'CheckedPreparation','mode':0,'declared_limits':limits,'fields':fields},'capacity_data':{'scope_ordinal':capacities[0],'static_minimum':capacities[1],'groups':capacities[2],'owners':capacities[3],'pending':capacities[4],'observations':capacities[5],'history':capacities[6],'continuations':capacities[7]},'qualification':'C source/header exact fixture bytes and archive/object observed; header/tool/native/runtime transitive closure remains Missing; BFD loading warnings are retained, not disproved.'}
(out/'post-link-readback.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'elf':pins['program'],'receipt':pin(project/'producer-receipt.bin'),'headers':len(rows),'load_segments':sum(r['type']==1 for r in rows),'readback_sha256':hashlib.sha256((out/'post-link-readback.json').read_bytes()).hexdigest()},indent=2))
