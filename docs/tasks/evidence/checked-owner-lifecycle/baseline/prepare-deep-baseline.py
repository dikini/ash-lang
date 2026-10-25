from pathlib import Path
import hashlib,json,subprocess,tempfile,tarfile
out=Path('/tmp/ash-pr97'); base='91e6dee036c9728d89f016aee61ff337b8a978e1'
root=Path(tempfile.mkdtemp(prefix='ash-pr97-deep-base-')); archive=out/'deep-baseline-source.tar'
with archive.open('wb') as f: subprocess.run(['git','archive','--format=tar',base],stdout=f,check=True)
with tarfile.open(archive) as tar: tar.extractall(root,filter='data')
entries=[]
for line in subprocess.check_output(['git','ls-tree','-r',base]).decode().splitlines():
 metadata,path=line.split('\t',1); mode,kind,oid=metadata.split()
 if kind!='blob':continue
 if path.startswith(('src/','tests/','spec/','libraries/','foreign-adapter/')) or path in ['.cargo/config.toml','Cargo.toml','Cargo.lock','build.rs','rust-toolchain.toml']:
  entries.append((path,oid,mode))
request=''.join(oid+'\n' for _,oid,_ in entries).encode(); result=subprocess.run(['git','cat-file','--batch'],input=request,stdout=subprocess.PIPE,check=True).stdout
pins={}; offset=0; gitpins={}
for path,oid,mode in entries:
 end=result.index(b'\n',offset); header=result[offset:end].decode().split(); size=int(header[2]); data=result[end+1:end+1+size];offset=end+size+2
 assert header[0]==oid and (root/path).read_bytes()==data
 h=hashlib.sha256(data).hexdigest(); pins[path]=h;gitpins[path]={'git_blob':oid,'mode':mode,'sha256':h}
assert offset==len(result)
aggregate=hashlib.sha256(json.dumps(pins,sort_keys=True,separators=(',',':')).encode()).hexdigest()
record={'base':base,'directory':str(root),'archive':str(archive),'archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'source_pins':pins,'git_pins':gitpins,'count':len(pins),'aggregate':aggregate,'aggregate_algorithm':'SHA256 of sorted-key compact JSON UTF-8 no newline','qualification':'Exact tracked-source Git/archive bytes, separate archive path and CARGO_MANIFEST_DIR; shared target/cache, one job, unchanged default policy. This is not a byte-identical filesystem/path environment. No evaluator/native execution.'}
(out/'deep-baseline-prepared.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({k:record[k] for k in ['base','directory','archive_sha256','count','aggregate']}))
