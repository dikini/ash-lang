from pathlib import Path
import subprocess,hashlib,json,os,time
root=Path('/home/dikini/Projects/ash-lang/.worktree/checked-ffi')
out=Path('/tmp/ash-pr94/final-verified');out.mkdir(exist_ok=True)
def pins():
 paths=subprocess.check_output(['git','ls-files','--cached','--others','--exclude-standard'],cwd=root,text=True).splitlines()
 paths=sorted(set(p for p in paths if p.startswith(('src/','tests/','foreign-adapter/','xtask/','spec/')) or p in ['.cargo/config.toml','Cargo.toml','Cargo.lock','build.rs','rust-toolchain.toml']))
 return {p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in paths if (root/p).is_file()}
def digest(value):return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()
env=os.environ.copy();env.update(RUSTC_WRAPPER='',CARGO_BUILD_JOBS='1',CARGO_TARGET_DIR='/home/dikini/Projects/ash-lang/.worktree/generic-cells/target')
commands=[
 ('resource-kinds',['cargo','test','-p','ash','--locked','--lib','resolved::checked_resource_kind_closure_tests','--','--nocapture']),
 ('closure',['cargo','test','-p','ash','--locked','--lib','declaration_closure','--','--nocapture']),
 ('checked-carriers',['cargo','test','-p','ash','--locked','--lib','resolved::checked_','--','--nocapture']),
 ('wrappers',['cargo','test','-p','ash','--locked','--test','checked_foreign_wrappers','--','--nocapture']),
 ('imports',['cargo','test','-p','ash','--locked','--lib','imported','--','--nocapture']),
 ('images',['cargo','test','-p','ash','--locked','--lib','build::image::source_resource_image::tests','--','--nocapture']),
 ('owners',['cargo','test','-p','ash','--locked','--lib','build::source_owner_post_record_tests','--','--nocapture']),
 ('capture',['cargo','test','-p','ash','--locked','--lib','core::capture::tests','--','--nocapture']),
 ('clippy',['cargo','clippy','-p','ash','--locked','--lib','--tests','--','-D','warnings']),
]
results=[]
for name,command in commands:
 before=pins();start=time.time()
 with (out/(name+'.log')).open('wb') as log:exit_code=subprocess.run(command,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT).returncode
 after=pins();assert before==after
 (out/(name+'.inputs.json')).write_text(json.dumps(before,indent=2)+'\n')
 receipt={'command':command,'exit_code':exit_code,'seconds':round(time.time()-start,3),'input_count':len(before),'input_aggregate_sha256':digest(before),'aggregate_algorithm':'SHA256 of JSON object sorted keys, compact separators (comma,colon), UTF-8, no final newline','before_after_equal':True,'raw_sha256':hashlib.sha256((out/(name+'.log')).read_bytes()).hexdigest(),'environment':{k:env.get(k) for k in ['RUSTC_WRAPPER','CARGO_BUILD_JOBS','CARGO_TARGET_DIR','RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS']}}
 (out/(name+'.receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n');results.append(receipt)
 print(name,exit_code,receipt['seconds'],len(before),receipt['input_aggregate_sha256'],flush=True)
 if name in ['resource-kinds','closure'] and exit_code:break
(out/'verification.json').write_text(json.dumps(results,indent=2)+'\n')
raise SystemExit(0 if all(r['exit_code']==0 for r in results) else 1)
