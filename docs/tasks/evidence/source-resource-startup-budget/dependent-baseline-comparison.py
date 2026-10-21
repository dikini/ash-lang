from pathlib import Path
import subprocess,tempfile,tarfile,io,hashlib,json,os,time
repo=Path('/home/dikini/Projects/ash-lang/.worktree/checked-ffi')
out=Path('/tmp/checked-ffi-hosts'); pin='a301a654bff2b7caed4befc32ce038abcf85dd7e'; name='startup91-dependent-base'
root=Path(tempfile.mkdtemp(prefix='ash-startup91-base-'))
archive=subprocess.check_output(['git','archive','--format=tar',pin],cwd=repo)
archive_path=out/(name+'.tar'); archive_path.write_bytes(archive)
with tarfile.open(fileobj=io.BytesIO(archive)) as stream: stream.extractall(root,filter='data')
def digest(data): return hashlib.sha256(data).hexdigest()
def snapshot():
 paths=[p for d in ('src','tests') for p in (root/d).rglob('*') if p.is_file()]+[root/p for p in ('Cargo.toml','Cargo.lock','rust-toolchain.toml','.cargo/config.toml','build.rs')]
 return {p.relative_to(root).as_posix():digest(p.read_bytes()) for p in sorted(paths)}
before=snapshot()
for path, value in before.items():
 assert digest(subprocess.check_output(['git','show',pin+':'+path],cwd=repo))==value,path
(out/(name+'.before.json')).write_text(json.dumps(before,sort_keys=True,indent=2)+'\n')
command=['cargo','test','-p','ash','--locked','--lib','build::image::source_resource_image::tests::dependent_discard_image_checks_original_facts_under_normal_cumulative_work','--','--exact','--nocapture']
env=os.environ.copy();env.update(RUSTC_WRAPPER='',CARGO_BUILD_JOBS='1',CARGO_TARGET_DIR='/home/dikini/Projects/ash-lang/.worktree/generic-cells/target')
start=time.monotonic()
with (out/(name+'.log')).open('wb') as log: result=subprocess.run(command,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT)
after=snapshot();(out/(name+'.after.json')).write_text(json.dumps(after,sort_keys=True,indent=2)+'\n')
binary=Path(env['CARGO_TARGET_DIR'])/'debug/deps/ash-7d3b3208691ff168'
receipt={'source_commit':pin,'source_root':str(root),'archive_path':str(archive_path),'archive_sha256':digest(archive),'command':command,'environment':{k:env[k] for k in ('RUSTC_WRAPPER','CARGO_BUILD_JOBS','CARGO_TARGET_DIR')},'exit':result.returncode,'elapsed_seconds':round(time.monotonic()-start,3),'tracked_git_blob_comparison':True,'source_configuration_before_after_equal':before==after,'file_count':len(before),'source_configuration_tree_sha256':digest(json.dumps(before,sort_keys=True,separators=(',',':')).encode()),'log_sha256':digest((out/(name+'.log')).read_bytes()),'unit_binary':str(binary),'unit_binary_sha256':digest(binary.read_bytes()) if binary.exists() else None,'configuration_difference':'Exact tracked bytes verified against retained Git blobs. CARGO_MANIFEST_DIR and source paths refer to this disposable /tmp archive, not the managed worktree. Same shared target, one job, empty RUSTC_WRAPPER. No native execution requested.'}
(out/(name+'.receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt));raise SystemExit(result.returncode if before==after else 99)
