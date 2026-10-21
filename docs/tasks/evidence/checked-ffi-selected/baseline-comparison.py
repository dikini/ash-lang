from pathlib import Path
import subprocess,tempfile,tarfile,io,hashlib,json,os,time
repo=Path('/home/dikini/Projects/ash-lang/.worktree/checked-ffi'); out=Path('/tmp/checked-ffi-hosts')
pin='0a85695774edbf9df082aef7f3ac9605243a6825'
root=Path(tempfile.mkdtemp(prefix='ash-pr89-base-'))
archive=subprocess.check_output(['git','archive','--format=tar',pin],cwd=repo)
with tarfile.open(fileobj=io.BytesIO(archive)) as stream: stream.extractall(root,filter='data')
def snapshot():
 paths=[p for d in ('src','tests') for p in (root/d).rglob('*') if p.is_file()]+[root/p for p in ('Cargo.toml','Cargo.lock','rust-toolchain.toml','.cargo/config.toml','build.rs')]
 return {p.relative_to(root).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)}
before=snapshot();(out/'selected-base.before.json').write_text(json.dumps(before,sort_keys=True,indent=2)+'\n')
command=['cargo','test','-p','ash','--locked','--lib','build::image::source_resource_image::tests::imported_buffer_two_owner_discard_has_normal_startup_budget','--','--exact','--nocapture']
env=os.environ.copy();env.update(RUSTC_WRAPPER='',CARGO_BUILD_JOBS='1',CARGO_TARGET_DIR='/home/dikini/Projects/ash-lang/.worktree/generic-cells/target')
start=time.monotonic()
with (out/'selected-base.log').open('wb') as log: result=subprocess.run(command,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT)
after=snapshot();(out/'selected-base.after.json').write_text(json.dumps(after,sort_keys=True,indent=2)+'\n')
receipt={'source_commit':pin,'source_root':str(root),'archive_sha256':hashlib.sha256(archive).hexdigest(),'command':command,'exit':result.returncode,'elapsed_seconds':round(time.monotonic()-start,3),'source_configuration_before_after_equal':before==after,'file_count':len(before),'source_configuration_tree_sha256':hashlib.sha256(json.dumps(before,sort_keys=True,separators=(',',':')).encode()).hexdigest(),'log_sha256':hashlib.sha256((out/'selected-base.log').read_bytes()).hexdigest(),'configuration_difference':'Tracked bytes from retained commit; CARGO_MANIFEST_DIR and source paths refer to disposable /tmp archive instead of managed worktree. Same shared target, one job, empty RUSTC_WRAPPER. No native execution requested.'}
(out/'selected-base.receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt));raise SystemExit(result.returncode if before==after else 99)
