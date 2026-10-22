from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
ROOT=Path('/home/dikini/Projects/ash-lang/.worktree/checked-owner-passive')
OUT=Path('/home/dikini/Projects/ash-lang/.worktree/generic-cells/target/checked-owner-passive-retained-regressions')
def pins():
 names=subprocess.check_output(['git','ls-files','-z','--cached','--others','--exclude-standard'],cwd=ROOT).decode().split('\0')
 return {n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in sorted(set(names)) if n and (ROOT/n).is_file()}
commands=[('owner-lifecycle', 26, ['cargo', 'test', '--offline', '--locked', '--lib', 'elaborate::checked_owner_lifecycle_tests::checked_owner_lifecycle_']), ('bridges', 5, ['cargo', 'test', '--offline', '--locked', '--lib', 'build::bridge::tests::']), ('native-image-startup', 3, ['cargo', 'test', '--offline', '--locked', '--lib', 'build::native_image_tests::']), ('opaque_owner_metadata_restores_shared_identity_without_owner_execution', 1, ['cargo', 'test', '--offline', '--locked', '--lib', 'build::image::tests::opaque_owner_metadata_restores_shared_identity_without_owner_execution', '--', '--exact']), ('access_image_restores_original_family_and_result_roles_without_pointer_execution', 1, ['cargo', 'test', '--offline', '--locked', '--lib', 'build::image::tests::access_image_restores_original_family_and_result_roles_without_pointer_execution', '--', '--exact']), ('initialized_byte_owner_image_preserves_extent_and_rejects_changed_original_facts', 1, ['cargo', 'test', '--offline', '--locked', '--lib', 'build::image::tests::initialized_byte_owner_image_preserves_extent_and_rejects_changed_original_facts', '--', '--exact']), ('scalar_preflight_image_reconstructs_authority_and_refuses_forged_records', 1, ['cargo', 'test', '--offline', '--locked', '--lib', 'build::image::tests::scalar_preflight_image_reconstructs_authority_and_refuses_forged_records', '--', '--exact']), ('clippy', None, ['cargo', 'clippy', '--offline', '--locked', '--lib', '--tests', '--', '-D', 'warnings'])]
env=os.environ.copy();env.update(RUSTC_WRAPPER='',CARGO_BUILD_JOBS='1',CARGO_TARGET_DIR='/home/dikini/Projects/ash-lang/.worktree/generic-cells/target')
(OUT/'runner-process.json').write_text(json.dumps({'pid':os.getpid(),'pgid':os.getpgid(0),'started_unix':time.time(),'argv':sys.argv},indent=2)+'\n')
print('RUNNER '+str(os.getpid()),flush=True)
results=[]
for name,expected,argv in commands:
 before=pins();started=time.monotonic();print('BEGIN '+name,flush=True)
 (OUT/(name+'.before.json')).write_text(json.dumps(before,indent=2)+'\n')
 with (OUT/(name+'.log')).open('wb') as log:
  run=subprocess.Popen(argv,cwd=ROOT,env=env,stdout=log,stderr=subprocess.STDOUT)
  process={'pid':run.pid,'pgid':os.getpgid(run.pid),'runner_pid':os.getpid(),'started_unix':time.time(),'argv':argv,'cwd':str(ROOT)}
  (OUT/(name+'.process.json')).write_text(json.dumps(process,indent=2)+'\n');print('CHILD '+json.dumps(process),flush=True)
  run.wait()
 after=pins();raw=(OUT/(name+'.log')).read_bytes();text=raw.decode(errors='replace');matches=re.findall(r'^running (\d+) tests?$',text,re.M);selected=int(matches[-1]) if matches else None
 (OUT/(name+'.inputs.json')).write_text(json.dumps({'before':before,'after':after},indent=2)+'\n')
 receipt={'command':argv,'cwd':str(ROOT),'exit_code':run.returncode,'seconds':round(time.monotonic()-started,3),'expected_selected':expected,'actual_selected':selected,'inputs_equal':before==after,'count':len(before),'aggregate_algorithm':'SHA256 sorted-key compact JSON UTF-8 no newline of every tracked and nonignored untracked file byte hash','aggregate_sha256':hashlib.sha256(json.dumps(before,sort_keys=True,separators=(',',':')).encode()).hexdigest(),'log_sha256':hashlib.sha256(raw).hexdigest(),'environment':{n:env.get(n) for n in ['RUSTC_WRAPPER','CARGO_BUILD_JOBS','CARGO_TARGET_DIR','RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS']}}
 (OUT/(name+'.receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n');results.append(receipt);print(json.dumps(receipt),flush=True)
 if run.returncode or selected!=expected or before!=after:break
(OUT/'batch-results.json').write_text(json.dumps(results,indent=2)+'\n')

BINARY=Path('/home/dikini/Projects/ash-lang/.worktree/generic-cells/target/debug/deps/ash-7d3b3208691ff168')
hash=hashlib.sha256()
with BINARY.open('rb') as stream:
 for chunk in iter(lambda:stream.read(1048576),b''):hash.update(chunk)
(OUT/'artifact-after.json').write_text(json.dumps({'path':str(BINARY),'size':BINARY.stat().st_size,'sha256':hash.hexdigest()},indent=2)+'\n')
