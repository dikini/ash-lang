import hashlib,json,os,subprocess,time
from pathlib import Path
r=Path('/home/dikini/Projects/ash-lang');os.chdir(r)
d=r/'.worktree/recovery/arena-completion-20261009/baseline-regression-1';d.mkdir(exist_ok=False)
def pins():
 names=subprocess.check_output(['git','ls-files','-z']).decode().split('\0')
 return {n:hashlib.sha256(Path(n).read_bytes()).hexdigest() for n in names if n and (n.endswith(('.rs','.ash')) or Path(n).name in ('Cargo.toml','Cargo.lock')) and Path(n).is_file()}
source=pins();drafts=json.loads((d.parent/'unrelated-draft-pins.json').read_text())
commands=[['cargo','test','--locked','-p','ash','--test','provider_sqlite_source','--test','provider_sqlite_copying','--test','provider_sqlite_sessions','--test','provider_sqlite_control','--test','provider_arena_source','--test','provider_arena_allocation','--no-fail-fast','--','--test-threads=1'],['cargo','test','--locked','--workspace','--all-features','--lib','--no-fail-fast','--','--exact','--test-threads=1','core::capture::tests::deep_capture_equations_and_retained_types_are_stack_safe_and_retryable','core::capture::tests::local_callable_partial_initialization_exhaustion_is_stack_safe','core::capture::tests::requested_metadata_deep_preparation_and_drop_use_explicit_storage','core::transform::tests::effect_handler_rebuild_is_exact_retryable_and_deep_drop_safe','core::provider::specialization::executable_scope_tests::arena_scope_transforms_reject_a_different_genuine_same_typed_family_dictionary'],['cargo','test','--locked','-p','ash-foreign-adapter','--lib','--test','arena','--no-fail-fast','--','--test-threads=1'],['python3',str(d.parent/'run-baseline-packaged-hosts.py'),'--repo',str(r),'--target-dir',str(r/'target'),'--evidence',str(d/'packaged-hosts')]]
receipt={'head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'source_before':source,'drafts_before':drafts,'commands':[],'completed':False}
(d/'source-pins.json').write_text(json.dumps(source,indent=2)+'\n')
for i,cmd in enumerate(commands,1):
 log=d/f'command-{i}.log';env=dict(os.environ,CARGO_BUILD_JOBS='1',RUSTC_WRAPPER='',RUST_TEST_THREADS='1');env.pop('ASH_ARENA_DIAGNOSTICS',None)
 print('START',i,cmd,flush=True);start=time.monotonic()
 with log.open('w') as f:ret=subprocess.run(cmd,env=env,stdout=f,stderr=subprocess.STDOUT)
 row={'command':cmd,'cwd':str(r),'exit_code':ret.returncode,'elapsed_seconds':time.monotonic()-start,'log':str(log),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()};receipt['commands'].append(row)
 (d/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(row),flush=True)
receipt['source_after']=pins();receipt['source_unchanged']=receipt['source_after']==source
receipt['draft_mismatches']=[n for n,h in drafts.items() if hashlib.sha256(Path(n).read_bytes()).hexdigest()!=h]
receipt['completed']=True;receipt['passed']=receipt['source_unchanged'] and not receipt['draft_mismatches'] and all(x['exit_code']==0 for x in receipt['commands'])
(d/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print('COMPLETE',receipt['passed'],flush=True)
raise SystemExit(not receipt['passed'])
