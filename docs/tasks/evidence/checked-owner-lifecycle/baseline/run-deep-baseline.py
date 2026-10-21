import hashlib,json,os,pathlib,subprocess,time
out=pathlib.Path('/tmp/ash-pr97');prep=json.loads((out/'deep-baseline-prepared.json').read_text());root=pathlib.Path(prep['directory']);keys=prep['source_pins']
def pins():return {p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in keys}
before=pins();assert before==keys
cmd=['cargo','test','-p','ash','--locked','--lib','resolved::tests::freeze_rejects_missing_local_hidden_nominal_before_cloning_deep_parameters','--','--exact','--nocapture']
env=os.environ.copy();env.update(RUSTC_WRAPPER='',CARGO_BUILD_JOBS='1',CARGO_TARGET_DIR='/home/dikini/Projects/ash-lang/.worktree/generic-cells/target');start=time.monotonic()
with (out/'deep-baseline-one.log').open('wb') as log:r=subprocess.run(cmd,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT)
after=pins();(out/'deep-baseline-one.inputs.json').write_text(json.dumps({'before':before,'after':after},indent=2)+'\n')
record={'command':cmd,'cwd':str(root),'base':prep['base'],'exit_code':r.returncode,'seconds':round(time.monotonic()-start,3),'inputs_equal':before==after,'all_git_and_archive_pins_equal':before==keys,'count':len(keys),'aggregate':prep['aggregate'],'log_sha256':hashlib.sha256((out/'deep-baseline-one.log').read_bytes()).hexdigest(),'environment':{k:env.get(k) for k in ['RUSTC_WRAPPER','CARGO_BUILD_JOBS','CARGO_TARGET_DIR','RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS']},'qualification':prep['qualification']}
artifact=pathlib.Path(env['CARGO_TARGET_DIR'])/'debug/deps/ash-7d3b3208691ff168'
if artifact.exists():
 h=hashlib.sha256()
 with artifact.open('rb') as f:
  for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
 record['unit_artifact']={'path':str(artifact),'bytes':artifact.stat().st_size,'sha256':h.hexdigest()}
(out/'deep-baseline-one.receipt.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record))
