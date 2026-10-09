import hashlib,json,os,subprocess,time,re
from pathlib import Path
r=Path('/home/dikini/Projects/ash-lang');os.chdir(r)
d=r/'.worktree/recovery/arena-completion-20261009/integration-regression-1';d.mkdir(exist_ok=False)
def pins():
 names=subprocess.check_output(['git','ls-files','-z']).decode().split('\0')
 return {n:hashlib.sha256(Path(n).read_bytes()).hexdigest() for n in names if n and (n.endswith(('.rs','.ash','.toml','.lock')) or n=='rust-toolchain') and Path(n).is_file()}
source=pins();drafts=json.loads((d.parent/'unrelated-draft-pins.json').read_text())
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();tree=subprocess.check_output(['git','rev-parse','HEAD^{tree}'],text=True).strip();branch=subprocess.check_output(['git','branch','--show-current'],text=True).strip()
assert branch=='codex/provider-experiments',branch
log=d/'verify.log';cmd=['cargo','xtask','verify'];start=time.monotonic();env=dict(os.environ,CARGO_BUILD_JOBS='1',RUSTC_WRAPPER='',RUST_TEST_THREADS='1');env.pop('ASH_ARENA_DIAGNOSTICS',None)
receipt={'head':head,'tree':tree,'branch':branch,'cwd':str(r),'command':cmd,'source_before':source,'drafts_before':drafts,'completed':False}
(d/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print('START integration gate',head,tree,flush=True)
with log.open('w') as f:ret=subprocess.run(cmd,env=env,stdout=f,stderr=subprocess.STDOUT)
receipt.update(completed=True,exit_code=ret.returncode,elapsed_seconds=time.monotonic()-start,log=str(log),log_sha256=hashlib.sha256(log.read_bytes()).hexdigest(),source_after=pins(),post_head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
receipt['draft_mismatches']=[n for n,h in drafts.items() if hashlib.sha256(Path(n).read_bytes()).hexdigest()!=h]
receipt['source_unchanged']=receipt['source_before']==receipt['source_after'];receipt['passed']=ret.returncode==0 and receipt['source_unchanged'] and not receipt['draft_mismatches'] and receipt['post_head']==head
text=log.read_text();blocks=re.split(r'(?m)^\s*Running ',text)[1:];summaries=[]
for block in blocks:
 matches=re.findall(r'(?m)^test result: (ok|FAILED)\. (\d+) passed; (\d+) failed; (\d+) ignored;',block)
 if matches:
  state,passed,failed,ignored=matches[-1];summaries.append({'target':block.splitlines()[0],'status':state,'passed':int(passed),'failed':int(failed),'ignored':int(ignored)})
receipt['target_summaries']=summaries;receipt['totals']={key:sum(t[key] for t in summaries) for key in ['passed','failed','ignored']}
receipt['steps']=re.findall(r'(?m)^running (format|metadata|build|clippy|test|documentation) check$',text)
(d/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:receipt[k] for k in ['passed','exit_code','elapsed_seconds','totals','steps','source_unchanged','draft_mismatches']}),flush=True)
raise SystemExit(not receipt['passed'])
