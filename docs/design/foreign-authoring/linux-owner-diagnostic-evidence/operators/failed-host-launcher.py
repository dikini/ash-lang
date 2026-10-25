from pathlib import Path
import os,stat,json,hashlib,subprocess,time
R=Path('/home/dikini/Projects/ash-lang/.worktree/generic-cells/target/checked-ffi-owner-packaging/owner-diagnostic')
def pin(p):
 h=hashlib.sha256();n=0
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b);n+=len(b)
 return dict(path=str(p),size=n,sha256=h.hexdigest())
L=R/'host-launch-proposal.json';assert pin(L)['sha256']=='57fff96d43acbefdbe95c4a6fe27a0478e9d944e62d274f1f8f441599146e449'
t=json.loads(L.read_text());assert t['environment']=={'PATH':'/usr/bin:/bin','LANG':'C','LC_ALL':'C'}
assert t['argv']==['/usr/bin/python3.14','-I','-S','-B',str(R/'diagnostic.py'),'--approval',str(R/'root-approval.json')] and t['cwd']==str(R)
st=R.stat();assert not R.is_symlink() and str(R.resolve())==str(R) and (st.st_dev,st.st_ino,st.st_uid,stat.S_IMODE(st.st_mode))==(66309,49555204,1000,0o700)
for n in ['diagnostic.py','policy.json','root-approval.json']:
 p=R/n;assert not p.is_symlink() and p.stat().st_uid==1000 and stat.S_IMODE(p.stat().st_mode)==0o400
for n in ['host-stdout.json','host-stderr.log','host-execution.json','host-execution-manifest.json','host-actual-handoff.json']:assert not (R/n).exists()
assert {p.name for p in R.glob('case-*')}=={'case-p__lm011'}
sandbox_inventory=pin(R/'execution-manifest.json')
assert sandbox_inventory['sha256']=='b257a33b93b9b89e5a4d820ef68cec0fdb9e0daf4cb5cb435f07e0540cb002b0'
sandbox_rows=json.loads((R/'execution-manifest.json').read_text())['files']
for a in sandbox_rows:
 assert pin(a['path'])=={k:a[k] for k in ['path','size','sha256']}
for key in ['inventory','execution','stdout','actual_handoff']:
 a=t['sandbox_provenance'][key];assert pin(a['path'])==a
before=[pin(Path(a['path'])) for a in t['pins']];assert before==t['pins']
assert pin(R/'root-approval.json')['sha256']=='24dc707fbdfdc4fd168808304ebe122af80c13f1c8b3254cd244baba9615e7bd'
assert pin(Path('/usr/bin/python3.14'))==t['interpreter']
record={'scope':'One separately root-assigned normal-tool-escalated trusted owner diagnostic; sandbox refusal preserved; no retry','launch':pin(L),'before':before,'interpreter_before':pin(Path('/usr/bin/python3.14')),'argv':t['argv'],'cwd':t['cwd'],'environment':t['environment'],'directory_identity':t['directory'],'started_unix':time.time()}
record['sandbox_inventory_before']=sandbox_inventory
p=R/'host-execution.json'
def save():p.write_text(json.dumps(record,indent=2)+'\n')
save()
with Path(t['output_stdout']).open('xb') as o,Path(t['output_stderr']).open('xb') as e:
 proc=subprocess.Popen(t['argv'],cwd=t['cwd'],env=t['environment'],stdin=subprocess.DEVNULL,stdout=o,stderr=e);record['pid']=proc.pid;save();print(json.dumps({'started_pid':proc.pid}),flush=True);code=proc.wait()
record.update(exit=code,finished_unix=time.time(),stdout=pin(Path(t['output_stdout'])),stderr=pin(Path(t['output_stderr'])),after=[pin(Path(a['path'])) for a in t['pins']],interpreter_after=pin(Path('/usr/bin/python3.14')));record['sandbox_inventory_after']=pin(R/'execution-manifest.json')
record['all_sandbox_records_equal']=record['sandbox_inventory_before']==record['sandbox_inventory_after'] and all(pin(a['path'])=={k:a[k] for k in ['path','size','sha256']} for a in sandbox_rows)
record['all_pins_before_after_equal']= record['before']==record['after'] and record['interpreter_before']==record['interpreter_after'];save()
print(json.dumps({'exit':code,'all_pins_before_after_equal':record['all_pins_before_after_equal'],'stdout':record['stdout'],'stderr':record['stderr']}),flush=True)
raise SystemExit(0 if code==0 and record['all_pins_before_after_equal'] and record['all_sandbox_records_equal'] else 1)
