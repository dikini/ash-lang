from pathlib import Path
import os,stat,json,hashlib,subprocess,time
R=Path('/home/dikini/Projects/ash-lang/.worktree/generic-cells/target/checked-ffi-owner-packaging/owner-diagnostic')
def pin(p):
 h=hashlib.sha256();n=0
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b);n+=len(b)
 return dict(path=str(p),size=n,sha256=h.hexdigest())
L=R/'launch-proposal.json';assert pin(L)['sha256']=='a165be2f6fc49885753fe8f7c5c95d2561bf37d690eacc8014ffb01227303eea'
t=json.loads(L.read_text());assert t['environment']=={'PATH':'/usr/bin:/bin','LANG':'C','LC_ALL':'C'}
assert t['argv']==['/usr/bin/python3.14','-I','-S','-B',str(R/'diagnostic.py'),'--approval',str(R/'root-approval.json')] and t['cwd']==str(R)
st=R.stat();assert not R.is_symlink() and str(R.resolve())==str(R) and (st.st_dev,st.st_ino,st.st_uid,stat.S_IMODE(st.st_mode))==(66309,49555204,1000,0o700)
for n in ['diagnostic.py','policy.json','root-approval.json']:
 p=R/n;assert not p.is_symlink() and p.stat().st_uid==1000 and stat.S_IMODE(p.stat().st_mode)==0o400
for n in ['sandbox-stdout.json','sandbox-stderr.log','sandbox-execution.json','execution-manifest.json','actual-handoff.json']:assert not (R/n).exists()
assert not list(R.glob('case-*'))
before=[pin(Path(a['path'])) for a in t['pins']];assert before==t['pins']
assert pin(R/'root-approval.json')['sha256']=='24dc707fbdfdc4fd168808304ebe122af80c13f1c8b3254cd244baba9615e7bd'
assert pin(Path('/usr/bin/python3.14'))==t['interpreter']
record={'scope':'One root-assigned default-sandbox owner diagnostic, no host fallback','launch':pin(L),'before':before,'interpreter_before':pin(Path('/usr/bin/python3.14')),'argv':t['argv'],'cwd':t['cwd'],'environment':t['environment'],'directory_identity':t['directory'],'started_unix':time.time()}
p=R/'sandbox-execution.json'
def save():p.write_text(json.dumps(record,indent=2)+'\n')
save()
with Path(t['output_stdout']).open('xb') as o,Path(t['output_stderr']).open('xb') as e:
 proc=subprocess.Popen(t['argv'],cwd=t['cwd'],env=t['environment'],stdin=subprocess.DEVNULL,stdout=o,stderr=e);record['pid']=proc.pid;save();print(json.dumps({'started_pid':proc.pid}),flush=True);code=proc.wait()
record.update(exit=code,finished_unix=time.time(),stdout=pin(Path(t['output_stdout'])),stderr=pin(Path(t['output_stderr'])),after=[pin(Path(a['path'])) for a in t['pins']],interpreter_after=pin(Path('/usr/bin/python3.14')));record['all_pins_before_after_equal']=record['before']==record['after'] and record['interpreter_before']==record['interpreter_after'];save()
print(json.dumps({'exit':code,'all_pins_before_after_equal':record['all_pins_before_after_equal'],'stdout':record['stdout'],'stderr':record['stderr']}),flush=True)
raise SystemExit(0 if code==0 and record['all_pins_before_after_equal'] else 1)
