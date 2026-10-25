"""Exact root-assigned six-step execution, no retry or candidate startup."""
from pathlib import Path
import hashlib,json,os,subprocess,sys,time
R=Path('/tmp/ash-owner-static-stage3-mangled')
ANCHORS={
R/'tuple.json':'8a7135d8a59d34edfbc5ff78cf0e24252c9b9613e3bdbda978a0c4a1e128f390',
R/'relink.monitor.json':'77d7591aeebdb62af79525b0327cb303ad3dac23cb1790340286f0638767d7b0',
R/'inspection.monitor.json':'9cd21cd0b2173bb00e37893c97919ec0f533651492759b818e039129a8806eb5',
R/'manifest.json':'887cf3244263bdde6c33c0ef19065768e346d778812e34ba167269c9d842f9a9',
R/'preflight-inputs.json':'d13aaf43f324abfee7ace916c163a8408c5024f1810d5ce70165a50f66e751fc',
R/'verify_inputs.py':'693c4f2707baa5c4d7a6f7a8ebf2f9b84fce27f2a5ec52e42c8f2f58a2846b36',
R/'prepare_candidate.py':'bb7fc46163204bfe6072b1cb37852a2621825de8bd187bd270a3984d5f01d394',
R/'finalize_static.py':'95743eceb7704b7d7367d716e3c3eb7574146ccf3a94d531336c145a6f44ff03',
Path('/tmp/ash-owner-map-class-monitor/build_monitor.py'):'b36fbefca8bdec200da79d01c36dc0c90039f948e6e0ca26c5d3d5cab17606a0',
Path('/usr/bin/python3.14'):'52e0a13e60a981d8c4b6478be2ba5176f69da07948a056bf49cf6f077e30cb41'}
def pin(p):
 h=hashlib.sha256();n=0
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b);n+=len(b)
 return {'path':str(p),'size':n,'sha256':h.hexdigest()}
record={'status':'ANCHOR_CHECK','anchors':{},'steps':[],'scope':'Root-assigned Stage3 packaging/passive inspection only; no startup','image_executed':False}
def save():
 (R/'execution-readback.pending').write_text(json.dumps(record,indent=2)+'\n');(R/'execution-readback.pending').replace(R/'execution-readback.json')
assert not (R/'execution-readback.json').exists(),'Do not rerun'
for path,expected in ANCHORS.items():
 actual=pin(path);assert actual['sha256']==expected,(path,actual);record['anchors'][str(path)]=expected
record['external_anchors_equal']=True
# Every frozen package file must still equal the independently reviewed manifest.
for row in json.loads((R/'manifest.json').read_text())['files']:
 actual=pin(R/row['path']);assert actual['size']==row['size'] and actual['sha256']==row['sha256'],row
record['reviewed_manifest_all_equal']=True;save()
t=json.loads((R/'tuple.json').read_text());env={'PATH':'/home/dikini/.rustup/toolchains/1.97.1-x86_64-unknown-linux-gnu/bin:/usr/bin:/bin','LANG':'C','LC_ALL':'C'}
assert t['outer_environment']==env and t['working_directory']==str(R)
for s in t['sequence']:
 assert s['environment']==env and s['argv'][:4]==['/usr/bin/python3.14','-I','-S','-B']
 out=Path(s['retain_stdout']);err=Path(s['retain_stderr'])
 row={'name':s['name'],'phase':s['phase'],'argv':s['argv'],'environment':env,'stdout':str(out),'stderr':str(err),'started_unix':time.time()};record['steps'].append(row);record['status']='RUNNING';save()
 with out.open('xb') as stdout,err.open('xb') as stderr:
  proc=subprocess.Popen(s['argv'],cwd=R,env=env,stdin=subprocess.DEVNULL,stdout=stdout,stderr=stderr)
  row['pid']=proc.pid;save();print(json.dumps({'started':s['name'],'pid':proc.pid}),flush=True)
  result=proc.wait()
 row['exit']=result;row['finished_unix']=time.time();row['stdout_sha256']=pin(out)['sha256'];row['stderr_sha256']=pin(err)['sha256'];save()
 if result!=0:
  record['status']='REFUSED_STOP_NO_RETRY';record['failed_step']=s['name'];save();print(json.dumps({'status':record['status'],'failed':s['name'],'exit':result}),flush=True);raise SystemExit(1)
 if s['name'] in ('static-relink','readelf-metadata'):
  response=json.loads(out.read_text());mp=Path(response['receipt']);mr=json.loads(mp.read_text());row['monitor_receipt']=pin(mp)
  okay=mr['reason']=='exit' and mr['child_exit']==0 and mr['cleanup']['all_children_reaped'] and not mr['cleanup']['remaining_children'] and not mr['cleanup']['reaping_pending'] and not mr['cleanup']['escaped_group_detected'] and not mr['output_truncated'] and not mr.get('final_limit_failures')
  if not okay:
   record['status']='MONITOR_SEMANTIC_REFUSAL_STOP';save();raise SystemExit(1)
  row['monitor_success_checked']=True;save()
record['status']='SUCCESS_STATIC_PACKAGING_NO_STARTUP';save();print(json.dumps({'status':record['status'],'receipt':str(R/'static-receipt.json'),'readback':str(R/'execution-readback.json')}),flush=True)
