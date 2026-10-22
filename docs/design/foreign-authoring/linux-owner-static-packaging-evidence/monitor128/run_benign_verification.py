"""One benign source-equal suite and production-default no-op; no native tool."""
from pathlib import Path
import hashlib,json,os,subprocess,tempfile,time
R=Path('/tmp/ash-owner-map128-monitor');O=R/'verification-run'
PINS={R/'build_monitor.py':'62adc0d5264b0d08835079174a19db49de954b0fa51e97ede216d036e549c914',R/'test_monitor.py':'d786829c5aa6834334d7630a5d0b64a7276acb2bcc678638876a7f4159504cb0',Path('/usr/bin/python3.14'):'52e0a13e60a981d8c4b6478be2ba5176f69da07948a056bf49cf6f077e30cb41',Path('/tmp/ash-owner-build-monitor/build_monitor.py'):'14aae43130d74022568e849ca83b912aa63b9572fa971d0963a2a46c39347e60',Path('/tmp/ash-owner-build-monitor/test_monitor.py'):'49f9440a5ad421a071d8f0e53c42d3ac09413b58bc2e9436366b3527bbb5763d',Path('/tmp/ash-owner-map-class-monitor/build_monitor.py'):'b36fbefca8bdec200da79d01c36dc0c90039f948e6e0ca26c5d3d5cab17606a0',Path('/tmp/ash-owner-map-class-monitor/test_monitor.py'):'2516606e251c73640c96895ef063933566aa68dbde3ea8f1426e8fffb0e1e4b0'}
HIST=[(Path('/tmp/ash-owner-build-monitor/manifest-repaired.json'),'b8fa966fbcedabf7143dcdb280a04df364090e8bae4c59a236d3885cc36c3de2'),(Path('/tmp/ash-owner-map-class-monitor/review-manifest.json'),'637d3f361af2cd383ef6faef29e624ab6824b1e1f9827cbb9f1750b02cd05ad7')]
ENV={'PATH':'/home/dikini/.rustup/toolchains/1.97.1-x86_64-unknown-linux-gnu/bin:/usr/bin:/bin','LANG':'C','LC_ALL':'C'}
def pin(p):
 p=Path(p);h=hashlib.sha256();n=0
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b);n+=len(b)
 return {'path':str(p),'size':n,'sha256':h.hexdigest()}
def js(name,v):(O/name).write_text(json.dumps(v,indent=2)+'\n')
def verify():
 rows=[pin(p) for p in PINS]
 for x in rows:assert x['sha256']==PINS[Path(x['path'])],x
 historical=[]
 for m,expected in HIST:
  actual=pin(m);assert actual['sha256']==expected
  items=json.loads(m.read_text())['files']
  for x in items:
   a=pin(m.parent/x['path']);assert a['size']==x['size'] and a['sha256']==x['sha256'],a
  historical.append({'manifest':actual,'all_records_equal':True,'record_count':len(items)})
 assert Path('/usr/bin/python3').resolve()==Path('/usr/bin/python3.14')
 return {'source_and_interpreter':rows,'historical':historical}
assert not O.exists(),'Never silently rerun';O.mkdir(mode=0o700)
before=verify();js('before.json',before)
old={p.name for p in R.glob('safe-test-evidence-*')}
argv=['/usr/bin/python3.14','-I','-S','-B',str(R/'test_monitor.py')]
js('suite-command.json',{'argv':argv,'cwd':str(R),'environment':ENV,'stdin':'DEVNULL','deadline_seconds':180,'scope':'21 benign test methods only'})
start=time.monotonic();c=subprocess.run(argv,cwd=R,env=ENV,stdin=subprocess.DEVNULL,capture_output=True,timeout=180)
(O/'suite-stdout.log').write_bytes(c.stdout);(O/'suite-stderr.log').write_bytes(c.stderr)
assert len(c.stdout)<=16777216 and len(c.stderr)<=16777216 and c.returncode==0,'Suite failed: stop, no rerun'
assert b'Ran 21 tests' in c.stderr and c.stderr.rstrip().endswith(b'OK')
created=[p for p in R.glob('safe-test-evidence-*') if p.name not in old];assert len(created)==1
cases=[]
for case in sorted(created[0].iterdir()):
 v=json.loads((case/'receipt.json').read_text());o=json.loads((case/'test-outcome.json').read_text());assert v['monitor']['sha256']==PINS[R/'build_monitor.py']
 assert v['cleanup']['all_children_reaped'] and not v['cleanup']['remaining_children'] and o['private_fixture_disposed']
 cases.append({'case':case.name,'receipt':pin(case/'receipt.json'),'config':pin(case/'config.json'),'reason':v['reason'],'returncode':o['returncode'],'all_reaped':True,'fixture_disposed':True})
assert len(cases)==36
js('suite-receipt.json',{'status':'PASS_BENIGN_METHODS','exit':c.returncode,'methods':21,'receipt_cases':36,'elapsed_seconds':time.monotonic()-start,'evidence_directory':str(created[0]),'cases':cases})
# A real no-op uses NO self-test override; records actual default128/16/16 limits.
obs=O/'production-noop';obs.mkdir(mode=0o700)
with tempfile.TemporaryDirectory(prefix='benign-production-config-',dir=R) as tmp:
 parent=Path(tmp);python=pin('/usr/bin/python3.14')
 config={'argv':['/usr/bin/python3.14','-I','-S','-B','-c','pass'],'executable_pin':{'size':python['size'],'sha256':python['sha256']},'cwd':tmp,'output_parent':tmp,'watch_root':tmp,'environment':{},'input_files':[],'artifact_files':[],'map_relative_path':'whole-static.map'}
 cfg=parent/'config.json';cfg.write_text(json.dumps(config,indent=2)+'\n');(obs/'config.json').write_bytes(cfg.read_bytes())
 cmd=['/usr/bin/python3.14','-I','-S','-B',str(R/'build_monitor.py'),str(cfg)]
 (obs/'command.json').write_text(json.dumps({'argv':cmd,'cwd':str(R),'environment':ENV,'scope':'Trusted benign Python pass only, production DEFAULT cap observation; no map/outputparent/candidate build'},indent=2)+'\n')
 done=subprocess.run(cmd,cwd=R,env=ENV,stdin=subprocess.DEVNULL,capture_output=True,timeout=30)
 (obs/'stdout.log').write_bytes(done.stdout);(obs/'stderr.log').write_bytes(done.stderr)
 response=json.loads(done.stdout);path=Path(response['receipt']);v=json.loads(path.read_text());(obs/'receipt.json').write_bytes(path.read_bytes());(obs/'output.log').write_bytes(Path(v['output_path']).read_bytes())
 assert done.returncode==0 and v['reason']=='exit' and v['child_exit']==0 and v['schema']==2
 assert v['limits']=={'deadline_seconds':1200,'output_bytes':16777216,'sidefile_bytes':16777216,'map_bytes':134217728}
 assert v['map_relative_path']=='whole-static.map' and not v['watched_files'] and v['observed_output_bytes']==0
 assert v['cleanup']['all_children_reaped'] and v['cleanup']['reaped_count']==1 and not v['cleanup']['remaining_children'] and not v['cleanup']['escaped_group_detected'] and not v['cleanup']['reaping_pending'] and not v.get('final_limit_failures')
 assert v['monitor']['sha256']==PINS[R/'build_monitor.py']
assert not parent.exists()
(obs/'outcome.json').write_text(json.dumps({'exit':done.returncode,'no_self_test_override':True,'actual_default_map_bytes':134217728,'actual_default_log_and_output_bytes':16777216,'private_benign_fixture_disposed':True,'all_children_reaped':True,'map_allocated':False,'real_build_output_parent_created':False,'native_tool_or_candidate_run':False},indent=2)+'\n')
after=verify();js('after.json',after);assert before==after
js('verification-receipt.json',{'status':'PASS_PREPARATION_ONLY_NOT_ACTIVATED','source_and_historical_before_after_equal':True,'suite_methods':21,'suite_receipt_cases':36,'production_default_noop_cases':1,'native_or_build_commands_run':False})
print(json.dumps({'suite_exit':0,'suite_methods':21,'suite_receipt_cases':36,'production_default_noop_exit':0,'source_and_historical_before_after_equal':True,'verification':str(O)}))
