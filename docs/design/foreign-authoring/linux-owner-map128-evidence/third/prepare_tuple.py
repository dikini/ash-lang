"""Prepare data/scripts only. No Cargo/readelf/candidate command is executed."""
from pathlib import Path
import json,hashlib,subprocess,ast,os
R=Path('/tmp/ash-owner-static-stage3-map64'); OLD=Path('/tmp/ash-owner-static-stage3-map-detail'); M=Path('/tmp/ash-owner-map-class-monitor'); REPO=Path('/home/dikini/Projects/ash-lang')
COMMIT='88db679943c981458b829e1c430e9af290976d9f'; CONTRACT='7e81587b5598f1d7184ce268725e2a1296341c8e84415a44de7cc180d65527ef'; MON='b36fbefca8bdec200da79d01c36dc0c90039f948e6e0ca26c5d3d5cab17606a0'; PREVIOUS='14aae43130d74022568e849ca83b912aa63b9572fa971d0963a2a46c39347e60'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p):
 p=Path(p);h=hashlib.sha256();n=0
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b);n+=len(b)
 return {'path':str(p),'resolved':str(p.resolve()),'size':n,'sha256':h.hexdigest()}
def js(p,v):p.write_text(json.dumps(v,indent=2)+'\n')
def load(p):return json.loads(p.read_text())
assert pin(M/'build_monitor.py')['sha256']==MON
b=subprocess.check_output(['git','show',COMMIT+':docs/design/foreign-authoring/linux-owner-inprocess-experiment.md'],cwd=REPO);assert sha(b)==CONTRACT;(R/'experiment-contract.md').write_bytes(b)
for name in ['default-linker-inputs.json','map-detail-evidence.json']:(R/name).write_bytes((OLD/name).read_bytes())
# Verifier remains read-only; add actual available-space observation and a finite known-artifact floor.
s=(OLD/'verify_inputs.py').read_text()
s=s.replace("phase = sys.argv[1]", "space = os.statvfs(ROOT)\navailable_bytes = space.f_bavail * space.f_frsize\nif available_bytes < spec['known_output_footprint_bytes']:\n    raise SystemExit('insufficient observed temporary space for enumerated bounded outputs; no reservation or quota')\nphase = sys.argv[1]",1)
s=s.replace("'source_is_hash_frozen_not_hostile_writer_containment':True", "'source_is_hash_frozen_not_hostile_writer_containment':True,'temporary_available_bytes':available_bytes,'known_output_footprint_bytes':spec['known_output_footprint_bytes'],'space_is_observation_not_reservation':True",1);(R/'verify_inputs.py').write_text(s)
# Both collectors bind the new monitor, while all generated/native/source gates remain.
for name in ['prepare_candidate.py','finalize_static.py']:
 s=(OLD/name).read_text().replace("MONITOR=Path('/tmp/ash-owner-build-monitor/build_monitor.py')", "MONITOR=Path('/tmp/ash-owner-map-class-monitor/build_monitor.py')").replace(PREVIOUS,MON)
 if name=='prepare_candidate.py':
  needle="need(r['reason']=='exit'"
  extra="""need(r['schema']==2 and r['map_relative_path']=='whole-static.map','wrong map monitor schema/path')
need(r['limits']=={'deadline_seconds':1200,'output_bytes':16777216,'sidefile_bytes':16777216,'map_bytes':67108864},'map/log limit split differs')
"""
  s=s.replace(needle,extra+needle,1)
 else:
  s=s.replace("map_bytes=read(map_path,16777216)","map_bytes=read(map_path,67108864)",1)
  s=s.replace("'contract_retained_commit':'2ac8c393846715249de5a475a65e47bf1309bb54','contract_sha256':'27430b69ee44dcbcb835a83dc38ff2b034826b81dddae40b7bb9ba7b4377cc3e'", "'contract_retained_commit':'"+COMMIT+"','contract_sha256':'"+CONTRACT+"','historical_generation_contract_sha256':'27430b69ee44dcbcb835a83dc38ff2b034826b81dddae40b7bb9ba7b4377cc3e'",1)
  s=s.replace("map_path=ROOT/'whole-static.map';", """relink=json.loads(read(receipt_path,4194304))
need(relink['schema']==2 and relink['map_relative_path']=='whole-static.map','wrong relink map policy')
need(relink['limits']=={'deadline_seconds':1200,'output_bytes':16777216,'sidefile_bytes':16777216,'map_bytes':67108864},'relink class bounds differ')
map_rows=[row for row in relink['watched_files'] if row['relative_path']=='whole-static.map']
need(len(map_rows)==1,'exact map observation missing/duplicated')
map_record=map_rows[0]
need(map_record['file_class']=='link_map' and map_record['limit_bytes']==67108864 and not map_record['hash_is_prefix'] and map_record['observed_peak_bytes']<=67108864,'incomplete/oversize/noncanonical map observation')
map_path=ROOT/'whole-static.map';""",1)
  s=s.replace('require_explicit_libc(loads)\nmanifest=', """require_explicit_libc(loads)
complete_map=digest(map_path)
need(complete_map['sha256']==map_record['sha256'] and complete_map['size']==map_record['hashed_bytes']==map_record['size_before']==map_record['size_after'],'complete map differs from settled monitored bytes')
manifest=""",1)
  s=s.replace("'link_map':digest(map_path)","'link_map':complete_map,'map_policy':{'exact_relative_path':'whole-static.map','map_bytes':67108864,'other_watched_log_bytes':16777216,'discarded_section_diagnostics_suppressed':True,'observed_peak_bytes':map_record['observed_peak_bytes'],'sampling_not_quota':True}",1)
 (R/name).write_text(s);ast.parse(s,filename=name)
# Keep source/tool/native pins and all old observation associations as historical inputs.
remapped={'verify_inputs.py','prepare_candidate.py','finalize_static.py','default-linker-inputs.json','map-detail-evidence.json','relink.monitor.json','inspection.monitor.json'}
def newpath(text):
 p=Path(text)
 return str(R/p.name) if p.parent==OLD and p.name in remapped else text
for name in ['relink.monitor.json','inspection.monitor.json']:
 c=load(OLD/name)
 c['argv']=[x.replace(str(OLD),str(R)) for x in c['argv']]
 for k in ['output_parent','watch_root'] :c[k]=str(R)
 if name=='inspection.monitor.json':c['cwd']=str(R)
 c['artifact_files']=[x.replace(str(OLD),str(R)) for x in c['artifact_files']]
 c['map_relative_path']='whole-static.map'
 c['input_files']=[{k:v for k,v in pin(newpath(x['path'])).items() if k!='resolved'} for x in c['input_files']]
 c['input_files'].append({k:v for k,v in pin(R/'experiment-contract.md').items() if k!='resolved'})
 js(R/name,c)
# Exact provenance for retained amendment, reviewed benign monitor, and both real map refusals.
provenance={'status':'THIRD_ATTEMPT_PREPARATION_ONLY_NO_ASSIGNMENT','retained_amendment':{'commit':COMMIT,'parent':'c8a1fee506a00f68065cb08c6e2e9911d44a58aa','tree':'d32739241785a8a84a049e9c2c9c36165538dc77','contract':pin(R/'experiment-contract.md')},'monitor_preparation':{'source':pin(M/'build_monitor.py'),'tests':pin(M/'test_monitor.py'),'schema':pin(M/'schema2.json'),'manifest':pin(M/'review-manifest.json'),'fresh_suite':pin(M/'reviewed-suite/suite-receipt.json'),'source_before':pin(M/'reviewed-suite/before.json'),'source_after':pin(M/'reviewed-suite/after.json'),'command':pin(M/'reviewed-suite/command.json'),'qualification':'Independent preparation clear; reduced synthetic caps, no real map success or tuple assignment.'},'failed_attempts':[]}
for folder,run in [('ash-owner-static-stage3','build-run-mwoqlg55'),('ash-owner-static-stage3-map-detail','build-run-gbjzjclf')]:
 p=Path('/tmp')/folder
 provenance['failed_attempts'].append({'inventory':pin(p/'execution-manifest.json'),'sequence':pin(p/'execution-readback.json'),'monitor_receipt':pin(p/run/'receipt.json'),'exact_bounded_prefix':pin(p/run/'watched-0.log'),'full_map_hash_claimed':False,'remains_refused':True})
js(R/'provenance.json',provenance)
spec=load(OLD/'preflight-inputs.json');spec['pins']=[pin(newpath(x['path'])) if Path(x['path']).parent==OLD and Path(x['path']).name in remapped else x for x in spec['pins']]
spec['pins']=[pin(M/'build_monitor.py') if x['path']=='/tmp/ash-owner-build-monitor/build_monitor.py' else x for x in spec['pins']]
spec['pins'].append(pin(R/'experiment-contract.md'));spec['pins'].append(pin(R/'provenance.json'))
for x in provenance['monitor_preparation'].values():
 if isinstance(x,dict) and 'path' in x and x['path'] not in {p['path'] for p in spec['pins']}:spec['pins'].append(x)
for a in provenance['failed_attempts']:
 for x in a.values():
  if isinstance(x,dict) and 'path' in x and x['path'] not in {p['path'] for p in spec['pins']}:spec['pins'].append(x)
spec['private_directories']=[str(R) if x==str(OLD) else x for x in spec['private_directories']]
spec['cargo_config_absence_paths']=[x.replace(str(OLD),str(R)) for x in spec['cargo_config_absence_paths']]
spec['known_output_footprint']={'raw_map':67108864,'two_monitors_retained_map_copies':2*67108864,'candidate':134217728,'two_monitor_outputs':2*16777216,'two_monitor_receipts':2*4194304,'static_manifest':4194304,'static_receipt':262144,'candidate_record':262144}
spec['known_output_footprint_bytes']=sum(spec['known_output_footprint'].values());spec['space_qualification']='Observed available bytes before/after are not reserved; sampled monitoring is not quota. This enumerates known artifact maxima, not every possible intermediate or sidefile, and does not authorize deletion or widening.'
js(R/'preflight-inputs.json',spec)
t=load(OLD/'tuple.json');t['status']='THIRD_STAGE3_MAP64_REVIEW_ONLY_NOT_ASSIGNED';t['contract_commit']=COMMIT;t['contract_sha256']=CONTRACT
for key,name in [('monitor',None),('relink_config','relink.monitor.json'),('inspection_config','inspection.monitor.json'),('preflight','preflight-inputs.json'),('verifier','verify_inputs.py'),('candidate_collector','prepare_candidate.py'),('receipt_collector','finalize_static.py')]:t[key]=pin(M/'build_monitor.py' if key=='monitor' else R/name)
t['working_directory']=str(R)
for seq in t['sequence']:
 seq['argv']=[x.replace(str(OLD),str(R)).replace('/tmp/ash-owner-build-monitor/build_monitor.py',str(M/'build_monitor.py')) for x in seq['argv']]
 for key in ['retain_stdout','retain_stderr']:seq[key]=seq[key].replace(str(OLD),str(R))
t['explicit_passive_readelf_child_argv']=[x.replace(str(OLD),str(R)) for x in t['explicit_passive_readelf_child_argv']]
t['limits'].pop('each_map_or_build_log_bytes');t['limits'].update({'complete_map_bytes':67108864,'each_other_watched_sidefile_or_log_bytes':16777216})
t['prior_failures']=provenance['failed_attempts'];t.pop('prior_failure');t['provenance']=pin(R/'provenance.json');t['map_policy']={'exact_relative_map_path':'whole-static.map','monitor_receipt_schema':2,'map64_log16':True,'qualified_observed_peaks_not_hard_quota':True,'collector_complete_map_matches_monitor_record':True}
t['diagnostic_only_change']['meaning']='Unchanged from second attempt: discard diagnostics suppressed. This third proposal changes only map-specific record cap/monitor/collector associations and fresh paths, not source/native/symbol/semantic flags.'
t['limits']['known_output_footprint_bytes']=spec['known_output_footprint_bytes'];t['historical_generation_contract_sha256']='27430b69ee44dcbcb835a83dc38ff2b034826b81dddae40b7bb9ba7b4377cc3e'
t['success']+=' Complete map<=64MiB must match settled monitor full hash (no prefix), recognized GNU/BFD framing, nonempty LOAD and exact pinned libc.a. Logs/output<=16MiB; observed free-space floor is not storage reservation.'
js(R/'tuple.json',t)
# No fresh command config has been executed by this preparer.
for name in ['whole-static.map','static-host','candidate-record.json','static-manifest.json','static-receipt.json']:assert not (R/name).exists()
print(json.dumps({'tuple':pin(R/'tuple.json'),'relink':pin(R/'relink.monitor.json'),'inspection':pin(R/'inspection.monitor.json'),'known_output_floor':spec['known_output_footprint_bytes']},indent=2))
