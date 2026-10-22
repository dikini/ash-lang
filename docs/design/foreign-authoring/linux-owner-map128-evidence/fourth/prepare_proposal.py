"""Prepare fourth proposal only; never invokes compiler/linker/inspection."""
from pathlib import Path
import json,hashlib,ast
R=Path('/tmp/ash-owner-static-stage3-mangled');OLD=Path('/tmp/ash-owner-static-stage3-map64');POST=Path('/tmp/ash-owner-map64-postmortem')
def pin(p):
 p=Path(p);h=hashlib.sha256();n=0
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b);n+=len(b)
 return {'path':str(p),'resolved':str(p.resolve()),'size':n,'sha256':h.hexdigest()}
def load(p):return json.loads(p.read_text())
def js(p,v):p.write_text(json.dumps(v,indent=2)+'\n')
for row in load(OLD/'manifest.json')['files']:
 a=pin(OLD/row['path']);assert a['size']==row['size'] and a['sha256']==row['sha256']
for name in ['experiment-contract.md','default-linker-inputs.json','map-detail-evidence.json','verify_inputs.py','prepare_candidate.py','finalize_static.py']:(R/name).write_bytes((OLD/name).read_bytes())
# Receipt disclosure only; full-map/LOAD/libc/static checks and all caps unchanged.
p=R/'finalize_static.py';s=p.read_text().replace("'discarded_section_diagnostics_suppressed':True", "'discarded_section_diagnostics_suppressed':True,'symbol_name_rendering':'mangled (--no-demangle); no additional active-map record removal'",1);p.write_text(s);ast.parse(s)
for name in ['relink.monitor.json','inspection.monitor.json']:
 c=load(OLD/name);c['argv']=[x.replace(str(OLD),str(R)) for x in c['argv']]
 if name=='relink.monitor.json':c['argv']+=['-C','link-arg=-Wl,--no-demangle']
 for k in ['output_parent','watch_root']:c[k]=str(R)
 if c['cwd']==str(OLD):c['cwd']=str(R)
 c['artifact_files']=[x.replace(str(OLD),str(R)) for x in c['artifact_files']]
 updated=[]
 for a in c['input_files']:
  p=Path(a['path']);p=R/p.name if p.parent==OLD else p
  updated.append({k:v for k,v in pin(p).items() if k!='resolved'})
 c['input_files']=updated;assert c['map_relative_path']=='whole-static.map' and 'self_test_limits' not in c;js(R/name,c)
prov=load(OLD/'provenance.json');prov['status']='FOURTH_REPRESENTATION_ONLY_PROPOSAL_NOT_ASSIGNED';prov['retained_amendment']['contract']=pin(R/'experiment-contract.md')
prov['failed_attempts'].append({'inventory':pin(OLD/'execution-manifest.json'),'sequence':pin(OLD/'execution-readback.json'),'monitor_receipt':pin(OLD/'build-run-5p6l8giw/receipt.json'),'exact_bounded_prefix':pin(OLD/'build-run-5p6l8giw/watched-0.log'),'full_map_hash_claimed':False,'remains_refused':True})
prov['representation_proposal']={'new_root_only_argument':['-C','link-arg=-Wl,--no-demangle'],'analysis':pin(POST/'prefix-analysis.json'),'postmortem':pin(POST/'README.md'),'postmortem_manifest':pin(POST/'manifest.json'),'manual':{'path':'/usr/share/man/man1/ld.bfd.1.gz','size':49180,'sha256':'2f7c363d588b25cf60ac64322f3cd30eb01c7807e6bddaa82580d256dbdd1e9e'},'scope':'Only output symbol-name representation; no additional map record removal, cap/semantic/native change, fit/candidate byte-identity claim or execution permission.'};js(R/'provenance.json',prov)
local={'experiment-contract.md','default-linker-inputs.json','map-detail-evidence.json','verify_inputs.py','prepare_candidate.py','finalize_static.py','relink.monitor.json','inspection.monitor.json','provenance.json'}
spec=load(OLD/'preflight-inputs.json');spec['pins']=[pin(R/Path(x['path']).name) if Path(x['path']).parent==OLD and Path(x['path']).name in local else x for x in spec['pins']]
for a in prov['failed_attempts'][-1].values():
 if isinstance(a,dict) and 'path' in a and a['path'] not in {x['path'] for x in spec['pins']}:spec['pins'].append(a)
for a in prov['representation_proposal'].values():
 if isinstance(a,dict) and 'resolved' in a and a['path'] not in {x['path'] for x in spec['pins']}:spec['pins'].append(a)
spec['private_directories']=[str(R) if x==str(OLD) else x for x in spec['private_directories']]
spec['cargo_config_absence_paths']=[x.replace(str(OLD),str(R)) for x in spec['cargo_config_absence_paths']];js(R/'preflight-inputs.json',spec)
t=load(OLD/'tuple.json');t['status']='FOURTH_STAGE3_NO_DEMANGLE_REVIEW_ONLY_NOT_ASSIGNED';t['working_directory']=str(R)
for k,name in [('relink_config','relink.monitor.json'),('inspection_config','inspection.monitor.json'),('preflight','preflight-inputs.json'),('verifier','verify_inputs.py'),('candidate_collector','prepare_candidate.py'),('receipt_collector','finalize_static.py'),('provenance','provenance.json')]:t[k]=pin(R/name)
for seq in t['sequence']:
 seq['argv']=[x.replace(str(OLD),str(R)) for x in seq['argv']]
 for key in ['retain_stdout','retain_stderr']:seq[key]=seq[key].replace(str(OLD),str(R))
t['explicit_passive_readelf_child_argv']=[x.replace(str(OLD),str(R)) for x in t['explicit_passive_readelf_child_argv']]
t['prior_failures']=prov['failed_attempts'];t['diagnostic_only_change']={'new_argument':['-C','link-arg=-Wl,--no-demangle'],'unchanged_discard_suppression':'-C link-arg=-Wl,--no-print-map-discarded','evidence':pin(POST/'prefix-analysis.json'),'meaning':'Render output symbol names in mangled form without removing additional active-map symbol/address/archive records. No semantic/native/source/cap change or prediction of complete-map fit. Fresh artifact bytes still required.'}
t.pop('preparation_space_observation');js(R/'tuple.json',t)
oldargv=load(OLD/'relink.monitor.json')['argv'];newargv=load(R/'relink.monitor.json')['argv'];assert newargv[:-2]==[x.replace(str(OLD),str(R)) for x in oldargv];assert newargv[-2:]==['-C','link-arg=-Wl,--no-demangle']
assert not any((R/x).exists() for x in ['whole-static.map','static-host','relink-response.json','inspection-response.json','static-receipt.json'])
print('Fourth proposal staged, no tool command executed')
