from pathlib import Path
import hashlib,json,os,re,shutil,signal,subprocess,time
ROOT=Path('/home/dikini/Projects/ash-lang/.worktree/checked-owner-passive')
TARGET=Path('/home/dikini/Projects/ash-lang/.worktree/generic-cells/target')
OUT=Path(__file__).resolve().parent
PROPOSAL=Path('/tmp/ash-owner-receipt-source-review/focused-proposal.json')
MANIFEST=Path('/tmp/ash-owner-receipt-source-review/manifest.json')
EXPECTED_PROPOSAL='be1be52df8125d496a7e3012786c543c25cf1126f88959a9687ab810d01b81ca'
EXPECTED_MANIFEST='ca1e1a8e12a9879bfa5c73e182d3be09bb197653c84910b4603697ad45b23d7c'
def pin(path):
    before=path.stat();h=hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda:f.read(1048576),b''):h.update(chunk)
    after=path.stat()
    assert (before.st_dev,before.st_ino,before.st_size,before.st_mtime_ns,before.st_ctime_ns)==(after.st_dev,after.st_ino,after.st_size,after.st_mtime_ns,after.st_ctime_ns)
    return {'path':str(path),'bytes':after.st_size,'sha256':h.hexdigest()}
def inputs():
    names=subprocess.check_output(['git','ls-files','-z','--cached','--others','--exclude-standard'],cwd=ROOT).decode().split('\0')
    return {n:pin(ROOT/n)['sha256'] for n in sorted(set(names)) if n and (ROOT/n).is_file()}
def processes(group=None):
    rows=[]
    for p in Path('/proc').iterdir():
        if not p.name.isdigit():continue
        try:
            raw=(p/'stat').read_text(); tail=raw.rsplit(')',1)[1].split();comm=(p/'comm').read_text().strip();pgid=int(tail[2])
            if (group is not None and pgid==group) or (group is None and comm in ('cargo','rustc','clippy-driver','gdb')):
                rows.append({'pid':int(p.name),'comm':comm,'pgid':pgid,'rss_bytes':int(tail[21])*os.sysconf('SC_PAGE_SIZE')})
        except (FileNotFoundError,PermissionError,ProcessLookupError):pass
    return rows
def sample(group=None):
    with open('/proc/meminfo') as f:mem=f.read(16384)
    found=re.search(r'^MemAvailable:\s+(\d+) kB$',mem,re.M)
    rows=processes(group) if group is not None else []
    return {'unix':time.time(),'available_memory_bytes':int(found[1])*1024 if found else None,'project_free_bytes':shutil.disk_usage(TARGET).free,'tmp_free_bytes':shutil.disk_usage('/tmp').free,'owned_group_rss_sum_bytes':sum(r['rss_bytes'] for r in rows),'processes':rows}
def cache_observation():
    total=files=0
    for directory,dirs,names in os.walk(TARGET):
        if Path(directory)==TARGET:dirs[:]=[d for d in dirs if d!='parallel-f3']
        for name in names:
            try:total+=(Path(directory)/name).lstat().st_size;files+=1
            except FileNotFoundError:pass
    return {'files_observed':files,'apparent_bytes':total,'excluded':'parallel-f3','qualification':'live apparent-size observation, not allocated storage or a reserved/quota/peak bound'}
assert pin(PROPOSAL)['sha256']==EXPECTED_PROPOSAL and pin(MANIFEST)['sha256']==EXPECTED_MANIFEST
proposal=json.loads(PROPOSAL.read_bytes());manifest=json.loads(MANIFEST.read_bytes())
for row in manifest['files']:
    actual=pin(ROOT/row['path']);assert actual['sha256']==row['after']['sha256'] and actual['bytes']==row['after']['bytes']
# F3 is explicitly allowed in its disjoint parallel-f3 cache. Only this
# runner's newly owned groups are cleanup/refusal boundaries.
env=os.environ.copy();env.update(proposal['environment_overrides'])
for key in proposal['required_absent']:assert not env.get(key)
(OUT/'cache-before.json').write_text(json.dumps(cache_observation(),indent=2)+'\n')
(OUT/'runner-process.json').write_text(json.dumps({'pid':os.getpid(),'pgid':os.getpgid(0),'namespace':os.readlink('/proc/self/ns/pid'),'script':pin(Path(__file__)),'proposal':pin(PROPOSAL),'manifest':pin(MANIFEST),'resource_scope':'namespace-local sampled process RSS sums; not unique physical memory, hard quota or complete peak proof'},indent=2)+'\n')
results=[]
for command in proposal['commands']:
    name,expected,argv=command['name'],command['expected_selected'],command['argv']
    before=inputs();before_processes=processes();started=time.monotonic();samples=[sample()];timed_out=False
    (OUT/(name+'.before.json')).write_text(json.dumps(before,indent=2)+'\n');print('BEGIN '+name,flush=True)
    with (OUT/(name+'.log')).open('wb') as output:
        run=subprocess.Popen(argv,cwd=ROOT,env=env,stdout=output,stderr=subprocess.STDOUT,start_new_session=True)
        proc={'pid':run.pid,'pgid':os.getpgid(run.pid),'argv':argv,'cwd':str(ROOT),'started_unix':time.time()}
        (OUT/(name+'.process.json')).write_text(json.dumps(proc,indent=2)+'\n');print('CHILD '+json.dumps(proc),flush=True)
        while True:
            samples.append(sample(run.pid))
            try:run.wait(timeout=5);break
            except subprocess.TimeoutExpired:
                if time.monotonic()-started>proposal['deadline_seconds_per_command']:
                    timed_out=True;os.killpg(run.pid,signal.SIGTERM)
                    try:run.wait(timeout=10)
                    except subprocess.TimeoutExpired:os.killpg(run.pid,signal.SIGKILL);run.wait()
                    break
    after=inputs();samples.append(sample());remaining=processes(run.pid)
    with (OUT/(name+'.log')).open('rb') as f:raw=f.read(16*1024*1024+1)
    output_limit=len(raw)>16*1024*1024;text=raw.decode(errors='replace')
    selected=re.findall(r'^running (\d+) tests?$',text,re.M);actual=int(selected[-1]) if selected else None
    artifacts=[]
    for line in text.splitlines():
        if not line.startswith('{'):continue
        try:message=json.loads(line)
        except json.JSONDecodeError:continue
        if message.get('reason')=='compiler-artifact' and message.get('manifest_path')==str(ROOT/'Cargo.toml'):
            artifact={'cargo':message}
            if message.get('executable'):artifact['observed']=pin(Path(message['executable']))
            artifacts.append(artifact)
    receipt={'command':argv,'cwd':str(ROOT),'exit_code':run.returncode,'seconds':round(time.monotonic()-started,3),'expected_selected':expected,'actual_selected':actual,'timed_out':timed_out,'output_limit':output_limit,'source_count':len(before),'inputs_equal':before==after,'source_aggregate_sha256':hashlib.sha256(json.dumps(before,sort_keys=True,separators=(',',':')).encode()).hexdigest(),'log':pin(OUT/(name+'.log')),'artifacts':artifacts,'child_reaped':run.returncode is not None,'processes_before_namespace':before_processes,'owned_group_after':remaining,'environment':{k:env.get(k) for k in list(proposal['environment_overrides'])+proposal['required_absent']},'resource_observations':{'sample_count':len(samples),'min_available_memory_bytes':min(s['available_memory_bytes'] for s in samples if s['available_memory_bytes'] is not None),'max_sampled_owned_group_rss_sum_bytes':max(s['owned_group_rss_sum_bytes'] for s in samples),'min_project_free_bytes':min(s['project_free_bytes'] for s in samples),'min_tmp_free_bytes':min(s['tmp_free_bytes'] for s in samples)}}
    (OUT/(name+'.inputs.json')).write_text(json.dumps({'before':before,'after':after},indent=2)+'\n');(OUT/(name+'.resources.json')).write_text(json.dumps(samples,indent=2)+'\n');(OUT/(name+'.receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n');results.append(receipt)
    print('END '+name+' '+json.dumps({'exit_code':run.returncode,'selected':actual,'equal':before==after,'remaining':remaining}),flush=True)
    if run.returncode or timed_out or output_limit or actual!=expected or before!=after or remaining or not artifacts:break
(OUT/'batch-results.json').write_text(json.dumps(results,indent=2)+'\n');(OUT/'cache-after.json').write_text(json.dumps(cache_observation(),indent=2)+'\n')
