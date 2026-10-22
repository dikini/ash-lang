"""Post-syntax evidence collection only; never starts a child."""
from pathlib import Path
import hashlib,json,os,stat,sys
R=Path(__file__).parent

def need(ok,why):
    if not ok:raise SystemExit(why)
def read(p,n):
    with p.open('rb') as f:b=f.read(n+1)
    need(len(b)<=n,'record exceeds bound');return b
def pin(p):
    resolved=p.resolve();h=hashlib.sha256();n=0
    with resolved.open('rb') as f:
        before=os.fstat(f.fileno());need(stat.S_ISREG(before.st_mode),'nonregular input')
        while b:=f.read(min(65536,before.st_size-n+1)):
            n+=len(b);need(n<=before.st_size,'input grew');h.update(b)
        after=os.fstat(f.fileno())
    need((before.st_dev,before.st_ino,before.st_size,before.st_mtime_ns)==(after.st_dev,after.st_ino,after.st_size,after.st_mtime_ns),'input changed')
    need(p.resolve()==resolved,'input path association changed')
    return {'path':str(p),'resolved':str(resolved),'size':n,'sha256':h.hexdigest()}
def admit_dependency(path, watched):
    expected=str(path)
    matches=[row for row in watched if row.get('relative_path')=='native-build.log']
    need(len(matches)==1,'missing or duplicate dependency observation')
    row=matches[0]
    need(row.get('path')==expected and path.resolve()==path and not path.is_symlink(),'dependency observation path differs')
    need(row.get('file_class')=='sidefile_log' and row.get('limit_bytes')==16777216,'dependency observation class/cap differs')
    need(row.get('hash_is_prefix') is False,'dependency observation is a prefix')
    need(0<=row.get('observed_peak_bytes',-1)<=16777216,'dependency observed peak invalid')
    with path.open('rb') as f:
        before=os.fstat(f.fileno());need(stat.S_ISREG(before.st_mode),'dependency is not regular')
        data=f.read(1048577);after=os.fstat(f.fileno())
    need(len(data)<=1048576,'dependency exceeds admitted1MiB')
    identity=lambda st:(st.st_dev,st.st_ino,st.st_size,st.st_mtime_ns)
    need(identity(before)==identity(after) and len(data)==before.st_size,'dependency changed during admission')
    sha=hashlib.sha256(data).hexdigest()
    need(row.get('size_before')==row.get('size_after')==row.get('hashed_bytes')==len(data),'dependency monitored size differs')
    need(row.get('device')==before.st_dev and row.get('inode')==before.st_ino,'dependency monitored object differs')
    need(row.get('sha256')==sha,'dependency monitored bytes differ')
    return data,{'path':expected,'resolved':expected,'size':len(data),'sha256':sha,'device':before.st_dev,'inode':before.st_ino,'mtime_ns':before.st_mtime_ns},row

def require_exact_dependencies(paths, expected):
    need(len(paths)==len(set(paths)) and set(paths)==set(expected),'syntax dependency path set differs from frozen discovery')

spec=json.loads(read(R/'preflight-inputs.json',262144));need(sys.flags.isolated and sys.flags.no_site and dict(os.environ)==spec['outer_environment'],'isolated exact environment required')
need(len(sys.argv)==2,'query monitor response required');response=json.loads(read(Path(sys.argv[1]),262144));rp=Path(response['receipt']);need(rp.parent.parent==R,'unexpected query receipt path');r=json.loads(read(rp,4194304))
need(r['config_sha256']==hashlib.sha256(read(R/'syntax.monitor.json',262144)).hexdigest(),'query config differs')
need(r['monitor']['sha256']=='b36fbefca8bdec200da79d01c36dc0c90039f948e6e0ca26c5d3d5cab17606a0','monitor differs')
need(r['reason']=='exit' and r['child_exit']==0 and r['cleanup']['all_children_reaped'] and not r['cleanup']['remaining_children'] and not r['cleanup']['reaping_pending'] and not r['cleanup']['escaped_group_detected'] and not r['output_truncated'] and not r.get('final_limit_failures'),'query did not succeed cleanly')
need(r['limits']['output_bytes']==16777216 and r['limits']['sidefile_bytes']==16777216 and r.get('map_relative_path') is None,'unexpected query log policy')
raw=read(Path(r['output_path']),16777216);need(hashlib.sha256(raw).hexdigest()==r['output_file']['sha256'],'query output differs');text=raw.decode('utf8')
commands=[x.strip() for x in text.splitlines() if x.strip().startswith(spec['cc1']+' ')]
need(len(commands)==1 and ' -fsyntax-only ' in ' '+commands[0]+' ' and ' -E ' not in ' '+commands[0]+' ','expected exact cc1 syntax-only command absent')
start=text.find('#include <...> search starts here:');end=text.find('End of search list.',start);need(start>=0 and end>start,'unknown verbose include format')
actual=[x.strip() for x in text[start:end].splitlines()[1:] if x.strip()];need(actual==spec['include_roots'],'actual include roots differ')
dep,dependency_pin,dependency_observation=admit_dependency(R/'native-build.log',r['watched_files']);need(b'\0' not in dep,'NUL dependency output');s=dep.decode('utf8').replace('\\\n',' ')
need(s.count(':')==1 and s.split(':',1)[0].strip()=='owner_header_abi','unsupported dependency rule')
rest=s.split(':',1)[1];need(not any(c in rest for c in '\\#$%\r'),'unsupported dependency escapes/directives')
paths=list(dict.fromkeys(rest.split()));need(0<len(paths)<=4096,'dependency count bound')
require_exact_dependencies(paths,spec['frozen_dependency_paths'])
source=Path(spec['source']);roots=list(map(Path,spec['include_roots']));rows=[]
for value in paths:
    p=Path(value);need(p.is_absolute() and str(p)==value and '..' not in p.parts,'noncanonical dependency path')
    resolved=p.resolve();need(p==source or any(resolved.is_relative_to(root) for root in roots),'dependency outside declared roots/source')
    rows.append(pin(p))
need({x['path']:(x['size'],x['sha256']) for x in rows}=={x['path']:(x['size'],x['sha256']) for x in spec['frozen_dependencies']},'collected header bytes differ from frozen discovery')
required={str(source),'/usr/include/stdlib.h','/usr/lib/gcc/x86_64-linux-gnu/15/include/stddef.h','/usr/lib/gcc/x86_64-linux-gnu/15/include/stdint.h','/usr/lib/gcc/x86_64-linux-gnu/15/include/limits.h'}
need(required<={x['path'] for x in rows},'direct required dependency missing')
manifest={'kind':'SEPARATELY_ASSIGNED_SYNTAX_ONLY_FROZEN_HEADER_RESULT','dependencies':rows,'exact_cc1_syntax_command':commands[0],'actual_include_roots':actual,'raw_dependency':dependency_pin,'settled_monitor_dependency_observation':dependency_observation,'qualification':'This separate syntax-only gate uses before/after frozen header pins and equal dependency set. Source target/static-assert/prototype checks passed only if exact GCC command succeeded; not libc implementation or complete native ABI/runtime proof.'}
encoded=(json.dumps(manifest,indent=2)+'\n').encode();need(len(encoded)<=4194304,'discovery manifest exceeds4MiB');mp=R/'syntax-manifest.json';need(not mp.exists(),'old discovery manifest');mp.write_bytes(encoded)
_,final_dependency_pin,final_dependency_observation=admit_dependency(R/'native-build.log',r['watched_files'])
need(final_dependency_pin==dependency_pin and final_dependency_observation==dependency_observation,'dependency changed before final receipt')
receipt={'kind':'FROZEN_HEADER_SYNTAX_ONLY_CONDITIONAL_CHECK','known_inputs_before_after_required':True,'syntax_manifest':pin(mp),'syntax_monitor_receipt':pin(rp),'raw_syntax_output':pin(Path(r['output_path'])),'raw_dependency':dependency_pin,'settled_monitor_dependency_observation':dependency_observation,'frozen_header_count':len(spec['frozen_dependency_paths']),'prototype_or_target_static_asserts_checked':True,'object_link_or_native_image_executed':False,'limits':'Conditional exact installed-header/target/prototype evidence only; no libc implementation, arbitrary ABI, native runtime, whole closure or startup acceptance'}
encoded=(json.dumps(receipt,indent=2)+'\n').encode();need(len(encoded)<=262144,'receipt exceeds256KiB');sys.stdout.buffer.write(encoded)
