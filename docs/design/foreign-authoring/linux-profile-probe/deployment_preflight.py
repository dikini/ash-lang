#!/usr/bin/python3
"""Read-only discovery and a reaped trusted setup child; never starts a worker.

Exit 78 means this probe cannot establish prerequisites. It is not an executor
or complete admission implementation. Host mode requires ordinary tool approval.
"""
import argparse,hashlib,json,os,pathlib,shutil,subprocess,sys

P=pathlib.Path

def digest(path):
 try:return hashlib.sha256(P(path).read_bytes()).hexdigest()
 except OSError:return None

def error(e):return {'errno':e.errno,'message':e.strerror}

def inspect(path,write_open=False):
 try:
  st=path.stat();r={'uid':st.st_uid,'gid':st.st_gid,'mode':oct(st.st_mode&0o777)}
  if path.name=='cgroup.procs':r['process_count']=len(path.read_text().splitlines())
  else:r['value']=path.read_text().strip()
  if write_open:
   try:fd=os.open(path,os.O_WRONLY|os.O_CLOEXEC);os.close(fd);r['write_open']='succeeded; no write performed'
   except OSError as e:r['write_open']=error(e)
  return r
 except OSError as e:return error(e)

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--label',required=True,choices=['sandbox','approved-host'])
a=parser.parse_args()
source=P(__file__).resolve();setup=source.with_name('setup_probe.py')
rel=P('/proc/self/cgroup').read_text().strip().split('::',1)[1]
parts=P(rel).parts[1:];base=P('/sys/fs/cgroup');ancestors=[]
for part in [None,*parts]:
 if part:base/=part
 ancestors.append({'path':str(base),'files':{name:inspect(base/name,True) for name in ['cgroup.controllers','cgroup.subtree_control','cgroup.procs','memory.max','memory.swap.max','cpu.max','pids.max']}})
child=subprocess.run([sys.executable,str(setup)],capture_output=True,text=True,timeout=8,check=True)
setup_result=json.loads(child.stdout)
helper_paths={x:shutil.which(x) for x in ['newuidmap','newgidmap','setpriv','unshare','cc']}
subids={}
import pwd
name=pwd.getpwuid(os.getuid()).pw_name
for path in ['/etc/subuid','/etc/subgid']:
 try:subids[path]=[s for s in P(path).read_text().splitlines() if s.startswith(name+':')]
 except OSError as e:subids[path]=error(e)
mounts=[]
for line in P('/proc/self/mountinfo').read_text().splitlines():
 fields=line.split();point=fields[4]
 if point in ['/','/tmp','/sys/fs/cgroup']:mounts.append({'mountpoint':point,'options':fields[5],'filesystem':fields[fields.index('-')+1],'super_options':fields[-1]})
r={'version':1,'label':a.label,'scope':'deployment discovery; no foreign or static image executed; no host policy/cgroup/mount/storage mutation','kernel':os.uname().release,'pins':{str(source.name):digest(source),str(setup.name):digest(setup),'python':digest(sys.executable)},'self_cgroup':rel,'cgroup_ancestors':ancestors,'mounts':mounts,'helpers':helper_paths,'subordinate_ids':subids,'setup':setup_result,'refusal':{'worker_started':False,'reason':'this discovery tool has no complete verified deployment configuration and never authorizes worker startup','external_requirement':'operator-provided trusted credential setup that clears supplementary groups before foreign startup and supplies non-root mappings; a reviewed configured mapping helper preserving setgroups authority is one possible prerequisite','remaining':['post-exec/re-exec configured worker credentials','private root/exclusive quota-backed storage','immutable authorized static image and receipt','reviewed native default-deny syscall policy','actual per-worker resource enforcement','native startup faults, termination/reaping and SQLite integration']}}
print(json.dumps(r,indent=2))
sys.exit(78)
