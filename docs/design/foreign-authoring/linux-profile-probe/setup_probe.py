#!/usr/bin/python3
"""Trusted setup only: no foreign image, no cgroup mutation or host-policy change."""
import ctypes,json,os,pathlib,subprocess,sys,hashlib

def facts():
 return {'uid':os.getuid(),'gid':os.getgid(),'groups':os.getgroups(),'uid_map':pathlib.Path('/proc/self/uid_map').read_text(),'gid_map':pathlib.Path('/proc/self/gid_map').read_text(),'setgroups':pathlib.Path('/proc/self/setgroups').read_text(),'status':[l for l in pathlib.Path('/proc/self/status').read_text().splitlines() if l.startswith(('Cap','NoNewPrivs:','Seccomp:'))]}

def attempt(call):
 try:return {'ok':True,'result':call()}
 except OSError as e:return {'ok':False,'errno':e.errno,'message':e.strerror}

if '--child' in sys.argv:
 r={'initial':facts()}; libc=ctypes.CDLL(None,use_errno=True)
 def unshare(flags):
  if libc.unshare(flags):raise OSError(ctypes.get_errno(),os.strerror(ctypes.get_errno()))
 r['unshare_user']=attempt(lambda:unshare(0x10000000))
 if r['unshare_user']['ok']:
  r['empty_groups_before_mapping']=attempt(lambda:os.setgroups([]))
  r['deny_setgroups']=attempt(lambda:pathlib.Path('/proc/self/setgroups').write_text('deny'))
  r['uid_map']=attempt(lambda:pathlib.Path('/proc/self/uid_map').write_text('1000 1000 1'))
  r['gid_map']=attempt(lambda:pathlib.Path('/proc/self/gid_map').write_text('1000 1000 1'))
  r['empty_groups_after_mapping']=attempt(lambda:os.setgroups([]))
  r['unshare_mount']=attempt(lambda:unshare(0x20000))
  r['after']=facts()
 print(json.dumps(r));sys.exit(0)
child=subprocess.run([sys.executable,__file__,'--child'],capture_output=True,text=True,timeout=5)
r={'scope':'trusted setup capability probe; no foreign code or isolated-profile success','script_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'python_sha256':hashlib.sha256(pathlib.Path(sys.executable).read_bytes()).hexdigest(),'kernel':os.uname().release,'returncode':child.returncode,'child':json.loads(child.stdout) if child.stdout else None,'stderr':child.stderr,'reaped':True}
print(json.dumps(r,indent=2))
