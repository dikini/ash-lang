#!/usr/bin/python3
"""Private build-tool FD delegation; an entry marker is not successful linking."""
import hashlib, json, os, runpy, stat, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
m = runpy.run_path(str(HERE.parent / 'observer.py'))
pay, pin, CFG = m['pay'], m['pin'], m['CFG']

def read(path,cap):
    with open(path,'rb') as f:
        st=os.fstat(f.fileno())
        if not stat.S_ISREG(st.st_mode) or st.st_size>cap:raise RuntimeError('Resource: BFD configuration')
        data=f.read(cap+1)
    if len(data)>cap:raise RuntimeError('Resource: BFD configuration')
    pay(len(data));return data

def main():
    data = read(HERE / 'tool.json', 4096)
    expected = json.loads(data, object_pairs_hook=m['unique_object'])
    if set(expected) != {'version','tool','observer','proxy','work_limit'} or expected['version'] != 1:
        raise RuntimeError('Malformed: BFD tool configuration')
    budget=expected['work_limit']
    used=CFG['work']-pay.__globals__['remaining']
    calculated=expected['tool']['bytes']+expected['observer']['bytes']+expected['proxy']['bytes']+8*CFG['record_bytes']+4096
    if type(budget) is not int or budget!=calculated or not used<=budget<=CFG['work']:
        raise RuntimeError('Resource: BFD reserved work')
    pay.__globals__['remaining']=budget-used
    if pin(HERE.parent / 'observer.py') != expected['observer'] or pin(__file__) != expected['proxy']:
        raise RuntimeError('Association: BFD proxy code')
    fixed = str(Path('/usr/bin/ld.bfd').resolve(strict=True))
    if expected['tool']['path'] != fixed or os.execve not in os.supports_fd:
        raise RuntimeError('Unsupported: fixed BFD FD execution')
    args = sys.argv[1:]
    if not args or len(args)>CFG['arguments']:
        raise RuntimeError('Resource: BFD arguments')
    for arg in args:
        pay(len(arg)+1)
        if arg.startswith('@'): raise RuntimeError('Unsupported: BFD response')
    outputs=[args[i+1] for i,a in enumerate(args[:-1]) if a=='-o']
    output=json.loads(read(HERE.parent/'output.json',CFG['record_bytes']),object_pairs_hook=m['unique_object'])
    if set(output)!={'output'} or outputs!=[output['output']]:
        raise RuntimeError('Association: BFD output')
    fd = os.open(fixed,os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW | os.O_NONBLOCK)
    try:
        a=os.fstat(fd)
        if not stat.S_ISREG(a.st_mode) or a.st_size>CFG['file_bytes']:
            raise RuntimeError('Resource: BFD opened tool')
        h=hashlib.sha256();size=0
        while True:
            b=os.read(fd,65536)
            if not b:break
            size+=len(b)
            if size>CFG['file_bytes']:raise RuntimeError('Resource: BFD growing tool')
            pay(len(b));h.update(b)
        z=os.fstat(fd)
        identity=lambda s:(s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns)
        actual=dict(path=fixed,device=a.st_dev,inode=a.st_ino,bytes=size,sha256=h.hexdigest())
        if identity(a)!=identity(z) or size!=a.st_size or actual!=expected['tool']:
            raise RuntimeError('Association: BFD opened identity')
        if 6*sum(len(a) for a in args)+4096>CFG['record_bytes']:raise RuntimeError('Resource: BFD marker arguments')
        pay(CFG['record_bytes'])
        marker=dict(version=1,arguments=args,output=outputs[0],tool=actual,
                    proxy=expected['proxy'],configuration=pin(HERE/'tool.json'),
                    process_group=os.getpgrp(),attempted_fd_exec=True,work_used=budget-pay.__globals__['remaining'])
        encoded=json.dumps(marker,sort_keys=True,separators=(',',':')).encode()
        if len(encoded)>CFG['record_bytes']:raise RuntimeError('Resource: BFD marker')
        # Exclusive creation refuses auxiliary/repeated linker invocations. The
        # collector still requires successful cc, map and final-output identity.
        with (HERE/'invocation.json').open('xb') as f:f.write(encoded)
        os.lseek(fd,0,os.SEEK_SET)
        os.execve(fd,[fixed,*args],dict(os.environ))
    finally:os.close(fd)

if __name__=='__main__':
    try:main()
    except BaseException as e:
        print('checked BFD delegation refused: '+str(e),file=sys.stderr)
        sys.exit(1)
