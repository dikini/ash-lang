#!/usr/bin/python3
"""Disposable trusted-reporter image identity probe; no Ash/native execution permission."""
import errno,fcntl,hashlib,json,mmap,os,selectors,signal,stat,struct,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
MAX_IMAGE=1024*1024
SEALS=fcntl.F_SEAL_WRITE|fcntl.F_SEAL_GROW|fcntl.F_SEAL_SHRINK|fcntl.F_SEAL_SEAL
class Refused(Exception): pass
def digest(data): return hashlib.sha256(data).hexdigest()
def bounded(path,limit):
    with open(path,'rb') as stream:
        data=stream.read(limit+1)
    if len(data)>limit: raise Refused('size limit')
    return data
def static_elf(data):
    if len(data)<64: raise Refused('short ELF')
    fields=struct.unpack_from('<16sHHIQQQIHHHHHH',data)
    ident,kind,machine,version,entry,phoff,shoff,flags,ehsize,phsize,phcount,*_=fields
    if ident[:7]!=b'\x7fELF\x02\x01\x01' or kind!=2 or machine!=62 or version!=1 or ehsize!=64:
        raise Refused('unsupported ELF/ABI')
    if phsize!=56 or not 0<phcount<=64 or phoff+phsize*phcount>len(data):
        raise Refused('invalid program table')
    types=[struct.unpack_from('<I',data,phoff+i*phsize)[0] for i in range(phcount)]
    if 3 in types or 2 in types: raise Refused('interpreter or dynamic section')
    if 1 not in types: raise Refused('missing load segment')
    return {'type':'ET_EXEC','machine':'EM_X86_64','pt_interp':False,'pt_dynamic':False,'pt_needed':False,'program_headers':phcount}
def admission(receipt_bytes,approval,candidate):
    if approval is None: raise Refused('explicit exact receipt approval absent')
    receipt=json.loads(receipt_bytes)
    if receipt.get('version')!=1: raise Refused('unsupported receipt version')
    if approval.get('receipt_sha256')!=digest(receipt_bytes): raise Refused('receipt not approved')
    image=receipt['images']['reporter-A']
    if approval.get('image_sha256')!=image['sha256']: raise Refused('image not approved')
    data=bounded(candidate,MAX_IMAGE)
    if len(data)!=image['size']: raise Refused('image size mismatch')
    elf=static_elf(data)
    fd=os.memfd_create('ash-trusted-reporter',os.MFD_CLOEXEC|os.MFD_ALLOW_SEALING|0x10) # MFD_EXEC
    try:
        view=memoryview(data)
        while view:
            count=os.write(fd,view)
            if count<=0: raise Refused('short image write')
            view=view[count:]
        os.fchmod(fd,0o500)
        fcntl.fcntl(fd,fcntl.F_ADD_SEALS,SEALS)
        if fcntl.fcntl(fd,fcntl.F_GET_SEALS)&SEALS!=SEALS: raise Refused('incomplete seals')
        final=os.pread(fd,MAX_IMAGE+1,0)
        if len(final)!=image['size'] or digest(final)!=image['sha256']: raise Refused('final immutable digest mismatch')
        return fd,elf
    except BaseException:
        os.close(fd)
        raise

def execute(fd):
    read_end,write_end=os.pipe2(os.O_CLOEXEC)
    pid=os.fork()
    if pid==0:
        try:
            os.close(read_end)
            os.dup2(write_end,1)
            os.dup2(write_end,2)
            os.close(write_end)
            os.execve(fd,['trusted-pinned-reporter'],{})
        except BaseException as error:
            os.write(2, (type(error).__name__+': '+str(error)+'\n').encode()[:1024])
            os._exit(125)
    os.close(write_end)
    selector=selectors.DefaultSelector()
    selector.register(read_end,selectors.EVENT_READ)
    output=bytearray(); status=None; deadline=time.monotonic()+3
    try:
        while status is None or selector.get_map():
            if time.monotonic()>=deadline: raise Refused('trusted reporter deadline')
            for key,_ in selector.select(0.05):
                chunk=os.read(key.fd,4096)
                if chunk:
                    output.extend(chunk)
                    if len(output)>4096: raise Refused('trusted reporter output limit')
                else: selector.unregister(key.fd)
            if status is None:
                done,wait_status=os.waitpid(pid,os.WNOHANG)
                if done: status=wait_status
        return {'exit_code':os.waitstatus_to_exitcode(status),'output':output.decode('ascii'),'reaped':True,'executed_via':'os.execve(fd), no filename reopened'}
    finally:
        if status is None:
            try: os.kill(pid,signal.SIGKILL)
            except ProcessLookupError: pass
            os.waitpid(pid,0)
        selector.close(); os.close(read_end)

def refusal(receipt,approval,candidate):
    try:
        fd,_=admission(receipt,approval,candidate)
    except Refused as error: return {'refused':str(error),'reporter_started':False}
    else:
        os.close(fd)
        raise AssertionError('negative admission unexpectedly accepted')

def main():
    receipt=bounded(ROOT/'producer-receipt.json',65536)
    approval=json.loads(bounded(ROOT/'operator-approval.json',65536))
    policy_path=Path('/proc/sys/vm/memfd_noexec')
    local_policy=policy_path.read_text().strip() if policy_path.exists() else 'not exposed'
    status={line.split(':',1)[0]:line.split(':',1)[1].strip() for line in Path('/proc/self/status').read_text().splitlines() if line.split(':',1)[0] in ['NoNewPrivs','Seccomp','Seccomp_filters']}
    results={'scope':'trusted self-authored reporter only; in-process host authority, no isolation','parent':{'uid':os.getuid(),'gid':os.getgid(),'groups':os.getgroups(),'status':status},'memfd_policy':{'create_flags':19,'flag_names':['MFD_CLOEXEC','MFD_ALLOW_SEALING','MFD_EXEC'],'mfd_noexec_seal_requested':False,'vm.memfd_noexec':local_policy},'receipt_sha256':digest(receipt),'approval_sha256':digest((ROOT/'operator-approval.json').read_bytes()),'observations':{}}
    candidate=ROOT/'candidate'
    candidate.write_bytes((ROOT/'reporter-A').read_bytes())
    fd,elf=admission(receipt,approval,candidate)
    try:
        results['elf']=elf
        results['sealed_fd']={'mode_octal':oct(stat.S_IMODE(os.fstat(fd).st_mode)),'seals':fcntl.fcntl(fd,fcntl.F_GET_SEALS),'size':os.fstat(fd).st_size,'sha256':digest(os.pread(fd,MAX_IMAGE+1,0))}
        failures={}
        for label,operation in [('pwrite',lambda:os.pwrite(fd,b'X',0)),('grow',lambda:os.ftruncate(fd,os.fstat(fd).st_size+1)),('shrink',lambda:os.ftruncate(fd,os.fstat(fd).st_size-1)),('add_seal',lambda:fcntl.fcntl(fd,fcntl.F_ADD_SEALS,0x10)),('shared_write_map',lambda:mmap.mmap(fd,1,flags=mmap.MAP_SHARED,prot=mmap.PROT_READ|mmap.PROT_WRITE))]:
            try: operation()
            except OSError as error: failures[label]={'errno':error.errno,'name':errno.errorcode[error.errno]}
            else: raise AssertionError('sealed mutation accepted: '+label)
        results['observations']['sealed_mutation_refusals']=failures
        replacement=ROOT/'replacement'
        replacement.write_bytes((ROOT/'reporter-B').read_bytes())
        os.replace(replacement,candidate)
        results['observations']['path_replacement']={'stage':'execve_fd after sealing/final verification','candidate_now_sha256':digest(candidate.read_bytes()),'execution':execute(fd)}
        execution=results['observations']['path_replacement']['execution']
        results['pinned_execution_observed']=execution['exit_code']==0 and 'trusted-reporter-A ' in execution['output']
        results['observations']['replacement_before_pin']=refusal(receipt,approval,candidate)
        candidate.write_bytes((ROOT/'reporter-A').read_bytes())
        results['observations']['missing_approval']=refusal(receipt,None,candidate)
        bad=json.loads(receipt); bad['version']=2
        results['observations']['unsupported_receipt']=refusal(json.dumps(bad).encode(),approval,candidate)
        bad=json.loads(receipt); bad['contract']='changed contract'
        results['observations']['changed_receipt']=refusal(json.dumps(bad).encode(),approval,candidate)
        altered=bytearray(candidate.read_bytes()); altered[-1]^=1; candidate.write_bytes(altered)
        results['observations']['changed_image']=refusal(receipt,approval,candidate)
        parser_negatives={}
        wrong_abi=bytearray((ROOT/'reporter-A').read_bytes()); struct.pack_into('<H',wrong_abi,18,183)
        for name,data in [('dynamic_elf',bounded(ROOT/'reporter-dynamic-negative',MAX_IMAGE)),('script',b'#!/bin/sh\nexit 0\n'),('wrong_machine',wrong_abi)]:
            try: static_elf(data)
            except Refused as error: parser_negatives[name]={'refused':str(error),'reporter_started':False}
            else: raise AssertionError('ELF negative accepted: '+name)
        results['observations']['nonexecuted_elf_parser_negatives']=parser_negatives

        assert results['sealed_fd']['sha256']==digest(os.pread(fd,MAX_IMAGE+1,0))
    finally:
        os.close(fd)
        candidate.unlink(missing_ok=True)
    print(json.dumps(results,sort_keys=True,indent=2))
    return 0 if results['pinned_execution_observed'] else 78
if __name__=='__main__': raise SystemExit(main())
