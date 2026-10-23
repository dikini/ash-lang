#!/usr/bin/python3
"""Private checked root-link observer. Data collection grants no launch authority."""
import hashlib, json, os, re, selectors, signal, stat, subprocess, sys, time
from pathlib import Path

HERE = Path(__file__).resolve().parent
with (HERE / 'limits.json').open('rb') as config_file:
    config_stat = os.fstat(config_file.fileno())
    if not stat.S_ISREG(config_stat.st_mode) or config_stat.st_size > 4096: raise RuntimeError('Resource: configuration file')
    config_bytes = config_file.read(4097)
if len(config_bytes)>4096: raise RuntimeError('Resource: configuration')
def unique_object(pairs):
    result = {}
    for k,v in pairs:
        if k in result: raise RuntimeError('Malformed: duplicate field')
        result[k]=v
    return result
CFG = json.loads(config_bytes, object_pairs_hook=unique_object)
maximum = dict(file_bytes=2**31,total_bytes=8*1024**3,map_bytes=256*1024**2,
               output_bytes=4*1024**2,record_bytes=4*1024**2,paths=4096,
               arguments=65536,seconds=120,cargo_bytes=16*1024**2,cargo_seconds=1800,work=64*1024**3)
if set(CFG)!=set(maximum) or any(type(CFG[k]) is not int or not 0<CFG[k]<=v for k,v in maximum.items()):
    raise RuntimeError('Resource: configuration bounds')
remaining = CFG['work']

def pay(n):
    global remaining
    if n < 0 or n > remaining:
        raise RuntimeError('Resource: work')
    remaining -= n

def read(path, cap):
    with open(path, 'rb') as f:
        b = f.read(cap + 1)
    if len(b) > cap:
        raise RuntimeError('Resource: bytes')
    pay(len(b))
    return b

def pin(path):
    p = Path(path).resolve(strict=True)
    if not p.is_absolute() or any(c.isspace() for c in str(p)):
        raise RuntimeError('Unsupported: path')
    pay(len(str(p)) + 1)
    with p.open('rb') as f:
        a = os.fstat(f.fileno())
        if not stat.S_ISREG(a.st_mode) or a.st_size > CFG['file_bytes']:
            raise RuntimeError('Resource: file path='+str(p)+' type='+oct(stat.S_IFMT(a.st_mode))+' bytes='+str(a.st_size)+' cap='+str(CFG['file_bytes']))
        h = hashlib.sha256(); size = 0
        while True:
            b = f.read(65536)
            if not b: break
            size += len(b)
            if size > CFG['file_bytes']: raise RuntimeError('Resource: growing file')
            pay(len(b)); h.update(b)
        z = os.fstat(f.fileno())
    identity = lambda x: (x.st_dev, x.st_ino, x.st_size, x.st_mtime_ns, x.st_ctime_ns)
    if identity(a) != identity(z) or size != a.st_size:
        raise RuntimeError('Association: changing input')
    return {'path':str(p), 'device':a.st_dev, 'inode':a.st_ino,
            'bytes':size, 'sha256':h.hexdigest()}

def response_tokens(data):
    # GNU response quoting is parsed as data, never shell/eval. Refuse escapes,
    # nested quotes within words and whitespace-bearing file arguments.
    text = data.decode('utf-8')
    result = []; i = 0
    while i < len(text):
        if text[i].isspace(): i += 1; continue
        quoted = text[i] in "\"'"; quote = text[i] if quoted else None
        if quoted: i += 1
        start = i
        while i < len(text) and (text[i] != quote if quoted else not text[i].isspace()):
            if text[i] == '\\' or (not quoted and text[i] in "\"'"):
                raise RuntimeError('Unsupported: response quoting')
            i += 1
        if quoted and (i == len(text) or (i + 1 < len(text) and not text[i + 1].isspace())):
            raise RuntimeError('Malformed: response quote')
        token = text[start:i]; i += int(quoted)
        if not token or any(c.isspace() for c in token): raise RuntimeError('Unsupported: response word')
        result.append(token)
    return result

def expand(args, responses, texts, depth=0):
    if depth > 4: raise RuntimeError('Resource: response depth')
    result = []
    for arg in args:
        pay(len(arg) + 1)
        if arg.startswith('@'):
            if not Path(arg[1:]).is_absolute(): raise RuntimeError('Unsupported: relative response')
            p = pin(arg[1:])
            if p['path'] != arg[1:]: raise RuntimeError('Unsupported: noncanonical response')
            if p['path'] in responses: raise RuntimeError('Malformed: duplicate response')
            responses[p['path']] = p
            data=read(p['path'],CFG['record_bytes']);texts[p['path']]=data.decode('utf-8')
            result.extend(expand(response_tokens(data),responses,texts,depth+1))
        else: result.append(arg)
        if len(result) > CFG['arguments']: raise RuntimeError('Resource: arguments')
    return result

def require_bfd(args):
    selected = None
    for arg in args:
        pay(len(arg) + 1)
        if arg.startswith('-fuse-ld'):
            if arg not in ('-fuse-ld=lld','-fuse-ld=bfd'):
                raise RuntimeError('Unsupported: linker selector '+arg)
            selected = arg
    if selected != '-fuse-ld=bfd':
        raise RuntimeError('Unsupported: effective linker selector')

def search_prefixes(args):
    paths=[];i=0
    while i<len(args):
        a=args[i];i+=1
        if a=='-B':
            if i==len(args):raise RuntimeError('Malformed: compiler prefix')
            a+=args[i];i+=1
        if a.startswith('-B'):
            pay(len(a)+1)
            p=Path(a[2:])
            if not p.is_absolute() or str(p.resolve(strict=True))!=str(p) or not str(p).endswith('/lib/rustlib/x86_64-unknown-linux-gnu/bin/gcc-ld'):
                raise RuntimeError('Unsupported: compiler prefix')
            names=[]
            with os.scandir(p) as entries:
                for e in entries:
                    pay(len(e.name)+1);names.append(e.name)
                    if len(names)>4:raise RuntimeError('Unsupported: compiler prefix entries')
            if set(names)!={'ld.lld','ld64.lld','lld-link','wasm-ld'}:
                raise RuntimeError('Unsupported: compiler prefix tools')
            paths.append({'path':str(p),'entries':[{'name':n,'input':pin(p/n)} for n in sorted(names)]})
    if len(paths)>1:raise RuntimeError('Unsupported: repeated compiler prefix')
    return paths

def classify(args):
    require_bfd(args)
    inputs = {}; searches = []; output = None; i = 0
    fixed = {'-m64','-static','-no-pie','-nodefaultlibs','-fuse-ld=bfd','-fuse-ld=lld'}
    wl = {'--as-needed','--no-as-needed','--push-state','--pop-state','-Bstatic','-Bdynamic',
          '--eh-frame-hdr','--gc-sections','--strip-debug','--strip-all','-O1','-z','noexecstack','relro','now'}
    while i < len(args):
        arg = args[i]; i += 1
        if arg in fixed: continue
        if arg == '-o':
            if output is not None or i == len(args): raise RuntimeError('Malformed: output')
            output = str(Path(args[i]).absolute()); i += 1; continue
        if arg in ('-L','-B'):
            if i == len(args): raise RuntimeError('Malformed: search')
            arg += args[i]; i += 1
        if arg.startswith(('-L','-B')) and len(arg)>2:
            p = Path(arg[2:]).resolve(strict=True)
            if not p.is_dir() or any(c.isspace() for c in str(p)): raise RuntimeError('Unsupported: search')
            searches.append(arg[:2] + str(p)); continue
        if arg.startswith('-l'):
            if not re.fullmatch(r'-l(?:gcc(?:_eh|_s)?|util|rt|pthread|m|dl|c)',arg):
                raise RuntimeError('Unsupported: library')
            continue
        if arg.startswith('-Wl,'):
            parts = arg[4:].split(',')
            if not parts or any(p not in wl for p in parts): raise RuntimeError('Unsupported: linker flag '+arg)
            n = 0
            while n < len(parts):
                if parts[n] == '-z':
                    if n+1 == len(parts) or parts[n+1] not in {'noexecstack','relro','now'}: raise RuntimeError('Malformed: linker -z')
                    n += 2
                elif parts[n] in {'noexecstack','relro','now'}: raise RuntimeError('Malformed: orphan linker value')
                else: n += 1
            continue
        if arg.startswith('-') or not arg.endswith(('.o','.a','.rlib')):
            raise RuntimeError('Unsupported: argument '+arg)
        if not Path(arg).is_absolute(): raise RuntimeError('Unsupported: relative object')
        entry = pin(arg); inputs[entry['path']] = entry
    if output is None or not inputs: raise RuntimeError('Malformed: missing output/inputs')
    return inputs, searches, output

def script_members(data):
    if len(data)>16384: raise RuntimeError('Resource: script')
    pay(len(data)*4)
    text=data.decode('ascii')
    clean=re.sub(r'/\*.*?\*/',' ',text,flags=re.S)
    if '/*' in clean or '*/' in clean: raise RuntimeError('Unsupported: script comment')
    tokens=re.findall(r'[()]|[^()\s]+',clean)
    if tokens[:4]!=['OUTPUT_FORMAT','(','elf64-x86-64',')'] or len(tokens)<8 or tokens[4] not in ['GROUP','INPUT'] or tokens[5]!='(' or tokens[-1]!=')':
        raise RuntimeError('Unsupported: script grammar')
    members=tokens[6:-1]
    if not members or len(members)!=len(set(members)): raise RuntimeError('Malformed: script members')
    for member in members:
        if not member.startswith('/') or not member.endswith(('.a','.o')) or str(Path(member).resolve(strict=True))!=member:
            raise RuntimeError('Unsupported: script member path')
    return members

def run(args):
    command = ['/usr/bin/cc', '-B'+str(HERE/'selected-bfd'), *args, '-v', '-Wl,--no-print-map-discarded,-Map=/dev/stdout']
    def terminated(signum, frame):
        raise RuntimeError('Input: terminated')
    previous = {s:signal.signal(s,terminated) for s in [signal.SIGTERM,signal.SIGINT,signal.SIGHUP]}
    child = None; streams = None; output = [bytearray(),bytearray()]; failure = None
    try:
        end = time.monotonic() + CFG['seconds']
        # Block caught signals across Popen/assignment so an asynchronous TERM
        # cannot land after fork but before the child owner is installed. This
        # single-threaded observer restores the mask in the child before exec.
        mask = signal.pthread_sigmask(signal.SIG_BLOCK, previous.keys())
        try:
            child = subprocess.Popen(command, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                     stderr=subprocess.PIPE, start_new_session=True,
                                     preexec_fn=lambda: signal.pthread_sigmask(signal.SIG_SETMASK,mask),
                                     env={'PATH':'/usr/bin:/bin','LC_ALL':'C','TZ':'UTC'})
        finally: signal.pthread_sigmask(signal.SIG_SETMASK,mask)
        streams = selectors.DefaultSelector()
        streams.register(child.stdout,selectors.EVENT_READ,0);streams.register(child.stderr,selectors.EVENT_READ,1)
        while streams.get_map():
            if time.monotonic() > end: raise RuntimeError('Resource: deadline')
            for key,_ in streams.select(0.05):
                b = os.read(key.fileobj.fileno(),65536)
                if not b: streams.unregister(key.fileobj);key.fileobj.close();continue
                at = key.data; cap = CFG['map_bytes'] if at == 0 else CFG['output_bytes']
                if len(output[at])+len(b) > cap: raise RuntimeError('Resource: output')
                pay(len(b));output[at].extend(b)
            if child.poll() is not None and not streams.get_map(): break
        if child.wait(timeout=max(0.01,end-time.monotonic())) != 0: raise RuntimeError('Input: linker failed')
    except BaseException as e:
        failure = e
    finally:
        # Block further caught termination while mandatory group cleanup runs.
        for sig in previous: signal.signal(sig,signal.SIG_IGN)
        if child is not None:
            try: os.killpg(child.pid,signal.SIGTERM)
            except ProcessLookupError: pass
            except BaseException as e: failure = failure or e
            try: os.killpg(child.pid,signal.SIGKILL)
            except ProcessLookupError: pass
            except BaseException as e: failure = failure or e
            try:
                child.kill() if child.poll() is None else None
            except BaseException as e: failure = failure or e
            try: child.wait(timeout=2)
            except BaseException as e: failure = failure or e
            try: os.killpg(child.pid,0)
            except ProcessLookupError: pass
            except BaseException as e: failure = failure or e
            else: failure = failure or RuntimeError('Input: unresolved command group')
        if streams is not None: streams.close()
        if child is not None:
            for f in [child.stdout,child.stderr]:
                if f is not None: f.close()
        for sig,handler in previous.items(): signal.signal(sig,handler)
    pay(len(output[1])*2)
    (HERE/'link.stderr').write_bytes(output[1]);sys.stderr.buffer.write(output[1]);sys.stderr.buffer.flush()
    if failure: raise failure
    return bytes(output[0]),bytes(output[1]),child.pid

def owned_names(path):
    names=[]
    with os.scandir(path) as entries:
        for entry in entries:
            pay(len(entry.name)+1);names.append(entry.name)
            if len(names)>3:raise RuntimeError('Resource: BFD proxy entries')
    return set(names)

def main():
    if (HERE/'record.json').exists(): raise RuntimeError('Association: repeated root link')
    raw = sys.argv[1:];responses = {};texts={};args = expand(raw,responses,texts)
    # Retain bounded actual invocation data even when classification refuses an
    # unsupported form. This is producer evidence, never an acceptance marker.
    pay(CFG['record_bytes'])
    invocation=json.dumps({'arguments':raw,'expanded':args,'responses':list(responses.values()),'response_texts':[{'path':p,'text':t} for p,t in texts.items()]},sort_keys=True,separators=(',',':')).encode()
    if len(invocation)>CFG['record_bytes']: raise RuntimeError('Resource: invocation record')
    (HERE/'invocation.json').write_bytes(invocation)
    prefixes=search_prefixes(args)
    before,searches,output = classify(args)
    tools = [pin(p) for p in ['/usr/bin/cc','/usr/bin/ld.bfd','/usr/bin/python3']]
    proxy_dir=HERE/'selected-bfd'
    if owned_names(proxy_dir)!={'ld.bfd','tool.json'}:raise RuntimeError('Association: BFD proxy directory')
    proxy=pin(proxy_dir/'ld.bfd');tool_config=pin(proxy_dir/'tool.json')
    selected=json.loads(read(proxy_dir/'tool.json',4096),object_pairs_hook=unique_object)
    reserved=selected['work_limit']
    if type(reserved) is not int or not 0<reserved<=CFG['work']:raise RuntimeError('Resource: BFD work reservation')
    pay(reserved)
    output_data=json.dumps({'output':output},sort_keys=True,separators=(',',':')).encode()
    pay(len(output_data));(HERE/'output.json').write_bytes(output_data)
    map_bytes,stderr,group = run(args)
    marker_bytes=read(proxy_dir/'invocation.json',CFG['record_bytes'])
    marker=json.loads(marker_bytes,object_pairs_hook=unique_object)
    if set(marker)!={'version','arguments','output','tool','proxy','configuration','process_group','attempted_fd_exec','work_used'} or marker['version']!=1 or marker['attempted_fd_exec'] is not True or marker['output']!=output or marker['tool']!=tools[1] or marker['proxy']!=proxy or marker['configuration']!=tool_config or marker['process_group']!=group or type(marker['work_used']) is not int or not 0<marker['work_used']<=reserved:
        raise RuntimeError('Association: BFD invocation')
    if owned_names(proxy_dir)!={'ld.bfd','tool.json','invocation.json'} or pin(proxy_dir/'ld.bfd')!=proxy or pin(proxy_dir/'tool.json')!=tool_config or search_prefixes(args)!=prefixes:
        raise RuntimeError('Association: changed BFD search/tool')
    # GNU/BFD map framing and every LOAD path. This is observed build input
    # correspondence, not a claim to runtime behavior or tool conformity.
    pay(len(map_bytes)*3)
    text = map_bytes.decode('utf-8')
    if 'Linker script and memory map\n' not in text: raise RuntimeError('Unsupported: BFD map')
    loads = [line[5:] for line in text.splitlines() if line.startswith('LOAD ')]
    if not loads or len(loads)>CFG['paths'] or not any(line.startswith('OUTPUT(') and 'elf64-x86-64' in line for line in text.splitlines()):
        raise RuntimeError('Unsupported: map framing')
    outputs = [line for line in text.splitlines() if line.startswith('OUTPUT(')]
    if outputs != ['OUTPUT('+output+' elf64-x86-64)']: raise RuntimeError('Association: map output')
    observed = {}; resolved_loads = []; scripts = []
    for path in loads:
        entry = pin(path)
        with open(entry['path'],'rb') as f: magic = f.read(20)
        # Text linker scripts, plugins and LTO intermediates require a separate
        # supported parser; never silently classify them as captured objects.
        if not ((magic.startswith(b'\x7fELF\x02\x01') and magic[16:18] == b'\x01\x00') or magic[:8] == b'!<arch>\n'):
            data=read(entry['path'],16384);members=script_members(data)
            scripts.append({'path':entry['path'],'text':data.decode('ascii'),'members':members})
        observed[entry['path']] = entry; resolved_loads.append(entry['path'])
    script_paths={s['path'] for s in scripts}
    if len(script_paths)!=len(scripts): raise RuntimeError('Malformed: duplicate scripts')
    for script in scripts:
        for member in script['members']:
            # Only one-level groups of real archive/relocatable inputs are in
            # this supported slice. Nested/cyclic/search/library scripts refuse.
            if member not in observed or member in script_paths:
                raise RuntimeError('Association: unobserved/nested script member')
    if not set(before).issubset(observed): raise RuntimeError('Association: omitted argument input')
    for path,p in before.items():
        if pin(path) != p or observed[path] != p: raise RuntimeError('Association: changed input')
    for path,p in responses.items():
        if pin(path)!=p: raise RuntimeError('Association: changed response')
    if sum(p['bytes'] for p in list(observed.values())+list(responses.values()))>CFG['total_bytes']: raise RuntimeError('Resource: total')
    if len(observed)+len(responses)>CFG['paths']: raise RuntimeError('Resource: paths')
    result = {'version':1,'arguments':raw,'expanded':args,'searches':searches,
              'command':['/usr/bin/cc','-B'+str(proxy_dir),*args,'-v','-Wl,--no-print-map-discarded,-Map=/dev/stdout'],
              'prefixes':prefixes,'bfd':marker,'bfd_marker':pin(proxy_dir/'invocation.json'),'bfd_marker_text':marker_bytes.decode('utf-8'),'cc_exit_code':0,
              'responses':list(responses.values()),'response_texts':[{'path':p,'text':text} for p,text in texts.items()],'inputs':list(observed.values()),'loads':loads,'resolved_loads':resolved_loads,'scripts':scripts,
              'tools':tools,'output':pin(output),'map':{'bytes':len(map_bytes),'sha256':hashlib.sha256(map_bytes).hexdigest()},
              'stderr':{'bytes':len(stderr),'sha256':hashlib.sha256(stderr).hexdigest()},
              'work_used':0,'child_reaped':True,'owned_group_empty':True}
    pay(CFG['record_bytes']+len(map_bytes))
    result['work_used']=CFG['work']-remaining
    data = json.dumps(result,sort_keys=True,separators=(',',':')).encode()
    if len(data)>CFG['record_bytes']: raise RuntimeError('Resource: record')
    (HERE/'link.map').write_bytes(map_bytes);(HERE/'record.json').write_bytes(data)

if __name__ == '__main__':
    try:
        main()
    except BaseException as error:
        print('checked root link observation refused: '+str(error),file=sys.stderr)
        sys.exit(1)
