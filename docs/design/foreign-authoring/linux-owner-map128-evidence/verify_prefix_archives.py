"""Bounded gzip-prefix verification only; no subprocess or decoded output file."""
from pathlib import Path
import gzip,hashlib,json,os,stat,sys
ROOT=Path(__file__).parent
LIMIT=67108864

def need(ok,why):
    if not ok:raise SystemExit(why)

def opened(path,expected):
    fd=os.open(path,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK|os.O_CLOEXEC)
    stream=os.fdopen(fd,'rb')
    info=os.fstat(fd)
    if not stat.S_ISREG(info.st_mode) or info.st_size!=expected:
        stream.close();raise SystemExit('regular-file/size association differs: '+str(path))
    return stream

class EncodedWindow:
    # Gzip sees at most the already pinned compressed length, even if the file grows.
    def __init__(self,stream,length):self.stream=stream;self.remaining=length
    def read(self,n=-1):
        need(n>=0,'unbounded compressed read refused')
        block=self.stream.read(min(n,self.remaining));self.remaining-=len(block);return block
    def seekable(self):return False

def identity(info):
    return (info.st_dev,info.st_ino,info.st_size,info.st_mtime_ns,info.st_ctime_ns)

need(sys.argv[1:] in ([],['--compare-originals']),'usage: verify_prefix_archives.py [--compare-originals]')
compare=bool(sys.argv[1:])
with (ROOT/'prefix-containers.json').open('rb') as f:raw=f.read(262145)
need(len(raw)<=262144,'container manifest exceeds256KiB')
spec=json.loads(raw);need(spec['decoded_limit_each']==LIMIT and len(spec['records'])==2,'unexpected prefix manifest')
expected_names={'third-prefix64MiB.gz','fourth-prefix64MiB.gz'};seen=set();results=[]
for row in spec['records']:
    name=Path(row['container_path']).name
    need(name in expected_names and name not in seen,'unknown/duplicate container')
    need(row['container_path']=='docs/design/foreign-authoring/linux-owner-map128-evidence/maps/'+name,'unexpected container path')
    seen.add(name);size=row['compressed_size']
    need(type(size) is int and 0<size<=LIMIT and row['original_size']==LIMIT,'unsupported encoded/decoded size')
    with opened(ROOT/'maps'/name,size) as stream:
        before=os.fstat(stream.fileno());h=hashlib.sha256();n=0
        for chunk in iter(lambda:stream.read(65536),b''):h.update(chunk);n+=len(chunk);need(n<=size,'compressed file grew')
        need(n==size and h.hexdigest()==row['compressed_sha256'],'compressed digest mismatch')
        stream.seek(0);header=stream.read(10)
        need(header[:8]==b'\x1f\x8b\x08\x00\x00\x00\x00\x00' and header[8:]==b'\x02\xff','noncanonical deterministic gzip header')
        stream.seek(0);original=opened(Path(row['original_path']),LIMIT) if compare else None
        original_before=os.fstat(original.fileno()) if original else None
        try:
            decoded=0;digest=hashlib.sha256()
            with gzip.GzipFile(fileobj=EncodedWindow(stream,size),mode='rb') as gz:
                while True:
                    chunk=gz.read(min(65536,LIMIT-decoded+1))
                    if not chunk:break
                    decoded+=len(chunk);need(decoded<=LIMIT,'decoded prefix exceeds64MiB')
                    digest.update(chunk)
                    if original:need(original.read(len(chunk))==chunk,'streaming original equivalence failed')
            need(decoded==LIMIT and digest.hexdigest()==row['original_sha256'],'decoded size/digest differs')
            if original:
                need(original.read(1)==b'','original has extra bytes')
                need(identity(original_before)==identity(os.fstat(original.fileno())),'original changed during comparison')
        finally:
            if original:original.close()
        need(identity(before)==identity(os.fstat(stream.fileno())),'container changed during read')
    results.append({'container':name,'compressed_size':size,'compressed_sha256':h.hexdigest(),'decoded_size':decoded,'decoded_sha256':digest.hexdigest(),'streaming_original_equal':compare,'decoded_file_written':False})
need(seen==expected_names,'missing container')
print(json.dumps({'status':'VERIFIED_DERIVED_BOUNDED_PREFIX_CONTENT_ONLY','compare_originals':compare,'manifest_sha256':hashlib.sha256(raw).hexdigest(),'records':results,'full_maps_verified':False},indent=2))
