from pathlib import Path
import hashlib,json,platform,subprocess
root=Path(__file__).resolve().parent
def digest(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def info(path):
    p=Path(path).resolve()
    return {'path':str(p),'size':p.stat().st_size,'sha256':digest(p)}
inputs=[]
for line in (root/'reporter-A.map').read_text().splitlines():
    if line.startswith('LOAD '): inputs.append(info(root/line[5:]))
headers=[info(root/p) for p in (root/'reporter-A.d').read_text().replace('\\\n',' ').split(':',1)[1].split()]
tools={}
for tool in ['cc','ld','as']:
    p='/usr/bin/'+tool
    tools[tool]={**info(p),'version':subprocess.check_output([p,'--version'],text=True).splitlines()[0]}
for tool in ['cc1','collect2']:
    p=subprocess.check_output(['/usr/bin/cc','-print-prog-name='+tool],text=True).strip()
    tools[tool]=info(p)
receipt={'version':1,'role':'trusted-self-authored-reporter-only','mode':'in-process-host-authority-experiment','target':'x86_64-linux-gnu','contract':'no Ash/native library operations; diagnostic reporter only','policy':'bounded-image-pinning-v1; no isolation claim','kernel':platform.release(),'source':info(root/'reporter.c'),'build_script':info(root/'build.sh'),'receipt_generator':info(__file__),'toolchain':tools,'link_inputs':inputs,'headers':headers,'images':{name:{**info(root/name),'link_map':info(root/(name+'.map')),'elf_report':info(root/(name+'.elf.txt'))} for name in ['reporter-A','reporter-B']},'approval':'required separately; this receipt grants none','limitations':['no SQLite archive','no evaluator/bridge build','no worker isolation','no accepted architecture']}
(root/'producer-receipt.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
print(json.dumps({'receipt_sha256':digest(root/'producer-receipt.json'),'images':{name:r['sha256'] for name,r in receipt['images'].items()}},indent=2))
