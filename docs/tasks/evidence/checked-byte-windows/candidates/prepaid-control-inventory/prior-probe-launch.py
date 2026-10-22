from pathlib import Path
import json,os,resource,runpy,sys
out=Path('/home/dikini/Projects/ash-lang/.worktree/generic-cells/target/checked-capture-code-inventory')
runner='/home/dikini/Projects/ash-lang/.worktree/checked-ffi/docs/tasks/evidence/checked-byte-windows/test-first/run.py'
os.environ['ASH_RECEIPT_DIR']=str(out)
resource.setrlimit(resource.RLIMIT_FSIZE,(1048576,1048576))
sys.argv=[runner,'code-inventory',*json.loads((out/'argv.json').read_text())]
runpy.run_path(runner,run_name='__main__')
