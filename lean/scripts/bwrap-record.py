#!/usr/bin/python3
from pathlib import Path
import os,sys,json,time
root=Path(__file__).resolve().parent.parent
args=[a for a in sys.argv[1:] if a!='--share-net']
i=args.index('--')
extra=['--setenv','LEAN_NUM_THREADS','1','--setenv','MATHLIB_NO_CACHE_ON_UPDATE','1','--setenv','GIT_ALLOW_PROTOCOL','file','--setenv','LAKE_CACHE_DIR','/tmp/lake-cache']
for p in [root/'.build-control/compile.lock',root/'evidence/compile-gate.jsonl']:
 extra+=['--bind',str(p),str(p)]
args=args[:i]+extra+args[i:]
with (root/'evidence/bwrap-invocations.jsonl').open('a') as f:f.write(json.dumps({'epoch':time.time(),'args':args,'network_disabled':True})+'\n')
exe='/opt/forgetting-arxiv-2026-11-10/bubblewrap/usr/bin/bwrap'
os.execv(exe,[exe,*args])
