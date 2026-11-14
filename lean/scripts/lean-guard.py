from pathlib import Path
import fcntl,json,os,subprocess,sys,time
ROOT=Path('/opt/domain-nonembedding-lean/project')
CONTROL=ROOT/'.build-control'
REAL=Path('/opt/forgetting-arxiv-2026-11-10/toolchain/bin/lean')
MAP_ROOTS=[ROOT]
if Path.cwd().resolve()==Path('/opt/domain-nonembedding-clean-2026-11-13'):
    MAP_ROOTS.append(Path.cwd().resolve())
def processes(name):
    p=subprocess.run(['pgrep','-x',name],capture_output=True,text=True)
    return [int(v) for v in p.stdout.split()]
def ancestors():
    out=set(); pid=os.getpid()
    while pid>1:
        out.add(pid)
        try: pid=int(next(x for x in Path(f'/proc/{pid}/status').read_text().splitlines() if x.startswith('PPid:')).split()[1])
        except (OSError,StopIteration): break
    return out
with (CONTROL/'compile.lock').open('a') as lock:
    fcntl.flock(lock,fcntl.LOCK_EX)
    wait_start=time.monotonic()
    while True:
        host=json.loads((CONTROL/'host-state.json').read_text())
        mem={k:int(v.split()[0])*1024 for k,v in (line.split(':',1) for line in Path('/proc/meminfo').read_text().splitlines())}
        foreign_lean=processes('lean')
        foreign_lake=[pid for pid in processes('lake') if pid not in ancestors()]
        record={'epoch':time.time(),'host':host,'wsl_available_bytes':mem['MemAvailable'],
            'foreign_lean':foreign_lean,'foreign_lake':foreign_lake,'args':sys.argv[1:]}
        permitted=(time.time()-host['epoch']<15 and host['available_bytes']>=8*1024**3
            and mem['MemAvailable']>=8*1024**3 and host['c_free_bytes']>=50_000_000_000
            and not host['lean_pids'] and not host['lake_pids'] and not foreign_lean and not foreign_lake)
        record['permitted']=permitted
        if permitted or time.monotonic()-wait_start>=55: break
        time.sleep(1)
    record['resource_wait_seconds']=time.monotonic()-wait_start
    with (ROOT/'evidence/compile-gate.jsonl').open('a') as f:f.write(json.dumps(record)+'\n')
    if not permitted:
        print('Compilation gate closed; no compiler started: '+json.dumps(record),file=sys.stderr)
        sys.exit(75)
    args=['-j1','-M5000',*sys.argv[1:]]
    child=subprocess.Popen([str(REAL),*args])
    mapped=set()
    while child.poll() is None:
        try:
            for line in Path(f'/proc/{child.pid}/maps').read_text().splitlines():
                fields=line.split(maxsplit=5)
                if len(fields)==6 and any(fields[5].startswith(str(p)+'/') for p in MAP_ROOTS):
                    mapped.add(fields[5])
        except (OSError,ProcessLookupError):pass
        time.sleep(.2)
    code=child.wait()
    for name in mapped:
        try:
            with open(name,'rb') as f:os.posix_fadvise(f.fileno(),0,0,os.POSIX_FADV_DONTNEED)
        except OSError:pass
    with (ROOT/'evidence/compile-gate.jsonl').open('a') as f:
        f.write(json.dumps({'end_epoch':time.time(),'lean_pid':child.pid,'exit':code})+'\n')
    sys.exit(code)
