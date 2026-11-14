from pathlib import Path
import subprocess,sys,json
foreign=[]
for name in ['lean','lake']:
    p=subprocess.run(['pgrep','-a','-x',name],capture_output=True,text=True)
    if p.stdout.strip(): foreign.append(p.stdout.strip())
mem={k:int(v.split()[0])*1024 for k,v in (line.split(':',1) for line in Path('/proc/meminfo').read_text().splitlines())}
if foreign or mem['MemAvailable']<8*1024**3:
    print(json.dumps({'foreign':foreign,'available_bytes':mem['MemAvailable']}));sys.exit(75)
