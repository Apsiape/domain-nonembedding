from pathlib import Path
import subprocess,sys
root=Path(__file__).resolve().parent.parent
name=sys.argv[1]
assert name in ['Challenge','Solution']
out=root/'.lake/build/lib/lean'/f'{name}.olean';out.parent.mkdir(parents=True,exist_ok=True)
subprocess.run(['lake','env','lean','-j1','-M5000','-o',str(out),name+'.lean'],cwd=root,check=True)
