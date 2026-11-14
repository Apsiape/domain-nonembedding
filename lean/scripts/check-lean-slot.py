"""Read-only process check in every running WSL distribution and Windows."""
import subprocess

def running(command):
    return subprocess.run(command,capture_output=True,check=True).stdout

names=running(['wsl','--list','--running','--quiet']).decode('utf-16le').replace('\x00','').splitlines()
for name in names:
    name=name.strip()
    if not name:
        continue
    result=subprocess.run(['wsl','-d',name,'--exec','sh','-c',
                           'pgrep -a -x lean; pgrep -a -x lake; true'],capture_output=True,text=True,check=True)
    print(name+': '+(result.stdout.strip() or 'no Lean/Lake'))
    assert not result.stdout.strip(), 'Lean slot occupied'
for name in ['lean.exe','lake.exe']:
    result=running(['tasklist','/FI','IMAGENAME eq '+name,'/FO','CSV','/NH']).decode(errors='replace')
    assert '"'+name+'"' not in result, 'Windows Lean slot occupied'
print('Machine-wide Lean slot clear; guarded resource check follows.')
