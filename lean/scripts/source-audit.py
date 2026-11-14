from pathlib import Path
import hashlib,json,os,re,subprocess
r=Path(__file__).resolve().parent.parent
owned=[]
for directory,subdirs,files in os.walk(r):
    subdirs[:]=[n for n in subdirs if n not in ['.git','.lake','.build-control','deps','__pycache__']]
    owned.extend(Path(directory)/n for n in files if n.endswith('.lean'))
census={};violations=[]
for p in owned:
    s=p.read_text(encoding='utf-8');rel=p.relative_to(r).as_posix()
    hits=len(re.findall(r'\bsorry\b',s))
    if rel=='Challenge.lean':
        assert hits==3, 'Challenge must have exactly three intentional holes'
        continue
    if hits:census[rel]=hits
    if hits and rel!='Statements.lean':violations.append('unfinished proof outside Statements: '+rel)
    if re.search(r'\b(native_decide|implemented_by|extern|axiom|sorryAx)\b',s):violations.append('forbidden declaration/token: '+rel)
    if 'set_option autoImplicit false' not in s:violations.append('missing autoImplicit setting: '+rel)
records=json.loads((r/'evidence/nonsofic-sha256.json').read_text(encoding='utf-8'))['files']
for row in records:
    p=r/'deps/nonsofic'/row['path']
    if hashlib.sha256(p.read_bytes()).hexdigest()!=row['sha256']:violations.append('reuse hash mismatch: '+row['path'])
manifest=json.loads((r/'lake-manifest.json').read_text(encoding='utf-8'))
for package in manifest['packages']:
    if package['type']=='path':
        target=(r/package['dir']).resolve()
        if not target.is_relative_to(r):violations.append('external path dependency: '+str(target))
result={'owned_lean_files':len(owned),'unfinished_proof_census':census,'total':sum(census.values()),
    'reuse_files_verified':len(records),'violations':violations,
    'note':'This is a source audit; it does not substitute for Lean type checking.'}
print(json.dumps(result,indent=2))
assert not violations
