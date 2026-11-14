from pathlib import Path
import os,sys,json,time,subprocess,shutil,hashlib,re
root=Path('/opt/domain-nonembedding-lean/project')
workspace=Path('/opt/domain-nonembedding-clean-2026-11-13')
assert workspace.parent==Path('/opt') and not workspace.exists()
out=root/'.lake/release/clean-clone';out.mkdir(parents=True,exist_ok=True)
for p in out.iterdir():
 if p.is_file():p.unlink()
env=os.environ.copy();env.pop('LEAN_PATH',None);env.pop('LEAN_SRC_PATH',None);env.update({'GIT_ALLOW_PROTOCOL':'https:file','MATHLIB_NO_CACHE_ON_UPDATE':'1','LEAN_NUM_THREADS':'1'})
records=[]
def run(label,cmd,cwd):
 start=time.time()
 with (out/(label+'.txt')).open('wb') as log:p=subprocess.run(cmd,cwd=cwd,env=env,stdout=log,stderr=subprocess.STDOUT)
 rec={'label':label,'command':cmd,'exit_code':p.returncode,'started_epoch':start,'finished_epoch':time.time()};records.append(rec)
 print(json.dumps(rec),flush=True)
 if p.returncode:raise RuntimeError(label+' failed')
result={'workspace':str(workspace),'network_scope':'GitHub pinned dependencies and Mathlib cache only','fresh_workspace':True,'preexisting_build_artifacts':False,'checks':records}
try:
 bundle=root/'work/clean-clone.bundle'
 result['local_bundle_sha256']=hashlib.sha256(bundle.read_bytes()).hexdigest()
 run('clone',['git','clone','--no-hardlinks',str(bundle),str(workspace)],Path('/opt'))
 result['tested_commit']=subprocess.check_output(['git','rev-parse','HEAD'],cwd=workspace,text=True).strip()
 assert not (workspace/'.lake').exists()
 control=workspace/'.build-control';control.mkdir();(control/'gitconfig').write_text('')
 for key,sub in [('LAKE_CACHE_DIR','lake-cache'),('MATHLIB_CACHE_DIR','mathlib-cache'),('XDG_CACHE_HOME','xdg-cache'),('TMPDIR','tmp'),('TMP','tmp'),('TEMP','tmp')]:
  p=control/sub;p.mkdir(exist_ok=True);env[key]=str(p)
 env['GIT_CONFIG_GLOBAL']=str(control/'gitconfig');env['GIT_CONFIG_NOSYSTEM']='1'
 run('cache-get',['lake','exe','cache','get'],workspace)
 try:
  run('build',['lake','build'],workspace)
 except RuntimeError:
  text=(out/'build.txt').read_text(errors='replace')
  if 'Compilation gate closed' not in text:raise
  shutil.copyfile(out/'build.txt',out/'build-resource-deferral.txt')
  # All hints target our own newly created workspace; no contents change.
  for p in workspace.rglob('*'):
   if p.is_file() and not p.is_symlink() and '.git' not in p.parts:
    try:
     with p.open('rb') as f:os.posix_fadvise(f.fileno(),0,0,os.POSIX_FADV_DONTNEED)
    except OSError:pass
  time.sleep(5)
  run('build-retry',['lake','build'],workspace)
  shutil.copyfile(out/'build-retry.txt',out/'build.txt')
 run('audit',['lake','env','lean','-j1','-M5000','Audit.lean'],workspace)
 run('solution',['lake','env','lean','-j1','-M5000','-o','.lake/build/lib/lean/Solution.olean','Solution.lean'],workspace)
 run('solution-audit',['lake','env','lean','-j1','-M5000','SolutionAudit.lean'],workspace)
 run('source-audit',['python3','-I','scripts/source-audit.py'],workspace)
 run('git-diff',['git','diff','--exit-code'],workspace)
 logs={k:(out/(k+'.txt')).read_text(errors='replace') for k in ['build','audit','solution','solution-audit']}
 assert all('declaration uses `sorry`' not in s and 'sorryAx' not in s for s in logs.values())
 assert 'FULL-AUDIT-PASS declarations=2792' in logs['audit']
 for n in ['paperData_exists','nonembedding_data','shear_nonembedding_data']:
  assert "'DomainNonembedding.Release."+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in logs['solution-audit']
 census=json.loads((out/'source-audit.txt').read_text());assert census['total']==0
 result.update({'status':'PASS','development_sorry_count':0,'challenge_intentional_holes':3,'compiled_sorry_warnings':0,'full_axiom_audit_declarations':2792,'solution_axiom_audit_declarations':3,'manifest_unchanged':True,'source_tree_unchanged':True})
except Exception as e:
 result.update({'status':'FAIL','error':str(e)})
finally:
 # The only recursive deletion: the exact newly created, authorized test workspace.
 if workspace.exists():
  assert workspace.resolve()==Path('/opt/domain-nonembedding-clean-2026-11-13')
  assert not workspace.is_symlink()
  shutil.rmtree(workspace)
 result['workspace_deleted']=not workspace.exists()
 result['log_sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in out.glob('*.txt')}
 (out/'receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
sys.exit(0 if result.get('status')=='PASS' else 1)
