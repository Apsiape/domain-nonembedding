from pathlib import Path
import os,sys,json,time,subprocess,hashlib,signal,resource
root=Path(__file__).resolve().parent.parent
out=root/'.lake/release';out.mkdir(parents=True,exist_ok=True)
mode=sys.argv[1]
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1<<20),b''):h.update(b)
 return h.hexdigest()
def memory():return {k:int(v.split()[0])*1024 for k,v in (x.split(':',1) for x in Path('/proc/meminfo').read_text().splitlines())}['MemAvailable']
initial_wsl=memory()
host=json.loads((root/'.build-control/host-state.json').read_text())
assert time.time()-host['epoch']<15 and host['available_bytes']>=8*1024**3 and memory()>=8*1024**3
assert host['c_free_bytes']>=50_000_000_000 and not host['lean_pids'] and not host['lake_pids']
resource.setrlimit(resource.RLIMIT_CORE,(0,0))
env=os.environ.copy();env['COMPARATOR_BWRAP']=str(root/'scripts/bwrap-record.py');env['LEAN_NUM_THREADS']='1';env['TMPDIR']=str(out)
cfg=json.loads((root/'comparator.json').read_text());tool=root/'.build-control/toolchain/bin'
primitives=['Nat.add','Nat.sub','Nat.mul','Nat.pow','Nat.gcd','Nat.div','Nat.mod','Nat.beq','Nat.ble','Nat.land','Nat.lor','Nat.xor','Nat.shiftLeft','Nat.shiftRight','String.ofList','Char.ofNat','List','eagerReduce','Nat','String','String.mk','Char','optParam','autoParam','semiOutParam','outParam']
roots=cfg['theorem_names']+['DomainNonembedding.Main.'+n for n in json.loads((root/'evidence/RELEASE-FORM.json').read_text())['proposition_bodies']]+['DomainNonembedding.rowRank_eq_columnRank','DomainNonembedding.ShearNonembedding.shear_rank_bound']
export=out/'Solution.ndjson'
if mode=='comparator':cmd=['lake','comparator','--config','comparator.json']
elif mode=='export':cmd=['lake','env',str(tool/'leanexport'),'Solution','--','Quot','Quot.mk','Quot.lift','Quot.ind',*roots,*cfg['permitted_axioms'],*primitives]
elif mode=='leanchecker':cmd=[str(tool/'leanchecker'),'--silent','--from-export',str(export)]
elif mode in ['nanoda','negative']:
 config={'use_stdin':False,'export_file_path':str(export),'num_threads':1,'nat_extension':True,'string_extension':True,'permitted_axioms':[a for a in cfg['permitted_axioms'] if mode!='negative' or a!='Classical.choice'],'unpermitted_axiom_hard_error':True}
 p=out/(mode+'.json');p.write_text(json.dumps(config,indent=2)+'\n');cmd=[str(tool/'nanoda_bin'),str(p)]
else:raise ValueError(mode)
start=time.time();cap=8192*1024**2;peak=0;limited=False
with (out/(mode+'.txt')).open('wb') as log, (export.open('wb') if mode=='export' else open(os.devnull,'wb')) as ex:
 child=subprocess.Popen(cmd,cwd=root,env=env,stdout=ex if mode=='export' else log,stderr=log,start_new_session=True)
 while child.poll() is None:
  procs={}
  for p in Path('/proc').iterdir():
   try:
    if p.name.isdigit():
     d=dict(x.split(':',1) for x in (p/'status').read_text().splitlines() if ':' in x);procs[int(p.name)]=(int(d['PPid']),int(d.get('VmRSS','0 kB').split()[0])*1024)
   except (OSError,ValueError,KeyError):pass
  ids={child.pid}
  for _ in range(20):ids|={p for p,(parent,_) in procs.items() if parent in ids}
  rss=sum(procs.get(p,(0,0))[1] for p in ids);peak=max(peak,rss)
  if rss>cap:limited=True;os.killpg(child.pid,signal.SIGTERM)
  time.sleep(.25)
 code=child.wait()
rec={'mode':mode,'command':cmd,'exit_code':code,'started_epoch':start,'finished_epoch':time.time(),'peak_tree_rss_bytes':peak,'rss_cap_bytes':cap,'cap_exceeded':limited,'host_before':host,'wsl_available_before':initial_wsl,'wsl_available_after':memory(),'log_sha256':sha(out/(mode+'.txt'))}
rec['tool_binaries_sha256']={n:sha(tool/n) for n in ['lake','leanexport','leanchecker','nanoda_bin']}
if mode=='export' and code==0:rec.update({'export_sha256':sha(export),'export_bytes':export.stat().st_size,'proof_roots':roots})
if mode=='comparator':rec.update({'bubblewrap':True,'network_disabled':True,'supplied_exports':False})
if mode=='negative':rec['expected_rejection']=code!=0 and 'unpermitted axiom' in (out/(mode+'.txt')).read_text(errors='replace')
(out/(mode+'-receipt.json')).write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec),flush=True)
if mode=='negative':sys.exit(0 if rec['expected_rejection'] and not limited else 1)
sys.exit(code if not limited else 76)
