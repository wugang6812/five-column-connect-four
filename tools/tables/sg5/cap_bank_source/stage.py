#!/usr/bin/env python3
"""Source-only 802,510-row cap candidate. No Lean runner or proof execution."""
from __future__ import annotations
from pathlib import Path
from array import array
from hashlib import file_digest
import hashlib,json,re,shutil,resource,sys,time
from types import ModuleType
P=Path(__file__).resolve().parent
R=P.parent
WORK=R.parent
A=R/'sg5_reroute_source_pilot_20261121/prepared'
D=R/'cap_only_external'
FAST=R/'cap_fast_pilot'
TAG=R/'cap_tagged_pilot'
CAP=R/'cap_working'
OLD=WORK/'sg5_branch_recovery/frozen_base/even_sg5_long_release_20261121'
GEN=R/'sg5_reroute_source_pilot_20261121/baseline_pins/generate_sg5_long.py'
STAGE=P/'candidate'
TMP=P/'candidate.part'
RANGE=5**10
N=4405983
NROWS=802510
NCAP=162563
NOLD=58067
NLEAF=220630
MISS=2**32-1
I=re.compile(r'^import (\S+)\s*$',re.M)
sys.path.insert(0,str(R/'sg5_reroute_source_pilot_20261121'))
from stage_source import word, unword, WINDOW_RE, row_tree
def need(x,z):
 if not x:raise RuntimeError(z)
def sha(path):
 with path.open('rb') as f:return file_digest(f,'sha256').hexdigest()
def jd(p):return json.loads(p.read_bytes())
def dump(p,x):p.write_text(json.dumps(x,sort_keys=True,indent=2)+'\n')

def pin_input():
 for file,hash0 in ((GEN,'3f04daeb3f453babfdb3092ceed5a627e81b729851dc92c2c9b4b436e0b974f2'),
        (OLD/'SG5LongSourceSHA256.json','a6ca3e5b1252250e8fa1fffabe65a99a2e9573237aaabfc67e426b13f7a374b6')):
    need(sha(file)==hash0,f'unexpected exact source: {file.name}')
 capzip=R/'C4W5_SG5_CapOnly_Retarget_Exact_802510_20261121_v1.zip'
 fastzip=R/'C4W5_SG5_CapFast_ExactSound_Matched8_20261121_v1.zip'
 need(sha(capzip)=='d746dcea507d120eea7208af40dce69e3721882cbf189b6a6dd2681227fcd7a7','cap graph archive changed')
 need(sha(fastzip)=='d3552460fffe7869240880014b61049f198712f40be8ddceff65201db8f5d32f','fast proof archive changed')
 import zipfile
 for arc,bs in [(capzip,D),(fastzip,FAST)]:
    with zipfile.ZipFile(arc) as z:
       ids={ln.split()[1]:ln.split()[0] for ln in z.read('SHA256SUMS').decode().splitlines()}
       for fn,h in ids.items():
          path=R/fn
          need(path.is_file() and sha(path)==h,f'changed pinned reference: {fn}')
 q=jd(D/'independent_cap_replay.json')
 need(q['status']=='EXACT_SELECTED_POLICY_REPLAY_PASS' and
      [(f['expanded'],f['cap_endpoints'],f['used_LongZO']) for f in q['roots']]==
      [(270873,61532,17001),(531637,101031,41066),(802510,162563,58067)],'old closure receipt scope')
 checktags=jd(FAST/'all_witness_words_audit.json')
 need(checktags['cap_source_sha256']==sha(D/'cap_witness_rows.txt') and checktags['rows']==NCAP,'caps changed since all-tag audit')

def cap_code(t,s,a,b,da,db,ia,ib):
 need(a%2==1 and b%2==0 and 0<=a//2<32 and 0<=b//2<32,'wrong target encoding')
 w=t+5*(s+5*(a//2+32*(b//2+32*(da+3*(db+3*(ia+4*ib))))))
 k=w
 for v,b0 in zip((t,s,a//2,b//2,da,db,ia,ib),(5,5,32,32,3,3,4,4)):
    k,r=divmod(k,b0);need(r==v,'cap decode differs')
 need(k==0 and w<3686400,'cap range')
 return w+117120

def project():
 expected=array('I',[MISS])*N
 seen=bytearray(N)
 for line in (D/'cap_policy_replies.txt').open():
    i,r=map(int,line.split());need(0<=i<N and expected[i]==MISS and 0<=r<RANGE,'bad selected row label')
    expected[i]=r
 rp=TMP/'inputs/selected_policy_rows.txt'; lp=TMP/'inputs/selected_tag_words.txt'
 rp.parent.mkdir()
 ready=changed=0; roots={}; last=-1
 dig=hashlib.sha256(); olddig=hashlib.sha256()
 oldroots=[]
 with rp.open('w') as out:
    for line in (D/'old_policy_projection.txt').open():
       row=line.split(); i=int(row[0]); r=expected[i]
       p=tuple(map(int,row[1:]))
       q=word(p)
       if i in (1670,1671):oldroots.append(q)
       else:
          need(q//RANGE>last,'original ordered non-root projection changed')
          last=q//RANGE
          olddig.update(q.to_bytes(48,'little'))
       if r==MISS:continue
       need(not seen[i],'duplicated policy board label')
       seen[i]=1
       ready+=1
       changed+=r!=p[-1]
       if i in (1670,1671):roots[i]={'height':p[0],'word':hex(word((*p[:-1],r))),
           'selected_rep':r,'old_rep':p[-1]}
       row[-1]=str(r);out.write(' '.join(row)+'\n')
 need(ready==NROWS and changed==25809 and sorted(roots)==[1670,1671],'policy count or exact roots changed')
 # Compare the *actual* previously decoded complete old bank files again. They
 # are a temporary streaming projection, not separately trusted new source.
 verify_old_projections()

 listed=bytearray(N)
 for line in (D/'used_old_long_leaf_ids.txt').open():
    i=int(line);need(0<=i<N and listed[i]==0 and not seen[i],'duplicate old witness selector');listed[i]=1
 total_old=total_cap=0
 with lp.open('w') as out:
    for line in (D/'old_leaf_projection.txt').open():
       i,H,*z=map(int,line.split())
       if not listed[i]:continue
       need(listed[i]==1 and not seen[i],'duplicate old witness')
       listed[i]=2;seen[i]=1
       t,rho,mask,d,k=z[-5:]
       code=t+5*(rho+61*(mask+32*(d+3*k)))
       need(code<117120,'old Long tag out of old range')
       out.write(' '.join(map(str,(0,i,H,*z[:10],code)))+'\n')
       total_old+=1
    for line in (D/'cap_witness_rows.txt').open():
       i,H,*z=map(int,line.split())
       need(not seen[i] and expected[i]==MISS,'overlap cap/policy/old leaf')
       seen[i]=1
       t,s,a,b,m,da,db,ia,ib=z[-9:]
       need(0<H<=64 and H%2==0 and z[5+t]%2==1 and z[5+s]%2==0 and z[5+s]<a<b<H,'bad cap stage data')
       need(m==sum(1<<c for c,h in enumerate(z[5:10]) if c not in (t,s) and h<H and h%2==0),'cap mask not reconstructed exactly')
       code=cap_code(t,s,a,b,da,db,ia,ib)
       dig.update(i.to_bytes(4,'little')+code.to_bytes(4,'little'))
       out.write(' '.join(map(str,(1,i,H,*z[:10],code)))+'\n')
       total_cap+=1
 need((total_old,total_cap)==(NOLD,NCAP) and sum(v==1 for v in listed)==0,'old/cap witnesses differ')
 need(dig.hexdigest()=='4999e6dc984d5599d057a5ebdda61fc579f167054196f6cc4efd8848087f232d','cap tag words do not match independent mask/tag audit')
 dump(TMP/'root_receipt.json',roots)
 return rp,lp,expected

def unpack_lean(file):
 for n,a,b,z in WINDOW_RE.findall(file.read_text()):
    n,a,b,z=int(n),int(a),int(b),int(z,16)
    for _ in range(n):
       z,d=divmod(z,a);yield b+d
    need(z==0,'overflow')

def verify_old_projections():
 man=jd(OLD/'SG5LongSourceSHA256.json')
 q=OLD/'sg5_long_source/SG5LongPacked'
 # Original ranks are stable by packed sort. Root lines were placed first for
 # the old graph walk and are checked by actual key rather than guessed rank.
 with (D/'old_policy_projection.txt').open() as f:
    rs=[tuple(map(int,f.readline().split())) for _ in range(2)]
    rid={x[0]:word(x[1:]) for x in rs}
    n=hits=0
    for i in range(167):
       p=q/f'D{i}.lean';need(sha(p)==man[f'sg5_long_source/SG5LongPacked/{p.name}'],'old D hash changed')
       for z in unpack_lean(p):
          if z in rid.values():hits+=1
          else:
             u=list(map(int,f.readline().split()))
             need(u[0]==10000+n and z==word(u[1:]),'old policy projection word or rank differs')
          n+=1
    need(hits==2 and n==1535820 and f.readline()== '','wrong baseline policy extent')
 p=q/'Witnesses.lean'
 need(sha(p)==man['sg5_long_source/SG5LongPacked/Witnesses.lean'],'old witness source changed')
 with (D/'old_leaf_projection.txt').open() as f:
    n=0
    for z in unpack_lean(p):
       u=list(map(int,f.readline().split()));t,r,m,d,i=u[-5:]
       code=t+5*(r+61*(m+32*(d+3*i)))
       need(u[0]==2500000+n and z==word((*u[1:12],code)),'old witness projection word changed')
       n+=1
    need(n==251809 and f.readline()=='','wrong old witness extent')

def patch_generator(rp,lp,selected):
 s=GEN.read_text()
 a=s.index('    binfile=ORIGINAL.open')
 b=s.index('    def pack(t):',a)
 replacements={
 s[a:b]:'    # Raw immutable boards and original tags were independently streamed against the frozen old source.\n',
 'assert row==original_at(idx)':'assert row[-1]==SELECTED_REP[idx]',
 '    mm.close();binfile.close()\n':'',
 '    assert len(witness)==251809 and':'    assert len(witness)==220630 and',
 "gm=('WindowLongGate' if reference else 'WindowLongGateFast')":"gm='CapFastTagged'",
 "g=('referenceGate' if reference else 'fastGate')":"g='CapFastTagged.gate'",
 'LongThreat.L h p.toBoard := {g}_sound fmt witnessBank':'CapTagged.L h p.toBoard := {g}_sound fmt witnessBank',
 "'theorem longGate_lift : LeafSound 2 LongThreat.L := LongThreat.leafSound (by decide)\n'"
  :"'theorem longGate_lift : LeafSound 2 CapTagged.L := CapTagged.leafSound (by decide)\n'",
 }
 # The two quotes below hold literal escape sequences in the received source.
 # Replace the body without trusting old payload metadata for the new tags.
 a=s.index('        idx,*tt=map(int,line.split());t=tuple(tt)')
 b=s.index('    witness.sort()',a)
 replacements[s[a:b]]='''        kind,idx,*record=map(int,line.split())
        assert len(record)==12
        assert (kind==0 and record[-1]<117120) or (kind==1 and 117120<=record[-1]<3803520)
        witness.append(pack(tuple(record)))
'''
 # The archived hook's source uses backslash-n within a Python string.
 long_lift=[x for x in replacements if 'LeafSound 2 LongThreat.L' in x][0]
 if long_lift not in s:
    dst=replacements.pop(long_lift).replace('\n','\\n')
    replacements[long_lift.replace('\n','\\n')]=dst
 for old,new in replacements.items():
    need(s.count(old)==1,f'generator patch ambiguous/incomplete: {old[:70]}')
    s=s.replace(old,new)
 dump(TMP/'generator_exact_edits.json',replacements)
 m=ModuleType('capSourceFrozenAdapter');m.__file__=str(GEN)
 exec(compile(s,m.__file__,'exec'),m.__dict__)
 m.P=TMP;m.TOP=TMP/'lean';m.W=m.TOP/'SG5LongPacked';m.ROWS=rp;m.LEAVES=lp;m.NROWS=NROWS
 m.SELECTED_REP=selected
 m.make(reference=False)
 need('CapFastTagged.gate' in (m.W/'Hooks.lean').read_text(),'new factory did not select fast-tag gate')
 return jd(TMP/'sg5_long_generation.json')

def freeze_support(order):
 sets=[(CAP,R/'cap_validation/receipt.json',['CapTransferArithmetic','CapTransferDefs','CapTransferBoard',
             'CapTransferRebase','CapTransferStretch','CapTransferCheck']),
        (TAG/'source',TAG/'actual/receipt.json',['CapTaggedGate']),
        (FAST/'source',FAST/'actual/receipt.json',['CapDoubleMasks','CapFastTagged'])]
 pinned={}; names=[]
 for rp,receipt,ms in sets:
    info=jd(receipt)['accepted']
    for m in ms:
       p=rp/(m+'.lean');q=TMP/'lean'/p.name
       need(sha(p)==info[m]['source_sha256'],'support source differs from real acceptance')
       shutil.copyfile(p,q);pinned[m]=info[m];names.append(m)
 p=OLD/'sg5_long_source/G5LongRoot.lean'
 need(sha(p)=='08cdc1751d209e2fdfd1a4cfc879a8e973c35b0d16aef530edc7de1a56b1e058','G5 generic bridge differs')
 shutil.copyfile(p,TMP/'lean'/p.name)
 order['compile_order']=[*names,'G5LongRoot',*order['compile_order']]
 order['gen_dir']='lean'
 order['checker']='proved CapFastTagged.gate with post-mask dominance'
 order['scope']='SOURCE_ONLY_UNCHECKED_PRODUCTION_CLOSURE'
 dump(TMP/'sg5_long_generation.json',order)
 dump(TMP/'actual_support_import_pins.json',pinned)

def audit(order):
 man=jd(OLD/'SG5LongSourceSHA256.json')
 root=TMP/'lean'
 pins={}
 prior=set(); names=order['compile_order']; expected=set(names)
 k_list=[]
 for m in names:
    p=root/(m.replace('.','/')+'.lean'); s=p.read_text()
    need(not re.search(r'\b(sorry|admit|native_decide|sorryAx)\b',s),'forbidden generated proof shortcut')
    h=sha(p);direct=I.findall(s)
    need(all(i in prior for i in direct if i in expected),'generated import order inconsistency')
    pins[m]={'source_sha256':h,'direct_imports':direct};prior.add(m)
    if not re.fullmatch(r'SG5LongPacked\.K\d+',m):continue
    need(direct==['SG5LongPacked.Top'],'non-independent K shard')
    k_list.extend(re.findall(r'^theorem (p\d+)_ok\b[^\n]+:= by decide \+kernel$',s,re.M))
 need(k_list==[f'p{x}' for x in range(2090)],'does not cover exactly all unique check groups')
 need(pins['SG5LongPacked.Layout']['source_sha256']==man['sg5_long_source/SG5LongPacked/Layout.lean'],'layout changed')
 oldmain=OLD/'sg5_long_source/SG5LongPacked/Main.lean'
 need(sha(oldmain)==man['sg5_long_source/SG5LongPacked/Main.lean'],'original public statements changed')
 select=lambda p:p.read_text().split('/-- Conditional generated release:',1)[1]
 need(select(oldmain)==select(root/'SG5LongPacked/Main.lean'),'public theorem bodies/statement/axioms-notes changed')
 need(pins['SG5LongPacked.Main']['direct_imports']==['G5LongRoot',*(f'SG5LongPacked.K{i}' for i in range(697))],
      'incorrect top imports')
 dump(TMP/'lean_imports_and_sha256.json',pins)
 flow={}
 for typ,proj in [('policy',TMP/'inputs/selected_policy_rows.txt'),('witness',TMP/'inputs/selected_tag_words.txt')]:
    xs=sorted(word(list(map(int,a.split()[2 if typ=='witness' else 1:]))) for a in proj.open())
    paths=[root/'SG5LongPacked/Witnesses.lean'] if typ=='witness' else [root/f'SG5LongPacked/D{i}.lean' for i in range(88)]
    idx=0; h=hashlib.sha256()
    for p in paths:
       for z in unpack_lean(p):
          need(idx<len(xs) and z==xs[idx],'exact emitted numeric stream mismatch')
          idx+=1;h.update(z.to_bytes(48,'little'))
    need(idx==len(xs),'decoded source misses some selected rows')
    flow[typ]={'rows':idx,'word_stream_sha256':h.hexdigest()}
 return {'source_modules':len(pins),'source_bytes':sum((root/(m.replace('.','/')+'.lean')).stat().st_size for m in pins),
        'decoded':flow,'new_groups':2090,'K_shards':697,'data_modules':88}

def main():
 need(not STAGE.exists() and not TMP.exists(),'no overwrite of existing staged source')
 need(shutil.disk_usage(P).free>3*2**30,'not enough disk headroom')
 pin_input();TMP.mkdir()
 x,y,z=project()
 rec=patch_generator(x,y,z)
 freeze_support(rec)
 verified=audit(rec)
 dump(TMP/'readiness.json',{'status':'SOURCE_ONLY_NOT_KERNEL_ACCEPTED','no_lean_launched':True,**verified,
    'roots_sha256':sha(TMP/'root_receipt.json'),'input_sha256':{p.name:sha(p) for p in [x,y]},
    'source_profile':'cap-only 802,510 policy and 220,630 witnesses; both original public families',
    'rss_peak_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss})
 TMP.replace(STAGE)
 print(json.dumps(verified,indent=2))
if __name__=='__main__':main()
