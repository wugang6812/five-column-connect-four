#!/usr/bin/env python3
"""Export the independently replayed SGZ5R fixed projection to canonical banks
and uncompiled Lean source. No closure replay, solver, or compiler."""
from pathlib import Path
from array import array
import hashlib, json, mmap, shutil, struct, sys, time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'wide_gate_pilot'))
from pick_micro import unpack, key, code_cap, RR, EXP, NT, REC, ROOT
FLAT_SHA='565f6bf1ddd9b84b90a2a76d804b6f615c02797fcffe8fa0b007873f317b781e'
PICK_SHA='e59a0f31582745007dcc8367b12267123cfe4ac734e4a41bf780087dbf7b30e1'
WIT_ARCHIVE_SHA='d8d52d441057869e2c2f5849a5f2749710783f07e92f797e41741712cd2e3309'
ACCEPTED_GATE_ZIP_SHA='b6ba6af40a7c419f6faeb3c30926e2fe69eb2df631684d882694cd6f55948181'
OLD_SHA='f464ce6ca403f1f589e8dbf61dbca331d586f67a09eecb93f00f94df8c13ed74'
NS='C4W5.SGZLongPacked'
PRE='SGZLongPacked.'
HEAD=struct.Struct('<8sIHH')
BLOCK=struct.Struct('<HHHH')
WINDOW=24; GROUP=16; DATA_DIV=24; CHECK_DIV=3
HEADER=f'''namespace {NS}
open Connect4.NarrowBoards C4W5.WindowBank C4W5.CompactSGZ
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
'''
TAIL=f'\nend {NS}\n'
CAP_HIST_EXPECTED=(905511,116548,155994)
def sha(p):
    with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def shortage(out):
    f=shutil.disk_usage(out)
    if f.used>13*1024**3 or f.free<1024**3:
        raise SystemExit('disk admission guard before source/bank staging')
def as_bytes(n):return n.to_bytes((n.bit_length()+7)//8,'little')
def decode_cap(c):
    assert 117120<=c<3803520
    q,t=divmod(c-117120,5);q,s=divmod(q,5)
    q,a=divmod(q,32);q,b=divmod(q,32)
    q,da=divmod(q,3);q,db=divmod(q,3);ib,ia=divmod(q,4)
    assert 0<=ib<4
    return t,s,2*a+1,2*b,da,db,ia,ib
def projection(flat,pick):
    assert len(flat)==NT*REC.size
    # One byte/index for exact uniqueness. Preserve both sorted source banks,
    # then merge only in the explicit mixed-terminal sorted key.
    chosen=bytearray(NT);policy=[];hints=[]
    hist={b'P':0,b'L':0,b'C':0}; rootmatch=[]
    for line in pick:
        t,i,rep,*raw=line.split()
        i=int(i);rep=int(rep);assert 0<=i<NT and not chosen[i] and t in hist
        chosen[i]=t[0];hist[t]+=1
        q,r,oro=unpack(flat,i)
        assert rep==r and oro==int(t==b'L') and 0<=rep<RR
        assert not(q[0]%2) and 0<q[0]<=60 and all(l==0 or h==q[0] for h,l in zip(q[2],q[3]))
        if t==b'C':
            w=list(map(int,raw));assert len(w)==9
            x=code_cap(q,w)
            assert decode_cap(x)==tuple(w[:4]+w[5:])
        else:
            assert not raw
            x=rep
            if t==b'L':assert 0<=x<117120
        val=key(q)*RR+x
        if t==b'P':policy.append((val,i))
        else:hints.append((val,i))
        if q==ROOT:rootmatch.append((i,t,val))
    assert tuple(hist[x] for x in (b'P',b'L',b'C'))==CAP_HIST_EXPECTED
    assert len(rootmatch)==1 and rootmatch[0][0:2]==(379,b'P')
    policy.sort();hints.sort()
    for ws in (policy,hints):
        assert all(x[0]//RR<y[0]//RR for x,y in zip(ws,ws[1:]))
    def no_overlap():
        i=j=0
        while i<len(policy) and j<len(hints):
            k=policy[i][0]//RR;l=hints[j][0]//RR
            assert k!=l
            if k<l:i+=1
            else:j+=1
    no_overlap()
    return policy,hints,rootmatch[0][2]
def rowtree(ws):
    if len(ws)==1:
        n,r,b,p=ws[0]
        return f'(.window {n} {r} {b} 0x{p:x})'
    i=len(ws)//2
    return f'(.branch {ws[i][2]//RR} {rowtree(ws[:i])} {rowtree(ws[i:])})'
def pack(words,file):
    windows=[]
    hs=hashlib.sha256()
    with file.open('wb') as f:
        f.write(HEAD.pack(b'C4WSZB01',len(words),WINDOW,0))
        for i in range(0,len(words),WINDOW):
            seq=words[i:i+WINDOW]
            n=len(seq);b=seq[0][0]//RR*RR;w=max(1,(seq[-1][0]-b).bit_length());r=(1<<w)+1
            p=0
            for x,_ in reversed(seq):p=p*r+x-b
            for x,_ in seq:hs.update(x.to_bytes(40,'little'))
            bb,pb=as_bytes(b),as_bytes(p)
            f.write(BLOCK.pack(n,w,len(bb),len(pb)));f.write(bb);f.write(pb)
            windows.append((n,r,b,p))
    # Separate raw byte decoder, reconstruct absolutely every word and key.
    out=hashlib.sha256();z=0;prior=-1
    with file.open('rb') as f:
        assert HEAD.unpack(f.read(HEAD.size))==(b'C4WSZB01',len(words),WINDOW,0)
        for record in windows:
            n,w,lb,lp=BLOCK.unpack(f.read(BLOCK.size))
            b=int.from_bytes(f.read(lb),'little');p=int.from_bytes(f.read(lp),'little')
            r=(1<<w)+1;assert (n,r,b,p)==record
            for _ in range(n):
                p,x=divmod(p,r);x+=b
                assert words[z][0]==x and x//RR>prior
                prior=x//RR;z+=1
                out.update(x.to_bytes(40,'little'))
            assert p==0
        assert z==len(words) and f.read(1)==b''
    assert out.hexdigest()==hs.hexdigest()
    return windows,{'rows':len(words),'windows':len(windows),'bytes':file.stat().st_size,
                    'sha256':sha(file),'semantic_word_sha256':out.hexdigest()}
def emit(d,pc,hc,words,rootword,gate_source):
    d.mkdir();stage=d/'SGZLongPacked';stage.mkdir()
    order=[]
    for n,want in [('SGZLayout','b7ca643768d13816eebe0eaf495d6f799cdf0791060c64242a81b0e8d15b8ab8'),
      ('WindowZoneTagged','188719913210662dffcf02bc2236db3582a7986835975130aa58650ed930c16a')]:
        p=gate_source/(n+'.lean');assert sha(p)==want
        shutil.copyfile(p,d/(n+'.lean'));order.append(n)
    def put(n,imp,s):
        p=stage/(n+'.lean')
        p.write_text(''.join('import '+x+'\n' for x in imp)+'\n'+HEADER+s+TAIL)
        return PRE+n
    def make(ws,prefix):
        names=[];texts=[];mods=[];nodes=[];proof=[]
        for i in range(0,len(ws),GROUP):
            sub=ws[i:i+GROUP];n=f'{prefix}P{len(names):04d}'
            names.append((n,sub[0][2]//RR))
            texts.append(f'def {n} : Bank := {rowtree(sub)}')
        for i in range(0,len(names),DATA_DIV):
            mods.append(put(f'{prefix}D{len(mods):03d}',['SGZLayout'],'\n'.join(texts[i:i+DATA_DIV])))
        def merge(xs):
            if len(xs)==1:return xs[0][0]
            i=len(xs)//2;l=merge(xs[:i]);r=merge(xs[i:]);n=f'{prefix}N{len(nodes):04d}'
            nodes.append(f'def {n} : Bank := .branch {xs[i][1]} {l} {r}')
            proof.append(f'theorem {n}_ok : all fmt.radix checkPolicyRow {n} = true := all_branch {l}_ok {r}_ok')
            return n
        root=merge(names)
        return mods,names,nodes,proof,root
    md,mn,mnodes,mproof,main=make(pc,'E');hd,hn,hnodes,_,hint=make(hc,'H')
    hintidx=put('WitnessIndex',hd,'\n'.join(hnodes)+f'\ndef hints : Bank := {hint}\n')
    order += hd+[hintidx]+md
    top=put('Top',[*md,hintidx,'WindowZoneTagged'],'\n'.join(mnodes)+f'''
def mainBank : Bank := {main}
def terminalGate : ZEndGate := ZoneTagged.gate true fmt hints
def checkPolicyRow : Nat → Bool := zoneEndsRow 2 fmt mainBank terminalGate
''')
    order.append(top)
    ks=[];checks=[f'theorem {n}_ok : all fmt.radix checkPolicyRow {n} = true := by decide +kernel' for n,_ in mn]
    for i in range(0,len(checks),CHECK_DIV):
        ks.append(put(f'K{len(ks):04d}',[top],'\n'.join(checks[i:i+CHECK_DIV])))
    order+=ks
    order.append(put('Main',ks,'\n'.join(mproof)+f'''
theorem checked : all fmt.radix checkPolicyRow mainBank = true := {main}_ok
theorem rootEntry : szmem fmt mainBank 14 g5p ⟨0,0,0,0,0⟩ = true := by decide +kernel
theorem g5_wide (m b : Nat) (hb : 5 ≤ b) (hbm : b + 3 ≤ m) : Safe (2 * m) (G b) :=
  ZoneTagged.g5_wide_of_tagged fmt mainBank hints checked rootEntry m b hb hbm
#print axioms g5_wide
'''))
    # Optional future micro-admission target against the full actual production
    # banks, separate from Main and all other check obligations.
    ri=next(i for i,(w,_) in enumerate(words) if w==rootword)
    wi=ri//WINDOW;ids=[j for _,j in words[wi*WINDOW:(wi+1)*WINDOW]]
    rep=put('Representative24',[top],f'''
/- Future-only benchmark target. Not used or checked by the production archive. -/
def productionRootWindow : Bank := {rowtree([pc[wi]])}
theorem productionRootWindow_ok : all fmt.radix checkPolicyRow productionRootWindow = true := by decide +kernel
#print axioms productionRootWindow_ok
''')
    files={n:d/Path(*n.split('.')).with_suffix('.lean') for n in [*order,rep]}
    assert all(p.is_file() for p in files.values())
    return {'source_modules':len(files),'source_bytes':sum(p.stat().st_size for p in files.values()),
        'policy_data_modules':len(md),'witness_data_modules':len(hd),'K_modules':len(ks),'lookup_groups':{'policy':len(mn),'witness':len(hn)},
        'compile_order_for_future_only':order,'sha256':{n:sha(p) for n,p in files.items()},
        'representative_future_only':{'module':rep,'rows':len(ids),'normal_order_excluded':True,
            'contains_root':379 in ids,'root_policy_rank':ri,'window_index':wi,'exact_original_indices':ids,'lookup':'full production Top'}}

def main(flat,pick,out):
    start=time.monotonic()
    out.mkdir()
    shortage(out)
    assert sha(flat)==FLAT_SHA and sha(pick)==PICK_SHA
    with flat.open('rb') as f,mmap.mmap(f.fileno(),0,access=mmap.ACCESS_READ) as a,pick.open('rb') as b:
        p,h,r=projection(a,b)
    shortage(out)
    eb=out/'sgz5r_DirectCap_expanded_24.bin';hb=out/'sgz5r_DirectCap_tagged_hints_24.bin'
    pw,pe=pack(p,eb);hw,he=pack(h,hb)
    sh=emit(out/'lean',pw,hw,p,r,HERE.parent/'wide_gate_pilot/source')
    assert sh['representative_future_only']['contains_root']
    shortage(out)
    receipt={'status':'FULL_FIXED_DIGIT_SOURCE_ONLY_NOT_KERNEL_CHECKED','wall_seconds':round(time.monotonic()-start,3),
        'no_strategy_replay_or_new_search_or_compilation':True,
        'old_bank_input':{'Drive_id':'11yF-W79Fp-K_lNyBSl03tz2avioF8VNj','sha256':OLD_SHA},
        'thin_replay_archive_sha256':WIT_ARCHIVE_SHA,'accepted_gate_micro_matched_archive_sha256':ACCEPTED_GATE_ZIP_SHA,
        'flat_sha256':FLAT_SHA,'projection_sha256':PICK_SHA,
        'counts':{'expanded':CAP_HIST_EXPECTED[0],'old_long':CAP_HIST_EXPECTED[1],'direct_cap':CAP_HIST_EXPECTED[2],'total':sum(CAP_HIST_EXPECTED)},
        'wire':{'window_rows':WINDOW,'rep_radix':RR,'long_lt':117120,'cap_exclusive_limit':3803520,
            'root_exact_original_index':379,'root_word':str(r),'cutoff':14,'all_low':True},
        'banks':{'policy':pe,'tagged_witness':he},
        'banks_bytes_total':pe['bytes']+he['bytes'],'old_same_wire_banks_bytes':29673679,
        'public_declaration':'C4W5.SGZLongPacked.g5_wide',
        'public_type':'∀ m b : Nat, 5 ≤ b → b + 3 ≤ m → Safe (2 * m) (G b)',
        'lean':sh}
    (out/'EXPORT_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k not in ('lean','banks')},indent=2))
    print({k:sh[k] for k in ('source_modules','source_bytes','policy_data_modules','witness_data_modules','K_modules','representative_future_only')})
if __name__=='__main__':
    assert len(sys.argv)==4
    main(*(Path(x).resolve() for x in sys.argv[1:]))
