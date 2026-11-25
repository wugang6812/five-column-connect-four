#!/usr/bin/env python3
"""Source-only render of the exact verified STop compact Cap projection."""
import argparse,hashlib,json,re,struct,zipfile
from pathlib import Path
D=Path(__file__).resolve().parent
OLD_SHA='d0c42bb294b31a5266c788d7737530b96a23a2db2abda1a3dd5ee95d288e9e82'
RAW_SHA='bf90f2990b9286906ad181b962ffbdc9e2311b535a99a8291a1a2ddfbaa9cedc'
PROJ_SHA='e242cc8b66f9cf5b01ff06ca41d1be8b2586c66965529d1018744c6ae5f16ead'
OLD='C4W5_STop_compact_source_stage/'
PK='STopLongPacked'
PREFIX=f'stop_long_source/{PK}/'
LEN=struct.Struct('<B5B5QIB')
RAD=[9007199254740991,8796093022207,35184372088831,35184372088831]
R=5**10
CATS=('expanded','old-long','cap')
TEST='all fmt.radix (scheckExtraRow 2 fmt t longGate)'
HDR=f'''namespace C4W5.{PK}
open Connect4 (Player opponent)
open Connect4.NarrowBoards C4W5.WindowBank
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
'''
END=f'\nend C4W5.{PK}\n'
def sha(x):
    if isinstance(x,bytes):return hashlib.sha256(x).hexdigest()
    with Path(x).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def pack(H,h,B,p):
    q=((1<<h[0])-1)+B[0]
    for i,r in enumerate(RAD,1):
        u=((1<<h[i])-1)+B[i]
        assert 0<=u<r
        q=q*r+u
    return (q*27+H//2)*R+p
def readinputs(old,raw,projection):
    assert [sha(p) for p in (old,raw,projection)]==[OLD_SHA,RAW_SHA,PROJ_SHA]
    b=raw.read_bytes()
    assert len(b)==361606*LEN.size
    z=zipfile.ZipFile(old);p=json.loads(z.read(OLD+'STopLongSourceSHA256.json'))
    layout=z.read(OLD+PREFIX+'Layout.lean')
    assert sha(layout)==p[PREFIX+'Layout.lean']
    meta={};items={c:[] for c in CATS}; prev=-1
    for text in projection.read_text().splitlines():
        c,idx,*args=text.split();idx=int(idx)
        assert c in CATS and idx>prev;prev=idx
        H,*x=LEN.unpack_from(b,idx*LEN.size);h=x[:5];B=x[5:10];rep,z0=x[10:]
        assert 0<=rep<R and 0<H<=52 and H%2==0 and sum(h)%2==1 and all(0<=b<1<<y for y,b in zip(h,B))
        if c=='expanded':
            assert z0==0 and not args
            payload=rep
        elif c=='old-long':
            assert z0==1 and int(args[0])==rep and len(args)==1
            payload=rep;assert payload<117120
        else:
            assert z0==0 and len(args)==1
            payload=int(args[0]);assert 117120<=payload<3803520<R
        if c!='expanded' and c not in meta:meta[c]=dict(index=idx,H=H,h=h,B=B,payload=payload)
        items[c].append(pack(H,h,B,payload))
    assert list(map(len,items.values()))==[197869,14985,22800]
    e=sorted(items['expanded']);w=sorted(items['old-long']+items['cap'])
    assert len({k//R for k in e+w})==len(e)+len(w)
    rootKey=pack(10,(0,9,3,1,0),(0,170,5,1,0),0)//R
    roots=[x for x in e if x//R==rootKey];assert len(roots)==1
    meta['root']=dict(height=10,col_heights=[0,9,3,1,0],black_masks=[0,170,5,1,0],
                      key=rootKey,old_record=roots[0]%R,moves='3332222222224')
    return z,p,layout,e,w,meta

def chunks(lst,n):return [lst[i:i+n] for i in range(0,len(lst),n)]
def window(ws):
    b=(ws[0]//R)*R;a=(1<<max(1,(ws[-1]-b).bit_length()))+1
    z=0
    for w in reversed(ws):z=z*a+w-b
    return f'(.window {len(ws)} {a} {b} 0x{z:x})'
def branch(ws):
    if len(ws)==1:return window(ws[0])
    i=len(ws)//2
    return f'(.branch {ws[i][0]//R} {branch(ws[:i])} {branch(ws[i:])})'
def render(a):
    old,oldpins,layout,e,w,meta=readinputs(a.old,a.raw,a.projection)
    out=a.out
    W=out/'source'/PK
    assert not W.exists(),'refuse to overwrite a staged bank'
    W.mkdir(parents=True)
    gen=[]
    def put(name,body,imports=(),in_ns=True):
        f=W/(name+'.lean')
        if isinstance(body,bytes):f.write_bytes(body)
        else:
            f.write_text(''.join(f'import {x}\n' for x in imports)+'\n'+(HDR if in_ns else '')+
                         body+(END if in_ns else ''),encoding='utf-8')
        gen.append(f'{PK}.{name}')
    put('Layout',layout)
    def defs(keys,noun):
        blocks=chunks(chunks(keys,24),16)
        return [(f'{noun}{i}',block[0][0]//R,f'def {noun}{i} : Bank := '+branch(block))
                for i,block in enumerate(blocks)]
    wdefs=defs(w,'w')
    def wintree(values):
        if len(values)==1:return values[0][0]
        i=len(values)//2
        return f'(.branch {values[i][1]} {wintree(values[:i])} {wintree(values[i:])})'
    put('Witnesses','\n'.join(d[2] for d in wdefs)+'\ndef witnessBank : Bank := '+wintree(wdefs)+'\n',(f'{PK}.Layout',))
    put('Hooks','''def longGate := CapFastTagged.gate fmt witnessBank
theorem longGate_sound : ∀ h p, longGate h p = true → CapTagged.L h p.toBoard :=
  fun h p ok => CapFastTagged.gate_sound fmt witnessBank h p ok
theorem longGate_lift : LeafSound 2 CapTagged.L := CapTagged.leafSound (by decide)
''',('CapFastTagged',f'{PK}.Witnesses'))
    policy=defs(e,'p')
    dnames=[]
    for i,block in enumerate(chunks(policy,24)):
        name=f'D{i}';dnames.append(f'{PK}.{name}')
        put(name,'\n'.join(d[2] for d in block)+'\n',(f'{PK}.Layout',))
    nodes=[];proofs=[]
    def ttree(values):
        if len(values)==1:return values[0][0]
        i=len(values)//2;ln,rn=ttree(values[:i]),ttree(values[i:])
        n=f'n{len(nodes)}'
        nodes.append(f'def {n} : Bank := .branch {values[i][1]} {ln} {rn}')
        proofs.append(f'theorem {n}_ok : {TEST} {n} = true := all_branch {ln}_ok {rn}_ok')
        return n
    t=ttree(policy)
    put('Top','\n'.join(nodes)+f'\ndef t : Bank := {t}\n',(*dnames,f'{PK}.Hooks'))
    knames=[]
    for i,block in enumerate(chunks(policy,3)):
        name=f'K{i}';knames.append(f'{PK}.{name}')
        put(name,'\n'.join(f'theorem {p}_ok : {TEST} {p} = true := by decide +kernel' for p,k,d in block)+'\n',(f'{PK}.Top',))
    old_main=old.read(OLD+PREFIX+'Main.lean')
    assert sha(old_main)==oldpins[PREFIX+'Main.lean']
    # Exact old public theorem declaration/signature/body/comment and printed axioms.
    tail=re.search(r'/-- Original Top family.*?\n#print axioms top_all\n',old_main.decode(),re.S)[0]
    put('Main','\n'.join(proofs)+f'\ntheorem checked : {TEST} t = true := {t}_ok\n'+
       'theorem rootEntry : smem fmt t 10 stopPos = true := by decide +kernel\n\n'+tail,
       ('TopCheckedRoot',*knames))
    def pos(meta):
        return '⟨'+ ','.join(map(str,[*meta['B'],*meta['h']]))+'⟩'
    cap,long=meta['cap'],meta['old-long']
    probe=out/'source'/'STop197869MatchedRootProbe.lean'
    probe.write_text(f'''import {PK}.Top
import TopCheckedRoot

namespace C4W5.STop197869MatchedRootProbe
open Connect4.NarrowBoards C4W5.WindowBank C4W5.{PK}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

-- Probe only: no kernel closure shards or full top_all are imported.
def capPos : Pos := {pos(cap)}
def oldLongPos : Pos := {pos(long)}
theorem originalRootMember : smem fmt t 10 stopPos = true := by decide +kernel
theorem rootNotATag : longGate 10 stopPos = false := by decide +kernel
theorem capHit : longGate {cap['H']} capPos = true := by decide +kernel
theorem legacyLongHit : longGate {long['H']} oldLongPos = true := by decide +kernel
theorem capPolicyNotRetained : smem fmt t {cap['H']} capPos = false := by decide +kernel
theorem capLiftInterface : LeafSound 2 CapTagged.L := longGate_lift
theorem matchedCapLeaf : CapTagged.L {cap['H']} capPos.toBoard := longGate_sound _ _ capHit
#check @top_of_extra_window_bank
#print axioms matchedCapLeaf
#print axioms originalRootMember
end C4W5.STop197869MatchedRootProbe
''',encoding='utf-8')
    generation={'scope':'SOURCE_ONLY: no compiler or kernel proof was run','old_source_sha256':OLD_SHA,
                'decoded_input_sha256':RAW_SHA,'reached_projection_sha256':PROJ_SHA,
                'layout_unchanged_sha256':sha(layout),'top_all_public_slice_sha256':sha(tail.encode()),
                'counts':{'expanded':len(e),'old_long_hints':14985,'cap_hints':22800,'hints':len(w),
                          'groups':len(policy),'K_modules':len(knames),'D_modules':len(dnames),
                          'last_K_rows':len(e)%1152 or 1152},
                'proof_root_groups':t,'matched_positions':meta,'compile_order':gen,
                'probe_after_top':'STop197869MatchedRootProbe',
                'shard_slots':{f'K{i}':min(1152,len(e)-i*1152) for i in range(len(knames))},
                'source_sha256':{str(f.relative_to(out)):sha(f) for f in sorted((out/'source').rglob('*.lean'))}}
    assert generation['counts']['groups']==516 and generation['counts']['K_modules']==172
    (out/'STop197869_GENERATION.json').write_text(json.dumps(generation,indent=2)+'\n')
    print(json.dumps(generation['counts'],indent=2))
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for k in ('old','raw','projection','out'):p.add_argument('--'+k,required=True,type=Path)
    render(p.parse_args())
