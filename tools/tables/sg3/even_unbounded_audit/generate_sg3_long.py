"""Generate forward-pruned SG3 from exact rows and explicit LongThreat witnesses."""
import argparse,json,hashlib
from pathlib import Path
P=Path(__file__).resolve().parent
TOP=P/'sg3_long_source'
W=TOP/'SG3LongPacked'
ROWS=P/'sg3_long_expanded.txt'
LEAVES=P/'sg3_long_leaves.txt'
ORIGINAL=P/'sg3_original_rows.txt'
RR=5**10
NROWS=105869
MAXBLOCK=24
SHORT=16                 # rows per by-decide group <= 384
SHARD=3*SHORT            # kernel module groups 3 decidable checks
DATADIV=24               # data module groups 24 decidable checks

def height_tree(l,r):
    if l==r:return str(l)
    m=(l+r+1)//2
    return f'(if x < {1<<m} then {height_tree(l,m-1)} else {height_tree(m,r)})'

def layout(maxh,kr,cb):
    s=f'def colHeight (x : Nat) : Nat := {height_tree(0,maxh)}\n'
    s+='''def withColumn {α : Sort _} (v : Nat) (f : Nat → Nat → α) : α :=
  force (v+1) fun x => force (colHeight x) fun h => f (x - 2^h) h
'''
    s+=f'def packedPos (w : Nat) : Pos :=\n  force (w / {RR} / {kr}) fun k4 =>\n'
    for i in range(4,0,-1):s+=f'  force (k{i} / {cb[i]}) fun k{i-1} =>\n'
    for i in range(5):s+=f'  withColumn '+('(k'+str(i)+f' % {cb[i]})' if i else 'k0')+f' fun b{i} h{i} =>\n'
    s+='  ⟨b0,b1,b2,b3,b4,h0,h1,h2,h3,h4⟩\n'
    s+='def cw (p : Pos) (c : Nat) : Nat := 2 ^ (p.ht c) - 1 + p.bm c\n'
    x='cw p 0'
    for i in range(1,5):x=f'({x} * {cb[i]} + cw p {i})'
    s+=f'def packedKey (k : Nat) (p : Pos) : Nat := {x} * {kr} + k/2\n'
    s+=f'def fmt : SFormat := ⟨1,{RR},packedKey,(fun w => 2*(w / {RR} % {kr})),packedPos⟩\n'
    return s
def make(reference=False):
    rows=[tuple(map(int,l.split())) for l in ROWS.open()]
    assert len(rows)==NROWS
    leaves=[tuple(map(int,l.split())) for l in LEAVES.open()]
    assert len(leaves)==20457 and all(len(x)==17 for x in leaves)
    orig=set(tuple(map(int,l.split())) for l in ORIGINAL.open())
    assert len(orig)==432550 and all(r in orig for r in rows) and all(l[:12] in orig for l in leaves)
    assert len({x[:11] for x in rows+leaves})==len(rows)+len(leaves)
    kh=max(t[0] for t in orig)
    cs=[max(t[6+j] for t in orig) for j in range(5)]
    cr=[(1<<(v+1))-1 for v in cs];kr=kh//2+1
    def pack(t):
        h=t[0];assert h%2==0 and h<=kh and len(t)==12 and 0<=t[11]<RR
        q=0
        for j,c in enumerate(cr):
            b=t[1+j];y=t[6+j]
            assert 0<=y<=h and b<1<<y
            q=q*c+((1<<y)-1+b)
        return (q*kr+h//2)*RR+t[11]
    encoded=sorted(map(pack,rows))
    assert all(x//RR<y//RR for x,y in zip(encoded,encoded[1:]))
    assert any(x//RR==pack((14,0,106,5,0,0,0,7,3,1,0,0))//RR for x in encoded)
    witness=[]
    for t in leaves:
        c,rho,mask,d,i=t[12:]
        assert 0<=c<5 and 0<=rho<=60 and 0<=mask<32 and 0<=d<3 and 0<=i<4
        payload=c+5*(rho+61*(mask+32*(d+3*i)))
        witness.append(pack((*t[:11],payload)))
    witness.sort()
    assert all(a//RR<b//RR for a,b in zip(witness,witness[1:]))
    W.mkdir(parents=True,exist_ok=True)
    data=[];check=[];others=[];decls=[];merges=[];groups=0
    allwoods=[]
    openhdr='''namespace C4W5.SG3LongPacked
open Connect4 (Player opponent)
open Connect4.NarrowBoards C4W5.WindowBank
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
'''
    def write(name,s):
        (W/(name+'.lean')).write_text(s)
        return 'SG3LongPacked.'+name
    tail='\nend C4W5.SG3LongPacked\n'
    others.append(write('Layout','import WindowStretch\n\n'+openhdr+layout(kh,kr,cr)+tail))
    def window(ws):
        b=ws[0]//RR*RR;a=(1<<max(1,(ws[-1]-b).bit_length()))+1
        z=0
        for w in reversed(ws):z=z*a+w-b
        yz=z
        for w in ws:
            yz,w0=divmod(yz,a);assert w0+b==w
        assert yz==0
        return f'(.window {len(ws)} {a} {b} 0x{z:x})'
    def branch(ls):
        if len(ls)==1:return window(ls[0])
        i=len(ls)//2
        return f'(.branch {ls[i][0]//RR} {branch(ls[:i])} {branch(ls[i:])})'
    wb=[witness[i:i+MAXBLOCK] for i in range(0,len(witness),MAXBLOCK)]
    names=[];witness_decls=[]
    for i in range(0,len(wb),SHORT):
        n=f'w{i//SHORT}'
        names.append((n,wb[i][0]//RR))
        witness_decls.append(f'def {n} : Bank := {branch(wb[i:i+SHORT])}')
    def link_wits(ls):
        if len(ls)==1:return ls[0][0]
        i=len(ls)//2;a,b=link_wits(ls[:i]),link_wits(ls[i:])
        return f'(.branch {ls[i][1]} {a} {b})'
    others.append(write('Witnesses','import SG3LongPacked.Layout\n\n'+openhdr+'\n'.join(witness_decls)+f'\ndef witnessBank : Bank := {link_wits(names)}\n'+tail))
    gm=('WindowLongGate' if reference else 'WindowLongGateFast')
    g=('referenceGate' if reference else 'fastGate')
    others.append(write('Hooks',f'import {gm}\nimport SG3LongPacked.Witnesses\n\n'+openhdr+
        f'def longGate := {g} fmt witnessBank\n'
        f'theorem longGate_sound : ∀ h p, longGate h p = true → LongThreat.L h p.toBoard := {g}_sound fmt witnessBank\n'
        'theorem longGate_lift : LeafSound 2 LongThreat.L := LongThreat.leafSound (by decide)\n'+tail))
    ls=[encoded[i:i+MAXBLOCK] for i in range(0,len(encoded),MAXBLOCK)]
    for i in range(0,len(ls),SHORT):
        z=ls[i:i+SHORT];g=len(allwoods)
        allwoods.append((f'p{g}',z[0][0]//RR))
        decls.append(f'def p{g} : Bank := {branch(z)}')
    for k in range(0,len(decls),DATADIV):
        data.append(write('D'+str(len(data)), 'import SG3LongPacked.Layout\n\n'+openhdr+'\n'.join(decls[k:k+DATADIV])+tail))
    tree=[]
    def link(ls):
        if len(ls)==1:return ls[0][0]
        i=len(ls)//2;a,b=link(ls[:i]),link(ls[i:])
        nm=f'n{len(tree)}';tree.append(f'def {nm} : Bank := .branch {ls[i][1]} {a} {b}')
        merges.append(f'theorem {nm}_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) {nm} = true := all_branch {a}_ok {b}_ok')
        return nm
    root=link(allwoods)
    others.append(write('Top',''.join(f'import {m}\n' for m in data)+'import SG3LongPacked.Hooks\n\n'+openhdr+'\n'.join(tree)+f'\ndef t : Bank := {root}\n'+tail))
    thms=[f'theorem {n}_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) {n} = true := by decide +kernel' for n,_ in allwoods]
    for i in range(0,len(thms),SHARD//SHORT):
        check.append(write('K'+str(len(check)),'import SG3LongPacked.Top\n\n'+openhdr+'\n'.join(thms[i:i+SHARD//SHORT])+tail))
    root_proof=f'''
theorem checked : all fmt.radix (scheckExtraRow 2 fmt t longGate) t = true := {root}_ok
theorem rootEntry : smem fmt t 14 g3p = true := by decide +kernel

/-- Original G(3) family, every even H >= 14. -/
theorem g3_all (m : Nat) (hm : 7 ≤ m) : Safe (2*m) (G 3) :=
  g3_of_extra_window_bank fmt t longGate longGate_sound longGate_lift checked rootEntry m hm
#print axioms g3_all
'''
    fin=write('Main','import SG3CheckedRoot\n'+''.join(f'import {m}\n' for m in check)+'\n'+openhdr+'\n'.join(merges)+root_proof+tail)
    seq=[*others[:3],*data,others[3],*check,fin]
    receipt=dict(all_rows=NROWS,tail_rows=len(witness),checker=('reference' if reference else 'bits'),height_max=kh,col_max=cs,windows=len(ls),decidable_groups=len(allwoods),
                 data_modules=len(data),kernel_modules=len(check),orig_rows_sha256=hashlib.file_digest(ROWS.open('rb'),'sha256').hexdigest(),
                 total_source_bytes=sum((TOP/(m.replace('.','/')+'.lean')).stat().st_size for m in seq),
                 compile_order=seq,gen_dir=str(TOP))
    (P/'sg3_long_generation.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print({k:v for k,v in receipt.items() if k!='compile_order'})
if __name__=='__main__':
    args=argparse.ArgumentParser();args.add_argument('--reference',action='store_true');make(args.parse_args().reference)
