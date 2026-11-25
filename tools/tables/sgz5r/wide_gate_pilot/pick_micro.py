#!/usr/bin/env python3
"""Extract exactly 96 actual candidate parent rows and their one-step query
neighborhood. Copies no unbounded bank, walks no full closure, compiles nothing."""
import hashlib,json,mmap,random,struct
from array import array
from pathlib import Path

HERE=Path(__file__).resolve().parent
B=HERE.parent/'fixed_measure_work'
FLAT=B/'original_rows56.bin'; PICK=B/'selection.txt'; OUT=HERE/'source'
EXP=1455159; NL=229516; NT=EXP+NL; RR=5**10
SHAS={FLAT:'565f6bf1ddd9b84b90a2a76d804b6f615c02797fcffe8fa0b007873f317b781e',
 PICK:'e59a0f31582745007dcc8367b12267123cfe4ac734e4a41bf780087dbf7b30e1'}
RAD=tuple((1<<(h+1))-1 for h in (42,60,52,60,60))
REC=struct.Struct('<6QII')
ROOT=(14,(0,1706,5,0,0),(0,11,3,1,0),(0,0,0,0,0))
def low(h):return (1<<h)-1
def unpack(a,i):
    *bs,sh,rep,t=REC.unpack_from(a,i*56)
    h=tuple((sh>>(10+6*(4-c)))&63 for c in range(5))
    l=tuple((sh>>(2*(4-c)))&3 for c in range(5))
    return (sh>>40,tuple(bs),h,l),rep,t
def key(q):
    k,bs,h,l=q;v=0
    for b,t,r in zip(bs,h,RAD):v=v*r+low(t)+b
    return (v*31+k//2)*243+sum(c*3**i for i,c in enumerate(l))
def getidx(a,q):
    s=key(q)
    for ll,rr in [(0,EXP),(EXP,NT)]:
        lo,hi=ll,rr
        while lo<hi:
            md=(lo+hi)//2
            if key(unpack(a,md)[0])<s:lo=md+1
            else:hi=md
        if lo<rr and unpack(a,lo)[0]==q:return lo
    return None
def change(q,c,l):
    k,bs,h,ll=q;return k,bs,h,ll[:c]+(l,)+ll[c+1:]
def push(q,c,black):
    k,bs,h,l=q;v=h[c]
    return k,bs[:c]+(bs[c]|(black<<v),)+bs[c+1:],h[:c]+(v+1,)+h[c+1:],l
def lm(q):
    k,bs,h,l=q;m=1|(1<<k)
    for b,t in zip(bs,h):
        m|=1<<t
        if t:m|=(low(t-1)^((b^(b>>1))&low(t-1)))<<1
    return m
def clear(k,m,r):return 2<r<=k and (m>>(r-2))&31==0
def stretch(q,r):
    k,bs,h,l=q
    return k,tuple((b&low(r))|((b>>r&1)<<r)|((b>>(r-1)&1)<<(r+1))|((b>>r)<<(r+2)) if r<t else b for b,t in zip(bs,h)),tuple(t+2 if r<t else t for t in h),l
def norm(q,c):
    k,bs,h,l=q
    if h[c]<6 or k<2:return q
    r=h[c]-5
    z=(k-2,tuple((b&low(r))|((b>>(r+2))<<r) if r+2<t else b for b,t in zip(bs,h)),tuple(t-2 if r+2<t else t for t in h),l)
    if any(t>k-2 or b>>t for b,t in zip(z[1],z[2])):return q
    return z if clear(k-2,lm(z),r) and stretch(z,r)[1:3]==q[1:3] else q
def variants(q,c,b):
    k,mask,h,l=q;m=lm(q);x=h[c]+3
    yield push(q,c,b)
    if clear(k,m,x) and not clear(k,m,x+1):
        _,bb,hh,ll=stretch(q,x)
        yield push((k+2,bb,hh,ll),c,b)
def four(q,black):
    _,bs,h,_=q
    m=bs if black else tuple(low(t)^b for b,t in zip(bs,h))
    if any(x&(x>>1)&(x>>2)&(x>>3) for x in m):return True
    for i in range(2):
        a,b,c,d=m[i:i+4]
        if a&b&c&d or a&(b>>1)&(c>>2)&(d>>3) or (a>>3)&(b>>2)&(c>>1)&d:return True
    return False
def claim(q):
    k,b,h,l=q
    for c,t in enumerate(h):
        assert 0<=t<=k and b[c]<1<<t
        if t<k and t>=3 and (b[c]>>(t-3))&7==0:return False
    def dead(c,r,tar,t):
        for d in (-1,0,1):
            for i in range(4):
                for j in range(4):
                    x=c+j-i;y=r+(j-i)*d
                    if not(0<=x<5 and 0<=y<k):break
                    if (b[x]>>y)&1 or (x==tar and y>t and (y-t)%2):break
                else:return False
        return True
    ex=[]
    for c,t in enumerate(h):
        for r in range(min(k,t+1)):
            if (r==t or not(b[c]>>r&1)) and (r==0 or not(b[c]>>(r-1)&1)):ex.append((c,r))
    return any((k-t)%2 and all(dead(c,r,u,t) for c,r in ex) for u,t in enumerate(h))
def one(q,rep):
    k,b,h,l=q;qs=[]; white=black=wl=bl=cap=od=awin=0
    def reply(pr,c,e,must):
        nonlocal black,bl,awin
        pK,pb,ph,pl=pr
        if pl[e]==0 and ph[e]<pK:
            for j,v in enumerate(variants(pr,e,1)):
                black+=1;bl+=j
                if four(v,1):awin+=1;continue
                assert c==e or not must
                qs.append(norm(v,e))
        else:
            assert c==e or not must
            assert (pl[e]==0 and ph[e]==pK) or pl[e]==1
            qs.append(change(pr,e,pl[e]+1))
    for c in range(5):
        d,rep=rep%25,rep//25
        if l[c]==0 and h[c]<k:
            for j,v in enumerate(variants(q,c,0)):
                assert not four(v,0)
                white+=1;wl+=j;reply(norm(v,c),c,d//5 if j else d%5,h[c]+5>k)
        elif l[c]==0:
            cap+=1;qs.append(change(q,c,2))
        elif l[c]==1:
            od+=1;u=change(q,c,2)
            if not all(x==2 for x in u[3]):reply(u,c,d%5,False)
    return qs,dict(white=white,black=black,whiteStretch=wl,blackStretch=bl,forcedCap=cap,oddCap=od,immediateWin=awin)
def mask(q,t,s):
    h=q[2];return sum(1<<c for c in range(5) if c not in (t,s) and h[c]<q[0] and h[c]%2==0)
def code_cap(q,vals):
    t,s,a,b,m,da,db,ia,ib=vals
    assert 0<=t<5 and 0<=s<5 and 0<=da<3 and 0<=db<3 and 0<=ia<4 and 0<=ib<4
    assert a%2==1 and b%2==0 and 0<=a//2<32 and 0<=b//2<32
    assert all(l==0 or h==q[0] for h,l in zip(q[2],q[3])) and m==mask(q,t,s)
    x=t+5*(s+5*(a//2+32*(b//2+32*(da+3*(db+3*(ia+4*ib))))))
    assert 0<=x<3686400
    return 117120+x
def bank(rows):
    rows=sorted(rows); windows=[]
    assert rows and len({x//RR for x in rows})==len(rows)
    for i in range(0,len(rows),24):
        z=rows[i:i+24];bias=z[0]//RR*RR;r=(1<<(z[-1]-bias).bit_length())+1
        p=0
        for w in reversed(z):p=p*r+w-bias
        v=p
        for w in z:
            v,d=divmod(v,r);assert bias+d==w
        assert not v
        windows.append((z[0]//RR,f'(.window {len(z)} {r} {bias} 0x{p:x})'))
    def tree(xs):
        if len(xs)==1:return xs[0][1]
        m=len(xs)//2
        return f'(.branch {xs[m][0]} {tree(xs[:m])} {tree(xs[m:])})'
    return tree(windows)
def ident(q):
    k,w,h,l=q
    return f'{k} ⟨'+','.join(map(str,w+h))+'⟩ ⟨'+','.join(map(str,l))+'⟩'
def mutate(q):
    k,b,h,l=q
    for c in range(5):
        if h[c]==k:return (k,b,h,l[:c]+((l[c]+1)%3,)+l[c+1:])
    raise ValueError('use cap probe with saturated label')
def take(a,fd):
    offsets=array('I',[0])*NT;kind=bytearray(NT)
    while True:
        where=fd.tell();raw=fd.readline()
        if not raw:break
        tag,id,*_=raw.split(None,2);i=int(id)
        assert not kind[i]
        kind[i]=tag[0];offsets[i]=where
    def choice(i):
        fd.seek(offsets[i]);t,j,r,*ws=fd.readline().split();assert int(j)==i and ord(t)==kind[i]
        return t,int(r),list(map(int,ws))
    def decode_q(q):
        i=getidx(a,q)
        if i is None:
            assert claim(q),q
            return i,0,None
        assert kind[i], (q,i)
        tag,r,ws=choice(i)
        return i,tag,r if tag!=b'C' else code_cap(q,ws)
    # Focused 4x24, not a full graph traversal. Select deterministic native P
    # rows across several cutoff and label strata, including the exact root.
    seed=random.Random(20261121)
    picked={g:[] for g in ('cap_low','cap_labelled','long_no_cap','ordinary')}
    cutsets={g:set() for g in picked}
    id0=getidx(a,ROOT)
    order=[id0,*seed.sample(range(EXP),8192)]
    parent={};pol={};hints={};checks={}
    seen=set()
    for i in order:
        if i in seen or kind[i]!=ord('P'):continue
        seen.add(i)
        q,rep,t=unpack(a,i);assert not t
        outs,meta=one(q,rep)
        ys=[(u,*decode_q(u)) for u in outs]
        typ={t for _,_,t,_ in ys}
        group='cap_'+('labelled' if any(q[3]) else 'low') if b'C' in typ else 'long_no_cap' if b'L' in typ else 'ordinary'
        if len(picked[group])>=24:continue
        # Reserve early slots for varied cutoff and at least a few stretched
        # comparisons; remaining slots fill deterministically.
        if i!=id0 and len(picked[group])<6 and q[0] in cutsets[group]:continue
        cutsets[group].add(q[0])
        picked[group].append(i);checks[i]=rep
        pol[i]=rep
        for u,j,t,r in ys:
            if t==b'P':pol[j]=r
            elif t in (b'C',b'L'):hints[j]=r
        parent[i]={'row':q,'rep':rep,'edges':[{**dict(index=j,tag=t.decode() if t else 'Claim',state=u)} for u,j,t,r in ys],
            'move_observations':meta,'group':group}
        if all(len(v)==24 for v in picked.values()):break
    assert len(checks)==96 and id0 in checks, (id0,picked)
    def words(d):
        return [key(unpack(a,i)[0])*RR+r for i,r in d.items()]
    ns='C4W5.WideGatePilot'
    head=f'''import WindowZoneTagged
import SGZLayout

namespace {ns}
open Connect4.NarrowBoards C4W5.WindowBank C4W5.CompactSGZ
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
'''
    tail=f'\nend {ns}\n'
    common=head+f'''/- One-step measurement banks. Not a complete policy certificate. -/
def checkRows : Bank := {bank(words(checks))}
def policyNeighbors : Bank := {bank(words(pol))}
def terminalNeighbors : Bank := {bank(words(hints))}
def matched (postOnly : Bool) : Bool :=
  all fmt.radix (zoneEndsRow 2 fmt policyNeighbors (ZoneTagged.gate postOnly fmt terminalNeighbors)) checkRows
'''+tail
    (OUT/'Wide96Data.lean').write_text(common)
    for name,val in [('Dual','false'),('Post','true')]:
        (OUT/f'Wide96{name}.lean').write_text(f'''import Wide96Data

namespace {ns}
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem checkMatched{name} : matched {val} = true := by decide +kernel
#print axioms checkMatched{name}
end {ns}
''')
    cap_id=next(j for j in sorted(hints) if kind[j]==ord('C') and any(unpack(a,j)[0][3]))
    long_id=next(j for j in sorted(hints) if kind[j]==ord('L'))
    q=unpack(a,cap_id)[0];v=unpack(a,long_id)[0]; bad=mutate(q);assert bad!=v and key(bad)!=key(q)
    micro=head+f'''private def tiny : Bank := {bank(words({j:hints[j] for j in (cap_id,long_id)}))}
theorem actualCapDual : ZoneTagged.gate false fmt tiny {ident(q)} = true := by decide +kernel
theorem actualCapPost : ZoneTagged.gate true fmt tiny {ident(q)} = true := by decide +kernel
theorem actualLong : ZoneTagged.gate true fmt tiny {ident(v)} = true := by decide +kernel
theorem wrongLabelMiss : ZoneTagged.gate true fmt tiny {ident(bad)} = false := by decide +kernel
private def collide : SZFormat := {{ fmt with key := fun _ _ _ => fmt.key {ident(q)} }}
theorem wrongLabelOnForcedCollision : ZoneTagged.gate true collide tiny {ident(bad)} = false := by decide +kernel
theorem actualCapChecked : ZoneEnds.SZ.Extra {q[0]} (show Pos from ⟨{','.join(map(str,q[1]+q[2]))}⟩).toBoard :=
  ZoneTagged.gate_sound true fmt tiny {ident(q)} actualCapPost
#print axioms actualCapDual
#print axioms actualCapPost
#print axioms actualLong
#print axioms wrongLabelMiss
#print axioms wrongLabelOnForcedCollision
#print axioms actualCapChecked
'''+tail
    (OUT/'WideGateFixture.lean').write_text(micro)
    metrics={
        'groups':picked,'cutoffs_by_group':{g:sorted(v) for g,v in cutsets.items()},
        'candidate_parents_inspected':len(seen),'policy_neighbors':len(pol),'terminal_neighbors':len(hints),
        'cap_neighbors':sum(kind[i]==ord('C') for i in hints),
        'long_neighbors':sum(kind[i]==ord('L') for i in hints),
        'root_index':id0,'micro':{'Cap_ID':cap_id,'Long_ID':long_id},
        'moves':{k:sum(v['move_observations'][k] for v in parent.values()) for k in meta},
        'external_claim_occurrences':sum(x['tag']=='Claim' for y in parent.values() for x in y['edges']),
        'parent_count':len(checks)}
    (HERE/'matched96_receipt.json').write_text(json.dumps({'scope':'source-only selected one-step fixtures; no Lean and no full graph',**metrics,'parents':parent,'lookup_policy':pol,'lookup_terminals':hints},indent=2)+'\n')
    print(json.dumps(metrics,sort_keys=True))
if __name__=='__main__':
    for p,h in SHAS.items():
        with p.open('rb') as q:assert hashlib.file_digest(q,'sha256').hexdigest()==h
    with FLAT.open('rb') as f,mmap.mmap(f.fileno(),0,access=mmap.ACCESS_READ) as a,PICK.open('rb') as g:
        take(a,g)
