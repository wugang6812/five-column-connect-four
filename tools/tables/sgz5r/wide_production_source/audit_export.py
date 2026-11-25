#!/usr/bin/env python3
"""Read-only wire-to-Lean literals, immutable source and dependency audit.
This does not check game edges or invoke Lean."""
import hashlib,json,re,struct,sys
from pathlib import Path
HEAD=struct.Struct('<8sIHH');BLOCK=struct.Struct('<HHHH')
LIT=re.compile(rb'\(\.window ([0-9]+) ([0-9]+) ([0-9]+) 0x([a-f0-9]+)\)')
RR=5**10

def sha(p):
    with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def old_file_bytes(p,n,windows,digest):
    with p.open('rb') as f:
        assert HEAD.unpack(f.read(HEAD.size))==(b'C4WSZB01',n,24,0)
        seen=0;prev=-1;m=hashlib.sha256()
        for bidx in range(windows):
            k,w,bl,pl=BLOCK.unpack(f.read(BLOCK.size))
            bs=int.from_bytes(f.read(bl),'little');px=int.from_bytes(f.read(pl),'little')
            radix=(1<<w)+1
            assert 0<k<=24 and bs%RR==0 and 0<w<320
            it=px
            for _ in range(k):
                it,val=divmod(it,radix);val+=bs
                assert val//RR>prev
                prev=val//RR;seen+=1
                m.update(val.to_bytes(40,'little'))
            assert not it
            yield k,radix,bs,px
        assert seen==n and f.read(1)==b'' and m.hexdigest()==digest
def check(root):
    r=json.loads((root/'EXPORT_RECEIPT.json').read_text());d=root/'lean';m=d/'SGZLongPacked'
    assert r['status']=='FULL_FIXED_DIGIT_SOURCE_ONLY_NOT_KERNEL_CHECKED'
    assert r['counts']=={'expanded':905511,'old_long':116548,'direct_cap':155994,'total':1178053}
    totals={}
    for pfx,bk,base in [('E','policy','expanded'),('H','tagged_witness','tagged_hints')]:
        info=r['banks'][bk];binfile=root/f'sgz5r_DirectCap_{base}_24.bin'
        assert sha(binfile)==info['sha256']
        it=old_file_bytes(binfile,info['rows'],info['windows'],info['semantic_word_sha256'])
        num=0;groups=0
        for p in sorted(m.glob(pfx+'D*.lean')):
            by=p.read_bytes()
            gs=[int(x) for x in re.findall(rb'\bdef '+pfx.encode()+rb'P([0-9]+) : Bank :=',by)]
            assert gs==list(range(groups,groups+len(gs)))
            groups+=len(gs)
            for mat in LIT.finditer(by):
                assert (int(mat[1]),int(mat[2]),int(mat[3]),int(mat[4],16))==next(it)
                num+=1
        assert next(it,None) is None and num==info['windows']
        assert groups==r['lean']['lookup_groups']['policy' if pfx=='E' else 'witness']
        totals[bk]={'window_literals':num,'lookup_groups':groups}
    order=r['lean']['compile_order_for_future_only']; rep=r['lean']['representative_future_only']['module']
    assert rep not in order and order[-1]=='SGZLongPacked.Main' and len(order)+1==r['lean']['source_modules']
    known={'WindowFast','WindowZoneEnds','CapDoubleMasks','CapTaggedGate'}
    actual={n.relative_to(d).with_suffix('').as_posix().replace('/','.') for n in d.rglob('*.lean')}
    assert actual==set(order)|{rep}
    lint=('sorry','native_decide','ofReduceBool','axiom ')
    for n in [*order,rep]:
        p=d/Path(*n.split('.')).with_suffix('.lean')
        assert sha(p)==r['lean']['sha256'][n] and n not in known
        s=p.read_text()
        assert not any(t in s for t in lint)
        assert all(x in known for x in re.findall(r'^import ([\w.]+)',s,re.M))
        known.add(n)
    main=(m/'Main.lean').read_text();top=(m/'Top.lean').read_text()
    assert 'def terminalGate : ZEndGate := ZoneTagged.gate true fmt hints' in top
    assert 'theorem g5_wide (m b : Nat) (hb : 5 ≤ b) (hbm : b + 3 ≤ m) : Safe (2 * m) (G b)' in main
    assert 'ZoneTagged.g5_wide_of_tagged fmt mainBank hints checked rootEntry m b hb hbm' in main
    assert sum((m/f'K{i:04d}.lean').read_text().count('by decide +kernel') for i in range(r['lean']['K_modules']))==r['lean']['lookup_groups']['policy']
    q=(m/'Representative24.lean').read_bytes()
    rm=list(LIT.finditer(q));assert len(rm)==1
    pi=r['banks']['policy'];f=root/'sgz5r_DirectCap_expanded_24.bin'
    verify=old_file_bytes(f,pi['rows'],pi['windows'],pi['semantic_word_sha256'])
    v=next(x for i,x in enumerate(verify) if i==r['lean']['representative_future_only']['window_index'])
    assert (int(rm[0][1]),int(rm[0][2]),int(rm[0][3]),int(rm[0][4],16))==v
    verify.close()
    print(json.dumps({'status':'FULL_STATIC_SOURCE_WIRE_ROUNDTRIP_PASS_NO_COMPILATION',
        'matched_packed_windows':totals,'modules':len(actual),'future_rep_rows':v[0]},indent=2))
if __name__=='__main__':check(Path(sys.argv[1]))
