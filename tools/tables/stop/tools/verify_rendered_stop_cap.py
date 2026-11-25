"""Independent parsing/round-trip structural audit, never invokes Lean."""
import argparse,collections,hashlib,json,re,struct,zipfile
from pathlib import Path
def sha(b):return hashlib.sha256(b).hexdigest()
def j(p):return json.loads(p.read_text())
def verify(root,raw,projection,old_zip):
    g=j(root/'STop197869_GENERATION.json');S=root/'source/STopLongPacked'
    for n,h in g['source_sha256'].items():assert sha((root/n).read_bytes())==h,n
    raw=raw.read_bytes(); assert sha(raw)==g['decoded_input_sha256']
    proj=projection.read_bytes(); assert sha(proj)==g['reached_projection_sha256']
    expected={}
    for line in proj.splitlines():
        c,i,*xs=line.split();i=int(i)
        h, *v=struct.unpack_from('<B5B5QIB',raw,51*i)
        heights=tuple(v[:5]);b=tuple(v[5:10]); rep,z=v[10:]
        if c==b'expanded': typ=0; assert not z and not xs
        elif c==b'old-long': typ=1; assert z and len(xs)==1 and int(xs[0])==rep
        else:typ=2; assert c==b'cap' and not z and len(xs)==1;rep=int(xs[0])
        val=(h,heights,b)
        assert val not in expected;expected[val]=(typ,rep)
    with zipfile.ZipFile(old_zip) as z:
        p='C4W5_STop_compact_source_stage/stop_long_source/STopLongPacked/'
        assert z.read(p+'Layout.lean')==(S/'Layout.lean').read_bytes()
        o=z.read(p+'Main.lean')
    pub=re.compile(rb'/-- Original Top family.*?\n#print axioms top_all\n',re.S)
    m=(S/'Main.lean').read_bytes()
    assert pub.search(o)[0]==pub.search(m)[0]
    assert sha(pub.search(m)[0])==g['top_all_public_slice_sha256']
    def decode(w):
        # Direct mixed radix projection; no renderer encoder imported.
        x,h=divmod(w//9765625,27)
        vals=[]
        for k in (35184372088831,35184372088831,8796093022207,9007199254740991):
            vals.append(x%k);x//=k
        vals.append(x)
        hs=[];bs=[]
        for q in reversed(vals):
            h0=(q+1).bit_length()-1;hs.append(h0);bs.append(q+1-(1<<h0))
        return (2*h,tuple(hs),tuple(bs)),w%9765625
    allowed={0:0,1:0,2:0}
    groups={}
    atom=re.compile(r'\(|\)|\.[a-z]+|0x[0-9a-f]+|[0-9]+')
    def datatree(x,policy):
        ts=iter(atom.findall(x))
        def node():
            assert next(ts)=='('
            constructor=next(ts)
            if constructor=='.window':
                n=int(next(ts));a=int(next(ts));base=int(next(ts));z=int(next(ts),16)
                assert 0<n<=24 and a>1 and base%9765625==0
                out=[]
                for j in range(n):
                    w=base+z%a;z//=a
                    val,pay=decode(w)
                    typ,y=expected.pop(val)
                    assert y==pay and (typ==0)==policy
                    if typ==1: assert pay<117120
                    if typ==2: assert 117120<=pay<3803520
                    allowed[typ]+=1;out.append(w//9765625)
                assert z==0 and all(i<j for i,j in zip(out,out[1:]))
            else:
                assert constructor=='.branch'
                cut=int(next(ts));left=node();right=node()
                assert left[-1]<cut==right[0]
                out=left+right
            assert next(ts)==')'
            return out
        result=node(); assert next(ts,None) is None
        return result
    # Independent parser puts declared groups into source order.
    for i in range(22):
        for u,b in re.findall(r'^def (p\d+) : Bank := (.+)$',(S/f'D{i}.lean').read_text(),re.M):
            assert u==f'p{len(groups)}';groups[u]=datatree(b,True)
    assert len(groups)==516
    hints={}
    wt=(S/'Witnesses.lean').read_text()
    for u,b in re.findall(r'^def (w\d+) : Bank := (.+)$',wt,re.M):
        assert u==f'w{len(hints)}';hints[u]=datatree(b,False)
    assert not expected and list(allowed.values())==[197869,14985,22800]
    tree_definition=re.search(r'^def witnessBank : Bank := (.+)$',wt,re.M)[1]
    toks=iter(re.findall(r'\(|\)|\.branch|w\d+|\d+',tree_definition))
    def fold():
        a=next(toks)
        if a!='(':return hints.pop(a)
        assert next(toks)=='.branch'
        cut=int(next(toks));f=fold();g=fold()
        assert f[-1]<cut==g[0] and next(toks)==')'
        return f+g
    hintskey=fold();assert len(hintskey)==37785 and next(toks,None) is None and not hints
    top=(S/'Top.lean').read_text(); ordered=[]
    for n,c,a,b in re.findall(r'^def (n\d+) : Bank := \.branch (\d+) (\w+) (\w+)$',top,re.M):
        f=groups.pop(a);g0=groups.pop(b)
        assert f[-1]<int(c)==g0[0]
        groups[n]=f+g0;ordered.append((n,a,b))
    assert len(groups)==1
    t=re.search(r'^def t : Bank := (\w+)$',top,re.M)[1]
    livekeys=groups[t];root_key=g['matched_positions']['root']['key']
    assert len(livekeys)==197869 and livekeys.count(root_key)==1 and root_key not in hintskey
    theorem_rx=rb'^theorem (n\d+)_ok : .+ := all_branch (\w+)_ok (\w+)_ok$'
    assert ordered==[tuple(x.decode() for x in v) for v in re.findall(theorem_rx,m,re.M)]
    assert re.search(rb'^theorem checked : .+ := '+t.encode()+rb'_ok$',m,re.M)
    allrefs=[]
    for i in range(172):
        p=(S/f'K{i}.lean').read_text()
        assert p.splitlines()[0]=='import STopLongPacked.Top'
        allrefs+=re.findall(r'^theorem (p\d+)_ok .* := by decide \+kernel$',p,re.M)
    assert allrefs==[f'p{i}' for i in range(516)]
    assert re.findall(rb'^import STopLongPacked.K(\d+)$',m,re.M)==[str(i).encode() for i in range(172)]
    readout={'status':'SOURCE_ROUNDTRIP_AND_STRUCTURE_VERIFIED_NO_LEAN',
             'all_projected_records_exact':sum(allowed.values()),'policy_and_witness_keys_disjoint':True,
             'kept_policy_rows':allowed[0],'witness_payload_counts':{'long':allowed[1],'cap':allowed[2]},
             'layout_identical':True,'public_top_all_identical':True,
             'window_cuts_verified':True,'closure_groups_covered_exactly_once':len(allrefs),
             'kernel_source_files':172,'original_root_in_live_not_witness':True}
    (root/'STop197869_RENDER_AUDIT.json').write_text(json.dumps(readout,indent=2)+'\n')
    print(json.dumps(readout,indent=2))
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for s in ('root','raw','projection','old-zip'):p.add_argument(s,type=Path)
    x=p.parse_args()
    verify(x.root,x.raw,x.projection,getattr(x,'old-zip'))
