#!/usr/bin/env python3
"""Stream the archived original long-pruned SGZ banks into exact fixed-sized records."""
from pathlib import Path
import hashlib,json,struct,sys,zipfile
BASE='C4W5_SGZ5R_LongZO_candidate_banks/even_unbounded_audit/'
REC=struct.Struct('<6QII')
HEAD=struct.Struct('<8sIHH')
BLOCK=struct.Struct('<HHHH')
MHS=(42,60,52,60,60)
CS=tuple((1<<(h+1))-1 for h in MHS)
RR=5**10
EXPECTED_RECEIPT='4c45109cb98d357ec6ec982a66590e5d3236d7fa8024e7aaf898d77e7aaf297c'
EXPECTED_ARCHIVE_SIZE=26_274_842

def run(archive,out):
    assert Path(archive).stat().st_size==EXPECTED_ARCHIVE_SIZE
    with zipfile.ZipFile(archive) as z:
        raw_receipt=z.read(BASE+'sgz5r_LongZO_packed_receipt.json')
        assert hashlib.sha256(raw_receipt).hexdigest()==EXPECTED_RECEIPT
        receipt=json.loads(raw_receipt)
    partial=Path(out).with_suffix(Path(out).suffix+'.partial')
    with zipfile.ZipFile(archive) as z,partial.open('wb') as f:
        for kind,d in enumerate(('expanded','leaves')):
            name=BASE+f'sgz5r_LongZO_{d}_24.bin'; stats=receipt['banks'][d]
            expected=(1455159,229516)[kind]
            raw=hashlib.sha256();words=hashlib.sha256();n=0;wr=0;last=-1
            with z.open(name) as g:
                def take(k):
                    assert k<=3072
                    v=g.read(k);assert len(v)==k
                    raw.update(v);return v
                magic,nt,block,flags=HEAD.unpack(take(HEAD.size))
                assert (magic,nt,block,flags)==(b'C4WSZB01',expected,24,0)
                while n<nt:
                    nb,w,lb,lp=BLOCK.unpack(take(BLOCK.size))
                    assert 0<nb<=24 and n+nb<=nt and 0<w<320 and lb<=40 and lp<=960
                    base=int.from_bytes(take(lb),'little');pack=int.from_bytes(take(lp),'little')
                    assert base%RR==0
                    radix=(1<<w)+1
                    for _ in range(nb):
                        pack,part=divmod(pack,radix)
                        assert part < 1<<w
                        word=base+part
                        words.update(word.to_bytes(40,'little'));k,rep=divmod(word,RR)
                        assert k>last;last=k
                        k,l=divmod(k,243);k,bh=divmod(k,31);H=2*bh
                        assert 0<H<=60
                        bs=[0]*5;hs=[0]*5;ls=[]
                        for j in range(4,-1,-1):
                            k,t=divmod(k,CS[j]);v=t+1;hs[j]=v.bit_length()-1;bs[j]=v-(1<<hs[j])
                        assert k==0
                        shape=H
                        for j in range(5):
                            assert 0<=hs[j]<=min(H,MHS[j]) and 0<=bs[j]<1<<hs[j]
                            shape=(shape<<6)|hs[j]
                        for _ in range(5):l,v=divmod(l,3);ls.append(v)
                        assert l==0 and all(l==0 or h==H for h,l in zip(hs,ls,strict=True))
                        for v in ls:shape=(shape<<2)|v
                        f.write(REC.pack(*bs,shape,rep,kind));n+=1
                    assert not pack;wr+=1
                assert n==nt and not g.read(1)
            assert raw.hexdigest()==stats['file_sha256'] and words.hexdigest()==stats['semantic_row_sha256'] and wr==stats['windows']
            print(d,n,wr,raw.hexdigest(),words.hexdigest(),flush=True)
    assert partial.stat().st_size==94_341_800
    partial.replace(out)
if __name__=='__main__':run(*sys.argv[1:])
