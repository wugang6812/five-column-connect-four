#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,shutil,sys,zipfile

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
OUT=HERE/'export'
LIMIT=90*1024**2
OVERALL=13*1024**3
def sha(p):
    with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def close():
    assert shutil.disk_usage(HERE).used<OVERALL and shutil.disk_usage(HERE).free>1024**3
    r=json.loads((OUT/'EXPORT_RECEIPT.json').read_text());j=json.loads((HERE/'static_audit.json').read_text())
    assert r['status']=='FULL_FIXED_DIGIT_SOURCE_ONLY_NOT_KERNEL_CHECKED' and j['status']=='FULL_STATIC_SOURCE_WIRE_ROUNDTRIP_PASS_NO_COMPILATION'
    chosen=sorted([p for p in OUT.rglob('*') if p.is_file()]+
        [HERE/p for p in ('emit_fixed_wide.py','audit_export.py','seal_source.py','DELIVERY.md','export.log','static_audit.json')]+
        [ROOT/'decode_sgz_banks.py',ROOT/'wide_gate_pilot/pick_micro.py',ROOT/'wide_gate_pilot/source/SGZLayout.lean',
           ROOT/'wide_gate_pilot/source/WindowZoneTagged.lean'])
    if sum(p.stat().st_size for p in chosen)>85*1024**2:raise SystemExit('uncompressed preflight exceeds checkpoint ceiling; stop at staged exporter')
    catalog={p.relative_to(ROOT).as_posix():{'bytes':p.stat().st_size,'sha256':sha(p)} for p in chosen}
    mm=HERE/'CHECKPOINT_MANIFEST.json'
    mm.write_text(json.dumps({'status':r['status'],'static_audit':j['status'],'representative_future_only':r['lean']['representative_future_only'],
        'files':catalog},indent=2)+'\n')
    chosen.append(mm)
    a=ROOT/'C4W5_SGZ5R_DirectCap_Wide905511_Full_SOURCE_ONLY_20261121_v1.zip'
    pp=a.with_suffix('.zip.partial')
    with zipfile.ZipFile(pp,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
        for p in sorted(chosen):
            n=p.relative_to(ROOT).as_posix()
            i=zipfile.ZipInfo(n,(2026,11,21,0,0,0));i.external_attr=0o100644<<16
            z.writestr(i,p.read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=6)
            if pp.stat().st_size>LIMIT:raise SystemExit('ZIP ceiling exceeded; stop')
    with zipfile.ZipFile(pp) as z:
        assert z.testzip() is None and len(chosen)==len(z.namelist())
        for p,v in catalog.items():
            with z.open(p) as f:
                if hashlib.file_digest(f,'sha256').hexdigest()!=v['sha256']:raise ValueError(p)
    assert shutil.disk_usage(HERE).used<OVERALL
    pp.replace(a)
    print(a,a.stat().st_size,sha(a),len(chosen),'manifest',sha(mm))
if __name__=='__main__':close()
