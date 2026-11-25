#!/usr/bin/env python3
"""Build a source-only support capsule from the exact independently accepted archives."""
import argparse,hashlib,json,re,zipfile
from pathlib import Path
def sha(b):
    if isinstance(b,bytes):return hashlib.sha256(b).hexdigest()
    with Path(b).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def read(z,n):return json.loads(z.read(n))
def pin(p):
    p.out.mkdir(exist_ok=True)
    dep=p.out/'foundation';root=dep/'source';root.mkdir(parents=True,exist_ok=False)
    rec=dep/'receipts';rec.mkdir()
    files={}
    def place(name,blob,zip_name,original):
        q=root/name;q.parent.mkdir(exist_ok=True,parents=True);q.write_bytes(blob)
        files[name]={'archive':zip_name,'entry':original,'sha256':sha(blob)}
    def cover(archive,z,entry,dst,sha_required):
        raw=z.read(entry);assert sha(raw)==sha_required,(archive.name,entry)
        place(dst,raw,archive.name,entry)
    AZ={k:zipfile.ZipFile(getattr(p,k)) for k in ('old','pilot','cap','tagged','fast','original')}
    old=AZ['old'];prefix='C4W5_STop_compact_source_stage/'
    old_input=read(old,prefix+'INPUTS.json')
    for n,h in old_input['included_lean_support'].items():cover(p.old,old,prefix+n,n,h)
    old_bridge=old.read(prefix+'bridge_receipt.json')
    assert json.loads(old_bridge)['source_sha256']==files['TopCheckedRoot.lean']['sha256']
    (rec/'old_top_bridge_receipt.json').write_bytes(old_bridge)
    (rec/'old_stop_input_manifest.json').write_bytes(old.read(prefix+'INPUTS.json'))
    (rec/'old_stop_pilot_receipt.json').write_bytes(AZ['pilot'].read('stop_long_build_logs/receipt.json'))

    cap_receipt=AZ['cap'].read('cap_validation/receipt.json')
    (rec/'accepted_cap_transfer_receipt.json').write_bytes(cap_receipt)
    cs=json.loads(cap_receipt);assert cs['status']=='ALL_7_CAP_SOURCES_ACCEPTED'
    for n in ('CapTransferArithmetic','CapTransferDefs','CapTransferBoard','CapTransferRebase',
              'CapTransferStretch','CapTransferCheck'):
        x=cs['accepted'][n];assert x['status']=='PASS' and x['returncode']==0
        cover(p.cap,AZ['cap'],f'cap_working/{n}.lean',f'{n}.lean',x['source_sha256'])
    man=p.baseline.read_bytes();base_sha=sha(man)
    assert base_sha==cs['basis_manifest_sha256']=='4f61a79206cfa9a5692fcc3f848128d0eced92264d40b928db461f1f0399ed2b'
    (dep/'previous_verified_foundation_manifest.json').write_bytes(man)
    for label,status,pref,names in [
         ('tagged','TAGGED_PILOT_ACCEPTED','cap_tagged_pilot',('CapTaggedGate',)),
         ('fast','CAP_MASK_PROOF_ACCEPTED','cap_fast_pilot',('CapDoubleMasks','CapFastTagged'))]:
        z=AZ[label];entry=pref+'/actual/receipt.json';rr=z.read(entry);x=json.loads(rr)
        assert x['status']==status and x['base_manifest_sha256']==base_sha and x['cap_receipt_sha256']==sha(cap_receipt)
        (rec/f'accepted_{label}_receipt.json').write_bytes(rr)
        for n in names:
            reviewer=x['accepted'][n];assert reviewer['status']=='PASS'
            cover(getattr(p,label),z,f'{pref}/source/{n}.lean',f'{n}.lean',reviewer['source_sha256'])

    original=AZ['original'];basis='sgz_cap_transfer_direct_kernel/pinned_original_source/'
    for n in original.namelist():
        if n.startswith(basis) and n.endswith('.lean'):
            path=n[len(basis):];raw=original.read(n)
            if path in old_input['baseline_files']:
                assert sha(raw)==old_input['baseline_files'][path],path
            place(path,raw,p.original.name,n)
    for rel in ('lake-manifest.json','RECOVERY.json'):
        raw=original.read(basis+rel)
        if rel in old_input['baseline_files']:assert sha(raw)==old_input['baseline_files'][rel]
        (dep/rel).write_bytes(raw)
    # Record module order/closed source graph, with exact external missing dependencies.
    seen={};order=[];visiting=set();missing=set()
    known={Path(x).as_posix()[:-5].replace('/','.'):x for x in files}
    def visit(m):
        if m in seen:return
        if m not in known:missing.add(m);return
        assert m not in visiting
        visiting.add(m)
        src=(root/known[m]).read_text()
        nodes=re.findall(r'^(?:(?:private|public|meta)\s+)*import\s+(?:all\s+)?([\w.]+)\b',src,re.M)
        for n in nodes:visit(n)
        seen[m]=nodes;visiting.remove(m);order.append(m)
    # Roots of the combined real board leaf and conditional Top bridge.
    for m in ('TopCheckedRoot','CapFastTagged'):visit(m)
    direct_fingerprint=json.loads((rec/'old_stop_pilot_receipt.json').read_text())['signature']['foundation_oleans_sha256']
    plan={'scope':'Pinned sources and exact historical foundation contracts; no new compilation',
          'module_prerequisite_order':order,'direct_imports':seen,'external_base_imports':sorted(missing),
          'foundation_source_members':files,'reference_original_proof_not_imported':True,
          'previous_verified_foundation_manifest_sha256':base_sha,
          'previous_accepted_stop_foundation_oleans_sha256':direct_fingerprint,
          'basis_archives':{getattr(p,k).name:sha(getattr(p,k)) for k in AZ},
          'toolchain':json.loads(man)['toolchain'],
          'foundation_prerequisite_claim':'Use already checked exact external base artifacts from the pinned manifest or reproduce their source build; none have been loaded or rebuilt for this candidate.'}
    assert 'CapFastTagged' in order and 'CapTaggedGate' in order and 'TopCheckedRoot' in order
    assert not any(n.startswith('C4W5.Cert.Gen.') for n in missing|set(order))
    (p.out/'STop197869_DEPENDENCIES.json').write_text(json.dumps(plan,indent=2)+'\n')
    print(json.dumps({'included_source_members':len(files),'required_internal_modules':len(order),
                     'external_missing_imports':sorted(missing),
                     'validated_cap_foundation_receipts':3},indent=2))
if __name__=='__main__':
 q=argparse.ArgumentParser()
 for k in ('old','pilot','cap','tagged','fast','original','baseline','out'):q.add_argument('--'+k,required=True,type=Path)
 pin(q.parse_args())
