from pathlib import Path
from hashlib import file_digest
import json,subprocess,sys,re,shutil
HERE=Path(__file__).resolve().parent
R=HERE.parent
WORK=R.parent
A=R/'sg5_reroute_source_pilot_20261121/prepared'
B=HERE/'candidate'
D=R/'cap_only_external'
KN=HERE/'matched_plan'
OP=KN/'fixtures'
sys.path.insert(0,str(R/'sg5_reroute_source_pilot_20261121'))
from stage_source import word,row_tree,WINDOW_RE
def sha(p):
 with p.open('rb') as f:return file_digest(f,'sha256').hexdigest()
def check(b,m):
 if not b:raise RuntimeError(m)
def jout(p,o):p.write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')
def intersection():
 f=A/'inputs/selected_policy_rows.txt';g=B/f.relative_to(A)
 check(sha(f)=='f9c235a5c301af65d311db47774a145f024e1bbd114a146d421def9d32da65f3','wrong unchanged-checker baseline projection')
 check(sha(g)==json.loads((B/'readiness.json').read_bytes())['input_sha256'][g.name],'wrong cap bank projection')
 full={word(list(map(int,l.split()[1:]))) for l in f.open()}
 check(len(full)==1073122,'baseline words mismatch')
 p=KN/'intersection_tmp.txt'
 with p.open('w') as out:
  for line in g.open():
   if word(list(map(int,line.split()[1:]))) in full:out.write(line)
 return p
def make():
 check(B.is_dir() and A.is_dir() and not KN.exists(),'require both isolated source roots and new plan')
 KN.mkdir();OP.mkdir()
 p=intersection()
 cpp=HERE/'fixture_candidates.cpp'
 exe=KN/'fixture_candidates'
 subprocess.run(['g++','-O3','-std=c++17','-DNDEBUG',cpp,'-o',exe],check=True)
 ran=subprocess.run([exe,p,D/'cap_witness_rows.txt'],check=True,capture_output=True,text=True)
 d=json.loads(ran.stdout)
 c=d['cases']
 check(len(c)==96 and len({x['id'] for x in c})==96 and sum(x['cap_edges']>0 for x in c)==48,'bad 96-row stratified fixture')
 cases_path=KN/'exact_rows_and_variants.json';jout(cases_path,d)
 w=sorted(word(q['data']) for q in c)
 st=f'''import SG5LongPacked.Top
open Connect4.NarrowBoards C4W5.WindowBank C4W5.SG5LongPacked
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private def matched : Bank := {row_tree(w)}
theorem capVersusRerouteMatched : all fmt.radix (scheckExtraRow 2 fmt t longGate) matched = true := by
  decide +kernel
#print axioms capVersusRerouteMatched
'''
 (OP/'Matched96.lean').write_text(st)
 shutil.copyfile(R/'KernelRootProbe.lean',OP/'KernelRootProbe.lean')
 (OP/'ImportOnly.lean').write_text('import SG5LongPacked.Top\n#check C4W5.SG5LongPacked.t\n#check C4W5.SG5LongPacked.longGate\n')
 # Stage exactly the original K0 obligations for each side, with no need to
 # force a monolithic 1,152-row reduction past the approved guard.
 ko={}
 for label,root in [('A_reroute932',A/'lean'),('B_cap697',B/'lean')]:
    sources=KN/label;sources.mkdir()
    data=root/'SG5LongPacked/D0.lean'; orig=root/'SG5LongPacked/K0.lean'
    names=re.findall(r'^theorem (p\d+)_ok',orig.read_text(),re.M)
    check(names==['p0','p1','p2'],'must assemble exact current K0')
    pieces=[]
    for n in names:
      line=re.search(rf'^def {n} : Bank := (.+)$',data.read_text(),re.M)[1]
      tokens=re.findall(r'\(|\)|\.branch|\.window|0x[0-9a-f]+|\d+',line)
      z=iter(tokens)
      def parse():
         check(next(z)=='(','constructor start'); k=next(z)
         if k=='.branch':
            cut=next(z);out=(k,cut,parse(),parse())
         else:
            check(k=='.window','only exact window leaves allowed')
            out=(k,next(z),next(z),next(z),next(z))
         check(next(z)==')','constructor ends')
         return out
      tree=parse();check(next(z,None) is None,'trailing token')
      def emit(t):
          return '(.branch '+t[1]+' '+emit(t[2])+' '+emit(t[3])+')' if t[0]=='.branch' else '('+' '.join(t)+')'
      def nrows(t):
          if t[0]=='.window':return int(t[1])
          return nrows(t[2])+nrows(t[3])
      check(emit(tree)==line and nrows(tree)==384,'split reconstructor changed original row group')
      for path,tt in [('LL',tree[2][2]),('LR',tree[2][3]),('RL',tree[3][2]),('RR',tree[3][3])]:
          check(nrows(tt)==96,'noncanonical quarter')
          name=n+'_'+path
          file=sources/(name+'.lean')
          file.write_text('''import SG5LongPacked.Top
namespace C4W5.SG5ExactK0Plan
open Connect4.NarrowBoards C4W5.WindowBank C4W5.SG5LongPacked
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
'''+f'''theorem {name}_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) {emit(tt)} = true := by decide +kernel
end C4W5.SG5ExactK0Plan
''')
          pieces.append({'source':name+'.lean','source_sha256':sha(file),'rows':nrows(tt)})
      aes=sources/(n+'_assembly.txt')
      aes.write_text(f'''theorem {n}_ok : all fmt.radix (scheckExtraRow 2 fmt t longGate) {n} = true := by
  change all fmt.radix (scheckExtraRow 2 fmt t longGate) {line} = true
  exact all_branch (cut := {tree[1]})
    (all_branch (cut := {tree[2][1]}) C4W5.SG5ExactK0Plan.{n}_LL_ok C4W5.SG5ExactK0Plan.{n}_LR_ok)
    (all_branch (cut := {tree[3][1]}) C4W5.SG5ExactK0Plan.{n}_RL_ok C4W5.SG5ExactK0Plan.{n}_RR_ok)
''')
    st=''.join(f'import {x["source"][:-5]}\n' for x in pieces)
    official=orig.read_text()
    hdr=official[:official.index('theorem p0')]
    p2=sources/'K0ExactAssembly.lean'
    p2.write_text(st+hdr+''.join((sources/(z+'_assembly.txt')).read_text() for z in names)+'\nend C4W5.SG5LongPacked\n')
    ko[label]={'actual_module':'SG5LongPacked.K0','source_sha256':sha(orig),'source_rows':1152,
        'three_exact_group_definitions':names,'chunks':pieces,'assembly_source_sha256':sha(p2),
        'separate_overlay_only':True,'assembly_not_yet_elaborated':True}
 jout(KN/'plan.json',{'status':'STRICT_SOURCE_ONLY','lean_launched':False,
  'comparison_scope':'A=accepted loaded 932 reroute bank, B=new cap697 bank after cold setup; no stale same-name imports',
  'prespecified_96_identical_policy_words': {'source_sha256':sha(OP/'Matched96.lean'),'rows':96,
       'with_cap_query':48,'exact_cap_queries':sum(x['cap_edges'] for x in c),
       'white_variants':sum(x['white_variants'] for x in c),
       'black_variants':sum(x['black_variants'] for x in c),'data_receipt_sha256':sha(cases_path)},
  'root_probe_sha256':sha(OP/'KernelRootProbe.lean'),'import_only_sha256':sha(OP/'ImportOnly.lean'),
  'K0':ko,'compiled_proof_work':0,'caution': 'actual K0 sides can contain different rows; the 96-row fixture is the matched control'})
 print(json.dumps({'intersection_rows':d['total_intersection'],'pickedrows':len(c),'cap_calls':sum(x['cap_edges'] for x in c),
     'white_variants':sum(x['white_variants'] for x in c),'black_variants':sum(x['black_variants'] for x in c),'K0split':['A 12×96','B 12×96']},indent=2))
if __name__=='__main__':make()
