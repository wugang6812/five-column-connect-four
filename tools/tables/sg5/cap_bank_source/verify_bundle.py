"""Standalone byte/format/no-launch check for extracted cap-bank-source archive."""
from pathlib import Path
from hashlib import file_digest,sha256
import json,re
P=Path(__file__).resolve().parent
B=P/'candidate'
S=B/'lean'
def j(x):return json.loads(x.read_bytes())
def sha(x):
 with x.open('rb') as f:return file_digest(f,'sha256').hexdigest()
def word(vals):
 H=vals[0];q=0
 for b,h in zip(vals[1:6],vals[6:11]):
  assert 0<=h<=H and 0<=b<1<<h
  q=q*((1<<61)-1)+(1<<h)-1+b
 return (q*31+H//2)*(5**10)+vals[11]
def num(f):
 for n,d,b,z in re.findall(r'\(\.window (\d+) (\d+) (\d+) (0x[0-9a-f]+)\)',f.read_text()):
  n,d,b,z=int(n),int(d),int(b),int(z,16)
  for _ in range(n):z,r=divmod(z,d);yield b+r
  assert z==0
m=j(B/'readiness.json');assert m['status']=='SOURCE_ONLY_NOT_KERNEL_ACCEPTED'
for relative,expected in j(B/'lean_imports_and_sha256.json').items():
 p=S/(relative.replace('.','/')+'.lean');assert sha(p)==expected['source_sha256']
 assert re.findall(r'^import (\S+)\s*$',p.read_text(),re.M)==expected['direct_imports']
for mode,f,n,ff in [
 ('policy','selected_policy_rows.txt',1,[f'SG5LongPacked/D{i}.lean' for i in range(88)]),
 ('witness','selected_tag_words.txt',2,['SG5LongPacked/Witnesses.lean'])]:
 p=B/'inputs'/f;assert sha(p)==m['input_sha256'][f]
 expected=sorted(word(list(map(int,l.split()[n:]))) for l in p.open())
 h=sha256();i=0
 for q in ff:
  for x in num(S/q):
   assert expected[i]==x
   h.update(x.to_bytes(48,'little'));i+=1
 assert i==len(expected)==m['decoded'][mode]['rows'] and h.hexdigest()==m['decoded'][mode]['word_stream_sha256']
a=j(P/'matched_plan/plan.json')
assert sha(P/'matched_plan/fixtures/Matched96.lean')==a['prespecified_96_identical_policy_words']['source_sha256']
assert all(sum(x['rows'] for x in v['chunks'])==1152 for v in a['K0'].values())
assert sha(B/'root_receipt.json')==m['roots_sha256']
print('SOURCE_ONLY_FULL_READBACK_PASS',m['decoded'])
