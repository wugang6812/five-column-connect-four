// Restrict an existing zone/stretch witness by choosing other certified replies.
// Input and output use szgen's 17-integer format. Every emitted nonterminal
// edge must lead to an emitted row. Sources above 63 rows are rejected here.
#define main szgen_search_main
#include "szgen.cpp"
#undef main
#include <array>
#include <fstream>
#include <limits>

namespace {
struct Row { std::array<u64,5> b; std::array<unsigned char,5> h,l; unsigned char top; int rep; };
struct IndexKey { std::array<u64,6> w; bool operator==(const IndexKey& o) const { return w==o.w; } };
struct IndexHash { size_t operator()(const IndexKey& k) const { u64 h=0x9e3779b97f4a7c15ULL;
  for(auto w:k.w){h^=w; h*=0xff51afd7ed558ccdULL; h^=h>>29;} return h; } };
IndexKey ix(const S& s){ IndexKey k; u64 a=s.H; for(int c=0;c<5;++c){ if(s.b[c]>>64) { std::abort(); } k.w[c]=(u64)s.b[c]; a=a*128+s.h[c]; }
  for(int c=0;c<5;++c)a=a*4+s.l[c]; k.w[5]=a; return k; }
S unpack(const Row& row){ S s{};s.H=row.top;for(int c=0;c<5;++c){s.b[c]=row.b[c];s.h[c]=row.h[c];s.l[c]=row.l[c];}return s; }
std::unordered_map<IndexKey,int,IndexHash> ids;
std::vector<Row> rows;
std::vector<unsigned char> reached;
std::vector<int> queue,reps;
bool fastleaf(const S& s) {
  if(s.H%2) return false;
  MK whites[5],ex[5],op[5]; const MK ceiling=low(s.H);
  for(int c=0;c<5;c++){ int h=s.h[c]; whites[c]=low(h)^s.b[c];
    if(h<s.H && h>=3 && ((whites[c]>>(h-3))&7)==7)return false;
    ex[c]=whites[c]&((whites[c]<<1)|1);
    if(h<s.H && (!h || ((whites[c]>>(h-1))&1)))ex[c]|=ONE<<h;
    op[c]=ceiling^s.b[c]; }
  for(int q=0;q<5;q++) if((s.H-s.h[q])%2){
    bool ok=true; MK prior=op[q]; MK odd=~MK(0)/3*2;
    op[q]&=~((odd<<s.h[q])&ceiling);
    for(int a=0;a<2 && ok;a++) for(int d=-1;d<=1 && ok;d++){
      MK live=ceiling,hit=0;for(int j=0;j<4;j++){int sh=d>0?j:d<0?3-j:0; live&=op[a+j]>>sh;hit|=ex[a+j]>>sh;}
      if(live&hit)ok=false; }
    op[q]=prior; if(ok)return true;
  } return false;
}
struct Targets { int id[2]; int count=0; };
bool target(const S& s, Targets& z){
  if(fastleaf(s))return true;auto it=ids.find(ix(s));if(it==ids.end())return false;
  if(z.count==0 || z.id[0]!=it->second)z.id[z.count++]=it->second;return true;
}
bool replyTargets(const S& s,int e,bool must,int col,Targets& z){
  if(lowPush(s,e)){S bs[2];int n=vars(s,e,1,bs);for(int i=0;i<n;i++)if(!four(bs[i],1)){
    if(must && e!=col)return false;if(!target(normAt(bs[i],e),z))return false;
  }return true;}
  if(must && e!=col)return false;
  S q;return outState(s,e,q)&&target(q,z);
}
void add(int id){if(!reached[id]){reached[id]=1;queue.push_back(id);}}
int policy=0;
long long rank(const Targets& z,int e,int old){
  long long score=0;for(int j=0;j<z.count;j++){ int id=z.id[j];const auto& r=rows[id];
    long long w=1000000; if(reached[id]) w=(policy==2?1000:50000);
    int active=0, hsum=0;for(int c=0;c<5;++c){active+=r.l[c]!=2; hsum+=r.h[c];}
    w+=((policy==2)?10000:100)*active+20*r.top-hsum;score+=w;
  }return score*10+(e!=old); }
int choose(const S& s,int old,bool must,int col){ Targets best;int selected=-1;long long cost=std::numeric_limits<long long>::max();
  for(int i=0;i<5;i++){int e=(old+i)%5;Targets t; if(!replyTargets(s,e,must,col,t))continue;
    long long n=rank(t,e,old);if(n<cost){cost=n;best=t;selected=e;}if(n==0)break; }
  if(selected<0){std::fprintf(stderr,"no certified reply at col %d\n",col);std::exit(2);}for(int j=0;j<best.count;j++)add(best.id[j]);return selected;
}
int reduce(int id){ S s=unpack(rows[id]);int rep=rows[id].rep,ans=0;
  for(int c=0,pow=1;c<5;c++,pow*=25){int old=rep%25;rep/=25;
    if(s.l[c]==0 && s.h[c]<s.H){S children[2];int n=vars(s,c,0,children);for(int j=0;j<n;j++){
      if(four(children[j],0))std::abort();auto v=normAt(children[j],c);
      int e=choose(v,j?old/5:old%5,s.h[c]+5>s.H,c);ans+=e*pow*(j?5:1);}}
    else if(s.l[c]==0){S q=s;q.l[c]=2;Targets t;if(!target(q,t))std::abort();if(t.count)add(t.id[0]);}
    else if(s.l[c]==1){S q=s;q.l[c]=2;bool dead=true;for(int a:q.l)if(a!=2)dead=false;
      if(!dead)ans+=pow*choose(q,old%5,false,c);}
  }return ans;
}
}
static int loadTable(const char* path){
  std::ifstream input(path);if(!input)std::exit(1); std::ios::sync_with_stdio(false);
  ids.reserve(7600000);rows.reserve(7500000);int h,rep;while(input>>h){Row r{};if(h<0 || h>63)std::exit(3);r.top=h;for(auto& x:r.b)input>>x;
    for(auto& x:r.h){int v;input>>v;if(v<0||v>h)std::exit(3);x=v;}for(auto& x:r.l){int v;input>>v;if(v<0||v>2)std::exit(3);x=v;}if(!(input>>rep))std::exit(3);r.rep=rep;
    auto s=unpack(r);if(rows.size()%197==0 && fastleaf(s)!=leaf(s))std::exit(4);
    if(!ids.emplace(ix(s),rows.size()).second)std::exit(5);rows.push_back(r);}
  if(rows.empty())std::exit(2);S root{};root.H=14;std::string seq="333222222222242";
  for(size_t i=0;i<seq.size();++i)root=push(root,seq[i]-'1',i%2==0);
  auto first=ids.find(ix(root));if(first==ids.end())std::exit(5);
  return first->second;
}
#ifndef SZ_GRAPH_DRIVER
int main(int argc,char** argv){if(argc<3)return 1; D=2;policy=argc>3?std::atoi(argv[3]):1;
  int first=loadTable(argv[1]);
  std::fprintf(stderr,"input %zu unique rows\n",rows.size());reached.resize(rows.size());add(first);
  for(size_t i=0;i<queue.size();i++){int repNew=reduce(queue[i]);reps.push_back(repNew);
    if(i%200000==0)std::fprintf(stderr,"processed %zu discovered %zu\n",i,queue.size());}
  std::ofstream out(argv[2]);if(!out)return 1;for(size_t i=0;i<queue.size();++i){auto& r=rows[queue[i]];out<<int(r.top);for(auto x:r.b)out<<' '<<x;for(auto x:r.h)out<<' '<<int(x);for(auto x:r.l)out<<' '<<int(x);out<<' '<<reps[i]<<'\n';}
  if(!out)return 1;std::fprintf(stderr,"closed witness candidate %zu of %zu\n",queue.size(),rows.size());return 0;
}

#endif
