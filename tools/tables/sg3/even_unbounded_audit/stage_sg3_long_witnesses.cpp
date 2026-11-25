// Read-only replay of accepted SG3. No policy search; no change of reply digits.
// Move, clear-cut, normAt, four and Claim primitives are included from recovered source.
#define main unused_original_sz_solver
#include "../even_full_recovery/source/gen/szgen.cpp"
#undef main
#include <fstream>
#include <iostream>
#include <chrono>
#include <array>
#include <stdexcept>
static auto started=std::chrono::steady_clock::now();
static double secs(){return std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count();}
struct R { S s; uint32_t rep; uint8_t z; int t,rho,mask,dir,hole; };
static std::vector<R> records;
static std::unordered_map<K,uint32_t,KH> ids;
static std::vector<uint64_t> offsets;
static std::vector<uint32_t> edges;
struct Cnt{uint64_t white=0,black=0,wstretch=0,bstretch=0,wfull=0,bwin=0,claim=0;};
static bool allblocked(const S&s,const MK ex[5],const MK gs[5]){
 MK op[5];for(int c=0;c<5;c++)op[c]=low(s.H)&~(s.b[c]|gs[c]);
 const int dy[3][4]={{0,0,0,0},{0,1,2,3},{3,2,1,0}};
 for(int st=0;st<2;st++)for(auto&of:dy){MK live=op[st]>>of[0],hit=ex[st]>>of[0];
  for(int j=1;j<4;j++){live &=op[st+j]>>of[j];hit |=ex[st+j]>>of[j];}if(live&hit)return false;}
 return true;
}
// Bit0 = old one-cover ZO; bit1 = long odd-threat criterion.
static uint8_t zo(R& z){
 const S&s=z.s;z.t=-1;
 if(s.H%2 || four(s,0)||four(s,1))return 0;
 MK ex[5],claim[5],base[5];
 for(int c=0;c<5;c++){
  int h=s.h[c];MK w=low(h)&~s.b[c];
  if(h<s.H&&h>=3&&((w>>(h-3))&7)==7)return 0;
  ex[c]=w&(ONE|(w<<1));if(h<s.H&&(h==0||((w>>(h-1))&1)))ex[c]|=ONE<<h;
  claim[c]=0;for(int r=h+1;r<s.H;r+=2)claim[c]|=ONE<<r;
  base[c]=(h<s.H&&(s.H-h)%2==0)?claim[c]:0;
 }
 uint8_t ans=0;
 for(int t=0;t<5;t++)if(s.h[t]<s.H&&(s.H-s.h[t])%2){
  for(int r=s.h[t]+1;r<s.H;r+=2){S b=s;b.b[t]|=ONE<<r;if(!four(b,1))continue;
   MK gs[5];for(int c=0;c<5;c++)gs[c]=base[c];gs[t]=claim[t]|(low(s.H)&~low(r));
   if(allblocked(s,ex,gs)){ans|=2;if(r==s.h[t]+1)ans|=1;
     if(z.t<0)for(int d=0;d<3;d++)for(int j=0;j<4;j++){
       int dy=d==0?0:(d==1?1:-1),x=t-j,y=r-j*dy;bool win=true;
       for(int a=0;a<4;a++)if(a!=j&&!cellBlack(s,x+a,y+a*dy))win=false;
       if(win&&z.t<0){
         z.t=t;z.rho=r;z.dir=d;z.hole=j;z.mask=0;
         for(int c=0;c<5;c++)if(s.h[c]<s.H&&(s.H-s.h[c])%2==0)z.mask|=1<<c;
       }
     }
   }
  }
 }
 if((ans&2)&&z.t<0)throw std::runtime_error("missing nonvertical witness");
 return ans;
}
static void row(std::ostream&o,const R&r){o<<r.s.H;for(auto b:r.s.b){if(b>>64)throw std::runtime_error("JSON low mask overflow");o<<' '<<(u64)b;}for(int h:r.s.h)o<<' '<<h;o<<' '<<r.rep;}
struct Walk{uint64_t visited=0,expanded=0,leaves=0,arcs=0;};
static std::ofstream expandedOut, leafOut;
static Walk walk(const std::vector<uint32_t>&roots,int mode,const std::string&label){
 std::vector<uint8_t>seen(records.size(),0);std::vector<uint32_t>q; q.reserve(records.size());
 for(auto i:roots)if(!seen[i]){seen[i]=1;q.push_back(i);}Walk a;
 for(size_t at=0;at<q.size();at++){auto i=q[at];if(mode&&(records[i].z&mode)){a.leaves++;
   if(mode==2){auto&x=records[i];row(leafOut,x);leafOut<<' '<<x.t<<' '<<x.rho<<' '<<x.mask<<' '<<x.dir<<' '<<x.hole<<'\n';}
   continue;}
  a.expanded++;
  if(mode==2){row(expandedOut,records[i]);expandedOut<<'\n';}
  for(auto k=offsets[i];k<offsets[i+1];k++){a.arcs++;auto j=edges[k];if(!seen[j]){seen[j]=1;q.push_back(j);}}
 }a.visited=q.size();std::cout<<"walk "<<label<<" mode "<<mode<<" visited "<<a.visited<<" expanded "<<a.expanded<<" new_terminal_states "<<a.leaves<<" transition_arcs "<<a.arcs<<" seconds "<<secs()<<std::endl;return a;
}
int main(int argc,char**argv){try{
 if(argc!=5)return 1;expandedOut.open(argv[3]);leafOut.open(argv[4]);if(!expandedOut||!leafOut)return 1;D=2;std::ifstream in(argv[1],std::ios::binary);if(!in)throw std::runtime_error("input missing");
 records.reserve(432550);ids.reserve(440000);std::array<unsigned char,90>buf;
 while(in.read((char*)buf.data(),90)){
  R r{};r.s.H=buf[0];for(int c=0;c<5;c++)r.s.h[c]=buf[c+1];
  for(int j=0;j<4;j++)r.rep|=uint32_t(buf[6+j])<<(8*j);
  for(int c=0;c<5;c++)for(int j=0;j<16;j++)r.s.b[c]|=MK(buf[10+c*16+j])<<(8*j);
  if(!ids.emplace(key(r.s),records.size()).second)throw std::runtime_error("duplicate key");
  int n=0;for(int c=0;c<5;c++){n+=r.s.h[c];if(r.s.h[c]>r.s.H||(r.s.b[c]>>r.s.h[c]))throw std::runtime_error("invalid input");}
  if(r.s.H%2||n%2!=1||r.rep>=9765625)throw std::runtime_error("parity/rep invalid");
  records.push_back(r);
 }
 if(!in.eof()||in.gcount()||records.size()!=432550)throw std::runtime_error("row count/length");
 std::cout<<"loaded "<<records.size()<<" seconds "<<secs()<<std::endl;
 Cnt a;uint64_t old=0,lng=0;offsets.reserve(records.size()+1);edges.reserve(records.size()*5);
 for(size_t i=0;i<records.size();i++){
  R&r=records[i];const S&s=r.s;offsets.push_back(edges.size());r.z=zo(r);old+=bool(r.z&1);lng+=bool(r.z&2);
  for(int c=0,pow=1;c<5;c++,pow*=25)if(s.h[c]<s.H){S ws[2];int nw=vars(s,c,0,ws);a.wstretch+=nw-1;
   for(int j=0;j<nw;j++){a.white++;if(four(ws[j],0))throw std::runtime_error("White four");S p=normAt(ws[j],c);
    if(full(p)){a.wfull++;continue;}int e=r.rep/pow/(j?5:1)%5;
    if(p.h[e]>=p.H)throw std::runtime_error("illegal recorded reply");S bs[2];int nb=vars(p,e,1,bs);a.bstretch+=nb-1;
    for(int k=0;k<nb;k++){a.black++;if(four(bs[k],1)){a.bwin++;continue;}S q=normAt(bs[k],e);
     auto it=ids.find(key(q));if(it!=ids.end()){edges.push_back(it->second);continue;}
     if(!leaf(q))throw std::runtime_error("successor missing and not Claim");a.claim++;
    }
   }
  }
  if((i+1)%250000==0)std::cout<<"replayed "<<i+1<<" arcs "<<edges.size()<<" old "<<old<<" long "<<lng<<" seconds "<<secs()<<std::endl;
 }
 offsets.push_back(edges.size());std::vector<uint32_t>roots;
 for(int H:{14}){S r{};r.H=H;std::string ms="33322222242"; // 333(22)^5 42
  if(ms.size()!=11)throw std::runtime_error("root moves typo");for(size_t i=0;i<ms.size();i++)r=push(r,ms[i]-'1',i%2==0);
  if(r.b[1]!=106||r.h[1]!=7||r.b[2]!=5||r.h[2]!=3||r.h[3]!=1)throw std::runtime_error("root mismatch");
  auto it=ids.find(key(r));if(it==ids.end())throw std::runtime_error("root missing");roots.push_back(it->second);
 }
 std::ofstream out(argv[2]);out<<"{\n\"status\":\"PASS\",\n\"rows\":"<<records.size()<<",\n\"candidate_old_zo\":"<<old<<",\n\"candidate_long_zo\":"<<lng<<",\n";
 out<<"\"transition_audit\":{\"white_variants\":"<<a.white<<",\"black_variants\":"<<a.black<<",\"stretched_white\":"<<a.wstretch<<",\"stretched_black\":"<<a.bstretch<<",\"white_full\":"<<a.wfull<<",\"black_win\":"<<a.bwin<<",\"external_claim\":"<<a.claim<<",\"graph_arcs\":"<<edges.size()<<"},\n\"walks\":[\n";
 bool first=true;{std::vector<uint32_t>rr=roots;std::string label="H14";
  for(int mode:{0,1,2}){Walk w=walk(rr,mode,label);if(mode==0&&w.visited!=records.size())throw std::runtime_error("unreachable original rows");
   if(!first)out<<",\n";first=false;out<<"{\"root\":\""<<label<<"\",\"mode\":"<<mode<<",\"visited\":"<<w.visited<<",\"expanded\":"<<w.expanded<<",\"terminal_states\":"<<w.leaves<<",\"transition_arcs\":"<<w.arcs<<"}";
  }
 }out<<"\n],\n\"seconds\":"<<secs()<<",\n\"scope\":\"Exact fixed-policy canonical graph replay. New terminal predicates are mathematical research drafts, not kernel-accepted leaves or byte-saving guarantees.\"\n}\n";
 std::cout<<"PASS seconds "<<secs()<<std::endl;return 0;
 }catch(const std::exception&e){std::cerr<<"FAIL "<<e.what()<<" seconds "<<secs()<<std::endl;return 2;}}
