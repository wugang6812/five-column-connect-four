#define main unused_original_szgen
#include "../../sg5_branch_recovery/even_full_recovery/source/gen/szgen.cpp"
#undef main
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <unordered_set>
static void req(bool b,const char *msg){if(!b)throw std::runtime_error(msg);}
static uint64_t mix(uint64_t x){x^=x>>30;x*=0xbf58476d1ce4e5b9ULL;x^=x>>27;x*=0x94d049bb133111ebULL;return x^(x>>31);}
struct Case {uint64_t rank;int id,rep,hit,nw,nb;S st;};
int main(int argc,char**argv){try{
 req(argc==3,"inputs: identical-row input and exact cap endpoint projection");D=2;
 std::ifstream cap(argv[2]),common(argv[1]);req(cap.good()&&common.good(),"inputs unavailable");
 int id,r;S st{};u64 v;
 std::unordered_set<K,KH> capset;capset.reserve(165000);
 while(cap>>id>>st.H){
    for(auto &b:st.b){cap>>v;b=v;}for(auto &h:st.h)cap>>h;
    for(int j=0;j<10;j++)cap>>r;
    req(cap.good() && capset.insert(key(st)).second,"bad cap source");
 }
 req(capset.size()==162563,"wrong endpoint count");
 std::vector<Case> chosen[4][2];uint64_t sums[4][2]={};uint64_t loaded=0;
 while(common>>id>>st.H){
  for(auto&b:st.b){common>>v;b=v;}for(auto&h:st.h)common>>h;common>>r;
  req(common.good()&&r>=0&&r<9765625,"invalid common row");
  loaded++;
  int hit=0,nw=0,nb=0;
  for(int c=0,pow=1;c<5;c++,pow*=25)if(st.h[c]<st.H){
    S w[2];int cnt=vars(st,c,0,w);
    for(int j=0;j<cnt;j++){
      req(!four(w[j],0),"White already won at policy row");nw++;
      S p=normAt(w[j],c);
      if(full(p))continue;
      int e=r/pow/(j?5:1)%5;
      req(p.h[e]<p.H,"policy has illegal reply");
      S bb[2];int nt=vars(p,e,1,bb);
      for(int z=0;z<nt;z++){
       nb++;if(four(bb[z],1))continue;
       S q=normAt(bb[z],e);
       if(capset.find(key(q))!=capset.end())hit++;
      }
    }
  }
  int k=st.H<=16?0:st.H<=24?1:st.H<=32?2:3;
  int v1=hit>0?1:0;
  sums[k][v1]++;
  auto&vv=chosen[k][v1];
  Case x{mix((uint64_t)id+20261121ULL),id,r,hit,nw,nb,st};
  if(vv.size()<12)vv.push_back(x);
  else{
   auto m=std::max_element(vv.begin(),vv.end(),[](auto a,auto b){return a.rank<b.rank;});
   if(m->rank>x.rank)*m=x;
  }
 }
 std::cout<<"{\"status\":\"MATCHED_IDENTICAL_REAL_WORDS\",\"total_intersection\":"<<loaded<<",\"strata_pool\":[";
 for(int k=0;k<4;k++)std::cout<<(k?",":"")<<"["<<sums[k][0]<<","<<sums[k][1]<<"]";
 std::cout<<"],\"cases\":[";
 bool f=true;
 for(int k=0;k<4;k++)for(int l=0;l<2;l++){
  auto &z=chosen[k][l];req(z.size()==12,"underpopulated sampling stratum");
  std::sort(z.begin(),z.end(),[](auto a,auto b){return a.rank<b.rank;});
  for(auto c:z){
    std::cout<<(f?"":",")<<"{\"id\":"<<c.id<<",\"h_tier\":"<<k<<",\"cap_edges\":"<<c.hit
        <<",\"white_variants\":"<<c.nw<<",\"black_variants\":"<<c.nb<<",\"data\":["<<c.st.H;
    for(auto b:c.st.b)std::cout<<","<<(u64)b;
    for(auto h:c.st.h)std::cout<<","<<h;
    std::cout<<","<<c.rep<<"]}";f=false;
  }
 }
 std::cout<<"]}\n";return 0;
}catch(const std::exception&e){std::cerr<<e.what()<<std::endl;return 1;}}
