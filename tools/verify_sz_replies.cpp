// Check every written reply. The original solver's terminal and move routines
// are used here; the optimizer's bit-parallel leaf test is never used as evidence.
#define SZ_GRAPH_DRIVER
#include "reduce_sz.cpp"
#include <iostream>
static uint64_t whiteEvents=0,blackVariants=0,memberEdges=0,claimEdges=0,winningMoves=0;
static bool covered(const S& s){if(ids.count(ix(s))){++memberEdges;return true;}
  if(leaf(s)){++claimEdges;return true;}return false;}
static bool checkReply(const S& p,int e,int wc,bool must){
  if(!lowPush(p,e)){S q;return (!must||e==wc)&&outState(p,e,q)&&covered(q);}
  S bv[2];int count=vars(p,e,1,bv);for(int j=0;j<count;++j){++blackVariants;
    if(four(bv[j],1)){++winningMoves;continue;}if(must&&e!=wc)return false;
    if(!covered(normAt(bv[j],e)))return false;}return true;
}
int main(int argc,char** argv){if(argc!=2)return 1;D=2;int root=loadTable(argv[1]);
  for(size_t i=0;i<rows.size();++i){S s=unpack(rows[i]);for(int c=0,pow=1;c<5;c++,pow*=25){
    const int digits=rows[i].rep/pow%25;
    if(s.l[c]==0&&s.h[c]<s.H){S w[2];int count=vars(s,c,0,w);for(int j=0;j<count;j++){++whiteEvents;
      if(four(w[j],0)||!checkReply(normAt(w[j],c),j?digits/5:digits%5,c,s.h[c]+5>s.H)){std::cerr<<"failure "<<i<<' '<<c<<' '<<j<<'\n';return 6;}}}
    else if(s.l[c]==0){++whiteEvents;S q=s;q.l[c]=2;if(!covered(q))return 7;}
    else if(s.l[c]==1){++whiteEvents;S q=s;q.l[c]=2;bool dead=true;for(int a:q.l)if(a!=2)dead=false;if(!dead&&!checkReply(q,digits%5,c,false))return 8;}
  }}std::cout<<"{\"rows\":"<<rows.size()<<",\"root_index\":"<<root<<",\"white_events\":"<<whiteEvents<<",\"black_variants\":"<<blackVariants<<",\"member_edges\":"<<memberEdges<<",\"claim_edges\":"<<claimEdges<<",\"black_four_variants\":"<<winningMoves<<"}\n";
}
