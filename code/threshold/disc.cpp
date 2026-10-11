// Discrepancy table for the averaged root count g_{e,S}(m) = r_{2^e}(m) * prod_{l in S} r_l(m),
// r_l(m) = 1 + (m/l) for l odd prime (0 if l | m), r_{2^e}: e=0:1, e=1:[m odd], e=2: 2[m=1 mod 4], e>=3: 4[m=1 mod 8].
// For each (e,S) read from stdin: prints e, S, P, phi(P), beta0 = max_{0<=r<P} (G(r) - r*phi/P) as exact rational num/P.
// G(r) = sum_{m=1}^r g(m).  Input lines: e k l1 ... lk
#include <cstdio>
#include <vector>
#include <cstdint>
int main(){
  int e,k;
  while(scanf("%d %d",&e,&k)==2){
    std::vector<long long> S(k); for(auto&x:S) scanf("%lld",&x);
    long long m2 = e==0?1:(e==1?2:(e==2?4:8));
    long long P=m2; for(auto x:S) P*=x;
    // Legendre tables
    std::vector<std::vector<char>> qr(k);
    for(int i=0;i<k;i++){ long long l=S[i]; qr[i].assign(l,0); for(long long s=1;s<l;s++) qr[i][s*s%l]=1; }
    long long phi=1; // phi(P)
    if(e==1) phi=1; else if(e==2) phi=2; else if(e>=3) phi=4;
    for(auto l:S) phi*=(l-1);
    // G(r)*P - r*phi, maximize over r in [0,P)
    __int128 G=0; __int128 best=0; // r=0 gives 0
    for(long long m=1;m<P;m++){
      long long g=1;
      if(e==1){ if(m%2==0) g=0; }
      else if(e==2){ g = (m%4==1)?2:0; }
      else if(e>=3){ g = (m%8==1)?4:0; }
      for(int i=0;i<k && g;i++){ long long l=S[i]; long long t=m%l; if(t==0||!qr[i][t]) g=0; else g*=2; }
      G+=g;
      __int128 v = G*(__int128)P - (__int128)m*phi;
      if(v>best) best=v;
    }
    printf("%d %d",e,k); for(auto x:S) printf(" %lld",x);
    printf(" P=%lld phi=%lld beta0num=%lld\n",P,phi,(long long)best);
  }
}
