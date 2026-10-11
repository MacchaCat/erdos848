// For every witness b <= N: |Ex(b)| = #{a <= N : p^2 | ab+1 for some prime p > Y}, for each Y given.
// usage: ex_all N Y1 Y2 ...   output: b ex(Y1) ex(Y2) ...
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <cstdint>
typedef unsigned long long u64; typedef __uint128_t u128;
static long long inv_mod(long long a, long long m){ long long g=m,x=0,x1=1,a1=a%m; // ext gcd
  long long b0=m; long long t; long long q; long long aa=a1, mm=m; long long s0=1,s1=0;
  while(mm){ q=aa/mm; t=aa-q*mm; aa=mm; mm=t; t=s0-q*s1; s0=s1; s1=t; }
  long long r=s0% m; if(r<0) r+=m; return r; }
int main(int argc,char**argv){
  long long N=atoll(argv[1]); int k=argc-2; std::vector<long long> Y(k); for(int i=0;i<k;i++) Y[i]=atoll(argv[2+i]);
  long long L=1; while((L+1)*(L+1)<=N*N+1) L++;
  std::vector<char> sv(L+1,1); sv[0]=sv[1]=0; for(long long i=2;i*i<=L;i++) if(sv[i]) for(long long j=i*i;j<=L;j+=i) sv[j]=0;
  std::vector<long long> P; for(long long i=2;i<=L;i++) if(sv[i]) P.push_back(i);
  std::vector<int> mark(N+1,0); int stamp=0;
  for(long long b=1;b<=N;b++){
    printf("%lld",b);
    for(int t=0;t<k;t++){
      stamp++; long long c=0;
      for(long long p:P){ if(p<=Y[t]) continue; if(p*p>N*b+1) break; if(b%p==0) continue;
        long long q=p*p; long long a0=(q-inv_mod(b%q,q))%q; if(a0==0) a0=q;
        for(long long a=a0;a<=N;a+=q){ if(mark[a]!=stamp){mark[a]=stamp;c++;} } }
      printf(" %lld",c);
    }
    printf("\n");
  }
}
