# independent check of disc_table entries (small P) by brute force on the definition
# g(m) = #{s mod P : s^2 m == 1 mod P}, P = 2^e' * prod(Q)
import sys
from math import gcd
def beta0(e,Q):
    P=[1,2,4,8][e]
    for q in Q: P*=q
    g=[0]*P
    for s in range(P):
        if gcd(s,P)!=1: continue
        inv2=pow(s*s,-1,P) if P>1 else 0
        g[inv2%P]+=1
    phi=sum(g)
    G=0;best=0
    for m in range(1,P):
        G+=g[m%P]
        best=max(best,G*P-m*phi)
    return P,phi,best
bad=0;n=0
for line in open('disc_table.txt'):
    t=line.split(); e=int(t[0]);k=int(t[1]);Q=list(map(int,t[2:2+k]))
    P=int(t[2+k][2:])
    if P>50000: continue
    n+=1
    r=beta0(e,Q)
    if (r[0],r[1],r[2])!=(P,int(t[3+k][4:]),int(t[4+k][9:])): bad+=1; print("MISMATCH",line,r)
print("checked",n,"bad",bad)
