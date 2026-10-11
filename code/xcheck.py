# Independent check: brute omega(G_N) via networkx for every N <= L, compare with c7(N).
import networkx as nx, sys
L=int(sys.argv[1])
def nsf(n):
    p=2
    while p*p<=n:
        if n%(p*p)==0: return True
        p+=1
    return False
V=[n for n in range(1,L+1) if nsf(n*n+1)]
G=nx.Graph(); 
bad=[]
for i,a in enumerate(V):
    G.add_node(a)
    for b in V[:i]:
        if nsf(a*b+1): G.add_edge(a,b)
    N=a
    w=max(len(c) for c in nx.find_cliques(G))
    c7=(N-7)//25+1 if N>=7 else 0
    if w!=c7: bad.append((N,w,c7))
print("L",L,"|V|",len(V),"mismatches",bad[:10])
