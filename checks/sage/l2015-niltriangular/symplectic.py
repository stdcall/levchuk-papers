"""Check pp.39–41: C_n brackets, Lemma2.3, quotient type and (2).

Matrix checks cover C_n, n=3..6, GF(2),GF(3),GF(5), and the explicit
automorphism for n=5,6 over Z/2,Z/4,Z/6,Z/8,Z/9. They do not classify
all automorphisms over arbitrary coefficient rings.
"""
from sage.all import GF, ZZ, QQ, Integers, VectorSpace, matrix, identity_matrix
import json
checks=0
def check(c):
    global checks
    assert c
    checks+=1
def data(n,K):
    ps=[(i,j) for i in range(1,n+1) for j in range(-i,i) if j]
    def col(j): return j-1 if j>0 else n-j-1
    def unit(i,j):
        M=matrix(K,2*n); M[i-1,col(j)]=1
        if j>0: M[col(-j),col(-i)]=-1
        elif i!=-j: M[-j-1,col(-i)]=1
        return M
    bs=[unit(*p) for p in ps]
    def coords(M): return [M[i-1,col(j)] for i,j in ps]
    brackets=[[coords(A*B-B*A) for B in bs] for A in bs]
    return ps,bs,coords,brackets
for n in range(3,7):
    for order in (2,3,5):
        K=GF(order); ps,bs,coords,brackets=data(n,K)
        V=VectorSpace(K,len(ps)); es=V.basis(); ix={p:k for k,p in enumerate(ps)}
        def sub(pred): return V.subspace([es[k] for k,p in enumerate(ps) if pred(*p)])
        def T(i,j): return sub(lambda a,b:a>=i and b<=j)
        def centralizer(A):
            rows=[]
            for b in A.basis():
                C=matrix(K,[sum(b[j]*V(brackets[i][j]) for j in range(len(ps)))
                            for i in range(len(ps))])
                rows+=C.transpose().rows()
            return matrix(K,rows).right_kernel() if rows else V
        for i,j in ps:
            expected=T(1,-j-1)
            if i==n and order==2: expected+=T(n,n-1)
            check(centralizer(T(i,j))==expected)
        def height(i,j): return i-j if j>0 else i-j-1
        def L(k): return sub(lambda i,j:height(i,j)>=k)
        Z=V.zero_subspace()
        for i in range(1,2*n):
            Q=V.quotient(Z)
            rows=[]
            for b in range(len(ps)):
                C=matrix(K,[list(Q(V(brackets[a][b]))) for a in range(len(ps))])
                rows+=C.transpose().rows()
            Z=matrix(K,rows).right_kernel() if rows else V
            expected=L(2*n-i)
            if order==2 and i<2*n-1: expected+=L(2*n-i-1)
            check(Z==expected)
        quotient_positions=[p for p in ps if p[1]>0 or p[1]==-1]
        check(len(quotient_positions)==n*(n+1)//2)
        for a,p in enumerate(quotient_positions):
            for b,t in enumerate(quotient_positions):
                got=V(brackets[ix[p]][ix[t]])
                pi=(p[0],max(0,p[1])); tj=(t[0],max(0,t[1]))
                expected=V.zero()
                if pi[1]==tj[0]: expected+=es[ix[(pi[0],tj[1] or -1)]]
                if tj[1]==pi[0]: expected-=es[ix[(tj[0],pi[1] or -1)]]
                check(got-expected in T(2,-2))
for n in (5,6):
    for modulus in (2,4,6,8,9):
        K=Integers(modulus); ps,bs,coords,brackets=data(n,K); ix={p:k for k,p in enumerate(ps)}
        for t in K:
            if 2*t: continue
            A=identity_matrix(K,len(ps))
            A[ix[n-2,-n+3],ix[n,n-1]]+=t
            A[ix[n-1,-n+3],ix[n,n-2]]+=t
            A[ix[n-1,-n+2],ix[n,n-3]]+=t
            check(A.det()==1)
            ims=[sum(A[j,i]*bs[j] for j in range(len(ps))) for i in range(len(ps))]
            for i in range(len(ps)):
                for j in range(len(ps)):
                    check(ims[i]*ims[j]-ims[j]*ims[i]
                         ==sum((A*matrix(K,len(ps),1,brackets[i][j]))[k,0]*bs[k]
                               for k in range(len(ps))))
print(json.dumps({'checks':checks,'ranks':[3,4,5,6],
 'fields':[2,3,5],'automorphism_rings':[2,4,6,8,9]},ensure_ascii=False))
print(f'ok l2015-niltriangular symplectic: {checks} checks')
