"""All eight literal A3 root-product tables: association and Lemma7.

Matrix convention matches printed96: r=e21,p=e32,s=e43.
The six root vectors are signed lower4x4 matrix units over QQ.
Expected standard test is printed Lemma7(a), not a general ideal proof.
"""
import json
from itertools import product
from sage.all import QQ, GF, vector

roots=[(1,0),(2,1),(3,2),(2,0),(3,1),(3,0)]

def root_table(F,signs):
    sig=[1,1,1,*signs]
    table={}
    for i,(a,b) in enumerate(roots):
        for j,(c,d) in enumerate(roots):
            if b==c and (a,d) in roots:
                k=roots.index((a,d)); n=sig[i]*sig[j]*sig[k]
                if n>0:
                    table[i,j]=(k,F(1));table[j,i]=(k,F(1-n))
                else:
                    table[j,i]=(k,F(1));table[i,j]=(k,F(1+n))
    return table

def mul(F,T,u,v):
    w=vector(F,6)
    for (i,j),(k,c) in T.items(): w[k]+=u[i]*v[j]*c
    return w

results=[]
for F in [QQ,GF(2),GF(3)]:
    B=[vector(F,[int(i==j) for i in range(6)]) for j in range(6)]
    rows=[]
    for signs in product([-1,1],repeat=3):
        T=root_table(F,signs)
        associative=all(mul(F,T,mul(F,T,x,y),z)==mul(F,T,x,mul(F,T,y,z))
            for x,y,z in product(B,repeat=3))
        # r,s must not both lie in either one-sided annihilator of p.
        standard_condition=not(
            (mul(F,T,B[0],B[1])==0 and mul(F,T,B[2],B[1])==0) or
            (mul(F,T,B[1],B[0])==0 and mul(F,T,B[1],B[2])==0))
        assert not associative or standard_condition
        # Quotient by the third power/highest-root line is associative.
        quotient_associative=all(
            list(mul(F,T,mul(F,T,x,y),z))[:5]==
            list(mul(F,T,x,mul(F,T,y,z)))[:5]
            for x,y,z in product(B,repeat=3))
        assert quotient_associative
        # All brackets equal the signed lower-matrix commutator.
        for i,(a,b) in enumerate(roots):
            for j,(c,d) in enumerate(roots):
                expected=vector(F,6);sig=[1,1,1,*signs]
                if b==c and (a,d) in roots:
                    k=roots.index((a,d));expected[k]+=F(sig[i]*sig[j]*sig[k])
                if d==a and (c,b) in roots:
                    k=roots.index((c,b));expected[k]-=F(sig[i]*sig[j]*sig[k])
                assert mul(F,T,B[i],B[j])-mul(F,T,B[j],B[i])==expected
        rows.append({'signs':signs,'associative':associative,
            'Lemma7a_condition':standard_condition})
    assert sum(r['associative'] for r in rows)==2
    assert sum(r['Lemma7a_condition'] for r in rows)==4
    results.append({'field':str(F),'tables':rows})
print(json.dumps({'status':'PASS','fields':results,
 'scope':'eight A3 tables in QQ/GF2/GF3;216 basis associators per table; signed lower matrix brackets; no all-ideal or arbitrary-envelope classification'},indent=2))
