"""Exact finite matrix checks; no general classification proof.
Passages: lem:l2008-model-jordan-powers-hypercenters, lem:l2008-model-ideal-preserving-associative, th:l2008-model-jordan-automorphisms.
"""
from sage.all import GF, QQ, MatrixSpace, matrix, vector
import json
from copy import copy

checks=0
def check(condition):
    global checks
    assert condition
    checks += 1

def positions(n):
    return [(i,j) for i in range(n) for j in range(i)]

def upper_centers(n,field):
    pos=positions(n)
    space=MatrixSpace(field,n)
    units=[]
    for i,j in pos:
        e=copy(space.zero()); e[i,j]=1; units.append(e)
    center=matrix(field,0,len(pos)).row_space()
    dims=[0]
    for height in range(1,n):
        quotient=center.basis_matrix().right_kernel().basis_matrix()
        rows=[]
        for y in units:
            columns=[]
            for x in units:
                prod=x*y+y*x
                columns.append(quotient*vector(field,[prod[i,j] for i,j in pos]))
            rows.extend(matrix(field,columns).transpose().rows())
        center=matrix(field,rows).right_kernel()
        expected=[idx for idx,(i,j) in enumerate(pos) if i-j>=n-height]
        check(center.dimension()==len(expected))
        for idx in expected:
            check(vector(field,[int(k==idx) for k in range(len(pos))]) in center)
        dims.append(int(center.dimension()))
    return dims

dimensions={}
for n in range(3,9):
    for field in (QQ,GF(2),GF(3)):
        dimensions[f'{n}:{field}']=upper_centers(n,field)
check(dimensions['5:Rational Field'][1]==1)
check(dimensions['5:Rational Field'][2]==3)

# A noncommutative coefficient ring: upper triangular 2x2 matrices over F2.
field=GF(2); C=MatrixSpace(field,2); c=C([[0,1],[0,0]])
coeff=[C([[1,0],[0,0]]),c,C([[0,0],[0,1]])]
elements=[sum((coeff[i] for i in range(3) if mask>>i&1),C.zero()) for mask in range(8)]
for x in elements:
    for y in elements:
        check(c*(x*y+y*x)==C.zero())
check(elements[1]*elements[2]!=elements[2]*elements[1])

M=MatrixSpace(field,10)
def put(i,j,a):
    result=copy(M.zero())
    for u in range(2):
        for v in range(2): result[2*i+u,2*j+v]=a[u,v]
    return result
def block(a,i,j):
    return C([[a[2*i+u,2*j+v] for v in range(2)] for u in range(2)])
def shear(a):
    return a+put(4,2,c*block(a,1,0))+put(4,1,c*block(a,2,0))
basis=[put(i,j,a) for i,j in positions(5) for a in coeff]
for a in basis:
    check(shear(shear(a))==a)
    for b in basis:
        check(shear(a*b+b*a)==shear(a)*shear(b)+shear(b)*shear(a))

# Printed projection formula fails for the identity automorphism, n=5,m=4.
n=5;m=4;mp=n+1-m
Hm={(i,j) for i,j in positions(n) if i>=m and j<=m-1}
check((n-1,mp-1) in Hm)
check((n-1,mp-1) not in {(i,j) for i,j in positions(n) if i>=n-m and j<=n-m-1})

print(f'PASS {checks} exact assertions')
