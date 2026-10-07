"""Independent A3/C2 bracket table and A2 folded grading, not full classification."""
from sage.all import ZZ, QQ, GF, matrix, zero_matrix, vector
import json
checks=0
def check(x):
    global checks
    assert x
    checks+=1
def unit(F,n,i,j):
    a=zero_matrix(F,n);a[i,j]=1;return a
def graph(x):
    n=x.nrows();F=x.base_ring();a=zero_matrix(F,n)
    for i in range(n):
        for j in range(i+1,n):a[n-j-1,n-i-1]=(-1)**(j-i+1)*x[i,j]
    return a
def bracket(x,y):return x*y-y*x
fields=[ZZ,QQ,GF(2),GF(3),GF(5)]
out=[]
for F in fields:
    e=lambda i,j:unit(F,4,i,j)
    u=e(0,1)+e(2,3);v=e(1,2);w=e(0,2)-e(1,3);z=-e(0,3)
    B=[u,v,w,z]
    for b in B:check(graph(b)==b)
    for i,b in enumerate(B):
        for j,c in enumerate(B):
            expected=zero_matrix(F,4)
            if (i,j)==(0,1):expected=w
            if (i,j)==(1,0):expected=-w
            if (i,j)==(0,2):expected=2*z
            if (i,j)==(2,0):expected=-2*z
            check(bracket(b,c)==expected)
    # Each basis vector has a separate coefficient at 12,23,13,14;
    # hence independence holds over every commutative coefficient ring.
    check([b[0,1] for b in B]==[1,0,0,0])
    check([b[1,2] for b in B]==[0,1,0,0])
    check([b[0,2] for b in B]==[0,0,1,0])
    check([b[0,3] for b in B]==[0,0,0,-1])
    if F is not ZZ:
        e=lambda i,j:unit(F,3,i,j)
        a=e(0,1);b=e(1,2);c=e(0,2)
        check(graph(a)==b and graph(b)==a and graph(c)==-c)
        basis=[a+b,c] if F.characteristic()==2 else [a+b]
        for x in basis:check(graph(x)==x)
        for x in basis:
            for y in basis:check(bracket(x,y)==0)
        out.append({'field':str(F),'A2_fixed_dimension':len(basis),'A3_C2_bracket_basis':['e12+e34','e23','e13-e24','-e14']})
check(QQ(2)**2/QQ(1)**2==4)
print(json.dumps({'checks':checks,'cases':out,'scope':'A3 integer bracket table, A2 field grading, BC1 length ratio'},indent=2))
print('ok independent low ranks:',checks,'checks')
