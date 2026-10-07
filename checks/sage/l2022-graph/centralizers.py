"""Bounded checks of th:l2022-graph-centralizer-types.

Check the pinned diagram automorphism on NT(m,K) as a Lie algebra for
types A2 through A8 over QQ, GF(2), GF(3), GF(5). The rank exclusions in
Theorem 1 are preserved in the text and tested as an open issue: the
nontrivial pinned graph automorphism exists for A2 and A3 as well.
This does not establish the claimed Lie isomorphisms in types D or E,
the interpretation of BC_n, or uniqueness of enveloping embeddings.
"""
from sage.all import QQ,GF,Matrix,zero_matrix,RootSystem,vector
import json
import argparse

parser=argparse.ArgumentParser()
parser.add_argument('--output')
args=parser.parse_args()
count=0
results=[]
for field in [QQ,GF(2),GF(3),GF(5)]:
    for rank in range(2,9):
        size=rank+1
        positions=[(i,j) for i in range(size) for j in range(i+1,size)]
        def unit(i,j):
            x=zero_matrix(field,size); x[i,j]=1; return x
        basis=[unit(i,j) for i,j in positions]
        def theta(x):
            y=zero_matrix(field,size)
            for i,j in positions:
                y[size-1-j,size-1-i]=(-1)**(j-i+1)*x[i,j]
            return y
        for x in basis:
            assert theta(theta(x))==x; count+=1
            for y in basis:
                assert theta(x*y-y*x)==theta(x)*theta(y)-theta(y)*theta(x)
                count+=1
        for i in range(size-1):
            assert theta(unit(i,i+1))==unit(size-2-i,size-1-i); count+=1
        assert theta(basis[0])!=basis[0]; count+=1
        linear=Matrix(field, [[(theta(x)-x)[i,j] for x in basis] for i,j in positions])
        dimension=len(basis)-linear.rank()
        if rank%2:
            expected=((rank+1)//2)**2
        else:
            n=rank//2
            expected=n*(n+1) if field.characteristic()==2 else n*n
        assert dimension==expected; count+=1
        results.append({'rank_A':rank,'field':str(field),'fixed_dimension':int(dimension)})
assert [r['fixed_dimension'] for r in results if r['rank_A']==3]==[4,4,4,4]
count+=1
assert [r['fixed_dimension'] for r in results if r['rank_A']==2]==[1,2,1,1]
count+=1
graph_orders={}
for kind,n in [('A',1),('A',2),('A',3),('D',4),('D',5),('E',6),('B',2),('F',4),('G',2)]:
    matrix=RootSystem([kind,n]).cartan_matrix()
    # Coxeter bonds are products of off-diagonal Cartan entries.
    from sage.all import Graph
    coxeter=Graph()
    coxeter.add_vertices(range(n))
    for i in range(n):
        for j in range(i+1,n):
            weight=int(matrix[i,j]*matrix[j,i])
            if weight:
                coxeter.add_edge(i,j,weight)
    order=coxeter.automorphism_group(edge_labels=True).order()
    graph_orders[kind+str(n)]=int(order)
    assert order==({'A1':1,'A2':2,'A3':2,'D4':6,'D5':2,'E6':2,'B2':2,'F4':2,'G2':2}[kind+str(n)])
    count+=1
# Definition 1 as printed: an inclusion A1 -> A2 extends to a lattice
# homomorphism but is not onto. The one-node Coxeter graph has no symmetry.
A1={(1,),(-1,)}
A2={(1,0),(-1,0),(0,1),(0,-1),(1,1),(-1,-1)}
inclusion=Matrix(QQ,2,1,[1,0])
image={tuple(inclusion*vector(QQ,r)) for r in A1}
assert image <= A2 and image != A2 and inclusion.rank()==1
assert graph_orders['A1']==1
count+=2
# Page 679: with the printed denominator (r,s), the A3 pair alpha1,
# alpha3 gives division by zero; the corrected Cartan entry is zero.
r=vector(QQ,[1,-1,0,0]); s=vector(QQ,[0,0,1,-1])
assert r.dot_product(s)==0 and r.dot_product(r)==2
assert 2*r.dot_product(s)/r.dot_product(r)==0
count+=2
payload={'checks':count,'type_A_cases':results,'coxeter_symmetry_orders':graph_orders,
         'definition_counterexample':{'domain':'A1','codomain':'A2',
         'lattice_matrix':[[1],[0]],'image':[[int(c) for c in v] for v in sorted(image)],
         'domain_roots':2,'codomain_roots':6,'domain_graph_symmetry_order':1},
         'cartan_denominator_counterexample':{'type':'A3','r':[int(c) for c in r],'s':[int(c) for c in s],
         'dot_rs':0,'dot_rr':2,'corrected_entry':0}}
if args.output:
    with open(args.output,'w') as f: json.dump(payload,f,indent=2); f.write('\n')
print('ok l2022-graph:',count,'checks')
