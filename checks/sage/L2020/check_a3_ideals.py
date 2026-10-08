"""Exhaustive all GF(2) ideals of each of the eight A3 constructions.

Corner standardness is computed directly from the printed root poset.
This certifies only A3 over GF(2), not arbitrary fields or higher ranks.
"""
import json
from itertools import product
from sage.all import GF, VectorSpace
from check_a3 import root_table

F=GF(2);V=VectorSpace(F,6)
coeffs=[(1,0,0),(0,1,0),(0,0,1),(1,1,0),(0,1,1),(1,1,1)]
def encode(v): return sum(int(x)<<i for i,x in enumerate(v))
def greater(i,j): return i!=j and all(a>=b for a,b in zip(coeffs[i],coeffs[j]))
spaces=[]
for dim in range(7):
    for H in V.subspaces(dim):
        elements={encode(v) for v in H}
        basis=[encode(v) for v in H.basis()]
        support=[i for i in range(6) if any(v&(1<<i) for v in basis)]
        corners=[i for i in support if not any(greater(i,j) for j in support)]
        standard=all((1<<i) in elements for i in range(6)
            if any(greater(i,j) for j in corners))
        spaces.append((elements,basis,standard))
assert len(spaces)==2825
rows=[]
for signs in product([-1,1],repeat=3):
    T=root_table(F,signs)
    def mul(x,y):
        out=0
        for (i,j),(k,c) in T.items():
            if c and x&(1<<i) and y&(1<<j): out^=1<<k
        return out
    ideals=[(E,B,S) for E,B,S in spaces if all(
        mul(x,1<<i) in E and mul(1<<i,x) in E for x in B for i in range(6))]
    allstandard=all(S for E,B,S in ideals)
    # Same direct Lemma7(a) test as the basis-associator script.
    condition=not((mul(1,2)==0 and mul(4,2)==0) or
        (mul(2,1)==0 and mul(2,4)==0))
    assert allstandard==condition
    rows.append({'signs':signs,'ideals':len(ideals),'all_standard':allstandard,
        'nonstandard_ideals':sum(not S for E,B,S in ideals)})
assert sum(r['all_standard'] for r in rows)==4
print(json.dumps({'status':'PASS','all_subspaces_examined':2825,
    'eight_tables':rows,'scope':'all ideals of all eight GF2 A3 literal root-product tables'},indent=2))
