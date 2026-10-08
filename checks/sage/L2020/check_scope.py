"""Exact bounded checks for printed93 Proposition1 and Cartan coefficient.

Checks actual C2 matrix normalization over QQ and all four extraspecial sign
choices, compared as literal root-product tables over QQ and GF(2).
This does not classify arbitrary envelopes or their isomorphism classes.
"""
import json
from sage.all import QQ, GF, matrix, zero_matrix

def E(i, j):
    m = zero_matrix(QQ, 4)
    m[i, j] = 1
    return m

a = E(0, 1) - E(3, 2)
b = E(1, 3)
c = E(0, 3) + E(1, 2)
d = E(0, 2)
assert a*b-b*a == c
assert a*c-c*a == 2*d
h_b = E(1, 1)-E(3, 3)
assert h_b*a-a*h_b == -a
assert h_b*a-a*h_b != -2*a

def table(field, s, t):
    # Roots a,b,c=a+b,d=2a+b; simple root vectors fixed.
    # e_c=s*c and e_d=t*d, hence N_ab=s and N_ac=2*s*t.
    tab = [field(0)] * (4*4*4)
    for i,j,k,n in [(0,1,2,s),(0,2,3,2*s*t)]:
        if n > 0:
            tab[(i*4+j)*4+k]=field(1)
            tab[(j*4+i)*4+k]=field(1-n)
        else:
            tab[(j*4+i)*4+k]=field(1)
            tab[(i*4+j)*4+k]=field(1+n)
    return tuple(tab)

counts={}
for label,F in [('QQ',QQ),('GF2',GF(2))]:
    tables=[table(F,s,t) for s in [-1,1] for t in [-1,1]]
    counts[label]=len(set(tables))
assert counts == {'QQ':4,'GF2':2}
# A1: both zero multiplication and the field multiplication are associative
# exact envelopes of the same one-dimensional abelian Lie algebra.
F=GF(2)
for u in F:
    for v in F:
        assert u*v-v*u == 0
assert F(1)*F(1) != 0
print(json.dumps({'status':'PASS','C2_distinct_literal_tables':counts,
    'extraspecial_sign_choices':4,'Cartan_original_refuted':True,
    'A1_distinct_envelopes_zero_vs_field':True,
    'scope':'C2 exact matrices/sign tables; A1 exact counterexample; no classification'},
    ensure_ascii=False,indent=2))
