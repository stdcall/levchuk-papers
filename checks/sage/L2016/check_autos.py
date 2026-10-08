"""Check the valid root maps and detect the two incomplete printed maps.

Ranks are at least five, as in the automorphism classification. Formulas
(4) and (8) are tested here before their missing terms are added; the
corrected maps are checked independently in check_repairs.py.
"""
from sage.all import GF, Zmod, identity_matrix, matrix, vector

from model import root_data
count=0
cases=0
for n,q in [(n,q) for n in range(5,8) for q in (2,3)]+[(5,4),(6,4)]:
    k=Zmod(4) if q==4 else GF(q)
    roots,tables,bracket=root_data(n,k)
    one=identity_matrix(k,len(roots))
    basis=[one.column(i) for i in range(len(roots))]
    t=k(2) if q==4 else k(1 if q==2 else 0)
    for equation in range(2,9):
        f=matrix(k,one)
        def add(source,target,coefficient):
            f[roots.index(target),roots.index(source)]+=coefficient
        if equation==2:
            for i in range(1,n): add((i,0),(n,-i),1)
        if equation==3: add((n-1,n-2),(n,-n+2),1)
        if equation==4: add((n-1,n-2),(n,-n+3),t)
        if equation==5:
            add((n,n-1),(n-2,-n+3),t)
            add((n,n-2),(n-1,-n+3),t)
            add((n,n-3),(n-1,-n+2),t)
        if equation==6: add((n,n-1),(n-1,0),t)
        if equation==7:
            add((n,n-1),(n-2,0),t)
            add((n,n-2),(n-1,0),t)
        if equation==8:
            for i in range(2,n):
                add((i,-1),(i,0),t)
                add((i,-1),(n,-i),t)
        assert f.is_invertible(), (n,q,equation,'invertibility')
        failures=[]
        for i,x in enumerate(basis):
            for j,y in enumerate(basis):
                if f*tables[i][j]!=bracket(f*x,f*y):
                    failures.append({'roots':[roots[i],roots[j]]})
                count+=1
        incomplete = equation in (4,8) and t != 0
        assert bool(failures) == incomplete, (n,q,equation,failures)
        cases += 1
print('PASS',cases,'root-map cases;',count,
      'bracket pairs; incomplete printed (4),(8) detected')
