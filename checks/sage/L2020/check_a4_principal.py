"""A4/GF2, all 64 root-basis sign choices and 1023 principal ideals each."""
import json
from itertools import product
roots=[(i,j) for i in range(1,5) for j in range(i)]
idx={r:i for i,r in enumerate(roots)}
non_simple=[r for r in roots if r[0]-r[1]>1]
def span_basis(vectors):
    B={}
    for x in vectors:
        while x:
            p=x.bit_length()-1
            if p in B:x^=B[p]
            else:B[p]=x;break
    return B
def contains(B,x):
    while x:
        p=x.bit_length()-1
        if p not in B:return False
        x^=B[p]
    return True
def greater(a,b):
    i,j=roots[a];k,l=roots[b]
    return a!=b and i>=k and j<=l
rows=[]
for choice in product([-1,1],repeat=6):
    signs={r:1 for r in roots};signs.update(zip(non_simple,choice))
    table={}
    for i,(a,b) in enumerate(roots):
        for j,(c,d) in enumerate(roots):
            if b==c:r=(a,d);N=signs[a,b]*signs[c,d]*signs[r]
            elif d==a:r=(c,b);N=-signs[a,b]*signs[c,d]*signs[r]
            else:continue
            k=idx[r]
            # Printed Lemma3: sign decides which ordered product is nonzero.
            table[i,j]=(1<<k) if N>0 else 0
    def mul(x,y):
        z=0
        for (i,j),v in table.items():
            if x>>i&1 and y>>j&1:z^=v
        return z
    associative=all(mul(mul(1<<i,1<<j),1<<k)==mul(1<<i,mul(1<<j,1<<k))
        for i in range(10) for j in range(10) for k in range(10))
    bad=[]
    for x in range(1,1024):
        B=span_basis([x])
        while True:
            old=len(B)
            B=span_basis(list(B.values())+[mul(b,1<<i) for b in B.values() for i in range(10)]
                +[mul(1<<i,b) for b in B.values() for i in range(10)])
            if len(B)==old:break
        support=[i for i in range(10) if any(b>>i&1 for b in B.values())]
        corners=[i for i in support if not any(greater(i,j) for j in support)]
        standard=all(contains(B,1<<i) for i in range(10)
            if any(greater(i,j) for j in corners))
        if not standard:bad.append(x)
    proper=[]
    for domain in ([idx[r] for r in roots if r[0]<=3],
                   [idx[r] for r in roots if r[1]>=1]):
        proper.append(all(mul(mul(1<<i,1<<j),1<<k)==mul(1<<i,mul(1<<j,1<<k))
            for i in domain for j in domain for k in domain))
    rows.append({'signs':choice,'associative':associative,
        'proper_A3_associative':proper,
        'all_principal_ideals_standard':not bad,'nonstandard_principal_count':len(bad),
        'first_nonstandard_generator':bad[0] if bad else None})
print(json.dumps({'status':'completed','roots':roots,'tables':rows,
    'associative_tables':sum(r['associative'] for r in rows),
    'all_standard_tables':sum(r['all_principal_ideals_standard'] for r in rows),
    'scope':'64 A4/GF2 literal tables; 1023 principal ideals per table'},indent=2))
