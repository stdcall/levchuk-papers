"""Exhaustive normality checks for small counterexamples; integer arithmetic only.

This checks whether Lemma 3.8 can be used before the later hypothesis 2I=I.
It does not assert validity in arbitrary radical rings.
"""
import json
from collections import deque

def normal_closure(modulus,seed):
    def adj(a,b):
        return ((a[0]+b[0]+a[0]*b[0]+a[1]*b[2])%modulus,
                (a[1]+b[1]+a[0]*b[1]+a[1]*b[3])%modulus,
                (a[2]+b[2]+a[2]*b[0]+a[3]*b[2])%modulus,
                (a[3]+b[3]+a[2]*b[1]+a[3]*b[3])%modulus)
    def inv(a):
        d=pow(((1+a[0])*(1+a[3])-a[1]*a[2])%modulus,-1,modulus)
        return ((d*(1+a[3])-1)%modulus,(-d*a[1])%modulus,
                (-d*a[2])%modulus,(d*(1+a[0])-1)%modulus)
    G=[(a,b,c,d) for a in range(0,modulus,2) for b in range(0,modulus,2)
       for c in range(modulus) for d in range(0,modulus,2)]
    orbit={adj(adj(inv(g),seed),g) for g in G}
    generators=orbit|{inv(g) for g in orbit}
    H={(0,0,0,0)};queue=deque(H)
    while queue:
        h=queue.popleft()
        for g in generators:
            k=adj(h,g)
            if k not in H:H.add(k);queue.append(k)
    assert all(adj(adj(inv(g),h),g) in H for g in G for h in H)
    return H,len(G)

H,size=normal_closure(8,(0,0,1,0))
assert {h[2] for h in H}==set(range(8))
assert (0,4,0,0) not in H
assert len(H)==32 and size==512
print(json.dumps({'K':'Z/8','J':'2K','seed':'e21','normal_group_order':len(H),
 'ambient_group_order':size,'T':sorted({h[2] for h in H}),
 'J2T':'4K','4e12_contained':(0,4,0,0) in H,'all_conjugations_checked':True},indent=2))
import sys
print(f"ok l2002-radical lemma 3.8: {len(H)*size} conjugations, "
      "three counterexample checks", file=sys.stderr)
