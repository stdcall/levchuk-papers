"""Integral C-type quotient brackets and bounded center calculations.

Passages: lem:l2018-malcev-semilinear-isomorphism and
lem:l2018-malcev-hypercenters. Every bracket pair is checked for ranks
3 through 8 over ZZ; centers are checked over QQ, GF(2), GF(3).
This is not a universal classification proof.
"""
from sage.all import ZZ, QQ, GF, matrix
import json

results = []
for n in range(3, 9):
    # Indices 1..n,-1..-n. Standard integral symplectic root matrices.
    def E(i, j):
        ans = matrix(ZZ, 2*n)
        def index(k): return k-1 if k > 0 else n-k-1
        ans[index(i), index(j)] = 1
        return ans
    basis = {}
    for i in range(1, n+1):
        for j in range(1, i):
            basis[i,j] = E(i,j)-E(-j,-i)
        for j in range(1, i+1):
            basis[i,-j] = E(i,-j) if i == j else E(i,-j)+E(j,-i)
    killed = {key for key in basis if key[0] >= 2 and key[1] <= -2}
    def coords(mat):
        ans = {key: mat[key[0]-1, key[1]-1 if key[1]>0 else n-key[1]-1]
               for key in basis}
        reconstructed = sum((ans[key]*basis[key] for key in basis), matrix(ZZ,2*n))
        assert reconstructed == mat
        return ans
    def image(key):
        out = matrix(ZZ,n+1)
        if key not in killed:
            i,j = key
            out[i, j if j>0 else 0] = 1
        return out
    pairs = 0
    for a, A in basis.items():
        for b, B in basis.items():
            bracket = coords(A*B-B*A)
            if a in killed or b in killed:
                assert all(c == 0 or key in killed for key,c in bracket.items())
            lhs = sum((c*image(key) for key,c in bracket.items()),matrix(ZZ,n+1))
            assert lhs == image(a)*image(b)-image(b)*image(a)
            pairs += 1
    assert len(basis)-len(killed) == n*(n+1)//2
    centers = []
    keys = list(basis)
    for field in (QQ, GF(2), GF(3)):
        columns = []
        for a in keys:
            columns.append([field(c) for B in basis.values()
                            for c in coords(basis[a]*B-B*basis[a]).values()])
        equations = matrix(field, columns).transpose()
        center = equations.right_kernel()
        expected_keys = [(n,-n)] + ([(n,-n+1)] if field.characteristic()==2 else [])
        expected = matrix(field, [[1 if key==r else 0 for key in keys]
                                 for r in expected_keys]).row_space()
        assert center == expected
        centers.append(dict(characteristic=int(field.characteristic()),
                            dimension=int(center.dimension()), basis=expected_keys))
    results.append(dict(rank=n, basis=len(basis), ideal=len(killed), quotient=n*(n+1)//2,
                        centers=centers,
                        checked_pairs=pairs, coefficient_ring='ZZ', passed=True))
print(json.dumps(results, indent=2))
