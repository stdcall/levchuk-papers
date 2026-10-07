"""Exact root sets and bond multiplicities used by the diagrams."""
import json
import re
from pathlib import Path
from sage.all import CartanMatrix, RootSystem
from sage.env import SAGE_VERSION

ROOT = Path(__file__).resolve().parents[2]
text = (ROOT / 'content/papers/l1990-small/diagrams/b-f4-roots.typ').read_text()
drawn_roots = {tuple(map(int, match)) for match in
               re.findall(r'\(\((\d), (\d), (\d), (\d)\),', text)}
lattice = RootSystem(['F', 4]).root_lattice()
positive = {tuple(int(root.coefficient(i)) for i in range(1, 5))
            for root in lattice.positive_roots()}
assert drawn_roots == positive and len(positive) == 24
covers = [(a, b) for a in positive for b in positive
          if all(bi >= ai for ai, bi in zip(a, b))
          and sum(bi - ai for ai, bi in zip(a, b)) == 1]
assert len(covers) == 34
g2 = CartanMatrix(['G', 2])
f4 = CartanMatrix(['F', 4])
assert g2[0, 1] * g2[1, 0] == 3
assert f4[1, 2] * f4[2, 1] == 2
print(json.dumps({'sage_version': SAGE_VERSION, 'F4_roots': len(positive),
                  'F4_full_covers': len(covers), 'G2_bond': 3, 'F4_middle_bond': 2,
                  'scope': 'Root data and bond multiplicities; geometric layout is separate.'}))
