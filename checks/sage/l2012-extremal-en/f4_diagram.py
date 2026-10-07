"""Levchuk–Suleimanova2012, p.110: every root and edge of the native F4 root diagram.

The 24 root coordinates are literal readings of the printed diagram,
Bourbaki ordering (Carter 1972, §3.6). Independently computes positive
roots and all simple-root covers with Sage. No group classification.
"""
from pathlib import Path
from sage.all import RootSystem
import re

expected = ['1000','0100','0010','0001','1100','0110','0011','1110',
            '0120','0111','1120','1111','0121','1220','1121','0122',
            '1221','1122','1231','1222','1232','1242','1342','2342']
root = RootSystem(['F',4]).root_lattice()
positive = {tuple(r[i] for i in range(1,5)) for r in root.positive_roots()}
literal = {tuple(map(int,s)) for s in expected}
checks = 0
def check(value):
    global checks
    assert value
    checks += 1
check(len(positive) == 24)
check(literal == positive)
source = Path(__file__).resolve().parents[3] / 'content/papers/l2012-extremal-en/diagrams/f4-roots.typ'
source_text = source.read_text()
# The renderer now imports the same ordered literal root table as the 1990
# diagram; only the selection/style of edges differs between the articles.
table_import = re.search(
    r'#import "([^"]+)":\s*\((?=[^)]*positive-roots)[^)]*\)', source_text)
check(table_import is not None)
table_path = (source.parent / table_import.group(1)).resolve()
table = re.search(r'#let positive-roots\s*=\s*\((.*?)\n\)',
                  table_path.read_text(), re.S)
check(table is not None)
coefficients = [tuple(map(int, row)) for row in re.findall(
    r'\(\((\d),\s*(\d),\s*(\d),\s*(\d)\),', table.group(1))]
check([''.join(map(str, row)) for row in coefficients] == expected)
check(len(coefficients) == len(set(coefficients)) == 24)
actual = set(coefficients)
check(actual == positive)
units = {tuple(int(i==j) for i in range(4)) for j in range(4)}
edges = {(a,b) for a in positive for b in positive
         if tuple(y-x for x,y in zip(a,b)) in units}
drawn = {(a,b) for a in actual for b in actual
         if all(y>=x for x,y in zip(a,b)) and sum(y-x for x,y in zip(a,b))==1}
check(drawn == edges)
check(len(edges) == 34)
for a,b in edges:
    check(sum(b) == sum(a)+1)
print(f'ok l2012-extremal-en F4 diagram: {checks} checks; 24 positive roots; {len(edges)} simple-root edges')
