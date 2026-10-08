from itertools import product
# Actual R2(Z4,2Z4), with additive generators e21,2e11,2e12,2e22.
elems=list(product([0,2],[0,2],range(4),[0,2]))
index={x:i for i,x in enumerate(elems)}
def add(x,y):return tuple((a+b)%4 for a,b in zip(x,y))
def scale(c,x):return tuple(c*a%4 for a in x)
def mul(x,y):
 a,b,c,d=x;e,f,g,h=y
 return ((a*e+b*g)%4,(a*f+b*h)%4,(c*e+d*g)%4,(c*f+d*h)%4)
gens=[(0,0,1,0),(2,0,0,0),(0,2,0,0),(0,0,0,2)]
def coefficients(x):return [x[2],x[0]//2,x[1]//2,x[3]//2]
tables=[]
four=[x for x in elems if x[2]%2]
two=[x for x in elems if scale(2,x)==(0,0,0,0)]
for images in product(four,two,two,two):
 def f(x):
  out=(0,0,0,0)
  for c,y in zip(coefficients(x),images):out=add(out,scale(c,y))
  return out
 if any(f(mul(x,y))!=mul(f(x),f(y)) for x,y in product(gens,gens)):continue
 table=tuple(index[f(x)] for x in elems)
 if len(set(table))!=32:continue
 tables.append(table)
assert len(set(tables))==32
# Each accepted additive map is verified on EVERY actual product.
for table in tables:
 for i,j in product(range(32),repeat=2):
  assert table[index[mul(elems[i],elems[j])]]==index[mul(elems[table[i]],elems[table[j]])]
print('PASS all',len(tables),'automorphisms,',len(tables)*32**2,'actual product pairs')
