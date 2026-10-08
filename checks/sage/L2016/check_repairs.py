from pathlib import Path
from sage.all import ZZ, matrix, identity_matrix
import json

work=Path(__file__).resolve().parent
from model import root_data
checks=0
profiles=[]
for n in range(5,9):
    roots,tables,bracket=root_data(n,ZZ)
    one=identity_matrix(ZZ,len(roots))
    basis=[one.column(i) for i in range(len(roots))]
    maps={}
    for label in ('four','eight-short','eight-long'):
        d=matrix(ZZ,len(roots))
        def add(source,target):
            d[roots.index(target),roots.index(source)]+=1
        if label=='four':
            add((n-1,n-2),(n,-n+3))
            add((n-1,n-3),(n,-n+2))
        if label=='eight-short':
            for i in range(2,n+1): add((i,-1),(i,0))
        if label=='eight-long':
            for i in range(2,n): add((i,-1),(n,-i))
        assert d*d==0
        defects=[];imagebrackets=[]
        for i,x in enumerate(basis):
            for j,y in enumerate(basis):
                defect=d*tables[i][j]-bracket(d*x,y)-bracket(x,d*y)
                image=bracket(d*x,d*y)
                assert all(z%2==0 for z in defect)
                assert all(z%2==0 for z in image)
                if label=='four': assert image==0
                if label=='eight-long': assert image==0
                if defect: defects.append([roots[i],roots[j],list(map(int,defect))])
                if image: imagebrackets.append([roots[i],roots[j],list(map(int,image))])
                checks+=3
        maps[label]={'square_zero':True,'derivation_defects':defects,
                    'image_brackets':imagebrackets}
        maps[label]['d']=d
    ds,dl=maps['eight-short']['d'],maps['eight-long']['d']
    assert ds*dl==dl*ds==0
    assert all(bracket(ds*x,dl*y)==bracket(dl*x,ds*y)==0
               for x in basis for y in basis)
    for profile in maps.values(): del profile['d']
    profiles.append({'rank':n,'profiles':maps})
print('PASS',checks,'integral even-defect certificates for repaired (4),(8)')
