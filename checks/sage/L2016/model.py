from sage.all import matrix, vector

def root_data(n, field):
    labels = list(range(-n, n+1))
    pos = {x:i for i,x in enumerate(labels)}
    def unit(i,j):
        m=matrix(field,2*n+1)
        m[pos[i],pos[j]]=1
        return m
    roots=[(i,j) for i in range(1,n+1) for j in range(-i+1,i)]
    basis=[]
    for i,j in roots:
        if j>0:
            m=unit(i,j)-unit(-j,-i)
        elif j<0:
            m=-unit(i,j)+unit(-j,-i)
        else:
            m=unit(i,0)-2*unit(0,-i)
        basis.append(m)
    def coordinates(m):
        v=vector(field,[(1 if j>=0 else -1)*m[pos[i],pos[j]] for i,j in roots])
        assert sum((v[k]*basis[k] for k in range(len(roots))),matrix(field,2*n+1))==m
        return v
    tables=[[coordinates(a*b-b*a) for b in basis] for a in basis]
    def bracket(x,y):
        return sum((x[i]*y[j]*tables[i][j] for i in range(len(roots))
                    for j in range(len(roots)) if x[i] and y[j]),vector(field,len(roots)))
    return roots, tables, bracket
