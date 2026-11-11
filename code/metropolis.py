"""Exact checks for uniform-target MH applied to the chorded weighted walk."""
from pathlib import Path
import sympy as s
import json,time
t=time.monotonic();x=s.Symbol('x');records=[]
for n in range(4,17,2):
    F=s.Poly(s.chebyshevu(n//2-1,1-x),x)
    lo=F.intervals(eps=s.Rational(1,10**14))[0][0][0]-s.Rational(1,10**14)
    for w in [s.Rational(1,2),s.Rational(1),s.Rational(5)]:
        for k in range(2,n//2+1):
            A=s.zeros(n)
            for i in range(n):A[i,(i+1)%n]=A[(i+1)%n,i]=1
            A[0,k]=A[k,0]=w
            d=[sum(A.row(i)) for i in range(n)]
            Q=s.zeros(n)
            for i in range(n):
                for j in range(n):
                    if i!=j:Q[i,j]=A[i,j]/max(d[i],d[j])
                Q[i,i]=1-sum(Q.row(i))
            assert Q==Q.T and all(sum(Q.row(i))==1 for i in range(n))
            p=s.Poly((s.eye(n)-Q).charpoly(x).as_expr(),x,domain=s.QQ)
            assert p.count_roots(0,lo)>=2
            # Separately reconstruct the entire MH Laplacian by edge-form updates.
            old=s.zeros(n)
            for i in range(n):
                b=s.zeros(n,1);b[i]=1;b[(i+1)%n]=-1;old+=b*b.T/2
            b=s.zeros(n,1);b[0]=1;b[k]=-1
            delta=w/(2*(2+w));formula=old+w/(2+w)*b*b.T
            for i in range(n):
                j=(i+1)%n
                if i in (0,k) or j in (0,k):
                    b=s.zeros(n,1);b[i]=1;b[j]=-1;formula-=delta*b*b.T
            assert formula==s.eye(n)-Q
            records.append({'n':n,'k':k,'w':str(w),'gap_strictly_below_cycle':True})
out={'graphs':len(records),'exact_sturm_classifications':len(records),
     'independent_edge_form_matrix_equalities':len(records),'records':records,
     'seconds':time.monotonic()-t,'passed':True}
Path('evidence/metropolis.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k!='records'},indent=2))
