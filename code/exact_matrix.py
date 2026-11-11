"""Path A: full rational random-walk matrices and exact polynomial root counts."""
from pathlib import Path
import time, json
import sympy as s
t=time.monotonic(); x=s.Symbol('x'); records=[]
weights=[s.Rational(1,2),s.Rational(1),s.Rational(5)]
for n in range(4,17,2):
    m=n//2
    F=s.Poly(s.chebyshevu(m-1,1-x),x,domain=s.QQ)
    a_interval=F.intervals(eps=s.Rational(1,10**14))[0][0]
    lo,hi=a_interval
    for w in weights:
        for k in range(2,m+1):
            A=s.zeros(n)
            for i in range(n): A[i,(i+1)%n]=A[(i+1)%n,i]=1
            A[0,k]=A[k,0]=w
            ds=[sum(A.row(i)) for i in range(n)]
            B=s.eye(n)-s.diag(*[1/d for d in ds])*A
            p=s.Poly(B.charpoly(x).as_expr()*s.prod(ds),x,domain=s.QQ)
            assert p.eval(0)==0 and p.diff().eval(0)!=0
            if k==m:
                q,r=s.div(p,F); assert r.is_zero
                # Use a rational strictly above the endpoint, including rational roots.
                upper=hi+s.Rational(1,10**14)
                assert q.count_roots(0,upper)==1 # the simple root zero only
                result='gap equals smallest root of U_(m-1)(1-x)'
            else:
                lower=lo-s.Rational(1,10**14)
                assert p.count_roots(0,lower)>=2 # zero and a strictly smaller positive root
                result='gap strictly below cycle gap'
            records.append({'n':n,'k':k,'w':str(w),'coefficients':[str(c) for c in p.all_coeffs()],
                            'a_interval':[str(lo),str(hi)],'classification':result})
out={'method':'full rational matrices; SymPy charpoly and Sturm root counting',
     'graphs':len(records),'antipodal':sum(r['n']==2*r['k'] for r in records),
     'strict':sum(r['n']!=2*r['k'] for r in records),'records':records,'seconds':time.monotonic()-t}
Path('evidence/exact_matrix.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k!='records'},indent=2))
