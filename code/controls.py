"""Exact controls that break tempting changes to the hypotheses."""
import sympy as s
from pathlib import Path
import json,time
t=time.monotonic();x=s.Symbol('x')
def matrix(n,chords,metropolis=False):
    A=s.zeros(n)
    for i in range(n):A[i,(i+1)%n]=A[(i+1)%n,i]=1
    for u,v,w in chords:A[u,v]=A[v,u]=w
    d=[sum(A.row(i)) for i in range(n)]
    if not metropolis:return s.diag(*[1/a for a in d])*A
    Q=s.zeros(n)
    for i in range(n):
        for j in range(n):
            if i!=j:Q[i,j]=A[i,j]/max(d[i],d[j])
        Q[i,i]=1-sum(Q.row(i))
    return Q
P=matrix(6,[(0,3,1)])
assert (P+s.eye(6)).det()==0
assert (s.eye(6)-P).charpoly(x).as_poly().eval(s.Rational(1,2))==0
assert s.Poly((s.eye(6)-P).charpoly(x).as_expr(),x).count_roots(0,s.Rational(1,2))==2
K=matrix(6,[(0,3,1)],True)
assert s.Poly((s.eye(6)-K).charpoly(x).as_expr(),x).count_roots(0,s.Rational(1,3))==2
assert (s.eye(6)-K).charpoly(x).as_poly().eval(s.Rational(1,3))==0
matching=[(i,i+4,1) for i in range(4)]
M=matrix(8,matching)
p=s.Poly((s.eye(8)-M).charpoly(x).as_expr(),x)
assert p.eval(s.Rational(2,3))==0 and p.count_roots(0,s.Rational(2,3))==2
heavy=matrix(8,[(i,i+4,10) for i in range(4)])
q=s.Poly((s.eye(8)-heavy).charpoly(x).as_expr(),x)
assert q.eval(s.Rational(1,6))==0 and q.count_roots(0,s.Rational(1,6))==2
original=1-s.sqrt(2)/2
assert s.Rational(2,3)>original>s.Rational(1,6)
# Check the degree-corrected variance identity with free symbols.
n,w,z=s.symbols('n w z',positive=True)
assert s.simplify(n+2*w*z*z-(2*w*z)**2/(2*n+2*w)-n*(1+2*w*z*z/(n+w)))==0
out={'single_antipodal_C6':{'ordinary_gap':'1/2','nonlazy_absolute_gap':'0',
      'half_lazy_gap':'1/4','uniform_target_MH_gap':'1/3'},
     'all_antipodal_C8_matching':{'unit_weight_gap':'2/3','weight_10_gap':'1/6',
      'original_gap':'1-sqrt(2)/2'},'symbolic_degree_variance_identity':'passed',
     'seconds':time.monotonic()-t,'passed':True}
Path('evidence/controls.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
print(json.dumps(out,indent=2))
