"""Path B: no matrix library. Two path continuants and Fraction-only Sturm chains."""
from fractions import Fraction as Q
from pathlib import Path
import json, time
t=time.monotonic()
def clean(p):
    p=list(p)
    while len(p)>1 and p[-1]==0:p.pop()
    return p
def add(p,q):
    r=[Q(0)]*max(len(p),len(q))
    for i,a in enumerate(p):r[i]+=a
    for i,a in enumerate(q):r[i]+=a
    return clean(r)
def scale(p,c):return clean([a*c for a in p])
def sub(p,q):return add(p,scale(q,-1))
def mul(p,q):
    r=[Q(0)]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):r[i+j]+=a*b
    return clean(r)
def divmodp(p,q):
    p=clean(p);q=clean(q)
    if q==[0]:raise ZeroDivisionError
    r=[Q(0)]*max(1,len(p)-len(q)+1)
    while p!=[0] and len(p)>=len(q):
        j=len(p)-len(q);c=p[-1]/q[-1];r[j]+=c
        p=sub(p,[Q(0)]*j+scale(q,c))
    return clean(r),clean(p)
def val(p,z):
    r=Q(0)
    for c in reversed(p):r=r*z+c
    return r
def derivative(p):return clean([i*p[i] for i in range(1,len(p))] or [Q(0)])
def variations(chain,z):
    signs=[(v>0)-(v<0) for p in chain if (v:=val(p,z))!=0]
    return sum(a!=b for a,b in zip(signs,signs[1:]))
def roots(p,lo,hi):
    # Both endpoints must be nonroots; repeated roots are counted distinctly.
    assert val(p,lo) and val(p,hi)
    seq=[clean(p),derivative(p)]
    while seq[-1]!=[0]:
        _,r=divmodp(seq[-2],seq[-1])
        if r==[0]:break
        r=scale(r,-1)
        # Positive scaling controls coefficient growth without changing signs.
        seq.append(scale(r,1/abs(r[-1])))
    return variations(seq,lo)-variations(seq,hi)
def path(j):
    if j==0:return [Q(1)]
    a=[Q(1)];b=[Q(2),Q(-2)]
    for _ in range(2,j+1):a,b=b,sub(mul([Q(2),Q(-2)],b),a)
    return b
def characteristic(n,k,w):
    a,b=path(k-1),path(n-k-1)
    ap,bp=path(k-2),path(n-k-2)
    ab=mul(a,b)
    diagonal=sub(sub(mul([2+w,-2-w],ab),mul(ap,b)),mul(bp,a))
    offdiag=add(add(scale(ab,w),a),b)
    p,r=divmodp(sub(mul(diagonal,diagonal),mul(offdiag,offdiag)),ab)
    assert r==[0]
    return p
data=json.loads(Path('evidence/exact_matrix.json').read_text(encoding='utf-8'))
coefficient_checks=0; sturm_checks=0; at=0; below=0
for row in data['records']:
    n,k,w=row['n'],row['k'],Q(row['w'])
    p=characteristic(n,k,w)
    expected=list(reversed([Q(c) for c in row['coefficients']]))
    assert p==expected,(n,k,w)
    coefficient_checks+=len(p)
    lo,hi=map(Q,row['a_interval']);epsilon=Q(1,10**14)
    # Independently verify that the supplied bracket contains the first
    # Dirichlet root; do not trust Path A's identification of the comparison.
    F=path(n//2-1)
    assert roots(F,Q(0),lo-epsilon)==0
    assert roots(F,lo-epsilon,hi+epsilon)==1
    if 2*k==n:
        q,r=divmodp(p,path(n//2-1)); assert r==[0]
        # Exclude the simple root zero analytically, then use nonroot endpoints.
        assert q[0]==0 and q[1]!=0
        q=q[1:]
        assert roots(q,Q(0),hi+epsilon)==0
        at+=1
    else:
        assert p[0]==0 and p[1]!=0
        assert roots(p[1:],Q(0),lo-epsilon)>=1
        below+=1
    sturm_checks+=1
out={'method':'two arc continuants, Schur elimination, custom Fraction polynomial arithmetic and Sturm chains',
     'graphs':len(data['records']),'coefficient_equalities':coefficient_checks,
     'independent_sturm_counts':sturm_checks,'independent_comparison_root_counts':2*sturm_checks,
     'antipodal':at,'strict':below,
     'seconds':time.monotonic()-t,'passed':True}
Path('evidence/exact_paths.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
print(json.dumps(out,indent=2))
