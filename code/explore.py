from pathlib import Path
import json, time
import numpy as np
t=time.monotonic(); checked=0; antipodal=0; strict=0; maxerr=0.0
weights=[0.01,0.5,1.0,10.0,1000.0]
rows=[]
for n in range(4,41,2):
    old=1-np.cos(2*np.pi/n)
    for w in weights:
        for k in range(2,n//2+1):
            A=np.zeros((n,n))
            for i in range(n): A[i,(i+1)%n]=A[(i+1)%n,i]=1
            A[0,k]=A[k,0]=w
            d=A.sum(axis=1)
            B=np.eye(n)-A/np.sqrt(np.outer(d,d))
            gap=float(np.linalg.eigvalsh(B)[1]); checked+=1
            if k==n//2:
                antipodal+=1; maxerr=max(maxerr,abs(gap-old))
                assert abs(gap-old)<2e-12
            else:
                strict+=1
                bound=old/(1+2*w/(n+w)*np.cos(np.pi*k/n)**2)
                assert gap<=bound+2e-12 and gap<old
            if n in (4,6,8,10) and w==1:
                rows.append({'n':n,'k':k,'weight':w,'gap':gap,'cycle_gap':old})
out={'kind':'floating-point exploration, not proof','cycle_orders':list(range(4,41,2)),
     'weights':weights,'graphs':checked,'antipodal_cases':antipodal,'strict_cases':strict,
     'max_antipodal_absolute_error':maxerr,'examples':rows,'seconds':time.monotonic()-t}
Path('evidence/exploration.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
print(json.dumps(out,indent=2))
