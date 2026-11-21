"""Compare exact row endpoints against the conditional angular formula."""
from math import cos,sin,sqrt

def rows(theta, sign):
    c,s=cos(theta),sin(theta)
    return [(c,-sign*s),(s,sign*c)]

def dot(u,v):
    return sum(x*y for x,y in zip(u,v))

def exact_endpoint(sigma,q,r,eps):
    left,right=[],[]
    for u,v in zip(q,r):
        plus=[(x+y)*sqrt(eps*s)/2 for x,y,s in zip(u,v,sigma)]
        minus=[(x-y)*sqrt(eps*s)/2 for x,y,s in zip(u,v,sigma)]
        a,b=dot(plus,plus),dot(minus,minus)
        scale=sqrt((1+sqrt(1+4*a*b))/(2*a))
        left.append([scale*x+y/scale for x,y in zip(plus,minus)])
        right.append([scale*x-y/scale for x,y in zip(plus,minus)])
    return [[dot(x,y) for y in right] for x in left]

for angle in (0.12,0.78,-0.61):
    for phase in (0.31,1.04,-0.57):
        q=rows(angle,1)
        for sign in (1,-1):
            r=rows(phase,sign)
            for sigma in ((3,1),(1.25,1),(9,0.5)):
                eps=1e-8
                w=exact_endpoint(sigma,q,r,eps)
                assert max(abs(w[i][i]-1) for i in range(2)) < 1e-12
                v=(sigma[0]-sigma[1])/sum(sigma)
                if sign>0:
                    t=angle+phase
                    target=v*sin(t)/sqrt(1-v*v*cos(t)**2)
                else:
                    h=[[(x+y)*sqrt(s) for x,y,s in zip(a,b,sigma)] for a,b in zip(q,r)]
                    target=1 if dot(*h)>0 else -1
                assert max(abs(w[0][1]-target),abs(w[1][0]-target)) < 2e-6
print('Finite-scale endpoints agree with both determinant-conditioned limits.')
