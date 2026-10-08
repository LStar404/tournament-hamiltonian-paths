"""Independent exact checks of cycle/core factorization and core error bounds.

The all-orders theorem is proved in the accompanying note, not by these tests.
"""
from fractions import Fraction as F
from itertools import product
from math import factorial, prod
from random import Random

from centered_permanent_coefficients import carousel, coefficients, triangle_flip
from check_higher_coefficient_envelope import multiply
from derive_centered_c6_symbolic import partitions
from verify_growing_degree_permanent_window import weighted_derangements, partition_pair_mass


def gaussian(s, half_degree):
    n=len(s)
    gram=[[sum(s[i][k]*s[j][k] for k in range(n)) for j in range(n)]
          for i in range(n)]
    power=[[int(i==j) for j in range(n)] for i in range(n)]
    r_log=[F(0)]
    for r in range(1,half_degree+1):
        power=multiply(power,gram)
        r_log.append(F(sum(power[i][i] for i in range(n)),2*n**(2*r)))
    g=[F(1)]
    for m in range(1,half_degree+1):
        g.append(sum(r_log[r]*g[m-r] for r in range(1,m+1))/m)
    return g


def core_coefficients(s, half_degree):
    n=len(s)
    a=coefficients(s,min(2*half_degree,n))
    g=gaussian(s,half_degree)
    c=[F(1)]
    for m in range(1,half_degree+1):
        normalized=(a[2*m]*F(prod(range(n-2*m+1,n+1)),n**(2*m))
                    if 2*m <= n else F(0))
        c.append(normalized-sum(g[r]*c[m-r] for r in range(1,m+1)))
    return a,g,c


def exact_core_majorant(m,n):
    effective_order=F(n,8)
    d=weighted_derangements(2*m,effective_order)
    p=partition_pair_mass(m,effective_order)
    return F(1,2**m)*(d*d-p*p)/(factorial(2*m)*effective_order**(2*m))


def no_pure_cycle_component(v,edges):
    degree=[0]*v
    adjacency=[set() for _ in range(v)]
    for a,b in edges:
        degree[a]+=1;degree[b]+=1
        adjacency[a].add(b);adjacency[b].add(a)
    seen=set()
    for root in range(v):
        if root in seen:
            continue
        stack=[root];component=[];seen.add(root)
        while stack:
            a=stack.pop();component.append(a)
            for b in adjacency[a]-seen:
                seen.add(b);stack.append(b)
        if all(degree[a]==2 for a in component):
            return False
    return True


def direct_core_sum(s,k):
    n=len(s);total=0;diagrams=0
    ps=partitions(k)
    def weight(pi):
        return (-1)**(k-len(pi))*prod(factorial(len(b)-1) for b in pi)
    for pi in ps:
        rows={x:i for i,b in enumerate(pi) for x in b}
        for sigma in ps:
            columns={x:len(pi)+j for j,b in enumerate(sigma) for x in b}
            edges=[(rows[x],columns[x]) for x in range(k)]
            v=len(pi)+len(sigma)
            if not no_pure_cycle_component(v,edges):
                continue
            diagrams+=1
            hom=sum(prod(s[labels[a]][labels[b]] for a,b in edges)
                    for labels in product(range(n),repeat=v))
            total+=weight(pi)*weight(sigma)*hom
    return F(total,factorial(k)*n**k),diagrams


def verify_factorization():
    for n,k in [(3,3),(3,4),(3,6),(5,4)]:
        s=carousel(n)
        direct,diagrams=direct_core_sum(s,k)
        expected=core_coefficients(s,k//2)[2][k//2] if k%2==0 else F(0)
        assert direct==expected,(n,k,direct,expected)
        print('Direct diagram factorization n=',n,'degree=',k,
              'core diagrams=',diagrams,'coefficient=',direct,flush=True)


def verify_coefficient_bounds():
    rng=Random(2026092704)
    for n in (7,9,11,13,15):
        s=carousel(n)
        for trial in range(3):
            if trial:
                for _ in range(n):
                    triangle_flip(s,rng)
            a,g,c=core_coefficients(s,min(n//2,6))
            assert c[1]==0
            if n==13 and trial==0:
                assert c[2]==F(-198,2197)
                assert c[3]==F(-9120,371293)
                assert c[5]==F(770816,10604499373)>0
            for m in range(1,len(c)):
                assert abs(c[m])<=exact_core_majorant(m,n)
                falling=prod(range(n-2*m+1,n+1))
                normalized=a[2*m]*F(falling,n**(2*m))
                convolution=sum(g[m-l]*exact_core_majorant(l,n) for l in range(1,m+1))
                assert abs(normalized-g[m])<=convolution
        print('Exact core and convolution bounds passed n=',n,flush=True)


def verify_constants():
    # Entirely rational checks of the intermediate bounds on representative n,m.
    for n in (257,1025,10001,1000001):
        for m in (1, max(1,__import__('math').isqrt(n)//16)):
            assert 256*m*m<=n
            q=F(16*m,n)
            eta=F(8*m*m,n)/(1-q)+F(32*m**3,9*n)/(1-q)**2
            assert q<=F(1,2)
            assert 2*eta<=F(544*m**3,9*n)<=F(17*m,72)
            assert exact_core_majorant(m,n)<=F(61*m**3,n)*F(2,3)**m
    r=F(2,3)
    assert r*(1+4*r+r*r)/(1-r)**4==222
    assert 4*61*222+48==54216<55000
    print('Rational constant checks passed.',flush=True)


if __name__=='__main__':
    verify_factorization()
    verify_coefficient_bounds()
    verify_constants()
