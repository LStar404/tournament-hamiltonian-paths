"""Exact low-order diagram checks for the kernel-activity linear window.

The general bounds use a combinatorial proof, not these finite tests.
"""
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from math import comb, factorial, prod

from derive_centered_c6_symbolic import partitions
from verify_spectral_core_window import no_pure_cycle_component


@lru_cache(None)
def composition_weight(total, blocks):
    if blocks==0:
        return F(int(total==0))
    return sum((composition_weight(total-d,blocks-1)/d
                for d in range(3,total-3*(blocks-1)+1)), F(0))


def kernel_weight(defect, vertices):
    edges=defect+vertices
    return (F(2**vertices*factorial(2*edges),
              2**edges*factorial(edges)*factorial(vertices))
            *composition_weight(2*edges,vertices))


def kernel_coefficient_bound(edges,defect):
    return sum((kernel_weight(defect,b)*comb(edges-1,b+defect-1)
                for b in range(1,2*defect+1) if b+defect<=edges), F(0))


def direct_absolute_core_counts(k):
    ps=partitions(k)
    weights=[prod(factorial(len(block)-1) for block in pi) for pi in ps]
    maps=[{x:i for i,block in enumerate(pi) for x in block} for pi in ps]
    result=defaultdict(int)
    for i,pi in enumerate(ps):
        r=len(pi)
        for j,sigma in enumerate(ps):
            v=r+len(sigma)
            if v==k:
                continue
            edges=[(maps[i][x],r+maps[j][x]) for x in range(k)]
            if no_pure_cycle_component(v,edges):
                result[k-v]+=weights[i]*weights[j]
    return dict(result)


def polynomial_product(a,b,size):
    out=[F(0)]*size
    for i,x in enumerate(a):
        for j,y in enumerate(b[:size-i]):
            out[i+j]+=x*y
    return out


def first_defect_series(maximum):
    size=maximum+1
    even=[F(int(k>=2 and k%2==0)) for k in range(size)]
    odd=[F(int(k%2==1)) for k in range(size)]
    even2=polynomial_product(even,even,size)
    even3=polynomial_product(even2,even,size)
    even2odd=polynomial_product(even2,odd,size)
    odd3=polynomial_product(polynomial_product(odd,odd,size),odd,size)
    return [F(3,2)*even2[k]+F(5,3)*even3[k]+even2odd[k]+F(2,3)*odd3[k]
            for k in range(size)]


def verify_diagram_counts():
    assert kernel_weight(1,1)==F(3,2)
    assert kernel_weight(1,2)==F(10,3)
    first=first_defect_series(8)
    for k in range(3,9):
        counts=direct_absolute_core_counts(k)
        for defect,weight in counts.items():
            assert F(weight,factorial(k))<=kernel_coefficient_bound(k,defect)
        assert F(counts.get(1,0),factorial(k))==first[k]
        print('Exact absolute core counts degree=',k,'by_defect=',counts,
              'first_defect=',first[k],flush=True)


def verify_activity_constants():
    rho=F(3,4);radius=F(11,10);weight=radius/(rho*(1-rho*radius))
    assert weight==F(176,21)<9
    constant=10**6
    assert 384*3*9**3<constant
    assert 1/(1-radius**2/2)==F(200,79)<3
    q=radius**2/2
    recovery=4*q*(1+q)/(1-q)**3
    assert recovery<64
    for defect in range(1,21):
        activity=sum(kernel_weight(defect,b)*weight**(defect+b)
                     for b in range(1,2*defect+1))
        assert activity<=(constant*defect)**defect
        if defect<=4:
            print('defect=',defect,'kernel_activity=',float(activity),
                  'activity^(1/j)/j=',float(activity)**(1/defect)/defect,flush=True)
    # Uniform geometric summation of (M*j/n)^j for j <= n/(4M).
    assert F(1,1)/(1-F(1,4))**2==F(16,9)<2
    print('Kernel activity and recovery constants verified exactly.',flush=True)


if __name__=='__main__':
    verify_diagram_counts()
    verify_activity_constants()
