"""Exact partition-mass bound and checks for a growing-degree spectral window.

This verifies the algebra and finite examples. The all-n proof is in the note;
in particular, no finite test is used to assert a bound on the untruncated tail.
"""
from decimal import Decimal, localcontext
from fractions import Fraction as F
from math import comb, factorial, prod
from random import Random

from centered_permanent_coefficients import carousel, coefficients, triangle_flip
from check_higher_coefficient_envelope import envelope


def weighted_derangements(k, n):
    d = [1, 0]
    for j in range(2, k+1):
        d.append((j-1)*(d[-1]+n*d[-2]))
    return d[k]


def partition_pair_mass(m, n):
    return factorial(2*m)//(2**m*factorial(m))*n**m


def exact_error_bound(m, n):
    k = 2*m
    d, p = weighted_derangements(k,n), partition_pair_mass(m,n)
    return F(d*d-p*p, factorial(k)*prod(range(n-k+1,n+1)))


def gaussian_coefficients(s):
    n = len(s)
    h = envelope(s)
    return [sum(h[m-j]*F(-1,2*n)**j/factorial(j) for j in range(m+1))
            for m in range(len(h))]


def verify_exact_partition_polynomials():
    # Independent permutation-by-cycle-type enumeration, not the recurrence.
    def cycle_types(k, minimum=2):
        if k == 0:
            yield ()
        for length in range(minimum,k+1):
            for rest in cycle_types(k-length,length):
                yield (length,)+rest
    for n in (7,31,1000):
        for k in range(2,15):
            total = 0
            for lengths in cycle_types(k):
                denominator = prod(lengths)
                for length in set(lengths):
                    denominator *= factorial(lengths.count(length))
                total += factorial(k)//denominator*n**len(lengths)
            assert total == weighted_derangements(k,n)
    print('Weighted permutation recurrence independently verified.',flush=True)


def verify_numeric_examples():
    rng=Random(2026092703)
    for n in (7,9,11,13,15):
        s=carousel(n)
        for trial in range(3):
            if trial:
                for _ in range(n):
                    triangle_flip(s,rng)
            a=coefficients(s,min(n,12))
            g=gaussian_coefficients(s)
            for m in range(1,min(n//2,6)+1):
                k=2*m
                rising_factor=F(n**k,prod(range(n-k+1,n+1)))
                actual=abs(a[k]-rising_factor*g[m])
                assert actual <= exact_error_bound(m,n)
        print('Exact coefficient error checks passed, n=',n,flush=True)


def verify_exponential_majorant():
    with localcontext() as context:
        context.prec=80
        for n,m in [(7,1),(7,3),(11,5),(100,10),(1000,10),
                    (10**6,10),(10**6,50),(10**9,100)]:
            q=F(2*m,n)
            eta=F(m*m,n)/(1-q)+F(4*m**3,9*n)/(1-q)**2
            d,p=weighted_derangements(2*m,n),partition_pair_mass(m,n)
            actual_ratio=Decimal(d)/Decimal(p)
            exponential=(Decimal(eta.numerator)/Decimal(eta.denominator)).exp()
            assert actual_ratio <= exponential
            if n >= 10**6:
                old=F(factorial(2*m)*n**(2*m-1),prod(range(n-2*m+1,n+1)))
                new=exact_error_bound(m,n)
                quotient=old/new
                decimal_quotient=Decimal(quotient.numerator)/Decimal(quotient.denominator)
                print('n=',n,'half_degree=',m,'new_error_bound=',float(new),
                      'old/new=',format(decimal_quotient,'.6E'),flush=True)
    print('Exponential majorant numerical checks passed.',flush=True)


if __name__=='__main__':
    verify_exact_partition_polynomials()
    verify_numeric_examples()
    verify_exponential_majorant()
