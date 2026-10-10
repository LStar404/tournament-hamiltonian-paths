# Constant-factor bounds for Hamiltonian paths in tournaments

Xingchen Liu and Xiangyu Ye

Independent Researchers

lxc-em5158@outlook.com

8 October 2026; revised 11 October 2026

## Abstract

Let $P(n)$ be the maximum number of directed Hamiltonian paths in an $n$-vertex tournament, and let $\mu_n=n!/2^{n-1}$ be the random-tournament expectation. We prove

$$
(L-O(n^{-1}))\mu_n\le P(n)\le(C_*+O(n^{-1}))\mu_n,
$$

where

$$
L=\frac{\cosh1}{\cos1}=2.855957892565\ldots,
\qquad
C_*=\frac{3\pi^4+4\pi^2-32}{\pi^4+4\pi^2-32}
=2.857401177672\ldots.
$$

The upper bound holds for every tournament. Its proof starts from a positive determinant–permanent identity for the path count. A uniform permanent approximation and quantitative matrix scaling convert this identity into a spectral estimate, while degree variance and a multiplicative score penalty control irregular tournaments. A skew spectral-radius bound then gives $C_*$ by convex optimization. Carousel tournaments of both parities give the lower bound. The relative gap between the two leading constants is about $0.050536\%$. A companion Lean development proves the main theorem and the uniform small-score path approximation.

Keywords: tournament; directed Hamiltonian path; permanent; matrix scaling; skew spectrum.

## 1. Introduction and main result

How many directed Hamiltonian paths can a tournament contain? For an $n$-vertex tournament $T$, let $H(T)$ count the orderings $(v_1,\ldots,v_n)$ for which $v_j\to v_{j+1}$ for every $j<n$. Paths are counted as directed vertex sequences. Define

$$
P(n)=\max_{|V(T)|=n}H(T),\qquad \mu_n=\frac{n!}{2^{n-1}}.
$$

Each ordering forms a directed path in a uniformly random tournament with probability $2^{-(n-1)}$. Thus $\mathbb E H(T)=\mu_n$ and $P(n)\ge\mu_n$. The question is how much a suitable orientation can improve on this expectation.

Alon [2] proved $P(n)=O(n^{3/2})\mu_n$ using permanents. Friedgut and Kahn's Hamiltonian-cycle bound [7], combined with the path-to-cycle construction in [2, Proposition 2.5], gives $P(n)=O(n^{3/2-\xi})\mu_n$, where $\xi\approx0.2507$. Wormald [6, Theorem 5] obtained $P(n)>2.85588\mu_n$ for infinitely many $n$ and conjectured a limiting ratio approximately $2.855958$. Our result places the maximum path count between two close constant multiples of $\mu_n$.

**Theorem 1.1 (Main result).** There are absolute constants $K\ge0$ and $n_0\ge2$ such that, for every integer $n\ge n_0$,

$$
(L-K/n)\mu_n\le P(n)\le(C_*+K/n)\mu_n,
$$

where

$$
L=\frac{\cosh1}{\cos1},\qquad
a_*=\frac4{\pi^2},\qquad
C_*=\frac{1+a_*}{1-a_*}\frac{3/2-a_*}{1/2+a_*}.
$$

The main task is the upper bound for arbitrary tournaments. Brégman's inequality controls a permanent from its row sums, but even for regular tournaments its bound leaves a factor of order $\sqrt n$ at the natural permanent scale $n!/2^n$. Removing this loss requires the relations between different rows imposed by the tournament orientation.

We use the determinant–permanent path identity of Irving and Omar [1]. Its summands are nonnegative, and only small deleted vertex sets contribute appreciably. This reduces the counting problem to accurate estimates for permanents of large submatrices. For nearly regular tournaments, these estimates yield a spectral factor $\rho_n(S)$, where $S=A-A^{\mathsf T}$ is the skew adjacency matrix. Section 2.3 explains its origin before the technical proofs.

Three points require quantitative control. First, the permanent approximation must hold uniformly for a whole class of matrices, rather than only for each fixed coefficient degree. Second, the actual adjacency submatrices must be scaled to have equal row and column sums; different deleted row and column sets arise when exceptional vertices are separated. Third, arbitrary tournaments must be reduced to a class in which this scaling is available. In that class, the restored scaling factors contain a negative score exponent that absorbs the approximation errors.

We present the counting argument first. Section 2 establishes the exact identities and the spectral bound. Section 3 proves the upper bound using a precisely stated permanent estimate, and Section 4 proves the small-score formula and the carousel lower bound. Sections 5 and 6 then prove the permanent and scaling estimates. The permanent argument builds on the determinantal viewpoint of McCullagh [5] and Gaussian permanent tools used by Han and Niles-Weed [3]; the skew spectral-radius comparison is given in Deng, Li, Shader and So [4]. We include the versions and proofs needed here. Appendix A records the correspondence with the companion formalization.

