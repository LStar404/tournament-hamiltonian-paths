# Constant-factor bounds for Hamiltonian paths in tournaments

Xingchen Liu

Independent Researcher

lxc-em5158@outlook.com

8 October 2026

Research manuscript. The arguments have undergone an AI-assisted internal proof audit, not external peer review. No claim of publication priority or a complete determination of the extremal tournaments is made.

## Abstract

Let $P(n)$ be the maximum number of directed Hamiltonian paths in a tournament on $n$ vertices, and put $\mu_n=n!/2^{n-1}$. We develop a uniform permanent approximation for bounded, doubly centred kernels with a fixed singular-value gap, together with a local scaling construction and a linear Gaussian-determinant error bound for different row and column deletions. These ingredients permit a full-graph reduction without assuming that an extremal tournament is regular or balanced. The resulting bounds are

$$
(L-O(n^{-1}))\mu_n\le P(n)\le(C_*+O(n^{-1}))\mu_n,
$$

where $L=\cosh(1)/\cos(1)$ and

$$
C_*=\frac{3\pi^4+4\pi^2-32}{\pi^4+4\pi^2-32}.
$$

Numerically, $L=2.855957892565\ldots$ and $C_*=2.857401177672\ldots$, leaving a relative leading-constant gap of about $0.050536\%$. The upper constant follows from the maximal skew singular value and a convex spectral relaxation. The lower bound is obtained from near-regular carousel tournaments of both parities. The paper does not determine the exact finite extremal value, the first correction coefficient of path counts, or uniqueness of an extremal tournament.

Keywords: tournament; directed Hamiltonian path; permanent; matrix scaling; skew spectrum; Gaussian determinant.

## 1. Introduction and main result

A tournament is an orientation of the complete graph. Write $H(T)$ for the number of vertex permutations $(v_1,\ldots,v_n)$ satisfying $v_j\to v_{j+1}$ for every $j<n$. These are directed paths and are not counted modulo reversal. We study

$$
P(n)=\max_{|V(T)|=n}H(T),\qquad \mu_n=\frac{n!}{2^{n-1}}.
$$

The random-tournament expectation is $\mu_n$, so $P(n)\ge\mu_n$. Alon's permanent method [2] gives a polynomial-factor upper bound; subsequent work of Friedgut and Kahn [7] improves related counting bounds. Wormald [6] studies constant-factor improvements and discusses the candidate constant approximately $2.855958$. We cite these historical results without asserting that this brief literature comparison settles current publication priority.

Determinantal approximations to dense permanents have important precedent, in particular McCullagh's work [5]. Since the precise uniformity needed here includes nonsymmetric kernels and matrices with zero support, Section 3 supplies a complete argument for its own assumptions rather than importing an unverified approximation. Likewise, the maximum skew spectral-radius comparison is known [4]; we give a short proof sufficient for our application, and do not import its equality classification.

**Main theorem.** There exist absolute constants $K<\infty$ and $n_0$ such that, for every integer $n\ge n_0$,

$$
(L-K/n)\mu_n\le P(n)\le(C_*+K/n)\mu_n,
$$

where

$$
L=\frac{\cosh1}{\cos1},\qquad
a_*=\frac4{\pi^2},\qquad
C_*=\frac{1+a_*}{1-a_*}\frac{3/2-a_*}{1/2+a_*}.
$$

The constants implicit in this theorem are not presently optimized or evaluated into a usable finite-order threshold. In particular, the numerical difference between $C_*$ and $L$ is not a finite-$n$ error certificate.

The proof has three analytic components. A coefficient-level partition expansion and an independently controlled tail give a uniform zeroth-order permanent formula. A quantitative local scaling construction makes that formula applicable to the actual nonnegative matrices arising in path counting, including nonprincipal minors. Finally, a positive determinant-permanent convolution separates high score variance, exceptional degrees and the remaining dense class. The score penalty is retained until all short-subset errors have been summed. No unproved regularity of an extremal tournament is assumed.

## 2. Notation and exact preliminary identities

### 2.1 Matrices, scores and spectral factors

The adjacency matrix $A$ has zero diagonal and $A_{ij}=1$ precisely when $i\to j$. Put

$$
S=A-A^{\mathsf T},\qquad 2A=J-I+S,\qquad s=S\mathbf1.
$$

Here $I$ is the identity, $J=\mathbf1\mathbf1^{\mathsf T}$ and $\mathbf1$ is the all-ones column vector. If $d_i^+$ is the outdegree, then $s_i=2d_i^+-(n-1)$ and $\sum_i s_i=0$. We use

$$
\mathcal E=\|s\|_2^2,\qquad d=\|s\|_\infty,\qquad
a=\frac{s}{n-1},\qquad \tau=\|a\|_2^2.
$$

The normalized scores $a$ and $\tau$ are defined for $n\ge2$. A regular odd-order tournament has $s=0$. A balanced even-order tournament has $s_i\in\{-1,1\}$. Neither condition is assumed for arbitrary tournaments in the upper-bound proof.

For a vertex set $U$, the notation $A[U]$ denotes a principal submatrix. For possibly different row and column sets $R,C$, write $A[R,C]$. The determinant and permanent of the empty matrix are both one. The permanent is

$$
\operatorname{per}M=\sum_{\pi\in\mathfrak S_m}\prod_{i=1}^m M_{i,\pi(i)}.
$$

Write $\pm i\lambda_j$ for the nonzero eigenvalue pairs of $S$, and add zero frequencies when convenient. Define

$$
x_j=\frac{\lambda_j^2}{n^2},\qquad
D_n(S)=\det(I-S^{\mathsf T}S/n^2)^{-1/2},
$$

$$
\rho_n(S)=D_n(S)\det(I+S/n)=\prod_j\frac{1+x_j}{1-x_j}.
$$

Skew singular values occur in pairs, and $\|S\|_F^2=n(n-1)$, whence

$$
\sum_jx_j=\frac{n-1}{2n},\qquad \|S/n\|_{\rm op}^2\le\frac{n-1}{2n}<\frac12.
$$

Thus $D_n$ and $\rho_n$ are positive and bounded by absolute constants. In particular,

$$
D_n(S)=\det(I+iS/n)^{-1}.
$$

The notation $D_n$ in this paper is a spectral factor, not the integer determinant bounds used in separate finite-order computations.

### 2.2 The positive path convolution

**Path convolution lemma.** For every tournament,

$$
H(T)=\sum_{U\subseteq V(T)}\det(I+A[U])\operatorname{per}A[U^c].
$$

This is the tournament specialization of Irving and Omar's Proposition 2 [1]. To make the complement convention explicit, the complement adjacency matrix for a general digraph is $\overline A=J-A$, including possible diagonal loops. For a tournament, $\overline A=I+A^{\mathsf T}$, not merely $A^{\mathsf T}$.

Here is also a generating-function verification. Put $X=\operatorname{diag}(z_1,\ldots,z_n)$. The generating series of all walks, with each vertex occurrence carrying its variable, is

$$
1+\mathbf1^{\mathsf T}(I-XA)^{-1}X\mathbf1
=\frac{\det(I+X\overline A)}{\det(I-XA)}.
$$

The equality is the rank-one determinant lemma. Taking the coefficient of $z_1\cdots z_n$ selects exactly the Hamiltonian paths. The principal-minor expansion of the numerator and the multilinear coefficient identity for the reciprocal determinant give

$$
H(T)=\sum_U\det\overline A[U]\operatorname{per}A[U^c].
$$

Using $\overline A[U]=I+A[U]^{\mathsf T}$ proves the assertion.

If $k=|U|$, the symmetric part of $I+A[U]$ is $(I+J)/2$, which is positive definite. Therefore its determinant is positive. Hadamard's inequality and the average outdegree give

$$
0<\det(I+A[U])\le h_k,\qquad h_k=\left(\frac{k+1}{2}\right)^{k/2}.
$$

Set $h_0=1$ and

$$
w_k=\frac{2^k h_k}{k!}.
$$

For every fixed $c>0$ and fixed nonnegative integer $r$,

$$
\sum_{k\ge0}k^r c^k w_k<\infty.
$$

Indeed, Stirling's formula gives $\log(c^kw_k)=-(k/2)\log k+O_c(k)$. With

$$
k_n=\left\lceil\frac{4\log n}{\log\log n}\right\rceil
$$

for sufficiently large $n$, it follows that $\sum_{k>k_n}c^kw_k=n^{-2+o(1)}$.

The Brégman degree bound and degree balancing [2], followed by Stirling, give a universal constant $C$ with

$$
\operatorname{per}A_T\le C\sqrt{m+1}\,\frac{m!}{2^m}
$$

for every tournament of order $m$, including $m=0$ after enlarging $C$. Section 5 also proves the stronger variance-penalized form. Consequently, the contribution to the path convolution from $|U|>k_n$, divided by $\mu_n$, is at most

$$
\frac C2\sqrt{n+1}\sum_{k>k_n}w_k
=n^{-3/2+o(1)}=o(n^{-1}).
$$

This bound is uniform in the tournament.

### 2.3 A spectral cap and convex packing

**Spectral cap lemma.** Every tournament symbol matrix satisfies

$$
\|S\|_{\rm op}\le\cot\left(\frac{\pi}{2n}\right)<\frac{2n}{\pi},
\qquad \rho_n(S)\le C_*.
$$

Proof. The matrix $iS$ is Hermitian with symmetric spectrum, so its largest eigenvalue is $\|S\|_{\rm op}$. For any complex vector $z$, apply a signed permutation simultaneously to $z$ and $S$ so that the nonzero coordinate phases lie in $[0,\pi)$ in increasing order. Zero coordinates are placed arbitrarily. Then $c_{ij}=\operatorname{Im}(\overline z_i z_j)\ge0$ for $i<j$. If $T_n^0$ has upper-triangular entries one, then

$$
z^*iSz=-2\sum_{i<j}S_{ij}c_{ij}
\le2\sum_{i<j}c_{ij}=z^*(-iT_n^0)z.
$$

Taking Rayleigh maxima gives $\|S\|_{\rm op}\le\|T_n^0\|_{\rm op}$. To compute the latter, the eigenvalue equations for adjacent rows give $(\lambda-1)v_i=(\lambda+1)v_{i+1}$. Their geometric ratio $r=(\lambda-1)/(\lambda+1)$ satisfies $r^n=-1$ by the first-row equation. Thus the eigenvalues are $i\cot((2j-1)\pi/(2n))$, $1\le j\le n$, and the claimed norm follows. The final strict inequality uses $\tan u>u$.

Hence $0\le x_j\le a_*$ and $\sum_jx_j<1/2$. The function

$$
\phi(x)=\log\frac{1+x}{1-x}
$$

is increasing and convex on $[0,1)$. Transferring mass between two interior coordinates toward a capped coordinate and a remainder cannot decrease $\sum_j\phi(x_j)$. Appending zeros if necessary, and increasing the total mass to $1/2$, the relaxed maximum has coordinates $a_*,1/2-a_*,0,\ldots$, because $1/4<a_*<1/2$. Exponentiation gives exactly $C_*$. This is a relaxation; no tournament realization of the packed vector is asserted. The norm comparison is consistent with the established result [4]. This proves the lemma.

The same eigenvalue calculation also yields

$$
\det(I+zT_n^0)=\frac{(1+z)^n+(1-z)^n}{2}.
$$

These identities concern spectra, not path counts: a transitive tournament itself has only one Hamiltonian path.
