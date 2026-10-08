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

## 3. A uniform zeroth-order permanent theorem

This section proves a permanent approximation for general real matrices. Normality, skew-symmetry, and entrywise nonnegativity are not assumptions. The spectral hypothesis concerns singular values, not eigenvalue moduli. The result will therefore remain applicable after a tournament matrix undergoes unequal row and column deletions and subsequent diagonal scaling.

Write $J_n$ for the all-ones matrix, $P_n=J_n/n$, and $\mathbf 1$ for the all-ones vector. The operator norm is the Euclidean operator norm. For a complex matrix $Z$, the notation $Z^*$ means conjugate transpose, and

$$
|Z|=(Z^*Z)^{1/2}.
$$

Thus $|Z|$ is an operator absolute value, not the matrix of entrywise absolute values.

### 3.1. Statement and an explicit error budget

**Theorem (uniform zeroth-order permanent approximation).** Fix $0\le C<\infty$ and $0\le q<1$. Suppose that $E\in\mathbb R^{n\times n}$ satisfies

$$
E\mathbf1=E^{\mathsf T}\mathbf1=0,\qquad
\max_{i,j}|E_{ij}|\le C,\qquad
\|E/n\|_{\mathrm{op}}\le q.
$$

Set $B=E/n$. Uniformly over all such matrices,

$$
\frac{\operatorname{per}(J_n+E)}{n!}
=\det(I-BB^{\mathsf T})^{-1/2}+O_{C,q}(n^{-1}).
$$

The same statement holds with a relative factor $1+O_{C,q}(n^{-1})$ multiplying the determinant factor.

Here and below the determinant square root is the positive square root on the real interval under consideration. The assumptions imply $\|B\|_{\mathrm F}^2\le C^2$. Consequently, the determinant factor is bounded above by a constant depending only on $C,q$, and it is at least one.

We prove the theorem with an explicit, though deliberately conservative, error budget. Define

$$
f(t)=\frac{\operatorname{per}(J_n+tE)}{n!},
\qquad G(t)=\det(I-t^2BB^{\mathsf T})^{-1/2}.
$$

Choose $1<\sigma<R<1/q$, omitting the last restriction when $q=0$. For example, one can use

$$
R=\frac{3+q}{2(1+q)},\qquad \sigma=\frac{1+R}{2}.
$$

Put

$$
W=\max\left\{1,CR+\frac{C^2R^2}{1-Rq}\right\},
\qquad D=710W^3,\qquad
T_1=\frac32W^2+\frac{10}{3}W^3,
$$

$$
\alpha=\min\left\{\frac14,\frac1{16D},\frac{\log\sigma}{2}\right\},
\qquad
\Gamma(r)=\exp\left(\frac{C^2r^2}{2(1-q^2r^2)}\right),
\qquad
\beta=\frac{RC}{1-Rq}.
$$

For the Gaussian coefficient recovery, let

$$
u_\sigma=\frac{\sigma^2C^2}{1-\sigma^2q^2},
\qquad
v_\sigma=\frac{\sigma^2C^2(1+\sigma^2q^2)}
{(1-\sigma^2q^2)^2},
$$

$$
K_G=\frac{\Gamma(\sigma)}{2(1-\alpha)}
\left(u_\sigma^2+v_\sigma\right).
$$

**Explicit error budget.** For every integer $n\ge4/\alpha$,

$$
|f(1)-G(1)|
\le \frac{\Gamma(R)T_1+K_G}{n}
+\frac{8\Gamma(R)D^2}{n^2}
+\frac{R}{R-1}\exp\!\left(\beta\sqrt n-\alpha n\log R\right)
+\sigma\Gamma(\sigma)\exp\!\left(-\alpha n\log\sigma\right).
$$

All parameters on the right depend only on $C,q$ and the chosen radii. The two exponential terms are $o(n^{-1})$. This proves the asserted uniform error once the budget has been established.

### 3.2. Exact coefficient normalization and the centered expansion

Write $f(t)=\sum_{k=0}^n a_kt^k$. Expansion of the permanent by the entries from $E$ gives

$$
a_k=\frac1{(n)_k}
\sum_{\substack{I,J\subseteq[n]\\|I|=|J|=k}}
\operatorname{per}E[I,J],
$$

where $(n)_k=n(n-1)\cdots(n-k+1)$ and $(n)_0=1$. Define

$$
F_k=\frac{(n)_k}{n^k}a_k
=\frac1{k!}
\sum_{\substack{i_1,\ldots,i_k\ \mathrm{distinct}\\
j_1,\ldots,j_k\ \mathrm{distinct}}}
\prod_{\ell=1}^kB_{i_\ell j_\ell},
\qquad
F(t)=\sum_{k=0}^nF_kt^k.
$$

The right-hand sum also makes sense for $k>n$, when it is empty and equals zero. This convention is useful for the formal identities below.

Let $\Pi_k$ be the lattice of set partitions of $[k]$. The indicator that $k$ coordinates are distinct has the standard partition-lattice inclusion-exclusion expansion. The Möbius weight of a block of size $d$ is $(-1)^{d-1}(d-1)!$. Apply this expansion independently to the row and column coordinates in $F_k$. A pair of partitions becomes a bipartite multigraph: its edges carry labels $1,\ldots,k$, its row and column vertices are the partition blocks, and each block of size $d$ has the above weight.

The numerical label of each vertex is summed independently over $[n]$; numerical labels of different vertices are allowed to coincide. If a row vertex has degree one, summing its label gives a column sum of $B$, which is zero. A degree-one column vertex similarly gives a zero row sum. Hence only graphs with all vertex degrees at least two survive.

The connected components in which every vertex has degree two are the pure two-degree components. Their total exponential generating function is $G(t)$. One direct verification uses two independent standard real Gaussian vectors $X,Y$. Wick's formula shows that the coefficient of $t^k$ in

$$
\mathbb E\exp(tX^{\mathsf T}BY)
$$

is exactly the sum over the two pairing partitions on the edge labels. These are the graphs all of whose vertices have degree two. Conditional Gaussian integration, followed by diagonalization of $BB^{\mathsf T}$, gives

$$
\mathbb E\exp(tX^{\mathsf T}BY)
=\mathbb E\exp\!\left(\frac{t^2}{2}X^{\mathsf T}BB^{\mathsf T}X\right)
=\det(I-t^2BB^{\mathsf T})^{-1/2}.
$$

The analytic identity holds for $|t|\|B\|_{\mathrm{op}}<1$ and identifies all its formal coefficients. In particular, $G$ has nonnegative coefficients, and

$$
G(r)\le\Gamma(r)\qquad(0\le r<1/q),
$$

because $-\log(1-x)\le x/(1-x)$ and $\sum_i s_i^2=\|B\|_{\mathrm F}^2\le C^2$, where $s_i$ are the singular values of $B$.

Remove every pure two-degree component from a surviving graph. Call what remains its core, which may be disconnected. If the core has $h$ edges and $v$ vertices, define its excess by $j=h-v$. A nonempty core has $j\ge1$. The labeled component decomposition gives the coefficientwise identity

$$
F(t)=G(t)\left(1+\sum_{j\ge1}C_j(t)\right),
$$

where $C_j$ is the generating series of cores of excess $j$, retaining all Möbius signs and matrix contractions. This is a formal identity. In a fixed degree $k$, only finitely many excesses occur; in fact, a nonempty core contributing to degree $k$ has $j<k$. We never assume that the infinite sum over $j$ converges at a nonzero value of $t$. Above degree $n$, its coefficients cancel to zero because the distinct-coordinate definition of $F_k$ is zero.

### 3.3. Compression and the full excess activity bound

**Lemma (compressed-core activity).** With the notation above,

$$
\|C_j\|_R\le(Dj/n)^j\qquad(j\ge1),
$$

and the first excess satisfies the sharper bound

$$
\|C_1\|_R\le T_1/n.
$$

Here $\|H\|_R=\sum_{k\ge0}|[t^k]H|R^k$.

*Proof.* Compress every maximal path whose internal vertices have degree two. Each resulting edge is a positive-length chain between vertices of degree at least three. Loops, parallel edges, and disconnected compressed graphs are allowed. If $b$ is the number of high-degree vertices and $e$ the number of compressed edges, compression preserves excess and yields

$$
e=b+j,\qquad
2j=\sum_{i=1}^b(d_i-2),\qquad
1\le b\le2j,\qquad e\le3j.
$$

We spell out the counting compensation to avoid hidden symmetry factors. Temporarily label the $b$ high-degree vertices and the $d_i$ half-edges at each vertex. Use these labels to select one reading direction for every chain. A given original edge-labeled core has $b!\prod_i d_i!$ such decorations. Conversely, a decorated half-edge pairing and a list of positive chain lengths determine all chain positions. The original $h$ edge labels can be assigned to these positions in $h!$ ways. Subject to the bipartite parity condition, the internal vertices and their colors are then determined.

After division by the original exponential generating-function factor $h!$ and removal of the decorations, multiplication by the absolute Möbius weights $\prod_i(d_i-1)!$ leaves

$$
\frac1{b!\prod_i d_i}.
$$

This argument includes loops and chain reversals: their two half-edges are already labeled, so no extra direction factor is introduced. Internal degree-two vertices have absolute Möbius weight one. There is no additional chain-length factorial.

Ignore the color restrictions only when taking an upper bound. For fixed $j,b$, the resulting total compensation is

$$
U_{j,b}=
\frac{2^b}{b!}\frac{(2e)!}{2^e e!}
\sum_{\substack{d_1+\cdots+d_b=2e\\d_i\ge3}}
\frac1{d_1\cdots d_b},
\qquad e=b+j.
$$

For a chain of length one the matrix entry is bounded by $C/n$. For a chain of length $\ell\ge2$, first sum its internal labels. Its contraction is an entry of an alternating product of $B$ and $B^{\mathsf T}$. Each endpoint row or column has norm at most $C/\sqrt n$, and all intermediate factors have operator norm at most $q$. Thus the absolute contraction is at most

$$
\frac{C^2}{n}q^{\ell-2}.
$$

Summing over lengths with $R$ weights bounds one chain by $W/n$. Summing the $b$ high-degree labels contributes at most $n^b$. Hence

$$
\|C_j\|_R\le n^{-j}
\sum_{b=1}^{2j}U_{j,b}W^{b+j}.
$$

The number of degree sequences is $\binom{2j-1}{b-1}\le4^j$: write $d_i=3+x_i$ and $\sum_i x_i=2j-b$. Also $\prod_i d_i^{-1}\le3^{-b}$, and the number of pairings is at most $(6j)^{b+j}$. It follows that

$$
\sum_{b=1}^{2j}U_{j,b}W^{b+j}
\le(24jW)^j
\sum_{b=1}^{2j}\frac{(4jW)^b}{b!}.
$$

For $\theta=1/(2W)\le1/2$,

$$
\sum_{b=0}^{2j}\frac{(4jW)^b}{b!}
\le\theta^{-2j}\exp(4jW\theta)
=(2\mathrm e W)^{2j}.
$$

Therefore the activity is at most $(96\mathrm e^2W^3j)^j$, which is bounded by $(710W^3j)^j$. For completeness, $\mathrm e<87/32$ follows by summing its exponential series through degree six and bounding the tail by $8/(7\cdot7!)$; this rational bound gives $96\mathrm e^2<710$.

For $j=1$ only $b=1,2$ are possible. The compensation formula gives

$$
U_{1,1}=\frac32,\qquad U_{1,2}=\frac{10}{3}.
$$

Their chain bounds give $\|C_1\|_R\le T_1/n$. $\square$

### 3.4. A finite linear window and factorial recovery

Use the truncation parameter

$$
M=\lfloor\alpha n\rfloor.
$$

It is unrelated to the main Hamilton-path constant $L$. Put $v_j=(Dj/n)^j$. Whenever $j+1\le M$,

$$
\frac{v_{j+1}}{v_j}
=\frac{D(j+1)}n\left(1+\frac1j\right)^j
\le\frac{\mathrm e D(j+1)}n
\le3D\alpha<\frac12.
$$

Thus, for $n\ge4/\alpha$,

$$
\sum_{j=2}^{M}v_j\le2v_2=\frac{8D^2}{n^2}.
$$

Only excesses $j\le M$ can contribute to degrees at most $M$ in the formal core identity. Positivity of the coefficients of $G$, the activity lemma, and the convolution inequality for weighted coefficient sums therefore give

$$
\sum_{k=0}^{M}|F_k-[t^k]G|R^k
\le\Gamma(R)\left(\frac{T_1}n+\frac{8D^2}{n^2}\right).
$$

This bound concerns a finite coefficient window, not the sum of all excesses evaluated at $R$.

Let $g_k=[t^k]G$ and $r_k=n^k/(n)_k$ for $0\le k\le M$. Since $\alpha\le1/4$,

$$
\log r_k
=\sum_{\ell=0}^{k-1}-\log(1-\ell/n)
\le\frac{k(k-1)}{2n(1-\alpha)}
\le\frac{k^2}n
\le\alpha k.
$$

The choice $\alpha\le(\log\sigma)/2$ implies $r_k\le\sigma^k$, and

$$
0\le r_k-1
\le\frac{k(k-1)}{2n(1-\alpha)}r_k.
$$

Because $a_k=r_kF_k$, we can split

$$
a_k-g_k=r_k(F_k-g_k)+(r_k-1)g_k.
$$

The sum of the first terms is bounded by the preceding $R$-weighted estimate. For the second terms, use the exact Gaussian coefficient moment rather than a coarse coefficient bound:

$$
\sum_{k\ge0}k(k-1)g_k\sigma^k
=\left((t\partial_t)^2-t\partial_t\right)G(t)\big|_{t=\sigma}.
$$

Set $a_i=\sigma^2s_i^2$. Differentiation of
$G(t)=\prod_i(1-t^2s_i^2)^{-1/2}$ yields

$$
\frac{\left((t\partial_t)^2-t\partial_t\right)G(t)}{G(t)}
\bigg|_{t=\sigma}
=\left(\sum_i\frac{a_i}{1-a_i}\right)^2
+\sum_i\frac{a_i(1+a_i)}{(1-a_i)^2}.
$$

The two sums are bounded by $u_\sigma^2$ and $v_\sigma$, respectively. Consequently,

$$
\sum_{k=0}^{M}(r_k-1)g_k\le K_G/n.
$$

Combining the two recovered contributions gives the first two terms of the explicit error budget.

### 3.5. Polarization and the analytic tail

The remaining task is to control the tail of the actual permanent polynomial. A bound that loses the factor $n!/n^n$ would not suffice.

**Lemma (permanent polarization).** For every complex square matrix $Z$,

$$
|\operatorname{per}Z|
\le\sqrt{\operatorname{per}|Z|\,
\operatorname{per}|Z^*|}.
$$

*Proof.* In $(\mathbb C^n)^{\otimes n}$, let

$$
\xi=(n!)^{-1/2}
\sum_{\pi\in S_n}
e_{\pi(1)}\otimes\cdots\otimes e_{\pi(n)}.
$$

Then $\|\xi\|=1$ and
$\langle\xi,Z^{\otimes n}\xi\rangle=\operatorname{per}Z$.
Extend the polar factor in $Z=U|Z|$ to a unitary matrix $U$ if $Z$ is singular. Put $T=|Z|^{\otimes n}$ and $V=U^{\otimes n}$. Cauchy–Schwarz in the positive semidefinite form induced by $T$ gives

$$
|\langle\xi,VT\xi\rangle|
\le\sqrt{\langle V^*\xi,TV^*\xi\rangle
\langle\xi,T\xi\rangle}.
$$

The two factors are $\operatorname{per}(U|Z|U^*)=\operatorname{per}|Z^*|$ and $\operatorname{per}|Z|$. Both are nonnegative because they are diagonal matrix elements of positive semidefinite tensor powers. $\square$

**Lemma (positive semidefinite permanent bound).** If $H$ is Hermitian positive semidefinite with eigenvalues $\lambda_1,\ldots,\lambda_n$, then

$$
\operatorname{per}H\le\frac{n!}{n^n}h_n(\lambda_1,\ldots,\lambda_n),
$$

where $h_n$ is the complete homogeneous symmetric polynomial of degree $n$. If $\lambda_1=1$ and $0\le\lambda_i<1$ for $i\ge2$, then

$$
\operatorname{per}H\le\frac{n!}{n^n}
\prod_{i=2}^n(1-\lambda_i)^{-1}.
$$

*Proof.* Let $Z$ be a circular complex Gaussian vector with covariance $H$. Complex Wick's formula gives
$\operatorname{per}H=\mathbb E\prod_i|Z_i|^2$.
Pointwise AM–GM bounds the product by $n^{-n}\|Z\|^{2n}$. After unitary diagonalization, $\|Z\|^2$ has the distribution of $\sum_i\lambda_i|\zeta_i|^2$, where the $\zeta_i$ are independent standard circular complex Gaussian variables. Their moments satisfy $\mathbb E|\zeta_i|^{2k}=k!$. The multinomial expansion consequently gives

$$
\mathbb E\left(\sum_i\lambda_i|\zeta_i|^2\right)^n
=n!h_n(\lambda_1,\ldots,\lambda_n).
$$

Finally, $h_n(1,\lambda_2,\ldots,\lambda_n)$ is the sum of all monomials in $\lambda_2,\ldots,\lambda_n$ of total degree at most $n$, and is at most the product of their infinite geometric sums. $\square$

For real positive semidefinite inputs, the Gaussian identity and AM–GM comparison above coincide with the ingredients of Han–Niles-Weed [3, Lemmas 4.3–4.4]. The extension to an arbitrary nonnormal permanent in this proof comes from the preceding polarization lemma; we do not use a positive semidefinite theorem directly on a nonnormal matrix.

The centering assumptions give $P_nB=BP_n=0$. On $|t|=R$ they imply

$$
|P_n+tB|=P_n+R(B^{\mathsf T}B)^{1/2},
\qquad
|(P_n+tB)^*|=P_n+R(BB^{\mathsf T})^{1/2}.
$$

Both matrices have eigenvalues $1$ and $Rs_i$ on $\mathbf1^\perp$, including zero singular values as needed. Since $Rq<1$, the two lemmas and the exact identity
$f(t)=(n^n/n!)\operatorname{per}(P_n+tB)$ give

$$
|f(t)|\le\prod_i(1-Rs_i)^{-1}
\le\exp\!\left(\frac{R}{1-Rq}\sum_i s_i\right)
\le\exp(\beta\sqrt n).
$$

The last step uses $\sum_i s_i\le\sqrt n\,\|B\|_{\mathrm F}\le C\sqrt n$. Thus Cauchy's coefficient estimate gives

$$
\sum_{k>M}|a_k|
\le\frac{R}{R-1}
\exp\!\left(\beta\sqrt n-\alpha n\log R\right).
$$

For the Gaussian tail, positivity of its coefficients gives the convenient, slightly weaker bound

$$
\sum_{k>M}g_k
\le \Gamma(\sigma)\sigma^{-M}
\le\sigma\Gamma(\sigma)\exp\!\left(-\alpha n\log\sigma\right).
$$

Together with the finite-window estimate, these are exactly the remaining terms of the explicit error budget. The uniform theorem follows. $\square$

### 3.6. Scope of the theorem

The proof is analytic and combinatorial for arbitrary dimension; its conclusion is not an extrapolation from finite permanent computations. It also does not assert an exact finite-dimensional determinant formula: higher-degree cores generally contribute nonzero corrections.

The hypotheses must be checked after every matrix transformation. In particular, a tournament adjacency matrix need not be doubly centered. Existence of a scaling, uniform entry bounds after scaling, and a fixed singular-value gap are separate requirements. This theorem supplies the permanent approximation once those requirements have been established; it does not, by itself, prove the global Hamilton-path extremal theorem or identify a finite extremal tournament.

## 4. Scaling and nonprincipal deletion

This section proves the analytic interfaces needed to apply the uniform permanent theorem of Section 3 to tournament matrices and to their nonprincipal submatrices. All constants in an estimate with fixed parameters are uniform over the matrices and deleted sets in question. No theorem about the support of an arbitrary nonnegative matrix is used to infer the existence of a scaling.

Write $\mathbf 1_p$ for the all-one vector, $P_p=\mathbf 1_p\mathbf 1_p^{\mathsf T}/p$, and $\Pi_p=I-P_p$. For a matrix $X$, its total mass is $\mathfrak m(X)=\sum_{i,j}X_{ij}$. Matrix norms without a subscript are not used: $\|\cdot\|_{\rm op}$, $\|\cdot\|_F$, and the induced one- and infinity-norms have their usual meanings.

### 4.1. A dimension-uniform local scaling lemma

**Lemma (Local scaling).** Let $X$ be a real $p\times p$ matrix of mass $p$. Put

$$
\alpha=X\mathbf 1_p-\mathbf 1_p,\qquad \beta=X^{\mathsf T}\mathbf 1_p-\mathbf 1_p,\qquad \varepsilon=\max(\|\alpha\|_\infty,\|\beta\|_\infty).
$$

Assume that $|X_{ij}|\le C/p$, that each absolute row and column sum is at most $2$, and that

$$
X_0=X-\frac{\alpha\mathbf 1_p^{\mathsf T}+\mathbf 1_p\beta^{\mathsf T}}p,\qquad E=X_0-P_p
$$

satisfies $|E_{ij}|\le C_0/p$ and $\|E\|_{\rm op}\le q<1$, where $C,C_0,q$ are fixed. Define

$$
L_0=\frac32+C_0+\frac{C_0^2}{1-q},
$$

$$
\varepsilon_0=\min\left\{\frac1{256L_0^2},\frac{1-q}{2(32L_0+2)}\right\}.
$$

If $\varepsilon\le\varepsilon_0$, there are finite real vectors $x,y$ with $\sum_i x_i=\sum_j y_j$ such that $B=\operatorname{diag}(e^x)X\operatorname{diag}(e^y)$ has all row and column sums equal to $1$. Moreover,

$$
\|(x,y)\|_\infty\le4L_0\varepsilon,\qquad |B_{ij}|\le2C/p,\qquad \|B-P_p\|_{\rm op}\le(1+q)/2.
$$

If $X\ge0$, the matrix $B$ is a genuine doubly stochastic scaling and has the same zero support as $X$.

**Proof.** The two marginal error vectors have zero sum, so $X_0$ has unit row and column sums, and $E$ is centered on both sides. Let $u=(\mathbf 1_p,-\mathbf 1_p)$ and $N=uu^{\mathsf T}/(2p)$. The balanced Hessian $\mathsf H_0$ has diagonal blocks $I$ and off-diagonal blocks $X_0,X_0^{\mathsf T}$. Its gauge-fixed inverse can be written explicitly. Set

$$
R_L=(I-EE^{\mathsf T})^{-1},\qquad R_R=(I-E^{\mathsf T}E)^{-1},\qquad O=ER_R.
$$

The four blocks of $(\mathsf H_0+N)^{-1}$ are

$$
M_{LL}=R_L-P_p/4,\qquad M_{RR}=R_R-P_p/4,
$$

$$
M_{LR}=-O-P_p/4,\qquad M_{RL}=-O^{\mathsf T}-P_p/4.
$$

Indeed, on the common constant direction the inverse eigenvalue is $1/2$, on the gauge direction it is $1$, and on the two zero-sum spaces this is the standard block inverse. The dense entry bound gives

$$
|(R_L-I)_{ij}|,\ |(R_R-I)_{ij}|\le\frac{C_0^2}{p(1-q^2)},
$$

$$
|O_{ij}|\le\frac{C_0}{p}+\frac{C_0^2q}{p(1-q^2)}.
$$

For the last bound, separate $O=E+EE^{\mathsf T}ER_R$ and use the Euclidean norms of the endpoint row and column. Consequently both induced one- and infinity-norms of this inverse are at most $L_0$.

Let $\mathsf H_X$ have diagonal blocks $\operatorname{diag}(X\mathbf 1_p)$ and $\operatorname{diag}(X^{\mathsf T}\mathbf 1_p)$, and off-diagonal blocks $X,X^{\mathsf T}$. The difference $\mathsf H_X-\mathsf H_0$ has both induced norms at most $3\varepsilon$. A Neumann series therefore bounds both induced norms of $(\mathsf H_X+N)^{-1}$ by $2L_0$.

Writing $z=(x,y)$ and $g=(\alpha,\beta)$, the balance equations are

$$
0=g+\mathsf H_Xz+\mathcal N_X(z).
$$

Here $\mathcal N_X(z)$ is the concatenation of the row and column sums of $X_{ij}(e^{x_i+y_j}-1-x_i-y_j)$. On a ball $\|z\|_\infty\le R\le1/4$, the absolute margin assumptions imply

$$
\|\mathcal N_X(z)\|_\infty\le8R^2,\qquad \|D\mathcal N_X(z)\|_{\infty\to\infty}\le16R.
$$

All these vectors are perpendicular to $u$. On the gauge subspace $u^\perp$, consider

$$
\mathcal T(z)=-(\mathsf H_X+N)^{-1}(g+\mathcal N_X(z)).
$$

Take $R=4L_0\varepsilon$. The image of the origin has norm at most $R/2$, and the Lipschitz constant is at most $128L_0^2\varepsilon\le1/2$. The map preserves the gauge ball and is contractive, giving the asserted finite potentials. If $\varepsilon=0$, take $z=0$ directly.

Finally, $R\le1/4$ implies the entry bound. The row and column absolute sums give

$$
\|B-X\|_{1\to1},\ \|B-X\|_{\infty\to\infty}\le32L_0\varepsilon.
$$

Since $\|X-X_0\|_{\rm op}\le2\varepsilon$, the second condition in $\varepsilon_0$ proves the centered gap. Positive diagonal factors retain both nonnegativity and the zero support. This proves the lemma.

**Lemma (Euclidean displacement and capacity).** Under the preceding assumptions, suppose in addition that $X\ge0$. Write $\theta_X=\sum_i x_i+\sum_j y_j$ for the total scaling potential. With constants depending only on the fixed density and gap parameters,

$$
\|(x,y)\|_2\le K\|(\alpha,\beta)\|_2,\qquad \|B-X\|_F\le\frac K{\sqrt p}\|(\alpha,\beta)\|_2,
$$

$$
0\le\theta_X\le K\|(\alpha,\beta)\|_2^2.
$$

For a nonnegative matrix $X$ of arbitrary positive mass, normalize $\widetilde X=pX/\mathfrak m(X)$ and apply these conclusions to $\widetilde X$. If $B$ is its scaling, the exact identities are

$$
\theta_X=\theta_{\widetilde X}+p\log\frac p{\mathfrak m(X)},\qquad \operatorname{per}X=e^{-\theta_X}\operatorname{per}B.
$$

In particular, if $\kappa=\mathfrak m(X)-p$, then $\operatorname{per}X\le e^\kappa\operatorname{per}B$. The potential $\theta_X$ itself need not be nonnegative when the mass is not $p$.

**Proof.** The convex potential is

$$
\Phi_X(x,y)=\sum_{i,j}X_{ij}e^{x_i+y_j}-\sum_i x_i-\sum_j y_j.
$$

Its gradient at the origin is $g=(\alpha,\beta)$, and the balancing point is a minimum. If $R=\|(x,y)\|_\infty$, its Hessian along $tz$, $0\le t\le1$, is bounded below by $e^{-2R}$ times the Hessian at $B$. On the gauge space the latter has least eigenvalue at least $1-\|B-P_p\|_{\rm op}$. Thus the whole segment has a fixed lower bound $\lambda>0$. Integrating the gradient gives $\|z\|_2\le\lambda^{-1}\|g\|_2$. The dense bound on $X$ and $|e^{x_i+y_j}-1|\le K|x_i+y_j|$ then give the Frobenius estimate.

Since $\Phi_X(0)=p$ and $\Phi_X(z)=p-\theta_X$, convexity gives $\theta_X\ge0$. Strong convexity gives $\theta_X\le\|g\|_2^2/(2\lambda)$. The nonunit-mass identity follows by absorbing the scalar $p/\mathfrak m(X)$ into the two diagonal potentials. Finally, $p\log(\mathfrak m(X)/p)\le\kappa$ proves the permanent upper bound.

### 4.2. Gaussian deletion and centering

For a real matrix $Z$ with $\|Z\|_{\rm op}<1$, define

$$
\mathcal G(Z)=\det(I-Z^{\mathsf T}Z)^{-1/2}.
$$

The same value is obtained with $ZZ^{\mathsf T}$; padding by zero rows or columns leaves it unchanged.

**Lemma (Gram deletion).** Suppose $\|Z\|_{\rm op}\le q_*<1$. Delete row set $I$ and column set $J$, with remaining sets $R,T$. Then

$$
0\le\log\mathcal G(Z)-\log\mathcal G(Z[R,T])\le\frac{\sum_{i\in I}\|Z_{i,\cdot}\|_2^2+\sum_{j\in J}\|Z_{\cdot,j}\|_2^2}{2(1-q_*^2)}.
$$

For a square remaining matrix $W$ of order $m$, put $u=\mathbf 1_m/\sqrt m$. Then

$$
0\le\log\mathcal G(W)-\log\mathcal G(\Pi_mW\Pi_m)\le\frac{\|W^{\mathsf T}u\|_2^2+\|Wu\|_2^2}{2(1-q_*^2)}.
$$

For any two real matrices of the same dimensions with operator norm at most $q_*$,

$$
|\log\mathcal G(U)-\log\mathcal G(V)|\le\frac{\|U\|_F+\|V\|_F}{2(1-q_*^2)}\|U-V\|_F.
$$

**Proof.** Deleting rows decreases the column Gram matrix by the positive semidefinite matrix $Z^{\mathsf T}(I-P_R)Z$, whose trace is the sum of the deleted row norms squared. For $F(H)=-\tfrac12\log\det(I-H)$ and a positive semidefinite direction $D$,

$$
DF(H)[D]=\tfrac12\operatorname{tr}((I-H)^{-1}D)\le\frac{\operatorname{tr}D}{2(1-q_*^2)}.
$$

Integrate this bound and then delete columns using the row Gram matrix. Projection off each all-one direction gives the centering bound in the same way. For the last assertion, integrate along the segment between the two Gram matrices and use

$$
\|U^{\mathsf T}U-V^{\mathsf T}V\|_*\le(\|U\|_F+\|V\|_F)\|U-V\|_F,
$$

where $\|\cdot\|_*$ is the trace norm. The Gram segment retains the operator gap.

Now let $S$ be a tournament sign matrix of order $n\ge4$, $s=S\mathbf 1_n$, and $\tau=\|s\|_2^2/(n-1)^2$. Put

$$
Y=\frac{S-I}{n-1},\qquad D_n(S)=\det(I-S^{\mathsf T}S/n^2)^{-1/2}.
$$

Skew symmetry and paired singular values imply

$$
\|Y\|_{\rm op}^2\le q_Y^2=\frac{n(n-1)/2+1}{(n-1)^2}<1.
$$

Delete any $t$ rows and any $t$ columns, put $m=n-t$, and set $Z=\Pi_mY[R,T]\Pi_m$. Each row and column of $Y$ has squared Euclidean norm $n/(n-1)^2$. Moreover,

$$
\|Y\mathbf 1_n\|_2^2=\|Y^{\mathsf T}\mathbf 1_n\|_2^2=\tau+\frac n{(n-1)^2},
$$

$$
\|Y\mathbf 1_J\|_2^2,\ \|Y^{\mathsf T}\mathbf 1_I\|_2^2\le\frac{t^2n}{(n-1)^2}.
$$

The preceding lemma therefore gives

$$
0\le\log\mathcal G(Y)-\log\mathcal G(Z)\le\frac{t n/(n-1)^2+2[\tau+n(1+t^2)/(n-1)^2]/m}{1-q_Y^2}.
$$

The full Gram identity is $Y^{\mathsf T}Y=(S^{\mathsf T}S+I)/(n-1)^2$. Its difference from $S^{\mathsf T}S/n^2$ is positive semidefinite and has trace

$$
\mathcal T_n=\frac{2n-1}{n(n-1)}+\frac n{(n-1)^2}.
$$

Hence $0\le\log\mathcal G(Y)-\log D_n(S)\le43/(4n)$. If $m\ge n/2$, the first loss is at most $(24t+18\tau+8)/n$. Both are nonnegative losses from the same full kernel, so

$$
|\log\mathcal G(Z)-\log D_n(S)|\le\frac{24t+18\tau+11}{n}.
$$

For completeness, $1-q_Y^2=n(n-3)/(2(n-1)^2)$. Substitution proves the stated constants directly, using $t\le n/2$. This estimate is finite-dimensional, permits $I\ne J$, and does not assert that the remaining matrix is skew symmetric.

### 4.3. Paired preconditioning and genuine scaling

Fix $a_0<1$ and finite positive parameters $A_0,B_0$. In this subsection suppose

$$
a_i=\frac{s_i}{n-1},\qquad \max_i|a_i|\le a_0,\qquad \tau=\sum_i a_i^2\le A_0\log n,\qquad t\le B_0\log n.
$$

Define

$$
C=\frac{J-I+S}{n-1}=\frac{2A}{n-1},\qquad \ell_i=\frac1{1+a_i},\qquad r_i=\frac1{1-a_i},\qquad g_i=\frac1{1-a_i^2}.
$$

Set $C'=\operatorname{diag}(\ell)C\operatorname{diag}(r)$, $F=C'-C$, and $\nu=\mathfrak m(C')-n$. To compute its mass, write $v_i=a_i/(1-a_i^2)$ and $w_i=a_i^2/(1-a_i^2)$, with $V=\sum_i v_i$ and $W=\sum_i w_i$. Expanding $\ell=\mathbf 1-v+w$ and $r=\mathbf 1+v+w$ gives the exact identity

$$
\nu=\frac{W^2-V^2+W+2w^{\mathsf T}Sv}{n-1}.
$$

Indeed, $\mathbf 1^{\mathsf T}Sv=-(n-1)W$ cancels the first-order mass change. The fixed score bound implies $W\le K\tau$, $|V|\le K\tau$, and $\|v\|_2\le K\sqrt\tau$. Estimating $Sv$ row by row gives

$$
|\nu|\le K\mathcal M_\tau,\qquad \mathcal M_\tau=\frac{\tau+\tau^2}{n}+\frac{\tau^{3/2}}{\sqrt n}=o(1).
$$

The marginal identities are

$$
C'\mathbf 1_n-\mathbf 1_n=\operatorname{diag}(\ell)C(r-\mathbf 1_n),
$$

$$
(C')^{\mathsf T}\mathbf 1_n-\mathbf 1_n=\operatorname{diag}(r)C^{\mathsf T}(\ell-\mathbf 1_n).
$$

Since each row and column of $C$ has Euclidean norm $O(n^{-1/2})$ and $\|C\|_{\rm op}=O(1)$, the infinity marginal error is $O(\sqrt{\tau/n})$, the Euclidean marginal error is $O(\sqrt\tau)$, and direct entrywise estimation gives

$$
\|F\|_F\le K\sqrt{\tau/n}.
$$

Normalize $\widehat C=nC'/\mathfrak m(C')$. Write its row and column errors as $e_i,f_j$, so $\sum e_i=\sum f_j=0$. For arbitrary deleted sets $I,J$ of size $t$, let

$$
X=\frac n m\widehat C[R,T],\qquad \kappa=\mathfrak m(X)-m,\qquad \widetilde X=\frac m{\mathfrak m(X)}X.
$$

The exact deletion mass identity is

$$
\kappa=\frac n m\left[-\sum_{i\in I}e_i-\sum_{j\in J}f_j+\sum_{i\in I,j\in J}\widehat C_{ij}-\frac{t^2}{n}\right].
$$

For each remaining row, the exact marginal error before the last normalization is

$$
(X\mathbf 1_m)_i-1=\frac n m\left[e_i+\frac t n-\sum_{j\in J}\widehat C_{ij}\right],
$$

and there is the corresponding column formula. Consequently,

$$
|\kappa|\le K\left[t\sqrt{\tau/n}+t^2/n\right],
$$

$$
\varepsilon(\widetilde X)\le K(\sqrt{\tau/n}+t/n),\qquad \|g(\widetilde X)\|_2\le K(\sqrt\tau+t/\sqrt n).
$$

Here $g(\widetilde X)$ is the concatenated row and column marginal error, not the vertex weight $g_i$. All entries of $\widetilde X$ are nonnegative and at most $K/m$.

The centered kernel needed by the local scaling lemma is obtained exactly, rather than inferred from a second-singular-value statement. With

$$
\eta=\frac{n^2}{\mathfrak m(C')\mathfrak m(X)}=1+O((t+1)/n),
$$

it is

$$
\Pi_m\widetilde X\Pi_m=\eta\left[Z+\Pi_mF[R,T]\Pi_m\right].
$$

The leading value of $\eta$ is $n/m$ when $t>0$; it has not been discarded. Compression preserves the operator norm bound for $Y$, and the displayed Frobenius estimate controls the second term. Thus the centered operator norm is at most $1/\sqrt2+o(1)$, uniformly under the fixed parameters. Its entries are $O(1/m)$, and the marginal infinity error tends to zero. The local scaling lemma applies for all sufficiently large $n$ and constructs a genuine doubly stochastic matrix $B_X$.

The Euclidean displacement lemma yields

$$
\|B_X-\widetilde X\|_F\le K(\sqrt{\tau/n}+t/n).
$$

Combining this with the sharper centered bound, the centered norm of $B_X$ is still $1/\sqrt2+o(1)$; for example, it is eventually at most $4/5$. The entries remain bounded by $K/m$.

Finally, apply the Gaussian deletion estimate to $Z$, then the logarithmic Lipschitz estimate to the preconditioning, normalization, and true-scaling perturbations. Since $B_X-P_m=\Pi_mB_X\Pi_m$, this gives

$$
|\log\mathcal G(B_X-P_m)-\log D_n(S)|\le K\left[\sqrt{\tau/n}+(t+1)/n\right].
$$

The term $\tau/n$ from centering is absorbed by $\sqrt{\tau/n}$. In particular, distinct deleted row and column sets require no square-root deletion loss.

### 4.4. Permanent restoration for nonprincipal submatrices

**Lemma (Paired nonprincipal permanent bound).** Under the fixed-parameter assumptions of Section 4.3, define $\Gamma=\prod_i(1-a_i^2)\le e^{-\tau}$. For all sufficiently large $n$ and all deleted sets $I,J$ of size $t$, with $m=n-t$,

$$
\operatorname{per}A[R,T]\le e^{-1}D_n(S)\Gamma\left(\prod_{i\in I}\ell_i\right)\left(\prod_{j\in J}r_j\right)\frac{m!}{2^m}\exp(K\mathcal R_{\tau,t}),
$$

where

$$
\mathcal R_{\tau,t}=\mathcal M_\tau+\sqrt{\tau/n}+(t+1)/n+t\sqrt{\tau/n}+t^2/n.
$$

The constant depends only on $a_0,A_0,B_0$ and the constants in the uniform permanent theorem.

**Proof.** The true scaling just constructed satisfies its density and centered-gap hypotheses, so the theorem of Section 3 gives

$$
\operatorname{per}B_X=\frac{m!}{m^m}\mathcal G(B_X-P_m)(1+O(1/m)).
$$

The row and column factors restore exactly as

$$
\prod_{i\in R}(1+a_i)\prod_{j\in T}(1-a_j)=\Gamma\prod_{i\in I}\ell_i\prod_{j\in J}r_j.
$$

Deleting rows restores the $\ell$ factors, and deleting columns restores the $r$ factors; these are not interchangeable. The complete scalar identity is

$$
\operatorname{per}A[R,T]=\Gamma\prod_{i\in I}\ell_i\prod_{j\in J}r_j\left[\frac{m(n-1)\mathfrak m(C')}{2n^2}\right]^m e^{-\theta_X}\operatorname{per}B_X.
$$

After restoring $m!/m^m$, the remaining scalar is

$$
\frac{m!}{2^m}(1-1/n)^m\left[\frac{\mathfrak m(C')}{n}\right]^m.
$$

Its logarithm differs from that of $e^{-1}m!/2^m$ by $O((t+1)/n+|\nu|)$. The capacity bound gives $e^{-\theta_X}\le e^\kappa$. Substituting the mass, Gaussian, and zero-order errors proves the claimed exponent. Every comparison is uniform over $I,J$, and none requires $I=J$.

### 4.5. The small-score two-sided approximation

**Lemma (Small-score permanent approximation).** Let $d=\|S\mathbf 1_n\|_\infty=o(\sqrt n)$. Fix $B_0<\infty$, delete any $t\le B_0\log n$ rows and any $t$ columns, and put $m=n-t$. Uniformly over these choices,

$$
\operatorname{per}A[R,T]=e^{-1}D_n(S)\frac{m!}{2^m}\left[1+O_{B_0}\left(\frac{(d+t+1)^2}{n}\right)\right].
$$

This is an asymptotic statement, not a finite-order guarantee for every small matrix. The constants are uniform whenever $(d+t+1)^2/n$ is in a fixed sufficiently small range; in the stated regime this quantity tends to zero.

**Proof.** No paired preconditioning is needed. Set $C=2A/(n-1)$ and $X=(n/m)C[R,T]$. Its full row and column errors are $s_i/(n-1)$ and $-s_i/(n-1)$. The exact mass and marginal formulas from Section 4.3 therefore give

$$
|\kappa|=O(t(d+t)/n),\qquad \varepsilon(X)=O((d+t)/n),\qquad \|g(X)\|_2=O((d+t)/\sqrt n).
$$

Normalize $\widetilde X=mX/\mathfrak m(X)$. Its density and centered gap are fixed, and the local scaling lemma applies. The Euclidean displacement and capacity estimates give

$$
\|B_X-\widetilde X\|_F=O((d+t)/n),\qquad 0\le\theta_{\widetilde X}=O((d+t)^2/n).
$$

The nonunit-mass correction then implies $|\theta_X|=O((d+t)^2/n)$. Also $\tau\le nd^2/(n-1)^2$. The finite deletion estimate, the normalization factor, and the true-scaling perturbation show

$$
|\log\mathcal G(B_X-P_m)-\log D_n(S)|=O((d+t+1)^2/n).
$$

The exact restoration, now without score products, is

$$
\operatorname{per}A[R,T]=\left[\frac{m(n-1)}{2n}\right]^m e^{-\theta_X}\operatorname{per}B_X.
$$

Apply the uniform permanent theorem and use $(1-1/n)^m=e^{-1}\exp(O((t+1)/n))$. All logarithmic errors are $O((d+t+1)^2/n)=o(1)$, so exponentiating them proves the stated relative approximation. The resulting short-minor estimate is the input used in Section 6 to obtain the actual Hamilton-path approximation; neither spectral switching nor matrix scaling is being asserted to preserve path counts.

## 5. The global reduction

We prove the upper bound uniformly over all tournaments, without assuming regularity or balance. Throughout this section $K$ denotes a positive constant which may increase from one occurrence to the next. All constants become absolute after fixing the degree thresholds below.

For an $n$-vertex tournament write $A$ for its adjacency matrix, $S=A-A^{\mathsf T}$, $s=S\mathbf 1$, and

$$
\mathcal E=\|s\|_2^2,\qquad V=\mathcal E/4,\qquad
\tau=\mathcal E/(n-1)^2,\qquad
\mu_n=n!/2^{n-1}.
$$

We use $D_n(S)$ and $\rho_n(S)=D_n(S)\det(I+S/n)$ as defined previously. The spectral cap lemma gives

$$
1\le \rho_n(S)\le C_*.
$$

### 5.1. The precise analytic interface and the long-subset tail

We first record the particular conclusion of the paired nonprincipal permanent bound that is needed here. Fix $b<1$ and constants $A_0,B_0$. For a tournament core of order $N$, put $a=S\mathbf 1/(N-1)$ and $\tau=\sum_i a_i^2$. Suppose

$$
\max_i|a_i|\le b,\qquad
\tau\le A_0\log N,\qquad
|I|=|J|=t\le B_0\log N.
$$

Define $\ell_i=(1+a_i)^{-1}$, $r_i=(1-a_i)^{-1}$,

$$
\Gamma=\prod_i(1-a_i^2),\qquad
\mathcal M_\tau=\frac{\tau+\tau^2}{N}+\frac{\tau^{3/2}}{\sqrt N}.
$$

For the complementary row and column sets $R,T$, the bound is

$$
\operatorname{per}A[R,T]\le
e^{-1}D_N(S)\Gamma
\left(\prod_{i\in I}\ell_i\right)
\left(\prod_{j\in J}r_j\right)
\frac{(N-t)!}{2^{N-t}}\exp(\varepsilon_{\tau,t}),
$$

$$
\varepsilon_{\tau,t}\le K\left[
\mathcal M_\tau+\sqrt{\tau/N}+\frac{t+1}{N}
+t\sqrt{\tau/N}+\frac{t^2}{N}\right].
$$

The constants are uniform over the core and over different row and column deletion sets. This is a statement about the actual permanent: the local scaling lemma and the uniform zeroth-order permanent lemma have already been applied. In particular, no unproved scaling assertion or additional permanent asymptotic will be used in this section.

Use the positive convolution from Section 2, based on [1], and its determinant and generic permanent bounds:

$$
H(T)=\sum_{U\subseteq[n]}\det(I+A[U])\operatorname{per}A[U^c],
$$

$$
\det(I+A[U])\le h_k,\qquad
\operatorname{per}A[U^c]\le K\sqrt{n-k+1}\frac{(n-k)!}{2^{n-k}},
\qquad k=|U|.
$$

Recall $w_k=2^kh_k/k!$. Set

$$
k_n=\left\lceil\frac{4\log n}{\log\log n}\right\rceil.
$$

For every fixed $c>0$ and nonnegative integer $j$, $\sum_k c^k k^j w_k$ converges. Indeed,

$$
\log(c^kw_k)=-\frac{k}{2}\log k+O_c(k).
$$

Consequently $\sum_{k>k_n}c^kw_k=n^{-2+o(1)}$. Summing the generic permanent bound over subsets yields the uniform estimate

$$
\frac{1}{\mu_n}
\sum_{|U|>k_n}\det(I+A[U])\operatorname{per}A[U^c]
\le K\sqrt{n+1}\sum_{k>k_n}w_k=o(1/n).
$$

We call the terms with $|U|\le k_n$ short terms. All following estimates concern these terms unless specified otherwise.

### 5.2. Exclusion of high score variance

We require a quantitative form of the Brégman bound [2]. Let $Q$ be a tournament of order $m$, with outdegrees $d_i$ and degree variance $V(Q)=\sum_i(d_i-(m-1)/2)^2$. Then

$$
\operatorname{per}A_Q\le
K\sqrt{m+1}\frac{m!}{2^m}\exp\left(-\frac{V(Q)}{8m^2}\right).
$$

Here and below the zero-order matrix is handled by its permanent being one. If any $d_i=0$, the asserted bound for positive order is immediate. Otherwise put $f(k)=\log(k!)/k$ for positive integers. A direct calculation gives, for $k\ge2$,

$$
2f(k)-f(k-1)-f(k+1)
=\frac{2[\log k-f(k-1)]-k\log(1+1/k)}{k(k+1)}.
$$

Arithmetic–geometric mean applied to $1,\ldots,k-1$ gives $\log k-f(k-1)\ge\log2$. Also $(1+1/k)^k<e<3$. The numerator is therefore at least $\log(4/3)\ge1/4$. On the degree interval $[1,m-1]$, the piecewise-linear interpolation of $f(k)+k^2/(8m^2)$ is concave. Jensen's inequality at the mean $\eta=(m-1)/2$ gives

$$
\sum_i f(d_i)
\le m\widetilde f(\eta)-\frac{V(Q)}{8m^2}+\frac{1}{32m},
$$

where $\widetilde f$ is linear interpolation. The last term accounts for a half-integer mean and is unnecessary for an integer mean. Stirling's formula gives

$$
\exp(m\widetilde f(\eta))\le K\sqrt{m+1}\frac{m!}{2^m}.
$$

Brégman's row-degree bound now proves the variance estimate.

For a deletion set $U$ of size $k$, each surviving centered degree changes by at most $k/2$. The removed squared deviations sum to at most $kn^2/4$. Applying Cauchy–Schwarz to the cross term therefore gives

$$
V(T-U)\ge V(T)-\frac{kn^2}{4}-k\sqrt{nV(T)}.
$$

If $V(T)\ge16n^2\log n$, then uniformly for $k\le k_n$,

$$
V(T-U)\ge(1-o(1))V(T).
$$

The variance penalty for every short permanent is at most $n^{-2+o(1)}$. Its factor $\sqrt n$ is harmless; summing the determinant weights shows that the normalized short contribution is at most $n^{-3/2+o(1)}$. Together with the long-subset tail,

$$
V(T)\ge16n^2\log n\quad\Longrightarrow\quad
H(T)/\mu_n=o(1/n),
$$

uniformly over this class.

### 5.3. Exclusion of extreme degrees by nonprincipal block expansion

Suppose henceforth that $V(T)<16n^2\log n$. Define the exceptional set

$$
F=\left\{i:\frac{d_i^+}{n-1}\notin[1/20,19/20]\right\},
\qquad f=|F|,\qquad M=T-F,\qquad N=n-f.
$$

An exceptional vertex contributes at least a fixed positive multiple of $n^2$ to $V(T)$, so $f=O(\log n)$. A nonexceptional full score has absolute value at most $0.9(n-1)$. Deleting $F$ changes it by at most $f$, whence, uniformly for all sufficiently large $n$,

$$
\max_i|(S_M\mathbf1)_i/(N-1)|<0.95,\qquad
\tau_M=O(\log n).
$$

The same bounds, with the same fixed constants, hold after deleting any further short subset of core vertices.

We first bound $\operatorname{per}A_T$. Use the paired core weights $\ell,r$ in Section 5.1. Their total displacement satisfies

$$
\sum_{i\in M}|\ell_i-1|+\sum_{i\in M}|r_i-1|
\le K\sqrt{N\log n}.
$$

For $x\in F$ let $q_x=N^{-1}|\{j\in M:x\to j\}|$. Then $q_x$ is within $O(f/n)$ of $[0,1/20]\cup[19/20,1]$. Weighted cross-neighbor sums are bounded by $N(q_x+\beta)$ and $N(1-q_x+\beta)$, where $\beta=O(\sqrt{\log n/n})$. Put

$$
u_x=2(q_x+\beta),\qquad v_x=2(1-q_x+\beta).
$$

Uniformly in $x$, we can choose

$$
u_xv_x\le c_n=19/100+o(1),\qquad u_x,v_x\le L_n=2+o(1).
$$

Decompose a permutation contributing to the permanent by its edges inside $F$. If there are $s$ such edges, their row set $R$ and column set $C$ each have size $s$, and each of the two cross directions has $t=f-s$ edges. The core row and column deletion sets $I,J$ each have size $t$, but need not agree. The exact four-block expansion is

$$
\operatorname{per}A_T
=\sum_{s=0}^{f}
\sum_{\substack{R,C\subseteq F\\|R|=|C|=s}}
\sum_{\substack{I,J\subseteq M\\|I|=|J|=f-s}}
\operatorname{per}A[R,C]\,
\operatorname{per}A[F\setminus R,J]\,
\operatorname{per}A[I,F\setminus C]\,
\operatorname{per}A[M\setminus I,M\setminus J].
$$

Every contributing permutation is classified exactly once. In the core bound, a deleted row supplies $\ell_i$, and a deleted column supplies $r_j$. Absorbing these factors into the corresponding cross matchings and dropping the distinctness restrictions bounds the two cross sums by

$$
N^{2t}2^{-2t}
\left(\prod_{x\notin R}u_x\right)
\left(\prod_{y\notin C}v_y\right).
$$

The internal permanent is at most $s!$. Upon division by $n!/2^n$, the exact remaining factorial and power-of-two factor is

$$
2^sN^{2t}\frac{(N-t)!}{(N+f)!}
=\left(\frac2N\right)^s\exp(O(f^2/N)).
$$

This factor includes the contributions from the two cross directions and the core order; none are omitted.

If $h=|R\cap C|$, the paired product satisfies

$$
\left(\prod_{x\notin R}u_x\right)
\left(\prod_{y\notin C}v_y\right)
\le c_n^{f-2s}L_n^{2s}(c_n/L_n^2)^h
\le c_n^{f-2s}L_n^{2s}.
$$

The first inequality follows by counting the vertices carrying both factors, one factor, or no factor. It remains valid when $f-2s$ is negative. The permanent error from Section 5.1 is $o(1)$ uniformly over $t\le f=O(\log n)$; we can discard its factor $\Gamma\le1$. Since $\binom fs^2s!\le f^{2s}/s!$, the complete sum gives

$$
\frac{\operatorname{per}A_T}{n!/2^n}
\le(1+o(1))e^{-1}D_N(S_M)c_n^f
\exp(O(f^2/N))
\exp\left(\frac{2L_n^2f^2}{c_n^2N}\right).
$$

The displayed extra exponents are $o(1)$. All these statements remain uniform after a short core subset $U$ is deleted. The core Gaussian factor then changes by $\exp(O(|U|/n))$: deleting rows and columns of $S_M/N$ costs $O(|U|/n)$ in logarithm by the Gaussian deletion lemma, and changing normalization from $N$ to $N-|U|$ has the same cost.

In the path convolution, the fraction of $k$-subsets meeting $F$ is at most $fk/n$. The generic permanent bound therefore makes their entire normalized short contribution at most

$$
K\frac{f}{\sqrt n}\sum_k k w_k=o(1).
$$

For subsets contained in the core, restore the falling factorial and sum positive principal minors. For any core order $N\le n$, the rank-one determinant identity gives

$$
\det\left(I_N+\frac2n(I_N+A_M)\right)
\le2e\det(I_N+S_M/N).
$$

To see this, extract $(1+1/n)^N\le e$. The remaining all-one rank-one factor is at most $1+N/(n+1)<2$, since the real quadratic form of the inverse of $I+S_M/(n+1)$ is at most the squared vector norm. Finally, the skew-frequency determinant product increases as its scale increases from $1/(n+1)$ to $1/N$.

For short subsets the falling-factorial restoration contributes $\exp(O(k_n^2/n))=1+o(1)$. Because $c_n<1/4$ eventually, the preceding uniform estimates imply

$$
\frac{H(T)}{\mu_n}
\le(1/4)^f\rho_N(S_M)+o(1)
\le C_*/4+o(1)<1,\qquad f\ge1.
$$

The long tail was already $o(1/n)$. Thus tournaments with exceptional vertices cannot maximize $H(T)$ for all sufficiently large $n$, since averaging over random tournaments gives $P(n)\ge\mu_n$. Only a uniform $o(1)$ error is needed for this exclusion; no $O(1/n)$ estimate for this class is asserted.

### 5.4. Retaining the full score penalty in the remaining class

We are left with tournaments satisfying

$$
\max_i|a_i|\le0.9,\qquad
a=s/(n-1),\qquad \tau=\sum_i a_i^2\le K\log n.
$$

Their paired product obeys

$$
\Gamma=\prod_i(1-a_i^2)\le e^{-\tau}.
$$

For completeness, put $\omega_i=a_i^2/(1-a_i^2)$ and $v_i=a_i/(1-a_i^2)$. The paired preconditioned matrix $C'=\operatorname{diag}(\ell)\,(2A/(n-1))\,\operatorname{diag}(r)$ has total mass $n+\nu$, with the exact identity

$$
\nu=\frac{(\sum_i\omega_i)^2-(\sum_iv_i)^2+\sum_i\omega_i+
2\omega^{\mathsf T}Sv}{n-1}.
$$

Using $\sum_i a_i=0$, the fixed bound on $|a_i|$, and row Euclidean norms $\sqrt{n-1}$ of $S$, this gives $|\nu|\le K\mathcal M_\tau$. These are the scores of the whole graph, not a newly selected core.

For a principal deletion set $U$ of size $k\le k_n$, Section 5.1 gives

$$
\operatorname{per}A[U^c]\le
e^{-1}D_n(S)\Gamma
\left(\prod_{i\in U}g_i\right)
\frac{(n-k)!}{2^{n-k}}\exp(R_\tau+R_{\tau,k}),
$$

$$
g_i=(1-a_i^2)^{-1}\le G:=100/19,
$$

$$
R_\tau\le K[\mathcal M_\tau+\sqrt{\tau/n}+1/n],\qquad
R_{\tau,k}\le K[k\sqrt{\tau/n}+(k+k^2)/n].
$$

The common factor $\Gamma$ must be retained while errors are summed. Define nonnegative coefficients

$$
c_k=(2/n)^k\sum_{|U|=k}\det(I+A[U])\prod_{i\in U}g_i.
$$

They satisfy $c_0=1$ and $c_k\le G^kw_k$. Restoring the falling factorial contributes

$$
\log\frac{n^k}{(n)_k}=O(k^2/n),\qquad k\le k_n.
$$

Put $\delta_n=\sqrt{\tau/n}+1/n$ and $r_k=R_{\tau,k}+\log(n^k/(n)_k)$. Uniformly over $\tau\le K\log n$, we have $0\le r_k\le K\delta_n(k+k^2)$ and $\max_{k\le k_n}r_k=o(1)$, taking the upper error budgets nonnegative. Thus

$$
\sum_{k\le k_n}c_ke^{r_k}
\le\sum_{k=0}^{n}c_k+
K\delta_n\sum_{k\ge0}G^kw_k(k+k^2)
\le\left(\sum_{k=0}^{n}c_k\right)e^{K\delta_n}.
$$

The last inequality uses $\sum_k c_k\ge1$ and convergence of the indicated fixed moments. Consequently the normalized short-path sum is at most

$$
\frac{e^{-1}D_n(S)\Gamma}{2}
e^{R_\tau+K\delta_n}
\det\left(I+\frac2n\operatorname{diag}(g)(I+A)\right).
$$

This is a relative error estimate with $\Gamma$ outside the complete sum.

We now remove the weights without losing the score penalty. Let $W=I+(2/n)(I+A)$ and $\Delta=(2/n)\operatorname{diag}(g-1)(I+A)$. The symmetric part of $W$ is at least $I$, so $\|W^{-1}\|_{\rm op}\le1$. Since every row of $I+A$ has Euclidean norm at most $\sqrt n$ and $\sum_i(g_i-1)\le K\tau$, decomposition into rank-one row matrices gives the nuclear-norm estimate

$$
\|\Delta\|_*\le K\tau/\sqrt n.
$$

The determinant inequality $|\det(I+E)|\le\exp(\|E\|_*)$ therefore implies

$$
\det(W+\Delta)\le\det(W)e^{K\tau/\sqrt n}.
$$

Both determinants are positive: $W$ has positive-definite symmetric part, and the weighted determinant has a principal-minor expansion with positive coefficients. The unweighted rank-one bound from Section 5.3, now with $N=n$, is $\det(W)\le2e\det(I+S/n)$.

Combining these inequalities and adding only the long-subset tail gives the uniform score-sensitive bound

$$
\frac{H(T)}{\mu_n}\le
\rho_n(S)\exp\left\{-\tau+
K\left[\frac{1+\tau+\tau^2}{n}
+\frac{\tau^{3/2}+\tau}{\sqrt n}+\sqrt{\tau/n}\right]\right\}
+o(1/n).
$$

For $\tau\le K\log n$, all polynomial terms except the constant $1/n$ can consume at most $\tau/4$ for sufficiently large $n$. The remaining square-root term is bounded by Young's inequality:

$$
K\sqrt{\tau/n}\le\tau/4+K^2/n.
$$

The entire exponent is consequently at most $-\tau/2+K/n$. The spectral cap now gives

$$
H(T)/\mu_n\le C_*e^{K/n}+o(1/n)=C_*+O(1/n).
$$

### 5.5. Completion of the uniform upper bound

The three classes cover every tournament. High-variance tournaments have normalized path count $o(1/n)$; the low-variance tournaments with exceptional vertices have count strictly below one; all remaining tournaments satisfy the preceding $C_*+O(1/n)$ bound. It follows that

$$
\boxed{P(n)\le\bigl(C_*+O(1/n)\bigr)\mu_n.}
$$

The proof uses no regularity assumption on an extremizer and no claim about the attainability of the relaxed packed spectrum. All estimates are uniform for sufficiently large $n$; they do not specify an effective starting order.

## 6. Small-score paths and the lower bound

**Small-score path theorem.** Let $T$ range over tournament sequences with $d=\|S\mathbf1\|_\infty=o(\sqrt n)$. Uniformly in this range,

$$
\frac{H(T)}{\mu_n}=\rho_n(S)+O\left(\frac{(d+1)^2}{n}\right).
$$

Proof. Use the small-score permanent approximation of Section 4 for every principal deletion $|U|=k\le k_n$. Since $d+k_n+1=o(\sqrt n)$, it applies uniformly. Restoring the falling factorial $(n)_k$, the positive path convolution gives

$$
\frac{H(T)}{\mu_n}
=\frac{e^{-1}D_n(S)}2
\sum_{k\le k_n}\left(\frac2n\right)^k
\sum_{|U|=k}\det(I+A[U])
+O\left(\frac{(d+1)^2}{n}\right).
$$

The error has this rate, without an additional logarithmic factor, because it is bounded by a fixed constant times

$$
\frac1n\sum_{k\ge0}w_k(d+k+1)^2
=O\left(\frac{(d+1)^2}{n}\right).
$$

The falling-factorial error contributes $O(n^{-1}\sum k^2w_k)$, and the actual long-path terms are $o(n^{-1})$ by Section 2. Extending the displayed short generating sum to all $k$ costs $n^{-2+o(1)}$, since its coefficients are bounded by $w_k$. Thus

$$
\frac{H(T)}{\mu_n}
=\frac{e^{-1}D_n(S)}2
\det\left(I+\frac2n(I+A)\right)
+O\left(\frac{(d+1)^2}{n}\right).
$$

Put $u=\mathbf1/\sqrt n$ and $Q=S/(n+1)$. The rank-one determinant lemma yields

$$
\det\left(I+\frac2n(I+A)\right)
=(1+1/n)^n\det(I+Q)
\left(1+\frac n{n+1}u^{\mathsf T}(I+Q)^{-1}u\right).
$$

Skew symmetry implies

$$
u^{\mathsf T}(I+Q)^{-1}u=u^{\mathsf T}(I-Q^2)^{-1}u,
$$

and its difference from one in absolute value is at most

$$
\|Qu\|_2^2\le\frac{d^2}{(n+1)^2}.
$$

Also $(1+1/n)^n=e(1+O(n^{-1}))$, while replacing $S/(n+1)$ by $S/n$ changes the log determinant by $O(n^{-1})$, using the bounded sum of normalized squared frequencies. Consequently,

$$
\det\left(I+\frac2n(I+A)\right)
=2e\det(I+S/n)\left(1+O(n^{-1}+d^2/n^2)\right).
$$

Substitution proves the theorem.

For odd $n$, define the carousel tournament $\mathrm{Car}_n$ on residues modulo $n$ by $i\to i+j$ for $1\le j\le(n-1)/2$. It is regular, so $d=0$. For even $n$, let $\mathrm{Car}_n$ be a one-vertex deletion from $\mathrm{Car}_{n+1}$; then $d=1$.

The odd carousel symbol matrix is signed-permutation similar to $T_n^0$. One explicit construction is to conjugate $T_n^0$ by the diagonal signs $(-1)^i$, $0\le i<n$, and reorder its indices as $0,2,\ldots,n-1,1,3,\ldots,n-2$. An edge check gives the carousel orientation. Restrict the inverse signed conjugation and reordering to an even-order one-vertex deletion: the resulting transformed matrix is $T_n^0$ on the remaining ordered indices. The actual even carousel is not being called transitive. Hence both parities have

$$
\rho_n(S_{\mathrm{Car}_n})
=r_n:=\frac{(n+1)^n+(n-1)^n}{(n+i)^n+(n-i)^n}.
$$

Dividing numerator and denominator by $n^n$, Taylor expansion of $(1+z/n)^n$ at the four fixed values $z=1,-1,i,-i$ gives

$$
r_n=\frac{\cosh1}{\cos1}+O(n^{-1})=L+O(n^{-1}).
$$

Therefore $H(\mathrm{Car}_n)/\mu_n=L+O(n^{-1})$ for both parities, and

$$
P(n)\ge(L-O(n^{-1}))\mu_n.
$$

Together with Section 5, this completes the proof of the main theorem. The signed similarity used here preserves only the spectral factor; it is not claimed to preserve Hamiltonian path counts.

## 7. Verification, scope and limitations

### 7.1 What was checked

The proof is an all-order analytic argument. Exact finite checks were used to detect normalization, sign and scalar-restoration errors, not to extrapolate an asymptotic theorem. The accompanying audit archive records fresh completed runs of the following checks:

- 23630 rational convex-packing checks and 276 integer phase-order checks; all 33867 labelled tournaments of orders 1 through 6 for the spectral-ratio bound, and all 1099 of orders 1 through 5 for a rational operator-cap check.
- 96 exact core-activity checks, 8381 falling-factorial checks, and 16 exact nonsymmetric, nonnormal rank-two permanent examples through order 384.
- 267 rational general-matrix deletion checks and 267 centring checks; 693 tournament Gaussian comparisons, 635 scalar-restoration checks, 56 exact permanent examples and 14 exact path examples.
- 1111 graph examples for reduction identities, with 36746 score-deletion checks, 36746 rank-one generating-determinant bounds, 579 weighted generating identities, 24 complete four-block decompositions and 112 exceptional-product checks.

All four reruns exited normally with code zero. Separate floating-point scaling examples are diagnostic only. The archive includes the original exact records and their scope descriptions, and the three component proof-audit reports.

For the constants, rational enclosures give

$$
2.855957892565113<L<2.855957892565114,
$$

$$
2.857401177672316<C_*<2.857401177672317.
$$

The leading-constant relative gap lies between $0.000505359379058$ and $0.000505359379059$. None of these checks certifies a finite threshold for the main theorem.

### 7.2 What is not proved

The present argument does not prove $\rho_n(S)\le r_n$ for every tournament, and therefore does not prove $P(n)=(L+O(n^{-1}))\mu_n$. The convex packing uses only the maximal singular value and total squared mass; its relaxed spectrum need not be realizable.

The theorem also does not prove that a finite extremizer is regular or balanced, that a carousel is a unique or even a finite-order extremizer, or that an exact formula exists for arbitrary $P(n)$. The small-score approximation alone cannot eliminate all other graphs; that is why the variance and exceptional-vertex reductions are required.

The $O(n^{-1})$ path approximation does not identify the coefficient of the first correction term. Nor do finite diagnostic examples make its constants effective. These questions are intentionally outside the claims of this manuscript.

### 7.3 Research and authorship disclosure

This manuscript was prepared with AI assistance for proof reconstruction, cross-checking, translation and exact-arithmetic diagnostics. The component audits were independent reconstructions within that AI-assisted workflow, not external human peer review or a formal proof-assistant certification. Author review and independent specialist review are recommended before submission. Existing results are attributed below; no claim of novelty follows merely from the internal audit.

## References

[1] John Irving and Mohamed Omar. Revisiting the Rédei-Berge Symmetric Functions via Matrix Algebra. The Electronic Journal of Combinatorics 32(4) (2025), P4.43. DOI: 10.37236/13841. [Original article](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v32i4p43/pdf/).

[2] Noga Alon. The Maximum Number of Hamiltonian Paths in Tournaments. [Author's manuscript](https://web.math.princeton.edu/~nalon/PDFS/hamilton.pdf). In particular, Lemma 2.1 supplies the Brégman permanent bound used here.

[3] Yanjun Han and Jonathan Niles-Weed. Approximate independence of permutation mixtures. arXiv:2408.09341. [Version 2, including Lemmas 4.3-4.4](https://arxiv.org/html/2408.09341v2). Cited as a comparison for Gaussian and positive-semidefinite permanent tools, not as a black-box formula for arbitrary nonsymmetric matrices.

[4] Bo Deng, Xueliang Li, Bryan Shader and Wasin So. On the Maximum Skew Spectral Radius and Minimum Skew Energy of Tournaments. [Author manuscript](https://cfc.nankai.edu.cn/_upload/article/files/09/3a/890a6a5c4660ae2350ac183d2dfa/cb663bb2-4ff4-476f-8047-50514a7780a5.pdf). DOI: 10.1080/03081087.2017.1357676.

[5] Peter McCullagh. An asymptotic approximation for the permanent of a doubly stochastic matrix. Journal of Statistical Computation and Simulation 84(2) (2014), 404-414. DOI: 10.1080/00949655.2012.712122. [arXiv:1205.5723](https://arxiv.org/abs/1205.5723).

[6] N. C. Wormald. Tournaments with many Hamilton cycles. [Author's preprint](https://users.monash.edu.au/~nwormald/papers/hamtourn.pdf).

[7] Ehud Friedgut and Jeff Kahn. On the Number of Hamiltonian Cycles in a Tournament. Combinatorics, Probability and Computing 14(5-6) (2005), 769-781. [DOI: 10.1017/S0963548305006863](https://doi.org/10.1017/S0963548305006863).
