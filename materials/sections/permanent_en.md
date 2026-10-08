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
