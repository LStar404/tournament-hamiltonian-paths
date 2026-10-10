## 2. Counting identities and the spectral factor

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

The normalized scores $a$ and $\tau$ are defined for $n\ge2$. A regular odd-order tournament has $s=0$, and a balanced even-order tournament has $s_i\in\{-1,1\}$. Thus $d$ measures the largest vertex imbalance, while $\tau$ measures its total squared size after normalization.

For a vertex set $U$, the notation $A[U]$ denotes a principal submatrix. For possibly different row and column sets $R,C$, write $A[R,C]$. The determinant and permanent of the empty matrix are both one. The permanent is

$$
\operatorname{per}M=\sum_{\pi\in\mathfrak S_m}\prod_{i=1}^m M_{i,\pi(i)}.
$$

For a real matrix $M$, its singular values are the square roots of the eigenvalues of $M^{\mathsf T}M$. Their maximum is $\|M\|_{\rm op}$, and the sum of their squares is $\|M\|_F^2=\sum_{i,j}|M_{ij}|^2$. For the skew matrix $S$, write $\pm i\lambda_j$, with $\lambda_j>0$, for the nonzero eigenvalue pairs, and add zero frequencies when convenient. Each $\lambda_j$ occurs twice among the singular values. Define

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

### 2.2 The positive path convolution

**Lemma 2.1 (Path convolution).** For every tournament,

<a id="eq-path-convolution"></a>

$$
H(T)=\sum_{U\subseteq V(T)}\det(I+A[U])\operatorname{per}A[U^c].
\tag{2.1}
$$

The permanent of an adjacency matrix counts directed cycle covers. The convolution [Equation (2.1)](#eq-path-convolution) converts those counts on complementary vertex sets into a path count. It is the tournament specialization of Irving and Omar's Proposition 2 [1], with complement adjacency matrix $\overline A=J-A=I+A^{\mathsf T}$; the complement includes its diagonal entries.

Here is also a generating-function verification. Put $X=\operatorname{diag}(z_1,\ldots,z_n)$. The generating series of all walks, with each vertex occurrence carrying its variable, is

$$
1+\mathbf1^{\mathsf T}(I-XA)^{-1}X\mathbf1
=\frac{\det(I+X\overline A)}{\det(I-XA)}.
$$

The equality is the rank-one determinant lemma. Taking the coefficient of $z_1\cdots z_n$ selects exactly the Hamiltonian paths. For the denominator, the formal identity $\det(I-XA)^{-1}=\exp(\sum_{r\ge1}\operatorname{tr}((XA)^r)/r)$ shows that a squarefree coefficient counts disjoint directed cycle covers, hence a permanent. Combining this with the principal-minor expansion of the numerator gives

$$
H(T)=\sum_U\det\overline A[U]\operatorname{per}A[U^c].
$$

Using $\overline A[U]=I+A[U]^{\mathsf T}$ proves the assertion.

If $k=|U|$, the symmetric part of $I+A[U]$ is $(I+J)/2$, which is positive definite. Every real eigenvalue is therefore positive, and nonreal eigenvalues occur in conjugate pairs, so its determinant is positive. The squared row norms are $1+d_i^+(T[U])$, with mean $(k+1)/2$. Hadamard's inequality followed by arithmetic–geometric mean therefore gives

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

Brégman's bound in the form [2, Lemma 2.1], together with degree balancing [2, Corollary 2.3] and Stirling's formula, gives a universal constant $C$ with

$$
\operatorname{per}A_T\le C\sqrt{m+1}\,\frac{m!}{2^m}
$$

for every tournament of order $m$, including $m=0$ after enlarging $C$. Lemma 3.2 proves a variance-penalized version of this bound. Consequently, the contribution to the path convolution from $|U|>k_n$, divided by $\mu_n$, is at most

$$
\frac C2\sqrt{n+1}\sum_{k>k_n}w_k
=n^{-3/2+o(1)}=o(n^{-1}).
$$

This bound is uniform in the tournament. We call $|U|\le k_n$ the short terms. Their accurate estimation is the only permanent problem left by the convolution.

### 2.3 Why the spectral factor appears

The following calculation explains the quantity to be bounded. Suppose for the moment that the maximum score satisfies $d=o(\sqrt n)$. Lemma 6.4 will show that, for a short deletion $|U|=k$,

$$
\operatorname{per}A[U^c]
=e^{-1}D_n(S)\frac{(n-k)!}{2^{n-k}}
\left(1+O\left(\frac{(d+k+1)^2}{n}\right)\right).
$$

The normalization satisfies $((n-k)!/2^{n-k})/\mu_n=2^{k-1}/(n)_k$. Thus inserting the leading term in Lemma 2.1 gives the normalized sum

$$
\frac{e^{-1}D_n(S)}2
\sum_{|U|\le k_n}\frac{2^{|U|}}{(n)_{|U|}}\det(I+A[U]),
$$

where $(n)_k=n(n-1)\cdots(n-k+1)$. Replacing $(n)_k$ by $n^k$ in the short sum and adding the negligible tail produces errors estimated in Section 4.1. The resulting full sum has the exact principal-minor identity

$$
\sum_U(2/n)^{|U|}\det(I+A[U])
=\det\left(I+\frac2n(I+A)\right).
$$

Since $2A=J-I+S$, the rank-one term $J$ contributes asymptotically a factor two, and the scalar term contributes $e$. More precisely, the small-score assumption gives

$$
\det\left(I+\frac2n(I+A)\right)
=2e\det(I+S/n)\left(1+O(n^{-1}+d^2/n^2)\right).
$$

The $e^{-1}$ in the permanent estimate comes from restoring $(1-1/n)^{n-k}$, which accounts for the zero diagonal. The factor $1/2$ comes from the path normalization above. Both cancel against the generating determinant's $2e$, leaving $D_n(S)\det(I+S/n)=\rho_n(S)$. The two determinants have separate origins: the first approximates cycle covers, and the second sums the path-convolution weights. Theorem 4.1 supplies the error summation and proves

$$
\frac{H(T)}{\mu_n}=\rho_n(S)+O((d+1)^2/n)
\qquad\text{when }d=o(\sqrt n).
$$

For the all-tournament upper bound, Section 3 treats large score variance and extreme degrees separately, then retains the score penalty in the remaining class. The next lemma bounds the same spectral factor for every tournament.

### 2.4 A spectral cap and convex packing

**Lemma 2.2 (Spectral cap).** Every tournament symbol matrix satisfies

$$
\|S\|_{\rm op}\le\cot\left(\frac{\pi}{2n}\right)<\frac{2n}{\pi},
\qquad \rho_n(S)\le C_*.
$$

**Proof.** We include the phase-ordering proof of the operator cap [4, Theorem 3.1 and Corollary 3.2], followed by the convex optimization needed here. The matrix $iS$ is Hermitian with symmetric spectrum, so its largest eigenvalue is $\|S\|_{\rm op}$. For any complex vector $z$, apply a signed permutation simultaneously to $z$ and $S$ so that the nonzero coordinate phases lie in $[0,\pi)$ in increasing order. Zero coordinates are placed arbitrarily. Then $c_{ij}=\operatorname{Im}(\overline z_i z_j)\ge0$ for $i<j$. If $T_n^0$ has upper-triangular entries one, then

$$
z^*iSz=-2\sum_{i<j}S_{ij}c_{ij}
\le2\sum_{i<j}c_{ij}=z^*(-iT_n^0)z.
$$

Taking Rayleigh maxima gives $\|S\|_{\rm op}\le\|T_n^0\|_{\rm op}$. To compute the latter, the eigenvalue equations for adjacent rows give $(\lambda-1)v_i=(\lambda+1)v_{i+1}$. Their geometric ratio $r=(\lambda-1)/(\lambda+1)$ satisfies $r^n=-1$ by the first-row equation. Thus the eigenvalues are $i\cot((2j-1)\pi/(2n))$, $1\le j\le n$, and the claimed norm follows. For $n\ge2$, the final strict inequality uses $\tan u>u$; the case $n=1$ is immediate.

Hence $0\le x_j\le a_*$ and $\sum_jx_j<1/2$. The function

$$
\phi(x)=\log\frac{1+x}{1-x}
$$

is increasing and convex on $[0,1)$. Transferring mass between two interior coordinates toward a capped coordinate and a remainder cannot decrease $\sum_j\phi(x_j)$. Appending zeros if necessary, and increasing the total mass to $1/2$, the relaxed maximum has coordinates $a_*,1/2-a_*,0,\ldots$, because $1/4<a_*<1/2$. Exponentiation gives exactly $C_*$. The feasible spectra of tournament matrices form a subset of this relaxed region, so its maximum is an upper bound for $\rho_n(S)$. This proves the lemma.

The same eigenvalue calculation, equivalently [4, Theorem 2.1], also yields

$$
\det(I+zT_n^0)=\frac{(1+z)^n+(1-z)^n}{2}.
$$

We will use this determinant polynomial to evaluate the spectral factor of the carousel construction in Section 4.

