## 4. Small-score paths and the lower bound

**Theorem 4.1 (Small-score path approximation).** There is an absolute constant $C$ with the following property. For every nonnegative function $d=d(n)$ satisfying $d(n)/\sqrt n\to0$, there is a threshold $n_0(d)$ such that every tournament of order $n\ge n_0(d)$ with $\|S\mathbf1\|_\infty\le d(n)$ satisfies

$$
\left|\frac{H(T)}{\mu_n}-\rho_n(S)\right|\le C\frac{(d(n)+1)^2}{n}.
$$

### 4.1 Proof of the small-score approximation

**Proof.** Write $d=d(n)$. Use Lemma 6.4 for every principal deletion $|U|=k\le k_n$. Since $d+k_n+1=o(\sqrt n)$, it applies uniformly. Restoring the falling factorial $(n)_k$, the positive path convolution gives

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

The falling-factorial error contributes $O(n^{-1}\sum k^2w_k)$, and the terms indexed by large deletion sets are $o(n^{-1})$ by Section 2.2. Extending the displayed short generating sum to all $k$ costs $n^{-2+o(1)}$, since its coefficients are bounded by $w_k$. Thus

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

Substitution proves the theorem. The estimates use one absolute constant; only the order after which the small-score conditions hold depends on the function $d$. $\square$

### 4.2 Carousel tournaments

**Corollary 4.2 (Carousel lower bound).** For the odd-order carousel and the even-order one-vertex deletion defined below,

$$
H(\mathrm{Car}_n)/\mu_n=L+O(n^{-1}).
$$

**Proof.** For odd $n$, define the carousel tournament $\mathrm{Car}_n$ on residues modulo $n$ by $i\to i+j$ for $1\le j\le(n-1)/2$. It is regular, so $d=0$. For even $n$, let $\mathrm{Car}_n$ be a one-vertex deletion from $\mathrm{Car}_{n+1}$; then $d=1$.

The odd carousel symbol matrix is signed-permutation similar to $T_n^0$. One explicit construction is to conjugate $T_n^0$ by the diagonal signs $(-1)^i$, $0\le i<n$, and reorder its indices as $0,2,\ldots,n-1,1,3,\ldots,n-2$. For two indices of the same parity the switched edge follows their increasing order; for two indices of opposite parity it follows the reverse order. Reading the indices in the displayed cyclic order gives precisely the carousel orientation. Restrict the inverse signed conjugation and reordering to an even-order one-vertex deletion: the resulting transformed matrix is $T_n^0$ on the remaining ordered indices. Thus the same signed-spectral computation applies after deleting any one vertex. Hence both parities have

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

The passage from the signed similarity to the path count uses Theorem 4.1, applied to scores $d=0$ and $d=1$. Let $K_l,N_l$ and $K_u,N_u$ be the constants and thresholds from the lower and upper bounds. Taking $K=K_l+K_u$ and $n_0=\max(N_l,N_u,2)$ proves Theorem 1.1. $\square$

