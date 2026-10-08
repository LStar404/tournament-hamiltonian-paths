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
