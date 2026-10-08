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
