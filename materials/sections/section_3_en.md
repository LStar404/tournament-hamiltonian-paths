## 3. The upper bound for all tournaments

Write

$$
V(T)=\sum_i\left(d_i^+-\frac{n-1}{2}\right)^2
=\frac14\|S\mathbf1\|_2^2,
\qquad
\tau=\frac{4V(T)}{(n-1)^2}.
$$

We divide the proof into three cases. If $V(T)\ge16n^2\log n$, the variance penalty in Brégman's inequality makes the path count negligible. Otherwise only $O(\log n)$ vertices can have degree outside $[(n-1)/20,19(n-1)/20]$. If any such vertices occur, we separate them from the rest and obtain a path count below the random expectation. The remaining tournaments have all normalized scores bounded away from $\pm1$ and $\tau=O(\log n)$. For them, the permanent estimate below retains the factor $e^{-\tau}$ needed to obtain an $O(n^{-1})$ final error.

Throughout this section, $K$ may increase from one occurrence to the next. Its value is absolute once the displayed degree thresholds are fixed. The long terms have already been bounded by $o(n^{-1})\mu_n$ in Section 2.2, so we estimate only the short terms $|U|\le k_n$.

### 3.1 The permanent estimate used in the reduction

The following lemma is the analytic input to the counting argument. Its proof, including existence of the required diagonal scaling, is given in Section 6.4. Row and column deletions are allowed to differ because a cycle cover may use different core vertices to enter and leave the exceptional set.

**Lemma 3.1 (Nonprincipal permanent bound).** Fix $0\le b<1$ and positive constants $A_0,B_0$. For a tournament core of order $N$, put $a=S\mathbf 1/(N-1)$ and $\tau=\sum_i a_i^2$. Suppose

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

For all sufficiently large $N$, the estimate holds simultaneously for every such tournament and every pair $I,J$. The constant $K$ and the threshold depend only on $b,A_0,B_0$.

The factor $\Gamma$ records the cost of the degree imbalance. In a principal deletion $I=J=U$, the restored vertex weight is $\ell_i r_i=(1-a_i^2)^{-1}$. For different deletions, the row and column factors remain separate. The error includes terms of order $\sqrt{\tau/N}$, so retaining $\Gamma\le e^{-\tau}$ is essential in the last case of the proof.

### 3.2 High score variance

**Lemma 3.2 (Variance-sensitive permanent bound).** There is an absolute constant $K$ such that every tournament $Q$ of order $m\ge1$, with outdegrees $d_i$ and degree variance $V(Q)=\sum_i(d_i-(m-1)/2)^2$, satisfies

$$
\operatorname{per}A_Q\le
K\sqrt{m+1}\frac{m!}{2^m}\exp\left(-\frac{V(Q)}{8m^2}\right).
$$

**Proof.** We refine the Brégman bound [2] by using the concavity of its row-degree factor. If any $d_i=0$, the asserted bound for positive order is immediate. Otherwise put $f(k)=\log(k!)/k$ for positive integers. A direct calculation gives, for $k\ge2$,

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

Brégman's row-degree bound now proves the variance estimate. $\square$

We apply this bound to each short deleted tournament. The variance must remain large after the deletion, which is why the following comparison is needed.

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

### 3.3 Exceptional vertices

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

For the squared-score bound, use $\|S_M\mathbf1\|_2\le\|S\mathbf1\|_2+f\sqrt N$ and divide by $N-1$. The same argument applies after any further short core deletion. Throughout those deletions we keep the original exceptional set $F$, so the constants are uniform.

We first bound $\operatorname{per}A_T$ by the number of ways a cycle cover can pass between $F$ and the core $M$. An exceptional vertex has few neighbors in one of the two directions. A cycle cover must use both directions unless it matches that vertex inside $F$, and the latter choice will cost a factor of order $1/N$. Use the paired core weights $\ell,r$ of Lemma 3.1. Their total displacement satisfies

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

Every contributing permutation is classified exactly once. Apply the uniform core bound of Lemma 3.1 before separating the cross sums. A deleted core row supplies $\ell_i$, and a deleted core column supplies $r_j$. For fixed $R,C$, the outgoing cross sum is exactly

$$
\begin{aligned}
&\sum_{\substack{J\subseteq M\\|J|=t}}
\operatorname{per}A[F\setminus R,J]\prod_{j\in J}r_j\\
&=\sum_{\phi:F\setminus R\hookrightarrow M}
\prod_{x\in F\setminus R}A_{x,\phi(x)}r_{\phi(x)}
\le\prod_{x\in F\setminus R}\sum_{j\in M}A_{xj}r_j.
\end{aligned}
$$

Independently, the incoming cross sum is

$$
\begin{aligned}
&\sum_{\substack{I\subseteq M\\|I|=t}}
\operatorname{per}A[I,F\setminus C]\prod_{i\in I}\ell_i\\
&=\sum_{\psi:F\setminus C\hookrightarrow M}
\prod_{y\in F\setminus C}A_{\psi(y),y}\ell_{\psi(y)}
\le\prod_{y\in F\setminus C}\sum_{i\in M}A_{iy}\ell_i.
\end{aligned}
$$

Here $\hookrightarrow$ denotes an injection. Each injection is counted once, by its image and the corresponding permanent term; there is no additional factor $t!$. The images $I,J$ need be neither equal nor disjoint, because they refer to separate row and column copies of the core. Removing injectivity is legitimate because all factors are nonnegative. The product of the two upper bounds is

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

Here $N+f-(N-t)=f+t=2f-s$, so the factorial ratio supplies $N^{-(2f-s)}\exp(O(f^2/N))$. Multiplication by $N^{2t}$ leaves exactly $N^{-s}$.

If $h=|R\cap C|$, the paired product satisfies

$$
\left(\prod_{x\notin R}u_x\right)
\left(\prod_{y\notin C}v_y\right)
\le c_n^{f-2s}L_n^{2s}(c_n/L_n^2)^h
\le c_n^{f-2s}L_n^{2s}.
$$

The first inequality follows by counting the vertices carrying both factors, one factor, or no factor. It remains valid when $f-2s$ is negative. The error in Lemma 3.1 is $o(1)$ uniformly over $t\le f=O(\log n)$; we can discard its factor $\Gamma\le1$. Since $\binom fs^2s!\le f^{2s}/s!$, the complete sum gives

$$
\frac{\operatorname{per}A_T}{n!/2^n}
\le(1+o(1))e^{-1}D_N(S_M)c_n^f
\exp(O(f^2/N))
\exp\left(\frac{2L_n^2f^2}{c_n^2N}\right).
$$

The displayed extra exponents are $o(1)$. To make the uniformity explicit, after deleting a short core subset $U$ the core order is $N'=n-f-|U|\sim n$, while the exceptional set remains the original $F$. The normalized core score cap is still $0.95$ eventually, its squared-score sum is $O(\log n)$, and the cross deletion size is $t\le f=O(\log n)$. The exponent in Lemma 3.1 is consequently

$$
O\!\left(\frac{(\log n)^{3/2}}{\sqrt n}+\frac{(\log n)^2}{n}\right)=o(1),
$$

with constants independent of $U,I,J$. The cross-neighbor fractions change by only $O((f+|U|)/n)$ from the original full-tournament fractions, and the weight displacement remains $O(\sqrt{n\log n})$. Thus all the preceding cross-sum estimates are uniform as well. The core Gaussian factor then changes by $\exp(O(|U|/n))$: deleting rows and columns of $S_M/N$ costs $O(|U|/n)$ in logarithm by the Gaussian deletion lemma, and changing normalization from $N$ to $N-|U|$ has the same cost.

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

Since $P(n)\ge\mu_n$, the fixed gap below one excludes these tournaments from the maximum for all sufficiently large $n$. This case requires only an $o(1)$ error. We keep the paired spectral factor here to make its connection with the later reduction visible. For the short convolution terms whose deletion sets are disjoint from $F$, the Lean proof uses the weaker sufficient bound $(10/3)4^{-f}(1+\varepsilon_n)$. The short terms meeting $F$ and the long terms contribute an additional $\delta_n$, giving

<a id="eq-exceptional-bound"></a>

$$
\frac{H(T)}{\mu_n}\le\frac{10}{3}4^{-f}(1+\varepsilon_n)+\delta_n,
\qquad \varepsilon_n,\delta_n\longrightarrow0.
\tag{3.1}
$$

Both errors are uniform over the low-variance class under discussion. They are kept separate because $f$ may grow with $n$. In the formal proof, $1+\varepsilon_n\le21/20$ and each of the other two contributions is at most $1/25$ eventually. Thus, for $f\ge1$, [Equation (3.1)](#eq-exceptional-bound) gives the explicit budget

$$
\frac{10}{3}\cdot\frac14\cdot\frac{21}{20}+\frac1{25}+\frac1{25}
=\frac{191}{200}<1.
$$

Neither choice affects the final upper constant.

### 3.4 The score penalty in the remaining class

We are left with tournaments satisfying

$$
\max_i|a_i|\le0.9,\qquad
a=s/(n-1),\qquad \tau=\sum_i a_i^2\le K\log n.
$$

Here and below, fix one absolute constant $K_0$ with $\tau\le K_0\log n$. Their paired product obeys

$$
\Gamma=\prod_i(1-a_i^2)\le e^{-\tau}.
$$

We now use Lemma 3.1 on the whole tournament. The score product is common to every short term; keeping it outside the sum will absorb errors that are larger than $1/n$ individually.

For a principal deletion set $U$ of size $k\le k_n$, Lemma 3.1 gives

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

Put $\delta_n=\sqrt{\tau/n}+1/n$ and $r_k=R_{\tau,k}+\log(n^k/(n)_k)$. Uniformly over $\tau\le K_0\log n$, we have $0\le r_k\le K\delta_n(k+k^2)$ and $\max_{k\le k_n}r_k=o(1)$, taking the upper error budgets nonnegative. Thus

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

The finite moments of $G^kw_k$ control the summed error, rather than the largest deletion size $k_n$. This is what prevents an extra logarithmic factor in the final bound.

We now remove the weights without losing the score penalty. Let $W=I+(2/n)(I+A)$ and $\Delta=(2/n)\operatorname{diag}(g-1)(I+A)$. The symmetric part of $W$ is at least $I$, so $\|W^{-1}\|_{\rm op}\le1$. Since every row of $I+A$ has Euclidean norm at most $\sqrt n$ and $\sum_i(g_i-1)\le K\tau$, the trace norm (the sum of singular values) can be estimated by decomposing $\Delta$ into rank-one row matrices. Since $\|uv^{\mathsf T}\|_*=\|u\|_2\|v\|_2$, this gives

$$
\|\Delta\|_*\le K\tau/\sqrt n.
$$

The determinant inequality $|\det(I+E)|\le\exp(\|E\|_*)$ therefore implies

$$
\det(W+\Delta)\le\det(W)e^{K\tau/\sqrt n}.
$$

Both determinants are positive: $W$ has positive-definite symmetric part, and the weighted determinant has a principal-minor expansion with positive coefficients. The unweighted rank-one bound from Section 3.3, now with $N=n$, is $\det(W)\le2e\det(I+S/n)$.

Combining these inequalities and adding only the long-subset tail gives the uniform score-sensitive bound

<a id="eq-score-penalty"></a>

$$
\frac{H(T)}{\mu_n}\le
\rho_n(S)\exp\left\{-\tau+
K\left[\frac{1+\tau+\tau^2}{n}
+\frac{\tau^{3/2}+\tau}{\sqrt n}+\sqrt{\tau/n}\right]\right\}
+o(1/n).
\tag{3.2}
$$

For $\tau\le K_0\log n$, all polynomial terms except the constant $1/n$ can consume at most $\tau/4$ for sufficiently large $n$. The remaining square-root term is bounded by Young's inequality:

$$
K\sqrt{\tau/n}\le\tau/4+K^2/n.
$$

The exponent in [Equation (3.2)](#eq-score-penalty) is consequently at most $-\tau/2+K/n$. The spectral cap now gives

$$
H(T)/\mu_n\le C_*e^{K/n}+o(1/n)=C_*+O(1/n).
$$

### 3.5 Completion of the upper bound

The three classes cover every tournament. High-variance tournaments have normalized path count $o(1/n)$; the low-variance tournaments with exceptional vertices have count strictly below one; all remaining tournaments satisfy the preceding $C_*+O(1/n)$ bound. It follows that

$$
\boxed{P(n)\le\bigl(C_*+O(1/n)\bigr)\mu_n.}
$$

The thresholds in the three cases are independent of the tournament, so one common threshold gives the upper half of Theorem 1.1.

