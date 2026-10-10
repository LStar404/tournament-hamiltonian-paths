## 6. Scaling and nonprincipal permanent estimates

Theorem 5.1 applies to a matrix with equal row and column sums after a scalar normalization. A tournament matrix generally has unequal margins: for $C=2A/(n-1)$,

$$
C\mathbf1=\mathbf1+a,\qquad C^{\mathsf T}\mathbf1=\mathbf1-a.
$$

We must correct these margins while controlling the change in the permanent and in its Gaussian factor. We first construct a local diagonal scaling and bound its total logarithmic cost. A Gram-matrix comparison then controls the effect of deleting rows and columns. Finally, paired score corrections put the tournament submatrices in the domain of the local theorem and yield Lemma 3.1.

Write $\mathbf1_p$ for the all-ones vector, $P_p=\mathbf1_p\mathbf1_p^{\mathsf T}/p$, and $\Pi_p=I-P_p$. The total mass of a matrix is $\mathfrak m(X)=\sum_{i,j}X_{ij}$. We use $\|\cdot\|_{\rm op}$ for the Euclidean operator norm, $\|\cdot\|_F$ for the Frobenius norm, and $\|\cdot\|_*$ for the trace norm. Constants in this section are uniform once the stated density and gap parameters are fixed.

For the application below, the dimensions and normalizations are as follows. The full tournament order is $n$, the retained order is $m=n-t$, and $p$ is the generic order in Lemmas 6.1–6.2; we set $p=m$ only when applying them. The matrices $C,C',\widehat C$ have order $n$, whereas $X,\widetilde X,B_X,Z$ have order $m$. Their masses, in that order where relevant, are

$$
\mathfrak m(C')=n+\nu,\quad \mathfrak m(\widehat C)=n,\quad
\mathfrak m(X)=m+\kappa,\quad
\mathfrak m(\widetilde X)=\mathfrak m(B_X)=m.
$$

Here $Z=\Pi_m[(S-I)/(n-1)][R,T]\Pi_m$ is the centered, unscaled retained kernel, not a doubly stochastic matrix. The letter $B_X$ denotes the final stochastic matrix; its perturbation in Theorem 5.1 is $mB_X-J_m$, whose normalization is $B_X-P_m$. This distinguishes the full-order normalization $n-1$ from the retained-order normalization $m$.

### 6.1 Local scaling and its cost

We seek $B_{ij}=X_{ij}e^{x_i+y_j}$ with all margins equal to one. Replacing $(x,y)$ by $(x+c\mathbf1,y-c\mathbf1)$ leaves $B$ unchanged; the condition $\sum x_i=\sum y_j$ removes this one-dimensional freedom. The singular-value gap controls the linearized balancing equations on the remaining subspace. The entry bound upgrades that control to an infinity-norm estimate independent of the dimension, allowing a contraction argument.

**Lemma 6.1 (Local scaling).** Let $p\ge1$ and let $X$ be a real $p\times p$ matrix of mass $p$. Put

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

The balance point alone is insufficient for the permanent estimate: restoring the diagonal factors multiplies the permanent by $\exp(-\sum x_i-\sum y_j)$. The next lemma bounds this total cost and also gives the Frobenius displacement needed to compare Gaussian factors.

**Lemma 6.2 (Displacement and capacity).** Under the preceding assumptions, suppose in addition that $X\ge0$. Write $\theta_X=\sum_i x_i+\sum_j y_j$ for the total scaling potential. With constants depending only on the fixed density and gap parameters,

$$
\|(x,y)\|_2\le K\|(\alpha,\beta)\|_2,\qquad \|B-X\|_F\le\frac K{\sqrt p}\|(\alpha,\beta)\|_2,
$$

$$
0\le\theta_X\le K\|(\alpha,\beta)\|_2^2.
$$

For a nonnegative matrix $X$ of arbitrary positive mass, suppose that $\widetilde X=pX/\mathfrak m(X)$ satisfies Lemma 6.1. Apply the preceding conclusions to $\widetilde X$. If $B$ is its scaling, the exact identities are

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

### 6.2 Gaussian deletion and centering

Deleting $t$ rows from a dense normalized matrix removes a total squared row norm of order $t/n$. Applying the log-determinant derivative to the corresponding Gram-matrix loss preserves this order. We then delete columns using the other Gram matrix. This gives a linear deletion error even when the retained matrix is nonprincipal.

For a real matrix $Z$ with $\|Z\|_{\rm op}<1$, define

$$
\mathcal G(Z)=\det(I-Z^{\mathsf T}Z)^{-1/2}.
$$

The same value is obtained with $ZZ^{\mathsf T}$; padding by zero rows or columns leaves it unchanged.

**Lemma 6.3 (Gram deletion and stability).** Suppose $\|Z\|_{\rm op}\le q_*<1$. Delete row set $I$ and column set $J$, with remaining sets $R,T$. Then

$$
0\le\log\mathcal G(Z)-\log\mathcal G(Z[R,T])\le\frac{\sum_{i\in I}\|Z_{i,\cdot}\|_2^2+\sum_{j\in J}\|Z_{\cdot,j}\|_2^2}{2(1-q_*^2)}.
$$

For a square remaining matrix $W$ of order $m\ge1$, put $u=\mathbf 1_m/\sqrt m$. Then

$$
0\le\log\mathcal G(W)-\log\mathcal G(\Pi_mW\Pi_m)\le\frac{\|W^{\mathsf T}u\|_2^2+\|Wu\|_2^2}{2(1-q_*^2)}.
$$

For any two real matrices of the same dimensions with operator norm at most $q_*$,

$$
|\log\mathcal G(U)-\log\mathcal G(V)|\le\frac{\|U\|_F+\|V\|_F}{2(1-q_*^2)}\|U-V\|_F.
$$

**Proof.** Let $P_R$ be the diagonal coordinate projection onto the retained rows. Deleting rows decreases the column Gram matrix by the positive semidefinite matrix $Z^{\mathsf T}(I-P_R)Z$, whose trace is the sum of the deleted row norms squared. For $F(H)=-\tfrac12\log\det(I-H)$ and a positive semidefinite direction $D$,

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

For completeness, $1-q_Y^2=n(n-3)/(2(n-1)^2)$. Substitution proves the stated constants directly, using $t\le n/2$. The estimate applies to independent row and column sets $I,J$; skew symmetry is used only for the original full matrix $S$.

### 6.3 Preparing the tournament submatrices

The row and column errors of $C=2A/(n-1)$ have opposite signs. Multiplying row $i$ by $(1+a_i)^{-1}$ corrects its original row sum, while multiplying column $i$ by $(1-a_i)^{-1}$ corrects its original column sum. Applying both corrections leaves a residual marginal error, estimated below. Their main advantage is that the total mass has no first-order change and their restored product is the score penalty $\Gamma$.

Fix $0\le a_0<1$ and finite positive parameters $A_0,B_0$. In this subsection suppose

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

Normalize $\widehat C=nC'/\mathfrak m(C')$. Write its row and column errors as $e_i,f_j$, so $\sum e_i=\sum f_j=0$. For arbitrary deleted sets $I,J$ of size $t$, write $R=[n]\setminus I$, $T=[n]\setminus J$ and $m=n-t$. Let

$$
X=\frac n m\widehat C[R,T],\qquad \kappa=\mathfrak m(X)-m,\qquad \widetilde X=\frac m{\mathfrak m(X)}X.
$$

The exact deletion mass identity is

<a id="eq-deletion-mass"></a>

$$
\kappa=\frac n m\left[-\sum_{i\in I}e_i-\sum_{j\in J}f_j+\sum_{i\in I,j\in J}\widehat C_{ij}-\frac{t^2}{n}\right].
\tag{6.1}
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

To apply Lemma 6.1, we now check the centered kernel of $\widetilde X$. With

$$
\eta=\frac{n^2}{\mathfrak m(C')\mathfrak m(X)}=1+O((t+1)/n),
$$

it is

$$
\Pi_m\widetilde X\Pi_m=\eta\left[Z+\Pi_mF[R,T]\Pi_m\right].
$$

Since $\mathfrak m(C')=n+o(1)$ and $\mathfrak m(X)=m+o(1)$, the leading value of $\eta$ is $n/m$. Compression preserves the operator norm bound for $Y$, and the displayed Frobenius estimate controls the second term. Thus the centered operator norm is at most $1/\sqrt2+o(1)$, uniformly under the fixed parameters. Its entries are $O(1/m)$, and the marginal infinity error tends to zero. In the notation of Lemma 6.1, $E=\Pi_m\widetilde X\Pi_m$, because $\widetilde X$ has mass $m$. We may therefore fix $q=3/4$ and fixed density bounds $C,C_0$ once and for all. The threshold $\varepsilon_0$ and inverse bound $L_0$ then depend only on $a_0,A_0,B_0$, not on $n$, the tournament, or the deletion sets. The local scaling lemma applies for all sufficiently large $n$ and constructs a genuine doubly stochastic matrix $B_X$; its immediate gap bound is $7/8$.

The Euclidean displacement lemma yields

$$
\|B_X-\widetilde X\|_F\le K(\sqrt{\tau/n}+t/n).
$$

Combining this with the sharper centered bound, the centered norm of $B_X$ is still $1/\sqrt2+o(1)$; for example, it is eventually at most $4/5$. The entries remain bounded by $K/m$.

Finally, apply the Gaussian deletion estimate to $Z$, then the logarithmic Lipschitz estimate to the preconditioning, normalization, and true-scaling perturbations. Since $B_X-P_m=\Pi_mB_X\Pi_m$, this gives

$$
|\log\mathcal G(B_X-P_m)-\log D_n(S)|\le K\left[\sqrt{\tau/n}+(t+1)/n\right].
$$

The term $\tau/n$ from centering is absorbed by $\sqrt{\tau/n}$. The deletion part of this estimate is linear in $t/n$, as needed when it is summed against the subset weights.

The error budget can now be read without changing dimensions. All constants and eventual thresholds depend only on the fixed $a_0,A_0,B_0$. The full-order mass error costs $O(|\nu|)\le K\mathcal M_\tau$ in the restored logarithm; deletion changes mass by at most $K[t\sqrt{\tau/n}+t^2/n]$; and the Gaussian logarithm costs $K[\sqrt{\tau/n}+(t+1)/n]$. Applying Theorem 5.1 at order $m\ge n/2$ adds $O(1/m)=O(1/n)$. The final scalar restoration contributes $e^{-1}\exp(O((t+1)/n))$. For $X$ of mass $m+\kappa$, capacity is used only as $e^{-\theta_X}\le e^\kappa$; no nonnegativity of $\theta_X$ is asserted at this nonunit mass. Section 6.4 restores these factors exactly, giving the exponent in Lemma 3.1.

### 6.4 Proof of the nonprincipal permanent bound

We prove Lemma 3.1, using $n$ for the full core order $N$ and $a_0=b$. The preceding construction provides the scaling matrix $B_X$. It remains to restore every diagonal and scalar factor and compare the resulting Gaussian determinant with $D_n(S)$.

**Proof.** The true scaling just constructed satisfies its density and centered-gap hypotheses, so Theorem 5.1 gives

$$
\operatorname{per}B_X=\frac{m!}{m^m}\mathcal G(B_X-P_m)(1+O(1/m)).
$$

The row and column factors restore exactly as

$$
\prod_{i\in R}(1+a_i)\prod_{j\in T}(1-a_j)=\Gamma\prod_{i\in I}\ell_i\prod_{j\in J}r_j.
$$

Thus deleted rows restore $\ell$ factors and deleted columns restore $r$ factors. The complete scalar identity is

<a id="eq-exact-restoration"></a>

$$
\operatorname{per}A[R,T]=\Gamma\prod_{i\in I}\ell_i\prod_{j\in J}r_j\left[\frac{m(n-1)\mathfrak m(C')}{2n^2}\right]^m e^{-\theta_X}\operatorname{per}B_X.
\tag{6.2}
$$

After inserting $m!/m^m$ into [Equation (6.2)](#eq-exact-restoration), the remaining scalar is

$$
\frac{m!}{2^m}(1-1/n)^m\left[\frac{\mathfrak m(C')}{n}\right]^m.
$$

Its logarithm differs from that of $e^{-1}m!/2^m$ by $O((t+1)/n+|\nu|)$. The capacity bound gives $e^{-\theta_X}\le e^\kappa$. Substituting the mass, Gaussian, and zero-order errors proves the claimed exponent. All constants are uniform over the tournament and the two deletion sets, proving Lemma 3.1. $\square$

### 6.5 The small-score two-sided estimate

When every score is $o(\sqrt n)$, the original margins are already close enough to one for direct local scaling. The capacity estimate then controls the restoration on both sides, giving the approximation used in Theorem 4.1.

**Lemma 6.4 (Small-score permanent approximation).** Let $d=\|S\mathbf 1_n\|_\infty=o(\sqrt n)$. Fix $0<B_0<\infty$, delete any $t\le B_0\log n$ rows and any $t$ columns, and put $m=n-t$. Uniformly over these choices,

<a id="eq-small-score-permanent"></a>

$$
\operatorname{per}A[R,T]=e^{-1}D_n(S)\frac{m!}{2^m}\left[1+O_{B_0}\left(\frac{(d+t+1)^2}{n}\right)\right].
\tag{6.3}
$$

More explicitly, for every fixed $B_0>0$ there are constants $C_{\mathrm{err}},\delta>0$ and an integer $N_0\ge4$, depending only on $B_0$, such that for every $n\ge N_0$, every tournament sign matrix $S$, and every pair of deletion sets $I,J\subseteq[n]$ with $|I|=|J|=t\le B_0\log n$, the following holds: if $d=\|S\mathbf1_n\|_\infty$ and $\eta=(d+t+1)^2/n\le\delta$, then the absolute relative error in [Equation (6.3)](#eq-small-score-permanent) is at most $C_{\mathrm{err}}\eta$. Here $R=[n]\setminus I$, $T=[n]\setminus J$, and $m=n-t$; the sets $I,J$ are independent. The constants are chosen before the dimension, tournament and deletion sets. In the stated asymptotic regime, $\eta\to0$.

**Proof.** Enlarge $N_0$ so that $2t\le n$ throughout the logarithmic deletion window; hence $m\ge n/2>0$. No paired preconditioning is needed. Set $C=2A/(n-1)$ and $X=(n/m)C[R,T]$. The row and column errors of the full matrix $C$ are $s_i/(n-1)$ and $-s_i/(n-1)$, respectively. The exact mass identity [Equation (6.1)](#eq-deletion-mass) and the marginal formulas from Section 6.3 therefore give

$$
|\kappa|=O(t(d+t)/n),\qquad \varepsilon(X)=O((d+t)/n),\qquad \|g(X)\|_2=O((d+t)/\sqrt n).
$$

The mass error satisfies $|\kappa|\le K\eta$. By reducing $\delta$ if necessary, $\mathfrak m(X)=m+\kappa>0$ uniformly. Normalize $\widetilde X=mX/\mathfrak m(X)$. Its density and centered gap are fixed, and the local scaling lemma applies. The Euclidean displacement and capacity estimates give

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

Apply the uniform permanent theorem and use $(1-1/n)^m=e^{-1}\exp(O((t+1)/n))$. All logarithmic errors are bounded by a fixed multiple of $\eta=(d+t+1)^2/n$. Choose $\delta$ sufficiently small; exponentiating these bounds gives an absolute relative error at most $C_{\mathrm{err}}\eta$, uniformly in the finite domain stated above. In the asymptotic regime $d=o(\sqrt n)$ and $t\le B_0\log n$, we have $\eta\to0$. This proves the uniform short-minor approximation used in Theorem 4.1. $\square$

