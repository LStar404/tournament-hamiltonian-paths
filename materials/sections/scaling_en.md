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
