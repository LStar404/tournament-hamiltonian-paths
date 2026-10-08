## 4. 缩放与非主删除

本节证明将第 3 节统一永久式定理用于竞赛矩阵及其非主子矩阵时所需的解析接口。含固定参数的估计，其常数对有关矩阵和删集一致。缩放的存在性不通过猜测零支撑，或调用任意非负矩阵的支撑定理来推断。

以 $\mathbf 1_p$ 表示全一向量，记 $P_p=\mathbf 1_p\mathbf 1_p^{\mathsf T}/p$、$\Pi_p=I-P_p$。矩阵 $X$ 的总质量为 $\mathfrak m(X)=\sum_{i,j}X_{ij}$。矩阵范数均注明下标；$\|\cdot\|_{\rm op}$、$\|\cdot\|_F$ 以及诱导一范数和无穷范数采用通常定义。

### 4.1. 关于维数一致的局部缩放引理

**引理（局部缩放）。** 设 $X$ 为总质量等于 $p$ 的实 $p\times p$ 矩阵。记

$$
\alpha=X\mathbf 1_p-\mathbf 1_p,\qquad \beta=X^{\mathsf T}\mathbf 1_p-\mathbf 1_p,\qquad \varepsilon=\max(\|\alpha\|_\infty,\|\beta\|_\infty).
$$

假设 $|X_{ij}|\le C/p$，每行和每列的绝对值之和至多为 $2$，并且

$$
X_0=X-\frac{\alpha\mathbf 1_p^{\mathsf T}+\mathbf 1_p\beta^{\mathsf T}}p,\qquad E=X_0-P_p
$$

满足 $|E_{ij}|\le C_0/p$ 和 $\|E\|_{\rm op}\le q<1$，其中 $C,C_0,q$ 为固定参数。定义

$$
L_0=\frac32+C_0+\frac{C_0^2}{1-q},
$$

$$
\varepsilon_0=\min\left\{\frac1{256L_0^2},\frac{1-q}{2(32L_0+2)}\right\}.
$$

若 $\varepsilon\le\varepsilon_0$，则存在满足 $\sum_i x_i=\sum_j y_j$ 的有限实向量 $x,y$，使 $B=\operatorname{diag}(e^x)X\operatorname{diag}(e^y)$ 的每行和每列之和均为 $1$。此外，

$$
\|(x,y)\|_\infty\le4L_0\varepsilon,\qquad |B_{ij}|\le2C/p,\qquad \|B-P_p\|_{\rm op}\le(1+q)/2.
$$

若 $X\ge0$，则 $B$ 是真实的双随机缩放，且与 $X$ 具有相同的零支撑。

**证明。** 两个边际误差向量的元素和均为零。因此，$X_0$ 的行列和均为 $1$，而 $E$ 双侧中心化。令 $u=(\mathbf 1_p,-\mathbf 1_p)$、$N=uu^{\mathsf T}/(2p)$。平衡 Hessian $\mathsf H_0$ 的对角块为 $I$，非对角块分别为 $X_0,X_0^{\mathsf T}$。其规范化逆可显式写出。置

$$
R_L=(I-EE^{\mathsf T})^{-1},\qquad R_R=(I-E^{\mathsf T}E)^{-1},\qquad O=ER_R.
$$

则 $(\mathsf H_0+N)^{-1}$ 的四个分块为

$$
M_{LL}=R_L-P_p/4,\qquad M_{RR}=R_R-P_p/4,
$$

$$
M_{LR}=-O-P_p/4,\qquad M_{RL}=-O^{\mathsf T}-P_p/4.
$$

这是因为：在共同常数方向上，逆特征值为 $1/2$；在规范方向上为 $1$；在两个零和子空间上则是标准的分块逆。稠密元素界给出

$$
|(R_L-I)_{ij}|,\ |(R_R-I)_{ij}|\le\frac{C_0^2}{p(1-q^2)},
$$

$$
|O_{ij}|\le\frac{C_0}{p}+\frac{C_0^2q}{p(1-q^2)}.
$$

最后一个估计由分解 $O=E+EE^{\mathsf T}ER_R$，再控制两端行、列的二范数得到。因此，上述逆矩阵的诱导一范数和无穷范数均至多为 $L_0$。

令 $\mathsf H_X$ 的两个对角块分别为 $\operatorname{diag}(X\mathbf 1_p)$ 和 $\operatorname{diag}(X^{\mathsf T}\mathbf 1_p)$，非对角块为 $X,X^{\mathsf T}$。差矩阵 $\mathsf H_X-\mathsf H_0$ 的两种诱导范数均至多为 $3\varepsilon$。由 Neumann 级数，$(\mathsf H_X+N)^{-1}$ 的两种诱导范数均至多为 $2L_0$。

记 $z=(x,y)$、$g=(\alpha,\beta)$，平衡方程为

$$
0=g+\mathsf H_Xz+\mathcal N_X(z).
$$

其中，$\mathcal N_X(z)$ 是 $X_{ij}(e^{x_i+y_j}-1-x_i-y_j)$ 的行和与列和拼接而成的向量。在球 $\|z\|_\infty\le R\le1/4$ 上，绝对边际界给出

$$
\|\mathcal N_X(z)\|_\infty\le8R^2,\qquad \|D\mathcal N_X(z)\|_{\infty\to\infty}\le16R.
$$

这些向量均与 $u$ 正交。在规范子空间 $u^\perp$ 上考虑

$$
\mathcal T(z)=-(\mathsf H_X+N)^{-1}(g+\mathcal N_X(z)).
$$

取 $R=4L_0\varepsilon$。原点的像的范数至多为 $R/2$，而 Lipschitz 常数至多为 $128L_0^2\varepsilon\le1/2$。因此，映射保持规范球且为压缩映射，得到所需的有限势向量。若 $\varepsilon=0$，直接取 $z=0$。

最后，由 $R\le1/4$ 得到元素界。行列绝对和的假设给出

$$
\|B-X\|_{1\to1},\ \|B-X\|_{\infty\to\infty}\le32L_0\varepsilon.
$$

又有 $\|X-X_0\|_{\rm op}\le2\varepsilon$，故 $\varepsilon_0$ 中的第二个条件证明中心核谱隙。正对角因子同时保留非负性与零支撑。引理得证。

**引理（二范数位移与容量）。** 在上述假设下，再设 $X\ge0$。以 $\theta_X=\sum_i x_i+\sum_j y_j$ 表示总缩放势。存在仅依赖固定稠密度与谱隙参数的常数，使

$$
\|(x,y)\|_2\le K\|(\alpha,\beta)\|_2,\qquad \|B-X\|_F\le\frac K{\sqrt p}\|(\alpha,\beta)\|_2,
$$

$$
0\le\theta_X\le K\|(\alpha,\beta)\|_2^2.
$$

对于总质量为任意正数的非负矩阵 $X$，先归一化为 $\widetilde X=pX/\mathfrak m(X)$，再对 $\widetilde X$ 应用以上结论。若 $B$ 为其缩放，则有精确恒等式

$$
\theta_X=\theta_{\widetilde X}+p\log\frac p{\mathfrak m(X)},\qquad \operatorname{per}X=e^{-\theta_X}\operatorname{per}B.
$$

特别地，若 $\kappa=\mathfrak m(X)-p$，则 $\operatorname{per}X\le e^\kappa\operatorname{per}B$。当质量不等于 $p$ 时，$\theta_X$ 本身不必非负。

**证明。** 凸势函数为

$$
\Phi_X(x,y)=\sum_{i,j}X_{ij}e^{x_i+y_j}-\sum_i x_i-\sum_j y_j.
$$

其在原点的梯度为 $g=(\alpha,\beta)$，平衡点是最小值点。若 $R=\|(x,y)\|_\infty$，则沿 $tz$、$0\le t\le1$ 的 Hessian 不小于平衡矩阵 $B$ 处 Hessian 的 $e^{-2R}$ 倍。在规范子空间上，后者的最小特征值至少为 $1-\|B-P_p\|_{\rm op}$。故整条线段上具有固定正下界 $\lambda$。对梯度积分得到 $\|z\|_2\le\lambda^{-1}\|g\|_2$。再由稠密元素界和 $|e^{x_i+y_j}-1|\le K|x_i+y_j|$，得到 Frobenius 位移估计。

由于 $\Phi_X(0)=p$、$\Phi_X(z)=p-\theta_X$，凸性给出 $\theta_X\ge0$。强凸性给出 $\theta_X\le\|g\|_2^2/(2\lambda)$。非单位质量恒等式由将标量 $p/\mathfrak m(X)$ 吸收入两个对角势中得到。最后，利用 $p\log(\mathfrak m(X)/p)\le\kappa$ 得到永久式上界。

### 4.2. Gaussian 删除与中心化

对满足 $\|Z\|_{\rm op}<1$ 的实矩阵 $Z$，定义

$$
\mathcal G(Z)=\det(I-Z^{\mathsf T}Z)^{-1/2}.
$$

改用 $ZZ^{\mathsf T}$ 得到相同数值；补零行或零列也不改变此值。

**引理（Gram 删除）。** 设 $\|Z\|_{\rm op}\le q_*<1$。删除行集 $I$ 和列集 $J$，剩余集合为 $R,T$，则

$$
0\le\log\mathcal G(Z)-\log\mathcal G(Z[R,T])\le\frac{\sum_{i\in I}\|Z_{i,\cdot}\|_2^2+\sum_{j\in J}\|Z_{\cdot,j}\|_2^2}{2(1-q_*^2)}.
$$

对阶数为 $m$ 的方形余矩阵 $W$，置 $u=\mathbf 1_m/\sqrt m$，则

$$
0\le\log\mathcal G(W)-\log\mathcal G(\Pi_mW\Pi_m)\le\frac{\|W^{\mathsf T}u\|_2^2+\|Wu\|_2^2}{2(1-q_*^2)}.
$$

对于维数相同、算子范数均至多为 $q_*$ 的两个实矩阵，另有

$$
|\log\mathcal G(U)-\log\mathcal G(V)|\le\frac{\|U\|_F+\|V\|_F}{2(1-q_*^2)}\|U-V\|_F.
$$

**证明。** 删除行使列侧 Gram 矩阵减少半正定矩阵 $Z^{\mathsf T}(I-P_R)Z$，其迹等于被删行的平方范数之和。对 $F(H)=-\tfrac12\log\det(I-H)$ 和半正定方向 $D$，

$$
DF(H)[D]=\tfrac12\operatorname{tr}((I-H)^{-1}D)\le\frac{\operatorname{tr}D}{2(1-q_*^2)}.
$$

积分此界，再改用行侧 Gram 矩阵处理删列。分别投影掉两个全一方向，以同一方法得到中心化界。对于最后一个结论，沿两个 Gram 矩阵之间的线段积分，并使用

$$
\|U^{\mathsf T}U-V^{\mathsf T}V\|_*\le(\|U\|_F+\|V\|_F)\|U-V\|_F,
$$

其中 $\|\cdot\|_*$ 为迹范数。Gram 线段始终保持所需算子谱隙。

现在设 $S$ 为 $n\ge4$ 阶竞赛符号矩阵，$s=S\mathbf 1_n$、$\tau=\|s\|_2^2/(n-1)^2$。置

$$
Y=\frac{S-I}{n-1},\qquad D_n(S)=\det(I-S^{\mathsf T}S/n^2)^{-1/2}.
$$

反对称性与奇异值成对出现给出

$$
\|Y\|_{\rm op}^2\le q_Y^2=\frac{n(n-1)/2+1}{(n-1)^2}<1.
$$

任删 $t$ 行与 $t$ 列，记 $m=n-t$、$Z=\Pi_mY[R,T]\Pi_m$。$Y$ 的每行和每列的平方二范数均为 $n/(n-1)^2$。此外，

$$
\|Y\mathbf 1_n\|_2^2=\|Y^{\mathsf T}\mathbf 1_n\|_2^2=\tau+\frac n{(n-1)^2},
$$

$$
\|Y\mathbf 1_J\|_2^2,\ \|Y^{\mathsf T}\mathbf 1_I\|_2^2\le\frac{t^2n}{(n-1)^2}.
$$

因此，前一引理给出

$$
0\le\log\mathcal G(Y)-\log\mathcal G(Z)\le\frac{t n/(n-1)^2+2[\tau+n(1+t^2)/(n-1)^2]/m}{1-q_Y^2}.
$$

全矩阵的 Gram 恒等式为 $Y^{\mathsf T}Y=(S^{\mathsf T}S+I)/(n-1)^2$。它与 $S^{\mathsf T}S/n^2$ 的差半正定，且其迹为

$$
\mathcal T_n=\frac{2n-1}{n(n-1)}+\frac n{(n-1)^2}.
$$

从而 $0\le\log\mathcal G(Y)-\log D_n(S)\le43/(4n)$。若 $m\ge n/2$，第一个损失至多为 $(24t+18\tau+8)/n$。两者都是相对于同一全矩阵核的非负损失，故

$$
|\log\mathcal G(Z)-\log D_n(S)|\le\frac{24t+18\tau+11}{n}.
$$

为明确常数，注意 $1-q_Y^2=n(n-3)/(2(n-1)^2)$。代入并利用 $t\le n/2$ 即可直接验证上述常数。此估计是有限维结论，允许 $I\ne J$，不将非主余矩阵假定为反对称矩阵。

### 4.3. 成对预缩放与真实缩放

固定 $a_0<1$ 和有限正参数 $A_0,B_0$。本小节假设

$$
a_i=\frac{s_i}{n-1},\qquad \max_i|a_i|\le a_0,\qquad \tau=\sum_i a_i^2\le A_0\log n,\qquad t\le B_0\log n.
$$

定义

$$
C=\frac{J-I+S}{n-1}=\frac{2A}{n-1},\qquad \ell_i=\frac1{1+a_i},\qquad r_i=\frac1{1-a_i},\qquad g_i=\frac1{1-a_i^2}.
$$

置 $C'=\operatorname{diag}(\ell)C\operatorname{diag}(r)$、$F=C'-C$、$\nu=\mathfrak m(C')-n$。为计算总质量，记 $v_i=a_i/(1-a_i^2)$、$w_i=a_i^2/(1-a_i^2)$，以及 $V=\sum_i v_i$、$W=\sum_i w_i$。展开 $\ell=\mathbf 1-v+w$ 和 $r=\mathbf 1+v+w$，得到精确恒等式

$$
\nu=\frac{W^2-V^2+W+2w^{\mathsf T}Sv}{n-1}.
$$

确切地说，$\mathbf 1^{\mathsf T}Sv=-(n-1)W$ 抵消了一阶质量变化。固定比分界给出 $W\le K\tau$、$|V|\le K\tau$、$\|v\|_2\le K\sqrt\tau$。逐行估计 $Sv$ 得到

$$
|\nu|\le K\mathcal M_\tau,\qquad \mathcal M_\tau=\frac{\tau+\tau^2}{n}+\frac{\tau^{3/2}}{\sqrt n}=o(1).
$$

边际恒等式为

$$
C'\mathbf 1_n-\mathbf 1_n=\operatorname{diag}(\ell)C(r-\mathbf 1_n),
$$

$$
(C')^{\mathsf T}\mathbf 1_n-\mathbf 1_n=\operatorname{diag}(r)C^{\mathsf T}(\ell-\mathbf 1_n).
$$

由于 $C$ 的每行和每列二范数为 $O(n^{-1/2})$，且 $\|C\|_{\rm op}=O(1)$，无穷范数边际误差为 $O(\sqrt{\tau/n})$，二范数边际误差为 $O(\sqrt\tau)$。直接逐元素估计还得到

$$
\|F\|_F\le K\sqrt{\tau/n}.
$$

归一化 $\widehat C=nC'/\mathfrak m(C')$。以 $e_i,f_j$ 表示其行、列误差，故 $\sum e_i=\sum f_j=0$。对大小均为 $t$ 的任意删集 $I,J$，令

$$
X=\frac n m\widehat C[R,T],\qquad \kappa=\mathfrak m(X)-m,\qquad \widetilde X=\frac m{\mathfrak m(X)}X.
$$

精确删行列质量恒等式为

$$
\kappa=\frac n m\left[-\sum_{i\in I}e_i-\sum_{j\in J}f_j+\sum_{i\in I,j\in J}\widehat C_{ij}-\frac{t^2}{n}\right].
$$

每个保留行在最后一次归一化前的边际误差为

$$
(X\mathbf 1_m)_i-1=\frac n m\left[e_i+\frac t n-\sum_{j\in J}\widehat C_{ij}\right],
$$

列侧有相同形式的对应恒等式。因此，

$$
|\kappa|\le K\left[t\sqrt{\tau/n}+t^2/n\right],
$$

$$
\varepsilon(\widetilde X)\le K(\sqrt{\tau/n}+t/n),\qquad \|g(\widetilde X)\|_2\le K(\sqrt\tau+t/\sqrt n).
$$

这里 $g(\widetilde X)$ 是行列边际误差拼接向量，不是顶点权重 $g_i$。$\widetilde X$ 的所有元素非负且至多为 $K/m$。

局部缩放引理所需的中心核通过精确恒等式得到，而不是从第二奇异值的表述推断。记

$$
\eta=\frac{n^2}{\mathfrak m(C')\mathfrak m(X)}=1+O((t+1)/n),
$$

则

$$
\Pi_m\widetilde X\Pi_m=\eta\left[Z+\Pi_mF[R,T]\Pi_m\right].
$$

当 $t>0$ 时，$\eta$ 的主值为 $n/m$，没有被遗漏。压缩不增大 $Y$ 的算子范数，第二项由已得 Frobenius 界控制。因此，在固定参数下，中心核的算子范数一致至多为 $1/\sqrt2+o(1)$。其元素为 $O(1/m)$，无穷范数边际误差趋于零。对所有充分大的 $n$，局部缩放引理适用，并构造真实的双随机矩阵 $B_X$。

二范数位移引理给出

$$
\|B_X-\widetilde X\|_F\le K(\sqrt{\tau/n}+t/n).
$$

与较强的中心核界结合，$B_X$ 的中心算子范数仍为 $1/\sqrt2+o(1)$，例如最终至多为 $4/5$。元素继续满足 $K/m$ 的界。

最后，对 $Z$ 应用 Gaussian 删除估计，再对预缩放、归一化和真实缩放扰动应用对数 Lipschitz 估计。由于 $B_X-P_m=\Pi_mB_X\Pi_m$，得到

$$
|\log\mathcal G(B_X-P_m)-\log D_n(S)|\le K\left[\sqrt{\tau/n}+(t+1)/n\right].
$$

中心化产生的 $\tau/n$ 项已吸收入 $\sqrt{\tau/n}$。特别地，不同行、列删集不会带来平方根量级的删除损失。

### 4.4. 非主子矩阵的永久式恢复

**引理（成对非主永久式界）。** 在第 4.3 节固定参数假设下，定义 $\Gamma=\prod_i(1-a_i^2)\le e^{-\tau}$。对所有充分大的 $n$，以及大小均为 $t$ 的任意删集 $I,J$，记 $m=n-t$，则

$$
\operatorname{per}A[R,T]\le e^{-1}D_n(S)\Gamma\left(\prod_{i\in I}\ell_i\right)\left(\prod_{j\in J}r_j\right)\frac{m!}{2^m}\exp(K\mathcal R_{\tau,t}),
$$

其中

$$
\mathcal R_{\tau,t}=\mathcal M_\tau+\sqrt{\tau/n}+(t+1)/n+t\sqrt{\tau/n}+t^2/n.
$$

常数仅依赖 $a_0,A_0,B_0$ 和统一永久式定理中的常数。

**证明。** 已构造的真实缩放满足稠密度与中心核谱隙假设，因此第 3 节定理给出

$$
\operatorname{per}B_X=\frac{m!}{m^m}\mathcal G(B_X-P_m)(1+O(1/m)).
$$

行列缩放因子精确恢复为

$$
\prod_{i\in R}(1+a_i)\prod_{j\in T}(1-a_j)=\Gamma\prod_{i\in I}\ell_i\prod_{j\in J}r_j.
$$

删除行对应恢复 $\ell$ 因子，删除列对应恢复 $r$ 因子，二者不能交换。完整的标量恒等式为

$$
\operatorname{per}A[R,T]=\Gamma\prod_{i\in I}\ell_i\prod_{j\in J}r_j\left[\frac{m(n-1)\mathfrak m(C')}{2n^2}\right]^m e^{-\theta_X}\operatorname{per}B_X.
$$

恢复 $m!/m^m$ 后，剩余标量为

$$
\frac{m!}{2^m}(1-1/n)^m\left[\frac{\mathfrak m(C')}{n}\right]^m.
$$

其对数与 $e^{-1}m!/2^m$ 的对数之差为 $O((t+1)/n+|\nu|)$。容量界给出 $e^{-\theta_X}\le e^\kappa$。代入质量、Gaussian 和零阶永久式误差，即得到所需指数预算。所有比较对 $I,J$ 一致，均不要求 $I=J$。

### 4.5. 小比分时的双侧近似

**引理（小比分永久式近似）。** 设 $d=\|S\mathbf 1_n\|_\infty=o(\sqrt n)$。固定 $B_0<\infty$，任删 $t\le B_0\log n$ 行与 $t$ 列，记 $m=n-t$。对这些选择一致地有

$$
\operatorname{per}A[R,T]=e^{-1}D_n(S)\frac{m!}{2^m}\left[1+O_{B_0}\left(\frac{(d+t+1)^2}{n}\right)\right].
$$

这是渐近结论，不是对每个小阶矩阵的有限阶保证。当 $(d+t+1)^2/n$ 位于某个固定、充分小的范围内时，常数一致；在所述渐近范围中此量趋于零。

**证明。** 此处不需要成对预缩放。令 $C=2A/(n-1)$、$X=(n/m)C[R,T]$。全矩阵的行列误差分别为 $s_i/(n-1)$、$-s_i/(n-1)$。因此，第 4.3 节的精确质量与边际恒等式给出

$$
|\kappa|=O(t(d+t)/n),\qquad \varepsilon(X)=O((d+t)/n),\qquad \|g(X)\|_2=O((d+t)/\sqrt n).
$$

归一化 $\widetilde X=mX/\mathfrak m(X)$。其稠密度与中心核谱隙固定，局部缩放引理适用。二范数位移和容量估计给出

$$
\|B_X-\widetilde X\|_F=O((d+t)/n),\qquad 0\le\theta_{\widetilde X}=O((d+t)^2/n).
$$

非单位质量修正随后给出 $|\theta_X|=O((d+t)^2/n)$。又有 $\tau\le nd^2/(n-1)^2$。有限删除估计、归一化因子和真实缩放扰动共同给出

$$
|\log\mathcal G(B_X-P_m)-\log D_n(S)|=O((d+t+1)^2/n).
$$

此时不含比分乘积的精确恢复为

$$
\operatorname{per}A[R,T]=\left[\frac{m(n-1)}{2n}\right]^m e^{-\theta_X}\operatorname{per}B_X.
$$

应用统一永久式定理，并使用 $(1-1/n)^m=e^{-1}\exp(O((t+1)/n))$。所有对数误差均为 $O((d+t+1)^2/n)=o(1)$，对其取指数即得到所述相对近似。此短余矩阵估计是第 6 节实际 Hamilton 路径近似的输入；这里没有宣称谱切换或矩阵缩放保持路径数。
