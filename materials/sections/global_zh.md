## 5. 全图归约

本节对全体竞赛图证明上界，不预先假设正则或平衡。以下 $K$ 表示可在不同位置增大的正常数；固定下面的度数阈值后，所有常数均为绝对常数。

对 $n$ 个顶点的竞赛图，记邻接矩阵为 $A$，$S=A-A^{\mathsf T}$，$s=S\mathbf1$，并置

$$
\mathcal E=\|s\|_2^2,\qquad V=\mathcal E/4,\qquad
\tau=\mathcal E/(n-1)^2,\qquad
\mu_n=n!/2^{n-1}.
$$

沿用前文定义的 $D_n(S)$ 和 $\rho_n(S)=D_n(S)\det(I+S/n)$。谱上限引理给出

$$
1\le\rho_n(S)\le C_*.
$$

### 5.1. 精确的解析接口与长删集尾项

先明确本节需要的成对非主永久式界。固定 $b<1$ 以及常数 $A_0,B_0$。对 $N$ 阶竞赛图核心，置 $a=S\mathbf1/(N-1)$，$\tau=\sum_i a_i^2$，并假设

$$
\max_i|a_i|\le b,\qquad
\tau\le A_0\log N,\qquad
|I|=|J|=t\le B_0\log N.
$$

定义 $\ell_i=(1+a_i)^{-1}$、$r_i=(1-a_i)^{-1}$，以及

$$
\Gamma=\prod_i(1-a_i^2),\qquad
\mathcal M_\tau=\frac{\tau+\tau^2}{N}+\frac{\tau^{3/2}}{\sqrt N}.
$$

令 $R,T$ 分别为行、列删集的补集，则有

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

常数对核心图以及可能不同的行、列删集统一。该结论直接涉及实际永久式：局部缩放引理与统一零阶永久式引理已在其中接入。因此，本节不再使用未证明的缩放存在性或额外永久式渐近假设。

使用第 2 节基于 [1] 的正卷积及其行列式、通用永久式界：

$$
H(T)=\sum_{U\subseteq[n]}\det(I+A[U])\operatorname{per}A[U^c],
$$

$$
\det(I+A[U])\le h_k,\qquad
\operatorname{per}A[U^c]\le K\sqrt{n-k+1}\frac{(n-k)!}{2^{n-k}},
\qquad k=|U|.
$$

回顾 $w_k=2^kh_k/k!$。取截断点

$$
k_n=\left\lceil\frac{4\log n}{\log\log n}\right\rceil.
$$

对任意固定 $c>0$ 和非负整数 $j$，级数 $\sum_k c^kk^jw_k$ 收敛。事实上，

$$
\log(c^kw_k)=-\frac{k}{2}\log k+O_c(k).
$$

因此 $\sum_{k>k_n}c^kw_k=n^{-2+o(1)}$。对所有删集求和，通用永久式界给出统一估计

$$
\frac1{\mu_n}
\sum_{|U|>k_n}\det(I+A[U])\operatorname{per}A[U^c]
\le K\sqrt{n+1}\sum_{k>k_n}w_k=o(1/n).
$$

称 $|U|\le k_n$ 的项为短项。除非另有说明，下文估计均针对短项。

### 5.2. 排除高比分方差

需要 Brégman 界 [2] 的一个定量版本。设 $Q$ 为 $m$ 阶竞赛图，出度为 $d_i$，度数方差为 $V(Q)=\sum_i(d_i-(m-1)/2)^2$，则

$$
\operatorname{per}A_Q\le
K\sqrt{m+1}\frac{m!}{2^m}\exp\left(-\frac{V(Q)}{8m^2}\right).
$$

零阶矩阵按永久式为一处理。对正阶图，若某个 $d_i=0$，上界显然成立。否则，对正整数定义 $f(k)=\log(k!)/k$。直接计算得，对 $k\ge2$，

$$
2f(k)-f(k-1)-f(k+1)
=\frac{2[\log k-f(k-1)]-k\log(1+1/k)}{k(k+1)}.
$$

对 $1,\ldots,k-1$ 使用算术—几何平均不等式，得到 $\log k-f(k-1)\ge\log2$。又有 $(1+1/k)^k<e<3$，故分子至少为 $\log(4/3)\ge1/4$。因此，在度数区间 $[1,m-1]$ 上，整数点函数 $f(k)+k^2/(8m^2)$ 的分段线性插值是凹函数。对平均值 $\eta=(m-1)/2$ 使用 Jensen 不等式得

$$
\sum_i f(d_i)
\le m\widetilde f(\eta)-\frac{V(Q)}{8m^2}+\frac{1}{32m},
$$

其中 $\widetilde f$ 为线性插值。最后一项处理半整数均值；整数均值时可省去。Stirling 公式给出

$$
\exp(m\widetilde f(\eta))\le K\sqrt{m+1}\frac{m!}{2^m}.
$$

再接入 Brégman 的行度数上界，即得上述方差估计。

删去大小为 $k$ 的集合 $U$ 后，每个剩余顶点的中心化度数改变至多 $k/2$；被删除的原平方偏差之和至多为 $kn^2/4$。对交叉项使用 Cauchy–Schwarz 不等式，得到

$$
V(T-U)\ge V(T)-\frac{kn^2}{4}-k\sqrt{nV(T)}.
$$

若 $V(T)\ge16n^2\log n$，则对所有 $k\le k_n$ 一致有

$$
V(T-U)\ge(1-o(1))V(T).
$$

于是每个短永久式的方差罚项至多为 $n^{-2+o(1)}$；前面的 $\sqrt n$ 因子可被吸收。按可求和的行列式权重求和，归一化短项总贡献至多为 $n^{-3/2+o(1)}$。加上长删集尾项，得到对该类图统一成立的结论

$$
V(T)\ge16n^2\log n\quad\Longrightarrow\quad
H(T)/\mu_n=o(1/n).
$$

### 5.3. 以非主四块展开排除极端度数

下面假设 $V(T)<16n^2\log n$。定义异常集

$$
F=\left\{i:\frac{d_i^+}{n-1}\notin[1/20,19/20]\right\},
\qquad f=|F|,\qquad M=T-F,\qquad N=n-f.
$$

每个异常顶点向 $V(T)$ 贡献至少某个固定正倍数的 $n^2$，故 $f=O(\log n)$。非异常顶点的原比分绝对值至多为 $0.9(n-1)$；删去 $F$ 改变它至多 $f$。因此，对所有充分大的 $n$ 一致有

$$
\max_i|(S_M\mathbf1)_i/(N-1)|<0.95,\qquad
\tau_M=O(\log n).
$$

进一步删除任意短核心子集后，同样的界仍成立，且常数保持固定。

先估计 $\operatorname{per}A_T$。使用第 5.1 节的核心成对权重 $\ell,r$，它们的总偏移满足

$$
\sum_{i\in M}|\ell_i-1|+\sum_{i\in M}|r_i-1|
\le K\sqrt{N\log n}.
$$

对 $x\in F$，记 $q_x=N^{-1}|\{j\in M:x\to j\}|$。它到 $[0,1/20]\cup[19/20,1]$ 的距离为 $O(f/n)$。两侧带权跨边邻居之和分别由 $N(q_x+\beta)$ 和 $N(1-q_x+\beta)$ 控制，其中 $\beta=O(\sqrt{\log n/n})$。置

$$
u_x=2(q_x+\beta),\qquad v_x=2(1-q_x+\beta).
$$

可对全部 $x$ 统一选取

$$
u_xv_x\le c_n=19/100+o(1),\qquad
u_x,v_x\le L_n=2+o(1).
$$

按排列在 $F$ 内部使用的边分解永久式。若内部有 $s$ 条边，其行集 $R$ 和列集 $C$ 均有 $s$ 个点；每个跨边方向恰有 $t=f-s$ 条边。核心行、列删集 $I,J$ 均有 $t$ 个点，但不必相同。精确四块展开为

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

每个有贡献的排列被唯一分类。核心永久式界中，删除行产生 $\ell_i$，删除列产生 $r_j$。将这些因子接入对应跨边匹配，再去掉互异性限制，两个跨边求和的乘积至多为

$$
N^{2t}2^{-2t}
\left(\prod_{x\notin R}u_x\right)
\left(\prod_{y\notin C}v_y\right).
$$

异常内部永久式至多为 $s!$。除以 $n!/2^n$ 后，完整的阶乘与二次幂恢复因子为

$$
2^sN^{2t}\frac{(N-t)!}{(N+f)!}
=\left(\frac2N\right)^s\exp(O(f^2/N)).
$$

该因子包含两个跨边方向和核心阶数的全部贡献，没有省略其中任何一项。

令 $h=|R\cap C|$。成对乘积满足

$$
\left(\prod_{x\notin R}u_x\right)
\left(\prod_{y\notin C}v_y\right)
\le c_n^{f-2s}L_n^{2s}(c_n/L_n^2)^h
\le c_n^{f-2s}L_n^{2s}.
$$

第一个不等式由分别计算携带两个因子、一个因子和零个因子的顶点得到；即使 $f-2s$ 为负，它仍正确。第 5.1 节的永久式误差在 $t\le f=O(\log n)$ 内统一为 $o(1)$，其因子 $\Gamma\le1$ 可舍去。由 $\binom fs^2s!\le f^{2s}/s!$，完整求和得到

$$
\frac{\operatorname{per}A_T}{n!/2^n}
\le(1+o(1))e^{-1}D_N(S_M)c_n^f
\exp(O(f^2/N))
\exp\left(\frac{2L_n^2f^2}{c_n^2N}\right).
$$

其中额外指数均为 $o(1)$。进一步删除短核心子集 $U$ 后，上述估计仍统一成立。此时核心 Gaussian 因子改变为原来的 $\exp(O(|U|/n))$ 倍：对 $S_M/N$ 使用 Gaussian 删行列引理，对数损失为 $O(|U|/n)$；将归一化尺度从 $N$ 改为 $N-|U|$ 也有同阶成本。

在路径卷积中，大小为 $k$ 且与 $F$ 相交的子集占比至多为 $fk/n$。通用永久式界因而使其全部归一化短项贡献至多为

$$
K\frac f{\sqrt n}\sum_k kw_k=o(1).
$$

对包含于核心的子集，恢复下降阶乘后，对正主子式求和。任意核心阶数 $N\le n$ 均满足由秩一行列式恒等式给出的界

$$
\det\left(I_N+\frac2n(I_N+A_M)\right)
\le2e\det(I_N+S_M/N).
$$

证明时先提出 $(1+1/n)^N\le e$。剩余全一秩一因子至多为 $1+N/(n+1)<2$，因为 $I+S_M/(n+1)$ 的逆矩阵的实二次型至多为向量范数的平方。最后，反对称频率行列式乘积在尺度从 $1/(n+1)$ 增至 $1/N$ 时单调增大。

短子集的下降阶乘恢复带来 $\exp(O(k_n^2/n))=1+o(1)$。由于最终 $c_n<1/4$，上述统一估计给出

$$
\frac{H(T)}{\mu_n}
\le(1/4)^f\rho_N(S_M)+o(1)
\le C_*/4+o(1)<1,\qquad f\ge1.
$$

长尾已经是 $o(1/n)$。对随机竞赛图取平均有 $P(n)\ge\mu_n$，故包含异常点的图在充分大阶数不能达到最大路径数。这里只需统一 $o(1)$ 误差便可排除该类图；并未声称对此类图取得 $O(1/n)$ 的近似公式。

### 5.4. 在剩余类中保留完整比分罚项

剩余竞赛图满足

$$
\max_i|a_i|\le0.9,\qquad
a=s/(n-1),\qquad \tau=\sum_i a_i^2\le K\log n.
$$

其成对乘积满足

$$
\Gamma=\prod_i(1-a_i^2)\le e^{-\tau}.
$$

为完整起见，置 $\omega_i=a_i^2/(1-a_i^2)$、$v_i=a_i/(1-a_i^2)$。成对预缩放矩阵 $C'=\operatorname{diag}(\ell)\,(2A/(n-1))\,\operatorname{diag}(r)$ 的总质量为 $n+\nu$，其中有精确恒等式

$$
\nu=\frac{(\sum_i\omega_i)^2-(\sum_iv_i)^2+\sum_i\omega_i+
2\omega^{\mathsf T}Sv}{n-1}.
$$

利用 $\sum_i a_i=0$、$|a_i|$ 的固定上界及 $S$ 每行的二范数 $\sqrt{n-1}$，可得 $|\nu|\le K\mathcal M_\tau$。这里使用的是整个图的比分，而非另选核心的比分。

对大小为 $k\le k_n$ 的主删集 $U$，第 5.1 节给出

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

在累计误差时，必须保留公共因子 $\Gamma$。定义非负系数

$$
c_k=(2/n)^k\sum_{|U|=k}\det(I+A[U])\prod_{i\in U}g_i.
$$

它们满足 $c_0=1$、$c_k\le G^kw_k$。下降阶乘的恢复产生

$$
\log\frac{n^k}{(n)_k}=O(k^2/n),\qquad k\le k_n.
$$

令 $\delta_n=\sqrt{\tau/n}+1/n$，$r_k=R_{\tau,k}+\log(n^k/(n)_k)$。将误差上界选为非负值后，对 $\tau\le K\log n$ 一致有 $0\le r_k\le K\delta_n(k+k^2)$，且 $\max_{k\le k_n}r_k=o(1)$。因此

$$
\sum_{k\le k_n}c_ke^{r_k}
\le\sum_{k=0}^{n}c_k+
K\delta_n\sum_{k\ge0}G^kw_k(k+k^2)
\le\left(\sum_{k=0}^{n}c_k\right)e^{K\delta_n}.
$$

最后一步使用 $\sum_kc_k\ge1$ 以及相应固定矩的收敛性。归一化短路径总和因而至多为

$$
\frac{e^{-1}D_n(S)\Gamma}{2}
e^{R_\tau+K\delta_n}
\det\left(I+\frac2n\operatorname{diag}(g)(I+A)\right).
$$

这是一个相对误差估计，$\Gamma$ 始终位于整个求和之外。

下面去除权重，同时保持比分罚项。令 $W=I+(2/n)(I+A)$、$\Delta=(2/n)\operatorname{diag}(g-1)(I+A)$。$W$ 的对称部分至少为 $I$，故 $\|W^{-1}\|_{\rm op}\le1$。由于 $I+A$ 每行的二范数至多为 $\sqrt n$，且 $\sum_i(g_i-1)\le K\tau$，将 $\Delta$ 分解为秩一行矩阵之和，得到核范数估计

$$
\|\Delta\|_*\le K\tau/\sqrt n.
$$

由行列式不等式 $|\det(I+E)|\le\exp(\|E\|_*)$，可得

$$
\det(W+\Delta)\le\det(W)e^{K\tau/\sqrt n}.
$$

两个行列式均为正：$W$ 的对称部分正定；加权行列式的主子式展开系数为正。第 5.3 节的无权秩一界在 $N=n$ 时为 $\det(W)\le2e\det(I+S/n)$。

合并上述各因子，最后仅加入长删集尾项，得到统一的比分敏感上界

$$
\frac{H(T)}{\mu_n}\le
\rho_n(S)\exp\left\{-\tau+
K\left[\frac{1+\tau+\tau^2}{n}
+\frac{\tau^{3/2}+\tau}{\sqrt n}+\sqrt{\tau/n}\right]\right\}
+o(1/n).
$$

当 $\tau\le K\log n$ 时，除常数 $1/n$ 外的多项式误差项，在充分大阶数总共至多消耗 $\tau/4$。剩余平方根项由 Young 不等式控制：

$$
K\sqrt{\tau/n}\le\tau/4+K^2/n.
$$

因此总指数至多为 $-\tau/2+K/n$。再使用谱上限，得到

$$
H(T)/\mu_n\le C_*e^{K/n}+o(1/n)=C_*+O(1/n).
$$

### 5.5. 完成统一上界

三类图覆盖全部竞赛图。高方差图的归一化路径数为 $o(1/n)$；低方差但含异常点的图严格低于一；所有剩余图满足刚才的 $C_*+O(1/n)$ 上界。因此

$$
\boxed{P(n)\le\bigl(C_*+O(1/n)\bigr)\mu_n.}
$$

证明没有对极值图预设正则性，也没有假设松弛装填频谱可以实现。所有估计在充分大阶数统一成立，但未给出有效起始阶数。
