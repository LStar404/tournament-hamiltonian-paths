# 竞赛图中 Hamilton 路径数的常数因子界

刘星辰、叶祥宇

个人研究者

lxc-em5158@outlook.com

2026年10月8日；2026年10月11日修订

## 摘要

设 $P(n)$ 为 $n$ 阶竞赛图中有向 Hamilton 路径数的最大值，$\mu_n=n!/2^{n-1}$ 为随机竞赛图的路径数期望。本文证明

$$
(L-O(n^{-1}))\mu_n\le P(n)\le(C_*+O(n^{-1}))\mu_n,
$$

其中

$$
L=\frac{\cosh1}{\cos1}=2.855957892565\ldots,
\qquad
C_*=\frac{3\pi^4+4\pi^2-32}{\pi^4+4\pi^2-32}
=2.857401177672\ldots.
$$

上界对所有竞赛图成立。证明从路径计数的正行列式—永久式恒等式出发，利用统一永久式近似与定量矩阵缩放将其化为谱估计，再用度数方差和乘法形式的比分罚项控制不规则竞赛图。最后，由反对称谱半径界和凸优化得到 $C_*$。奇偶两类圆环竞赛图给出下界。两个首项常数的相对间隙约为 $0.050536\%$。配套 Lean 工程证明了主定理及一致的小比分路径近似。

关键词：竞赛图；有向 Hamilton 路径；永久式；矩阵缩放；反对称谱。

## 1. 引言与主要结果

一个竞赛图最多能包含多少条有向 Hamilton 路径？对 $n$ 阶竞赛图 $T$，记 $H(T)$ 为满足全部相邻关系 $v_j\to v_{j+1}$ 的顶点排列 $(v_1,\ldots,v_n)$ 的数量。路径按有向顶点序列计数。定义

$$
P(n)=\max_{|V(T)|=n}H(T),\qquad \mu_n=\frac{n!}{2^{n-1}}.
$$

每个排列在均匀随机竞赛图中形成有向路径的概率为 $2^{-(n-1)}$。因此 $\mathbb E H(T)=\mu_n$ 且 $P(n)\ge\mu_n$，即 Szele [10] 的经典下界。问题是如何通过选择方向，使路径数比这一期望大得更多。

Adler、Alon 和 Ross [9，定理 1] 将下界改进为 $P(n)\ge(e-o(1))\mu_n$，并提出 $P(n)=\Theta(\mu_n)$ 是否成立的问题 [9，备注 3]。Wormald [6, Theorem 5] 对无穷多个 $n$ 证明了 $P(n)>2.85588\mu_n$，并猜想极限比值约为 $2.855958$。

上界方面，Alon [2] 用永久式证明了 $P(n)=O(n^{3/2})\mu_n$。将 Friedgut 与 Kahn [7] 的 Hamilton 圈上界与 [2, Proposition 2.5] 的路径到圈构造结合，可得 $P(n)=O(n^{3/2-\xi})\mu_n$，其中 $\xi\approx0.2507$。下面的定理 1.1 对任意竞赛图给出常数因子上界，从而确立 $P(n)=\Theta(\mu_n)$。其下界适用于所有充分大的阶数，给出显式首项常数和 $O(n^{-1})$ 误差；主要进展在于统一的常数因子上界，而不只是改进下界常数。

**定理 1.1（主要结果）。** 存在绝对常数 $K\ge0$ 及 $n_0\ge2$，使得对每个整数 $n\ge n_0$，

$$
(L-K/n)\mu_n\le P(n)\le(C_*+K/n)\mu_n,
$$

其中

$$
L=\frac{\cosh1}{\cos1},\qquad
a_*=\frac4{\pi^2},\qquad
C_*=\frac{1+a_*}{1-a_*}\frac{3/2-a_*}{1/2+a_*}.
$$

主要困难是对任意竞赛图证明上界。Brégman 不等式根据行和控制永久式，但即使对正则竞赛图，其上界与自然尺度 $n!/2^n$ 仍相差一个 $\sqrt n$ 量级的因子。要消除这一损失，需要利用竞赛图定向在不同行之间施加的关系。

我们使用 Irving 与 Omar [1] 的行列式—永久式路径恒等式。其各项均非负，而且只有较小的顶点删集具有显著贡献。因此，计数问题归结为对大子矩阵永久式的精确估计。对近正则竞赛图，这些估计给出谱因子 $\rho_n(S)$，其中 $S=A-A^{\mathsf T}$ 为反对称邻接矩阵。第 2.3 节先解释这一因子的来源，再进入技术证明。

证明需要解决三个定量问题。第一，永久式近似必须对一整类矩阵一致成立，而不只是逐个控制固定次数的系数。第二，需要把实际邻接子矩阵缩放为行列和相等的矩阵；分离异常顶点时，行删集与列删集还可能不同。第三，需要将任意竞赛图归约到可以实施这种缩放的图类。在该类中，恢复缩放因子会产生负的比分指数，用于吸收近似误差。

正文先给出计数论证。第 2 节建立精确恒等式和谱上界；第 3 节以一个明确陈述的永久式估计为输入，证明统一上界；第 4 节证明小比分路径公式及圆环图下界。第 5、6 节随后分别证明永久式估计和缩放估计。永久式证明使用 McCullagh [5] 的行列式近似视角及 Han 与 Niles-Weed [3] 使用的 Gaussian 永久式工具；反对称谱半径比较见 Deng、Li、Shader 与 So [4]。本文给出所需版本及其证明。附录 A 说明正文与配套形式化证明的对应关系。

## 2. 计数恒等式与谱因子

### 2.1 矩阵、比分与谱因子

邻接矩阵 $A$ 的对角元为零，且 $A_{ij}=1$ 当且仅当 $i\to j$。定义

$$
S=A-A^{\mathsf T},\qquad 2A=J-I+S,\qquad s=S\mathbf1.
$$

其中 $I$ 为单位矩阵，$J=\mathbf1\mathbf1^{\mathsf T}$，$\mathbf1$ 为全一列向量。若 $d_i^+$ 为出度，则 $s_i=2d_i^+-(n-1)$ 且 $\sum_i s_i=0$。使用记号

$$
\mathcal E=\|s\|_2^2,\qquad d=\|s\|_\infty,\qquad
a=\frac{s}{n-1},\qquad \tau=\|a\|_2^2.
$$

标准化比分 $a$ 与 $\tau$ 在 $n\ge2$ 时定义。奇阶正则图满足 $s=0$，偶阶平衡图满足 $s_i\in\{-1,1\}$。因此，$d$ 衡量最大的顶点不平衡程度，$\tau$ 则衡量归一化后的不平衡平方总量。

对顶点集 $U$，$A[U]$ 表示主子矩阵。对可能不同的行、列集 $R,C$，写 $A[R,C]$。空矩阵的行列式和永久式均约定为一。永久式定义为

$$
\operatorname{per}M=\sum_{\pi\in\mathfrak S_m}\prod_{i=1}^m M_{i,\pi(i)}.
$$

实矩阵 $M$ 的奇异值是 $M^{\mathsf T}M$ 的特征值的平方根。最大奇异值为 $\|M\|_{\rm op}$，奇异值平方之和为 $\|M\|_F^2=\sum_{i,j}|M_{ij}|^2$。对反对称矩阵 $S$，记其非零成对特征值为 $\pm i\lambda_j$，其中 $\lambda_j>0$，必要时补零频率。每个 $\lambda_j$ 在奇异值中出现两次。定义

$$
x_j=\frac{\lambda_j^2}{n^2},\qquad
D_n(S)=\det(I-S^{\mathsf T}S/n^2)^{-1/2},
$$

$$
\rho_n(S)=D_n(S)\det(I+S/n)=\prod_j\frac{1+x_j}{1-x_j}.
$$

反对称奇异值成对出现，且 $\|S\|_F^2=n(n-1)$，故

$$
\sum_jx_j=\frac{n-1}{2n},\qquad \|S/n\|_{\rm op}^2\le\frac{n-1}{2n}<\frac12.
$$

因此 $D_n$ 与 $\rho_n$ 都为正，且有绝对常数上界。特别地，

$$
D_n(S)=\det(I+iS/n)^{-1}.
$$

### 2.2 正路径卷积

**引理 2.1（路径卷积）。** 对任意竞赛图，

<a id="eq-path-convolution"></a>

$$
H(T)=\sum_{U\subseteq V(T)}\det(I+A[U])\operatorname{per}A[U^c].
\tag{2.1}
$$

邻接矩阵的永久式计算有向圈覆盖数。卷积[式 (2.1)](#eq-path-convolution)把互补顶点集上的圈覆盖数转换成路径数。它是 Irving 与 Omar 的 Proposition 2 [1] 在竞赛图上的特化，其中补邻接矩阵为 $\overline A=J-A=I+A^{\mathsf T}$，包含对角元。

也可用生成函数直接核对。令 $X=\operatorname{diag}(z_1,\ldots,z_n)$，每次访问一个顶点即乘上对应变量，则全部游走的生成函数为

$$
1+\mathbf1^{\mathsf T}(I-XA)^{-1}X\mathbf1
=\frac{\det(I+X\overline A)}{\det(I-XA)}.
$$

等号来自秩一行列式引理。取 $z_1\cdots z_n$ 的系数，恰选出全部 Hamilton 路径。对分母，形式恒等式 $\det(I-XA)^{-1}=\exp(\sum_{r\ge1}\operatorname{tr}((XA)^r)/r)$ 表明，其无平方因子系数计算不交有向圈覆盖数，因而等于永久式。再结合分子的主子式展开，得到

$$
H(T)=\sum_U\det\overline A[U]\operatorname{per}A[U^c].
$$

代入 $\overline A[U]=I+A[U]^{\mathsf T}$ 即得结论。

令 $k=|U|$。矩阵 $I+A[U]$ 的对称部分为正定矩阵 $(I+J)/2$，故实特征值均为正，非实特征值共轭成对，从而行列式为正。各行平方范数为 $1+d_i^+(T[U])$，平均值为 $(k+1)/2$。由 Hadamard 不等式及算术—几何平均不等式得

$$
0<\det(I+A[U])\le h_k,\qquad h_k=\left(\frac{k+1}{2}\right)^{k/2}.
$$

约定 $h_0=1$，并令

$$
w_k=\frac{2^k h_k}{k!}.
$$

对任意固定 $c>0$ 和非负整数 $r$，

$$
\sum_{k\ge0}k^r c^k w_k<\infty.
$$

因为 Stirling 公式给出 $\log(c^kw_k)=-(k/2)\log k+O_c(k)$。对充分大 $n$，取

$$
k_n=\left\lceil\frac{4\log n}{\log\log n}\right\rceil,
$$

即有 $\sum_{k>k_n}c^kw_k=n^{-2+o(1)}$。

使用 [2, Lemma 2.1] 所述的 Brégman 界及 [2, Corollary 2.3] 的度数平衡化，再结合 Stirling 公式，给出统一常数 $C$，使任意 $m$ 阶竞赛图满足

$$
\operatorname{per}A_T\le C\sqrt{m+1}\,\frac{m!}{2^m}.
$$

增大 $C$ 后也覆盖 $m=0$。引理 3.2 将证明含方差罚项的版本。于是路径卷积中 $|U|>k_n$ 的贡献除以 $\mu_n$ 后，至多为

$$
\frac C2\sqrt{n+1}\sum_{k>k_n}w_k
=n^{-3/2+o(1)}=o(n^{-1}).
$$

该界对所有竞赛图一致。称 $|U|\le k_n$ 的项为短项；路径卷积中的永久式只需在这些项上精确估计。

### 2.3 谱因子的来源

下面的计算说明需要控制的量为何是 $\rho_n(S)$。暂设最大比分满足 $d=o(\sqrt n)$。引理 6.4 将证明，对短删集 $|U|=k$，

$$
\operatorname{per}A[U^c]
=e^{-1}D_n(S)\frac{(n-k)!}{2^{n-k}}
\left(1+O\left(\frac{(d+k+1)^2}{n}\right)\right).
$$

归一化满足 $((n-k)!/2^{n-k})/\mu_n=2^{k-1}/(n)_k$。因此，将主项代入引理 2.1，所得归一化总和为

$$
\frac{e^{-1}D_n(S)}2
\sum_{|U|\le k_n}\frac{2^{|U|}}{(n)_{|U|}}\det(I+A[U]),
$$

其中 $(n)_k=n(n-1)\cdots(n-k+1)$。在短和中将 $(n)_k$ 换为 $n^k$，再补入可忽略的尾项，所产生的误差将在第 4.1 节估计。所得完整总和满足精确的主子式恒等式：

$$
\sum_U(2/n)^{|U|}\det(I+A[U])
=\det\left(I+\frac2n(I+A)\right).
$$

由 $2A=J-I+S$，秩一项 $J$ 渐近贡献因子二，标量项贡献 $e$。更确切地，小比分假设给出

$$
\det\left(I+\frac2n(I+A)\right)
=2e\det(I+S/n)\left(1+O(n^{-1}+d^2/n^2)\right).
$$

永久式估计中的 $e^{-1}$ 来自恢复 $(1-1/n)^{n-k}$，对应零对角线的影响；$1/2$ 则来自上述路径归一化。它们与生成行列式中的 $2e$ 抵消，留下 $D_n(S)\det(I+S/n)=\rho_n(S)$。两个行列式各有来源：前者近似圈覆盖数，后者对路径卷积的权重求和。定理 4.1 将完成误差求和，证明

$$
\frac{H(T)}{\mu_n}=\rho_n(S)+O((d+1)^2/n)
\qquad\text{当 }d=o(\sqrt n).
$$

为得到全体竞赛图的上界，第 3 节另行处理高比分方差及极端度数，并在剩余图类中保留比分罚项。下面的引理则对每个竞赛图控制同一个谱因子。

### 2.4 谱上限与凸装填

**引理 2.2（谱上限）。** 任意竞赛符号矩阵满足

$$
\|S\|_{\rm op}\le\cot\left(\frac{\pi}{2n}\right)<\frac{2n}{\pi},
\qquad \rho_n(S)\le C_*.
$$

**证明。** 这里先给出算子上限的相位排序证明 [4, Theorem 3.1 及 Corollary 3.2]，再完成所需的凸优化。$iS$ 为谱关于零对称的 Hermitian 矩阵，其最大特征值等于 $\|S\|_{\rm op}$。对任意复向量 $z$，同时对 $z,S$ 作带符号置换，使非零坐标的相位落入 $[0,\pi)$ 并递增排列；零坐标任意安放。于是 $i<j$ 时 $c_{ij}=\operatorname{Im}(\overline z_i z_j)\ge0$。设 $T_n^0$ 为上三角全一的传递符号矩阵，则

$$
z^*iSz=-2\sum_{i<j}S_{ij}c_{ij}
\le2\sum_{i<j}c_{ij}=z^*(-iT_n^0)z.
$$

取 Rayleigh 商最大值得 $\|S\|_{\rm op}\le\|T_n^0\|_{\rm op}$。计算后者时，相邻行的特征方程给出 $(\lambda-1)v_i=(\lambda+1)v_{i+1}$。由首行方程，几何比 $r=(\lambda-1)/(\lambda+1)$ 满足 $r^n=-1$，故全部特征值为 $i\cot((2j-1)\pi/(2n))$，$1\le j\le n$。所述范数由此得出；当 $n\ge2$ 时，最后的严格不等式使用 $\tan u>u$；$n=1$ 的情形直接成立。

因此 $0\le x_j\le a_*$ 且 $\sum_jx_j<1/2$。函数

$$
\phi(x)=\log\frac{1+x}{1-x}
$$

在 $[0,1)$ 单调递增且凸。将两个内部坐标的质量移向一个上限坐标和一个余数坐标，不会减小 $\sum_j\phi(x_j)$。必要时补零，并把总质量放宽到 $1/2$。因 $1/4<a_*<1/2$，松弛最大值由 $a_*,1/2-a_*,0,\ldots$ 取得。取指数即得到 $C_*$。竞赛图矩阵的可实现谱包含在这个松弛区域中，故松弛问题的最大值给出 $\rho_n(S)$ 的上界。引理证毕。

同一特征值计算也给出下面的恒等式，亦见 [4, Theorem 2.1]：

$$
\det(I+zT_n^0)=\frac{(1+z)^n+(1-z)^n}{2}.
$$

第 4 节将用这一行列式多项式计算圆环构造的谱因子。

## 3. 对全体竞赛图的上界

记

$$
V(T)=\sum_i\left(d_i^+-\frac{n-1}{2}\right)^2
=\frac14\|S\mathbf1\|_2^2,
\qquad
\tau=\frac{4V(T)}{(n-1)^2}.
$$

证明分为三种情形。若 $V(T)\ge16n^2\log n$，Brégman 不等式中的方差罚项使路径数可以忽略。否则，度数落在 $[(n-1)/20,19(n-1)/20]$ 之外的顶点至多有 $O(\log n)$ 个。若存在这样的顶点，将它们与其余部分分离后，可得路径数低于随机期望。剩余竞赛图的归一化比分与 $\pm1$ 保持固定距离，且 $\tau=O(\log n)$。对它们，下面的永久式估计保留因子 $e^{-\tau}$，从而将最终误差控制到 $O(n^{-1})$。

本节中的 $K$ 可以在不同位置增大；固定上述度数阈值后，它是绝对常数。第 2.2 节已将长项控制为 $o(n^{-1})\mu_n$，故这里只估计短项 $|U|\le k_n$。

### 3.1 归约所需的永久式估计

下面的引理是计数论证的分析输入。包括所需对角缩放存在性在内的完整证明见第 6.4 节。这里允许行删集与列删集不同，因为圈覆盖进入、离开异常集时可能使用不同的核心顶点。

**引理 3.1（非主永久式界）。** 固定 $0\le b<1$ 及正常数 $A_0,B_0$。对 $N$ 阶竞赛图核心，置 $a=S\mathbf1/(N-1)$，$\tau=\sum_i a_i^2$，并假设

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

对所有充分大的 $N$，该估计对每个满足条件的竞赛图及每对 $I,J$ 同时成立。常数 $K$ 和起始阶数仅依赖 $b,A_0,B_0$。

因子 $\Gamma$ 记录度数不平衡的代价。对主删集 $I=J=U$，恢复的顶点权重为 $\ell_i r_i=(1-a_i^2)^{-1}$；删集不同时，行、列因子分别保留。误差中含有 $\sqrt{\tau/N}$ 量级的项，因此在最后一种情形中，必须保留 $\Gamma\le e^{-\tau}$。

### 3.2 高比分方差

**引理 3.2（含方差罚项的永久式界）。** 存在绝对常数 $K$，使每个 $m\ge1$ 阶竞赛图 $Q$，若其出度为 $d_i$，度数方差为 $V(Q)=\sum_i(d_i-(m-1)/2)^2$，则满足

$$
\operatorname{per}A_Q\le
K\sqrt{m+1}\frac{m!}{2^m}\exp\left(-\frac{V(Q)}{8m^2}\right).
$$

**证明。** 利用行度数因子的凹性，可以加强 Brégman 界 [2]。若某个 $d_i=0$，上界显然成立。否则，对正整数定义 $f(k)=\log(k!)/k$。直接计算得，对 $k\ge2$，

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

再接入 Brégman 的行度数上界，即得上述方差估计。$\square$

下面将此界用于每个短删集对应的竞赛图。为此，需要确认删点后方差仍然足够大。

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

### 3.3 异常顶点

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

对比分平方和，使用 $\|S_M\mathbf1\|_2\le\|S\mathbf1\|_2+f\sqrt N$，再除以 $N-1$。进一步删除短核心子集后，同一论证仍然适用。在这些删除中始终保留原异常集 $F$，因此常数可以统一选取。

先按圈覆盖在 $F$ 与核心 $M$ 之间的连接方式估计 $\operatorname{per}A_T$。异常顶点在某个方向上的邻居很少。圈覆盖需要使用两个方向的边，除非将该顶点匹配到 $F$ 内部；后一种选择会产生 $1/N$ 量级的代价。使用引理 3.1 的核心成对权重 $\ell,r$，它们的总偏移满足

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

每个有贡献的排列被唯一分类。先对核心永久式使用引理 3.1 的一致上界，再分离两个跨边求和。删除核心行产生 $\ell_i$，删除核心列产生 $r_j$。固定 $R,C$，向外跨边求和精确等于

$$
\begin{aligned}
&\sum_{\substack{J\subseteq M\\|J|=t}}
\operatorname{per}A[F\setminus R,J]\prod_{j\in J}r_j\\
&=\sum_{\phi:F\setminus R\hookrightarrow M}
\prod_{x\in F\setminus R}A_{x,\phi(x)}r_{\phi(x)}
\le\prod_{x\in F\setminus R}\sum_{j\in M}A_{xj}r_j.
\end{aligned}
$$

独立地，向内跨边求和为

$$
\begin{aligned}
&\sum_{\substack{I\subseteq M\\|I|=t}}
\operatorname{per}A[I,F\setminus C]\prod_{i\in I}\ell_i\\
&=\sum_{\psi:F\setminus C\hookrightarrow M}
\prod_{y\in F\setminus C}A_{\psi(y),y}\ell_{\psi(y)}
\le\prod_{y\in F\setminus C}\sum_{i\in M}A_{iy}\ell_i.
\end{aligned}
$$

其中 $\hookrightarrow$ 表示单射。每个单射由其像集及相应永久式项恰好计数一次，没有额外的 $t!$ 因子。像集 $I,J$ 不必相等，也不必不交，因为它们分别属于核心的行、列副本。所有因子非负，故可去掉单射限制。两个上界的乘积为

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

这里 $N+f-(N-t)=f+t=2f-s$，故阶乘比贡献 $N^{-(2f-s)}\exp(O(f^2/N))$，再乘 $N^{2t}$ 后恰留下 $N^{-s}$。

令 $h=|R\cap C|$。成对乘积满足

$$
\left(\prod_{x\notin R}u_x\right)
\left(\prod_{y\notin C}v_y\right)
\le c_n^{f-2s}L_n^{2s}(c_n/L_n^2)^h
\le c_n^{f-2s}L_n^{2s}.
$$

第一个不等式由分别计算携带两个因子、一个因子和零个因子的顶点得到；即使 $f-2s$ 为负，它仍正确。引理 3.1 的误差在 $t\le f=O(\log n)$ 内统一为 $o(1)$，其因子 $\Gamma\le1$ 可舍去。由 $\binom fs^2s!\le f^{2s}/s!$，完整求和得到

$$
\frac{\operatorname{per}A_T}{n!/2^n}
\le(1+o(1))e^{-1}D_N(S_M)c_n^f
\exp(O(f^2/N))
\exp\left(\frac{2L_n^2f^2}{c_n^2N}\right).
$$

其中额外指数均为 $o(1)$。具体地，删除短核心子集 $U$ 后，核心阶数为 $N'=n-f-|U|\sim n$，异常集合仍取原来的 $F$。核心的归一化比分最终仍不超过 $0.95$，平方比分和为 $O(\log n)$，而跨边删集大小为 $t\le f=O(\log n)$。因此引理 3.1 中的误差指数为

$$
O\!\left(\frac{(\log n)^{3/2}}{\sqrt n}+\frac{(\log n)^2}{n}\right)=o(1),
$$

其中常数与 $U,I,J$ 无关。跨边邻点比例相较于原始全图仅改变 $O((f+|U|)/n)$，权重的一范数位移仍为 $O(\sqrt{n\log n})$，故前述跨边求和估计也一致成立。此时核心 Gaussian 因子改变为原来的 $\exp(O(|U|/n))$ 倍：对 $S_M/N$ 使用 Gaussian 删行列引理，对数损失为 $O(|U|/n)$；将归一化尺度从 $N$ 改为 $N-|U|$ 也有同阶成本。

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

由于 $P(n)\ge\mu_n$，这个严格小于一的固定间隙说明：对所有充分大的阶数，这类竞赛图不能达到最大值。此处只需 $o(1)$ 误差。此处保留成对谱因子，以显示它与后续归约的联系。对于删除集与 $F$ 不相交的短卷积项，Lean 证明使用较弱但足够的界 $(10/3)4^{-f}(1+\varepsilon_n)$。与 $F$ 相交的短项及长项另贡献 $\delta_n$，因此完整上界为

<a id="eq-exceptional-bound"></a>

$$
\frac{H(T)}{\mu_n}\le\frac{10}{3}4^{-f}(1+\varepsilon_n)+\delta_n,
\qquad \varepsilon_n,\delta_n\longrightarrow0.
\tag{3.1}
$$

两个误差在所讨论的低方差图类上一致成立。由于 $f$ 可以随 $n$ 增长，二者不能混同。形式化证明最终取 $1+\varepsilon_n\le21/20$，另外两部分各不超过 $1/25$。于是当 $f\ge1$ 时，[式 (3.1)](#eq-exceptional-bound)给出明确预算

$$
\frac{10}{3}\cdot\frac14\cdot\frac{21}{20}+\frac1{25}+\frac1{25}
=\frac{191}{200}<1.
$$

两种选择均不影响最终上界常数。

### 3.4 剩余图类中的比分罚项

剩余竞赛图满足

$$
\max_i|a_i|\le0.9,\qquad
a=s/(n-1),\qquad \tau=\sum_i a_i^2\le K\log n.
$$

以下固定一个绝对常数 $K_0$，使 $\tau\le K_0\log n$。其成对乘积满足

$$
\Gamma=\prod_i(1-a_i^2)\le e^{-\tau}.
$$

现在对整个竞赛图应用引理 3.1。比分乘积是所有短项共有的因子；将它保持在总和之外，可以吸收那些单独看来比 $1/n$ 更大的误差。

对大小为 $k\le k_n$ 的主删集 $U$，引理 3.1 给出

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

令 $\delta_n=\sqrt{\tau/n}+1/n$，$r_k=R_{\tau,k}+\log(n^k/(n)_k)$。将误差上界选为非负值后，对 $\tau\le K_0\log n$ 一致有 $0\le r_k\le K\delta_n(k+k^2)$，且 $\max_{k\le k_n}r_k=o(1)$。因此

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

误差总和由 $G^kw_k$ 的有限矩控制，而非由最大删集大小 $k_n$ 控制。这避免了在最终误差中引入额外的对数因子。

下面去除权重，同时保持比分罚项。令 $W=I+(2/n)(I+A)$、$\Delta=(2/n)\operatorname{diag}(g-1)(I+A)$。$W$ 的对称部分至少为 $I$，故 $\|W^{-1}\|_{\rm op}\le1$。由于 $I+A$ 每行的二范数至多为 $\sqrt n$，且 $\sum_i(g_i-1)\le K\tau$，将 $\Delta$ 分解为秩一行矩阵之和，可以控制其迹范数，即奇异值之和。由 $\|uv^{\mathsf T}\|_*=\|u\|_2\|v\|_2$，得到

$$
\|\Delta\|_*\le K\tau/\sqrt n.
$$

由行列式不等式 $|\det(I+E)|\le\exp(\|E\|_*)$，可得

$$
\det(W+\Delta)\le\det(W)e^{K\tau/\sqrt n}.
$$

两个行列式均为正：$W$ 的对称部分正定；加权行列式的主子式展开系数为正。第 3.3 节的无权秩一界在 $N=n$ 时为 $\det(W)\le2e\det(I+S/n)$。

合并上述各因子，最后仅加入长删集尾项，得到统一的比分敏感上界

<a id="eq-score-penalty"></a>

$$
\frac{H(T)}{\mu_n}\le
\rho_n(S)\exp\left\{-\tau+
K\left[\frac{1+\tau+\tau^2}{n}
+\frac{\tau^{3/2}+\tau}{\sqrt n}+\sqrt{\tau/n}\right]\right\}
+o(1/n).
\tag{3.2}
$$

当 $\tau\le K_0\log n$ 时，除常数 $1/n$ 外的多项式误差项，在充分大阶数总共至多消耗 $\tau/4$。剩余平方根项由 Young 不等式控制：

$$
K\sqrt{\tau/n}\le\tau/4+K^2/n.
$$

[式 (3.2)](#eq-score-penalty)中的总指数因此至多为 $-\tau/2+K/n$。再使用谱上限，得到

$$
H(T)/\mu_n\le C_*e^{K/n}+o(1/n)=C_*+O(1/n).
$$

### 3.5 完成上界

三类图覆盖全部竞赛图。高方差图的归一化路径数为 $o(1/n)$；低方差但含异常点的图严格低于一；所有剩余图满足刚才的 $C_*+O(1/n)$ 上界。因此

$$
\boxed{P(n)\le\bigl(C_*+O(1/n)\bigr)\mu_n.}
$$

三种情形中的起始阶数均不依赖具体竞赛图，因此取一个共同阈值便得到定理 1.1 的上界。

## 4. 小比分路径公式与下界

**定理 4.1（小比分路径近似）。** 存在绝对常数 $C$，具有如下性质：对每个满足 $d(n)/\sqrt n\to0$ 的非负函数 $d=d(n)$，存在阈值 $n_0(d)$，使每个阶数为 $n\ge n_0(d)$ 且 $\|S\mathbf1\|_\infty\le d(n)$ 的竞赛图都满足

$$
\left|\frac{H(T)}{\mu_n}-\rho_n(S)\right|\le C\frac{(d(n)+1)^2}{n}.
$$

### 4.1 小比分近似的证明

**证明。** 以下记 $d=d(n)$。对每个主删集 $|U|=k\le k_n$，应用引理 6.4。因 $d+k_n+1=o(\sqrt n)$，其适用性对全部这些子集一致。恢复下降阶乘 $(n)_k$ 后，由正路径卷积得到

$$
\frac{H(T)}{\mu_n}
=\frac{e^{-1}D_n(S)}2
\sum_{k\le k_n}\left(\frac2n\right)^k
\sum_{|U|=k}\det(I+A[U])
+O\left(\frac{(d+1)^2}{n}\right).
$$

此误差率没有额外对数因子，因为误差至多为固定常数乘上

$$
\frac1n\sum_{k\ge0}w_k(d+k+1)^2
=O\left(\frac{(d+1)^2}{n}\right).
$$

下降阶乘恢复误差贡献 $O(n^{-1}\sum k^2w_k)$；大删集对应的项由第 2.2 节控制为 $o(n^{-1})$。将上式短生成和扩展到全部 $k$ 的代价为 $n^{-2+o(1)}$，因为系数被 $w_k$ 控制。于是

$$
\frac{H(T)}{\mu_n}
=\frac{e^{-1}D_n(S)}2
\det\left(I+\frac2n(I+A)\right)
+O\left(\frac{(d+1)^2}{n}\right).
$$

令 $u=\mathbf1/\sqrt n$，$Q=S/(n+1)$。秩一行列式引理给出

$$
\det\left(I+\frac2n(I+A)\right)
=(1+1/n)^n\det(I+Q)
\left(1+\frac n{n+1}u^{\mathsf T}(I+Q)^{-1}u\right).
$$

反对称性给出

$$
u^{\mathsf T}(I+Q)^{-1}u=u^{\mathsf T}(I-Q^2)^{-1}u,
$$

该量与一的差的绝对值不超过

$$
\|Qu\|_2^2\le\frac{d^2}{(n+1)^2}.
$$

又有 $(1+1/n)^n=e(1+O(n^{-1}))$；将 $S/(n+1)$ 换为 $S/n$ 的对数行列式误差为 $O(n^{-1})$，这是由归一化频率平方的有界总和得到的。因此

$$
\det\left(I+\frac2n(I+A)\right)
=2e\det(I+S/n)\left(1+O(n^{-1}+d^2/n^2)\right).
$$

代回即得定理。各估计使用同一个绝对常数；只有小比分条件开始成立的阶数依赖函数 $d$。$\square$

### 4.2 圆环竞赛图

**推论 4.2（圆环图下界）。** 对下面定义的奇阶圆环图及偶阶一点删除构造，

$$
H(\mathrm{Car}_n)/\mu_n=L+O(n^{-1}).
$$

**证明。** 对奇数 $n$，在模 $n$ 的剩余类上定义圆环竞赛图 $\mathrm{Car}_n$：当 $1\le j\le(n-1)/2$ 时，令 $i\to i+j$。该图正则，故 $d=0$。对偶数 $n$，令 $\mathrm{Car}_n$ 为 $\mathrm{Car}_{n+1}$ 删去一个顶点所得的图，此时 $d=1$。

奇阶圆环符号矩阵与 $T_n^0$ 带符号置换相似。一个显式构造是：用对角符号 $(-1)^i$，$0\le i<n$，共轭 $T_n^0$，再按 $0,2,\ldots,n-1,1,3,\ldots,n-2$ 重排指标；两个指标同奇偶时，切换后的边沿指标递增方向；异奇偶时方向相反。按上述循环顺序读取指标，即得到圆环方向。将逆向的带符号共轭和重排限制到偶阶的一点删除后，变换所得的矩阵为剩余有序指标上的 $T_n^0$。因此，删除任意一个顶点后，同一带符号谱计算仍然适用，奇偶两类均满足

$$
\rho_n(S_{\mathrm{Car}_n})
=r_n:=\frac{(n+1)^n+(n-1)^n}{(n+i)^n+(n-i)^n}.
$$

分子、分母均除以 $n^n$，并对四个固定值 $z=1,-1,i,-i$ 使用 $(1+z/n)^n$ 的 Taylor 展开，得到

$$
r_n=\frac{\cosh1}{\cos1}+O(n^{-1})=L+O(n^{-1}).
$$

故奇偶两类都有 $H(\mathrm{Car}_n)/\mu_n=L+O(n^{-1})$，于是

$$
P(n)\ge(L-O(n^{-1}))\mu_n.
$$

从带符号相似过渡到路径数，使用的是定理 4.1，分别对应 $d=0$ 和 $d=1$。设下界与上界的常数和阈值分别为 $K_l,N_l$ 与 $K_u,N_u$。取 $K=K_l+K_u$、$n_0=\max(N_l,N_u,2)$，即得定理 1.1。$\square$

## 5. 统一永久式近似

下面证明支撑全图归约的永久式估计。矩阵缩放到行列和均为一后，可以写成 $(J_n+E)/n$，其中 $E$ 在行、列两侧都中心化。下面的定理用 Gaussian 行列式近似其永久式，所需假设为元素有界及固定奇异值谱隙；第 6 节将对缩放后的竞赛图子矩阵验证这些条件。

McCullagh [5] 在适度偏离条件下得到了行列式主项。这里给出固定元素界 $C$、奇异值谱隙 $q$ 下的自包含版本，其误差对这些参数所确定的矩阵类一致成立。证明分别控制系数与尾项，以便将结论一致地用于第 6 节中的删除和缩放。Li [8, Theorem 2.1] 的近期相关近似假设中心扰动的最大绝对行和或列和为 $o(n)$；这一条件不覆盖相应行列和为 $n$ 量级的稠密核。

记 $P_n=J_n/n$。算子范数指 Euclidean 算子范数。对复矩阵 $Z$，以 $Z^*$ 表示共轭转置，$|Z|=(Z^*Z)^{1/2}$ 表示算子绝对值。

### 5.1 定理与证明思路

**定理 5.1（统一永久式近似）。** 固定 $0\le C<\infty$ 和 $0\le q<1$。设 $n\ge1$，$E\in\mathbb R^{n\times n}$ 满足

$$
E\mathbf1=E^{\mathsf T}\mathbf1=0,\qquad
\max_{i,j}|E_{ij}|\le C,\qquad
\|E/n\|_{\mathrm{op}}\le q.
$$

令 $B=E/n$。对所有满足上述条件的矩阵，一致地有

<a id="eq-uniform-permanent"></a>

$$
\frac{\operatorname{per}(J_n+E)}{n!}
=\det(I-BB^{\mathsf T})^{-1/2}+O_{C,q}(n^{-1}).
\tag{5.1}
$$

[式 (5.1)](#eq-uniform-permanent)也可写成行列式因子乘以相对误差 $1+O_{C,q}(n^{-1})$。

本节所用行列式平方根，在有关实区间上均取正平方根。假设给出 $\|B\|_{\mathrm F}^2\le C^2$。因此，行列式因子不小于一，并且被只依赖 $C,q$ 的常数一致控制。

主项来自配对。对行、列指标重复作容斥展开后，每个永久式系数成为二部多重图之和。中心化消去一度顶点，二度分量的总和恰为 Gaussian 行列式。其余分量按边数超过顶点数的数量，带来不同次幂的 $n^{-1}$ 因子。由此可在线性长度的系数范围内证明近似；随后，再用独立的复分析估计控制实际永久式多项式的剩余部分。

证明中令

$$
f(t)=\frac{\operatorname{per}(J_n+tE)}{n!},
\qquad G(t)=\det(I-t^2BB^{\mathsf T})^{-1/2}.
$$

选取 $1<\sigma<R<1/q$；当 $q=0$ 时不要求上界。例如可取

$$
R=\frac{3+q}{2(1+q)},\qquad \sigma=\frac{1+R}{2}.
$$

使用控制函数

$$
\Gamma(r)=\exp\left(\frac{C^2r^2}{2(1-q^2r^2)}\right),
\qquad r\ge0,\ rq<1.
$$

本节在 $q=0$ 时均省去涉及 $1/q$ 的上界限制。所有常数仅依赖 $C,q$ 及所选半径。第 5.6 节将它们合并为显式误差界。

### 5.2 系数与 Gaussian 配对

写 $f(t)=\sum_{k=0}^n a_kt^k$。按永久式中来自 $E$ 的元素展开，得到

$$
a_k=\frac1{(n)_k}
\sum_{\substack{I,J\subseteq[n]\\|I|=|J|=k}}
\operatorname{per}E[I,J],
$$

其中 $(n)_k=n(n-1)\cdots(n-k+1)$，$(n)_0=1$。定义

$$
F_k=\frac{(n)_k}{n^k}a_k
=\frac1{k!}
\sum_{\substack{i_1,\ldots,i_k\ \mathrm{distinct}\\
j_1,\ldots,j_k\ \mathrm{distinct}}}
\prod_{\ell=1}^kB_{i_\ell j_\ell},
\qquad
F(t)=\sum_{k=0}^nF_kt^k.
$$

右侧的求和在 $k>n$ 时仍有意义，此时求和集合为空，值为零。下面的形式恒等式采用这一约定。

记 $\Pi_k$ 为 $[k]$ 的集合分划格。“$k$ 个坐标互异”的示性函数具有标准的分划格容斥展开。[5, Section 4] 的永久式计算也使用成对分划展开。其中，大小为 $d$ 的块带 Möbius 权重 $(-1)^{d-1}(d-1)!$。分别对 $F_k$ 的行坐标和列坐标应用这一展开。每对分划对应一个二部多重图：边带互异标号 $1,\ldots,k$，两侧的顶点分别为行、列分划的块，每个大小为 $d$ 的块带上述权重。

每个顶点的数值标签独立地在 $[n]$ 中求和；不同顶点的数值标签允许相同。如果某个行顶点的度数为一，对其标签求和得到 $B$ 的一个列和，因而为零。度数为一的列顶点同样给出零行和。因此，只有所有顶点度数至少为二的图留下贡献。

例如，在二次和三次项中，保留下来的行、列分划各自都只有一个块。两侧 Möbius 权重的乘积分别为 $1$ 和 $4$，再除以 $k!$，得到

$$
F_2=\frac12\sum_{i,j}B_{ij}^2,
\qquad
F_3=\frac23\sum_{i,j}B_{ij}^3,
\qquad |F_3|\le\frac{2C^3}{3n}.
$$

二次项属于下面的 Gaussian 因子。三次项是第一个可能出现的核心修正，其 $n^{-1}$ 界展示了超额估计的作用。

所有顶点度数均为二的连通分量称为纯二度分量，其总指数生成函数为 $G(t)$。可用两个独立标准实 Gaussian 向量 $X,Y$ 直接验证：由 Wick 公式，

$$
\mathbb E\exp(tX^{\mathsf T}BY)
$$

中 $t^k$ 的系数恰等于边标号两侧的配对分划之和，而这些正是所有顶点均为二度的图。先对条件 Gaussian 分布积分，再将 $BB^{\mathsf T}$ 对角化，得到

$$
\mathbb E\exp(tX^{\mathsf T}BY)
=\mathbb E\exp\!\left(\frac{t^2}{2}X^{\mathsf T}BB^{\mathsf T}X\right)
=\det(I-t^2BB^{\mathsf T})^{-1/2}.
$$

该解析恒等式在 $|t|\|B\|_{\mathrm{op}}<1$ 时成立，并确定全部形式系数。特别地，$G$ 的系数非负，且

$$
G(r)\le\Gamma(r)\qquad(r\ge0,\ rq<1),
$$

因为 $-\log(1-x)\le x/(1-x)$，且 $\sum_i s_i^2=\|B\|_{\mathrm F}^2\le C^2$；这里 $s_i$ 为 $B$ 的奇异值。

从每个留下贡献的图中删除全部纯二度分量，称剩余部分为核心。核心可以不连通。如果核心有 $h$ 条边、$v$ 个顶点，定义其超额为 $j=h-v$。非空核心满足 $j\ge1$。带边标号的分量分解给出逐系数恒等式

$$
F(t)=G(t)\left(1+\sum_{j\ge1}C_j(t)\right),
$$

其中 $C_j$ 为超额 $j$ 的核心生成级数，保留全部 Möbius 符号与矩阵收缩。这是形式恒等式。在固定次数 $k$ 中只有有限个超额可以出现；事实上，贡献于次数 $k$ 的非空核心满足 $j<k$。我们从不假设对全部 $j$ 的无穷和在非零 $t$ 处收敛。高于 $n$ 次的系数全部抵消为零，因为 $F_k$ 的互异坐标定义在这些次数下为零。

### 5.3 非 Gaussian 核心的估计

算子谱隙可以控制长二度链的总和。压缩这些链后，超额为 $j$ 的图至多剩下 $2j$ 个顶点，因此剩余计数问题的复杂度取决于 $j$，而非原来的次数。令

$$
W=\max\left\{1,CR+\frac{C^2R^2}{1-Rq}\right\},
\qquad D=710W^3,\qquad
T_1=\frac32W^2+\frac{10}{3}W^3.
$$

**引理 5.2（压缩核心活动量）。** 在上述记号下，

<a id="eq-core-activity"></a>

$$
\|C_j\|_R\le(Dj/n)^j\qquad(j\ge1),
\tag{5.2}
$$

且首超额满足更精确的界

$$
\|C_1\|_R\le T_1/n.
$$

其中 $\|H\|_R=\sum_{k\ge0}|[t^k]H|R^k$。

*证明。* 压缩所有内部顶点均为二度的极大路径。每条压缩边对应一条两端度数至少为三、长度为正的链。允许自环、重边和非连通压缩图。若 $b$ 为度数至少为三的顶点数，$e$ 为压缩边数，则压缩不改变超额，并给出

$$
e=b+j,\qquad
2j=\sum_{i=1}^b(d_i-2),\qquad
1\le b\le2j,\qquad e\le3j.
$$

**增饰计数恒等式。** 固定超额及原始边数，对所有有序度数序列 $(d_1,\ldots,d_b)$、顶点的两种颜色配置、带标号半边配对及与颜色相容的正链长求和。除去临时标号后的绝对 Möbius 补偿为 $1/(b!\prod_i d_i)$。链收缩应先对内部数值指标求和，再取绝对值。

证明时须区分结构顶点（两个边标号分拆的块）与其在 $[n]$ 中的数值指标。不同结构顶点可以取得相同的数值指标，但这不会将对应分拆块合并。原始互异性约束已经由 Möbius 反演处理；此处数的是分拆对，而不是将相同数值指标合并后得到的简单图。临时为 $b$ 个高度数顶点及每个顶点的 $d_i$ 个半边分别加标号，并用这些标号为每条链选择唯一读取方向。遍历全部有序度数序列后，每个原始带边标号的核心有 $b!\prod_i d_i!$ 种增饰。对一个固定的度数序列，只有与之相容的顶点标号出现；对所有序列求和才恰好产生完整的 $b!$ 因子。每个结构顶点都能由其颜色及入射原始边标号辨认，每个入射半边则由其原始边标号辨认，故没有额外的自同构稳定子。反过来，给定增饰后的半边配对及全部正链长，所有链位置均被确定，原始 $h$ 个边标号可以按 $h!$ 种方式分配到这些位置。在满足二部颜色奇偶条件时，内部顶点及其颜色也随之确定。

除去原始指数生成函数的 $h!$ 因子及临时增饰，再乘回高度数顶点的绝对 Möbius 权重 $\prod_i(d_i-1)!$，补偿为

$$
\frac1{b!\prod_i d_i}.
$$

这一步包含自环和链反转：将每一对不同的带标号半边排序，从较小者开始读取该链。反转改变的是这些位置上的原始边标号列表，而不是额外提供自由的因子二；自环的两个半边也使用同一约定。内部二度顶点的绝对 Möbius 权重为一，也没有额外的链长阶乘。异色端点之间的链长为奇数，同色端点之间为偶数；尤其自环的长度至少为二且为偶数。这些限制属于精确恒等式的一部分。

例如，取一个行色四度顶点，以及两个长度为二的自环，各经过一个单独的列色二度顶点。此时 $j=b=1$、$h=4$。四个原始边标号分成两对共有三种方式，四度顶点的 Möbius 权重为 $(-1)^3 3!=-6$，而两个二度顶点的权重相乘为 $+1$；除以 $4!$ 后，其带符号贡献为

$$
-\frac34\sum_i\left(\sum_k B_{ik}^2\right)^2.
$$

即使某些求和项中数值指标相等，两个结构列顶点仍然不同。交换两种颜色得到 $-\tfrac34\sum_k(\sum_i B_{ik}^2)^2$。绝对补偿界使用的是这些项的绝对值。重边的例子是一个行顶点和一个列顶点之间的三条长度为一的链，其贡献为 $\tfrac{(2!)^2}{3!}\sum_{i,k}B_{ik}^3=\tfrac23\sum_{i,k}B_{ik}^3$，恰为前述三次项。这些例子同时展示自环、平行边和反转约定，而原图仍满足二部性。

仅在取上界时忽略颜色限制。固定 $j,b$ 后，所得总补偿为

$$
U_{j,b}=
\frac{2^b}{b!}\frac{(2e)!}{2^e e!}
\sum_{\substack{d_1+\cdots+d_b=2e\\d_i\ge3}}
\frac1{d_1\cdots d_b},
\qquad e=b+j.
$$

以下估计须先对每条链的内部数值指标求和，再取绝对值；若先逐项将 $B$ 换成 $|B|$，便无法保留算子谱隙的控制。长度为一的链对应矩阵元素，绝对值不超过 $C/n$。对于长度 $\ell\ge2$ 的链，先求和内部标签，其收缩是由 $B,B^{\mathsf T}$ 交替相乘所得矩阵的一个元素。两端行或列的二范数不超过 $C/\sqrt n$，中间因子的算子范数不超过 $q$。因此，收缩的绝对值不超过

$$
\frac{C^2}{n}q^{\ell-2}.
$$

按 $R$ 加权对长度求和，每条链的总活动量不超过 $W/n$。对 $b$ 个高度数顶点标签求和至多给出 $n^b$，故

$$
\|C_j\|_R\le n^{-j}
\sum_{b=1}^{2j}U_{j,b}W^{b+j}.
$$

度数组合数为 $\binom{2j-1}{b-1}\le4^j$：写 $d_i=3+x_i$，则 $\sum_i x_i=2j-b$。此外，$\prod_i d_i^{-1}\le3^{-b}$，半边配对数不超过 $(6j)^{b+j}$。于是

$$
\sum_{b=1}^{2j}U_{j,b}W^{b+j}
\le(24jW)^j
\sum_{b=1}^{2j}\frac{(4jW)^b}{b!}.
$$

取 $\theta=1/(2W)\le1/2$，则

$$
\sum_{b=0}^{2j}\frac{(4jW)^b}{b!}
\le\theta^{-2j}\exp(4jW\theta)
=(2\mathrm e W)^{2j}.
$$

因此，活动量不超过 $(96\mathrm e^2W^3j)^j$，进而不超过 $(710W^3j)^j$。为说明常数的严格性，对指数级数求和至六次，并用 $8/(7\cdot7!)$ 控制尾项，可得 $\mathrm e<87/32$；这一有理数界给出 $96\mathrm e^2<710$。

当 $j=1$ 时仅有 $b=1,2$。补偿公式分别给出

$$
U_{1,1}=\frac32,\qquad U_{1,2}=\frac{10}{3}.
$$

结合链界即有 $\|C_1\|_R\le T_1/n$。$\square$

### 5.4 线性系数窗口与阶乘恢复

活动量界[式 (5.2)](#eq-core-activity)在 $j/n$ 较小时有效。取

$$
\alpha=\min\left\{\frac14,\frac1{16D},\frac{\log\sigma}{2}\right\},
\qquad M=\lfloor\alpha n\rfloor.
$$

并令 $v_j=(Dj/n)^j$。当 $j+1\le M$ 时，

$$
\frac{v_{j+1}}{v_j}
=\frac{D(j+1)}n\left(1+\frac1j\right)^j
\le\frac{\mathrm e D(j+1)}n
\le3D\alpha<\frac12.
$$

故对 $n\ge4/\alpha$，

$$
\sum_{j=2}^{M}v_j\le2v_2=\frac{8D^2}{n^2}.
$$

形式核心恒等式中，次数不超过 $M$ 的贡献只能来自超额 $j\le M$。结合 $G$ 系数非负、活动量引理及加权系数和的卷积不等式，得到

$$
\sum_{k=0}^{M}|F_k-[t^k]G|R^k
\le\Gamma(R)\left(\frac{T_1}n+\frac{8D^2}{n^2}\right).
$$

这只是有限系数窗口的界，不是对全部超额在 $R$ 处取值。

记 $g_k=[t^k]G$，并在 $0\le k\le M$ 时令 $r_k=n^k/(n)_k$。由于 $\alpha\le1/4$，

$$
\log r_k
=\sum_{\ell=0}^{k-1}-\log(1-\ell/n)
\le\frac{k(k-1)}{2n(1-\alpha)}
\le\frac{k^2}n
\le\alpha k.
$$

由 $\alpha\le(\log\sigma)/2$ 可知 $r_k\le\sigma^k$，并且

$$
0\le r_k-1
\le\frac{k(k-1)}{2n(1-\alpha)}r_k.
$$

因为 $a_k=r_kF_k$，可以分解为

$$
a_k-g_k=r_k(F_k-g_k)+(r_k-1)g_k.
$$

第一部分的总和由前述 $R$ 加权估计控制。第二部分使用精确 Gaussian 系数矩，而不是粗糙的系数上界：

$$
\sum_{k\ge0}k(k-1)g_k\sigma^k
=\left((t\partial_t)^2-t\partial_t\right)G(t)\big|_{t=\sigma}.
$$

令 $a_i=\sigma^2s_i^2$。对
$G(t)=\prod_i(1-t^2s_i^2)^{-1/2}$ 求导，得到

$$
\frac{\left((t\partial_t)^2-t\partial_t\right)G(t)}{G(t)}
\bigg|_{t=\sigma}
=\left(\sum_i\frac{a_i}{1-a_i}\right)^2
+\sum_i\frac{a_i(1+a_i)}{(1-a_i)^2}.
$$

定义

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

导数公式中的两项分别不超过 $u_\sigma^2$ 与 $v_\sigma$。因此，

$$
\sum_{k=0}^{M}(r_k-1)g_k\le K_G/n.
$$

合并恢复后的两部分，恰得到显式误差预算的前两项。

### 5.5 控制剩余系数

目前已控制次数不超过 $M$ 的系数，其中 $M$ 与 $n$ 成正比。为用 Cauchy 不等式估计更高次系数，只需在固定圆周 $|t|=R>1$ 上将 $f$ 控制为 $\exp(O(\sqrt n))$。下面两个引理在保留归一化因子 $n!/n^n$ 的同时给出该界。

**引理 5.3（永久式极化）。** 对任意复方阵 $Z$，

$$
|\operatorname{per}Z|
\le\sqrt{\operatorname{per}|Z|\,
\operatorname{per}|Z^*|}.
$$

*证明。* 在 $(\mathbb C^n)^{\otimes n}$ 中令

$$
\xi=(n!)^{-1/2}
\sum_{\pi\in S_n}
e_{\pi(1)}\otimes\cdots\otimes e_{\pi(n)}.
$$

则 $\|\xi\|=1$，且
$\langle\xi,Z^{\otimes n}\xi\rangle=\operatorname{per}Z$。
作极分解 $Z=U|Z|$；若 $Z$ 奇异，将极分解的部分等距因子延拓为酉矩阵 $U$。记 $T=|Z|^{\otimes n}$，$V=U^{\otimes n}$。在由半正定算子 $T$ 诱导的半内积中应用 Cauchy–Schwarz 不等式，得到

$$
|\langle\xi,VT\xi\rangle|
\le\sqrt{\langle V^*\xi,TV^*\xi\rangle
\langle\xi,T\xi\rangle}.
$$

两个因子分别为 $\operatorname{per}(U|Z|U^*)=\operatorname{per}|Z^*|$ 与 $\operatorname{per}|Z|$。由于它们是半正定张量幂的对角矩阵元，均非负。$\square$

**引理 5.4（半正定永久式界）。** 设 $H$ 为 Hermitian 半正定矩阵，特征值为 $\lambda_1,\ldots,\lambda_n$。则

$$
\operatorname{per}H\le\frac{n!}{n^n}h_n(\lambda_1,\ldots,\lambda_n),
$$

其中 $h_n$ 为 $n$ 次完全齐次对称多项式。若 $\lambda_1=1$ 且 $0\le\lambda_i<1$（$i\ge2$），则

$$
\operatorname{per}H\le\frac{n!}{n^n}
\prod_{i=2}^n(1-\lambda_i)^{-1}.
$$

*证明。* 令 $Z$ 为协方差矩阵为 $H$ 的圆对称复 Gaussian 向量。复 Wick 公式给出
$\operatorname{per}H=\mathbb E\prod_i|Z_i|^2$。
逐点 AM–GM 不等式把该乘积控制为 $n^{-n}\|Z\|^{2n}$。酉对角化后，$\|Z\|^2$ 与 $\sum_i\lambda_i|\zeta_i|^2$ 同分布，其中 $\zeta_i$ 为独立标准圆对称复 Gaussian 变量，其矩为 $\mathbb E|\zeta_i|^{2k}=k!$。于是，多项式展开给出

$$
\mathbb E\left(\sum_i\lambda_i|\zeta_i|^2\right)^n
=n!h_n(\lambda_1,\ldots,\lambda_n).
$$

最后，$h_n(1,\lambda_2,\ldots,\lambda_n)$ 是关于 $\lambda_2,\ldots,\lambda_n$、总次数不超过 $n$ 的全部单项式之和，不超过各自无穷几何级数的乘积。$\square$

引理 5.4 中的 Gaussian 恒等式和 AM–GM 比较，是 Han–Niles-Weed [3，arXiv v2，引理 4.3–4.4] 用于半正定输入的工具。引理 5.3 将它们连接到这里需要的一般矩阵。

令 $\beta=RC/(1-Rq)$。双中心化假设给出 $P_nB=BP_n=0$。在 $|t|=R$ 上，因而有

$$
|P_n+tB|=P_n+R(B^{\mathsf T}B)^{1/2},
\qquad
|(P_n+tB)^*|=P_n+R(BB^{\mathsf T})^{1/2}.
$$

两者的特征值均为全一方向上的 $1$，以及 $\mathbf1^\perp$ 上的 $Rs_i$，必要时包含零奇异值。由于 $Rq<1$，两个引理结合精确恒等式
$f(t)=(n^n/n!)\operatorname{per}(P_n+tB)$，给出

$$
|f(t)|\le\prod_i(1-Rs_i)^{-1}
\le\exp\!\left(\frac{R}{1-Rq}\sum_i s_i\right)
\le\exp(\beta\sqrt n).
$$

最后一步使用 $\sum_i s_i\le\sqrt n\,\|B\|_{\mathrm F}\le C\sqrt n$。因此，Cauchy 系数估计给出

$$
\sum_{k>M}|a_k|
\le\frac{R}{R-1}
\exp\!\left(\beta\sqrt n-\alpha n\log R\right).
$$

对于 Gaussian 尾部，利用其系数非负，可用稍松但便利的界

$$
\sum_{k>M}g_k
\le \Gamma(\sigma)\sigma^{-M}
\le\sigma\Gamma(\sigma)\exp\!\left(-\alpha n\log\sigma\right).
$$

两个尾项均随 $n$ 指数衰减。将它们与有限窗口中的 $O(n^{-1})$ 估计合并，即证明定理 5.1。$\square$

### 5.6 合并误差界

**命题 5.5（显式误差界）。** 对每个整数 $n\ge4/\alpha$，

$$
|f(1)-G(1)|
\le \frac{\Gamma(R)T_1+K_G}{n}
+\frac{8\Gamma(R)D^2}{n^2}
+\frac{R}{R-1}\exp\!\left(\beta\sqrt n-\alpha n\log R\right)
+\sigma\Gamma(\sigma)\exp\!\left(-\alpha n\log\sigma\right).
$$

前两项来自第 5.4 节的系数窗口及阶乘恢复误差，后两项来自第 5.5 节的尾界。两个指数项均为 $o(n^{-1})$，从而得到定理 5.1 的一致误差率。Lean 工程通过几何系数矩证明了另一种足够的阶乘恢复估计，并非逐字形式化此处显示的特定常数 $K_G$（见附录 A.1）。

## 6. 缩放与非主永久式估计

定理 5.1 适用于经标量归一化后行列和相等的矩阵。竞赛图矩阵通常具有不同的行列和：若 $C=2A/(n-1)$，则

$$
C\mathbf1=\mathbf1+a,\qquad C^{\mathsf T}\mathbf1=\mathbf1-a.
$$

因此，需要在修正边际的同时，控制永久式及其 Gaussian 因子的变化。先构造局部对角缩放，估计其总对数代价；再用 Gram 矩阵比较控制删行、删列的影响；最后，通过成对比分修正，使竞赛图子矩阵满足局部定理的条件，从而证明引理 3.1。

记 $\mathbf1_p$ 为全一向量，$P_p=\mathbf1_p\mathbf1_p^{\mathsf T}/p$，$\Pi_p=I-P_p$。矩阵的总质量为 $\mathfrak m(X)=\sum_{i,j}X_{ij}$。以 $\|\cdot\|_{\rm op}$ 表示 Euclidean 算子范数，$\|\cdot\|_F$ 表示 Frobenius 范数，$\|\cdot\|_*$ 表示迹范数。本节常数在给定稠密度与谱隙参数后统一。

后续应用的维度与归一化约定如下。全图阶数为 $n$，保留阶数为 $m=n-t$；$p$ 是引理 6.1–6.2 的一般矩阵阶数，仅在应用时令 $p=m$。矩阵 $C,C',\widehat C$ 为 $n$ 阶，而 $X,\widetilde X,B_X,Z$ 为 $m$ 阶。有关质量依次为

$$
\mathfrak m(C')=n+\nu,\quad \mathfrak m(\widehat C)=n,\quad
\mathfrak m(X)=m+\kappa,\quad
\mathfrak m(\widetilde X)=\mathfrak m(B_X)=m.
$$

这里 $Z=\Pi_m[(S-I)/(n-1)][R,T]\Pi_m$ 是未作真实缩放的保留中心核，并非双随机矩阵。$B_X$ 表示最终双随机矩阵；定理 5.1 中对应的扰动为 $mB_X-J_m$，其归一化为 $B_X-P_m$。这样可以明确区分全阶归一化 $n-1$ 与保留阶归一化 $m$。

### 6.1 局部缩放及其代价

我们寻找形如 $B_{ij}=X_{ij}e^{x_i+y_j}$、行列和均为一的矩阵。将 $(x,y)$ 换为 $(x+c\mathbf1,y-c\mathbf1)$ 不改变 $B$；条件 $\sum x_i=\sum y_j$ 消去这一维自由度。奇异值谱隙控制其余子空间上的线性化平衡方程，而元素界进一步给出不依赖维数的无穷范数控制，从而可以使用压缩映射论证。

**引理 6.1（局部缩放）。** 设 $p\ge1$，$X$ 为总质量等于 $p$ 的实 $p\times p$ 矩阵。记

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

仅找到平衡点还不足以估计永久式：恢复对角因子时，需要将永久式乘以 $\exp(-\sum x_i-\sum y_j)$。下面的引理既控制这一总代价，也给出比较 Gaussian 因子所需的 Frobenius 位移界。

**引理 6.2（位移与容量）。** 在上述假设下，再设 $X\ge0$。以 $\theta_X=\sum_i x_i+\sum_j y_j$ 表示总缩放势。存在仅依赖固定稠密度与谱隙参数的常数，使

$$
\|(x,y)\|_2\le K\|(\alpha,\beta)\|_2,\qquad \|B-X\|_F\le\frac K{\sqrt p}\|(\alpha,\beta)\|_2,
$$

$$
0\le\theta_X\le K\|(\alpha,\beta)\|_2^2.
$$

对于总质量为任意正数的非负矩阵 $X$，假设 $\widetilde X=pX/\mathfrak m(X)$ 满足引理 6.1 的条件，再对 $\widetilde X$ 应用以上结论。若 $B$ 为其缩放，则有精确恒等式

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

### 6.2 Gaussian 删除与中心化

从稠密归一化矩阵中删除 $t$ 行，删去的行平方范数总量为 $t/n$ 量级。将对数行列式导数用于对应的 Gram 矩阵损失，可以保留这个量级。随后改用另一侧 Gram 矩阵处理删列。这样，即使保留的是非主子矩阵，也能得到线性的删除误差。

对满足 $\|Z\|_{\rm op}<1$ 的实矩阵 $Z$，定义

$$
\mathcal G(Z)=\det(I-Z^{\mathsf T}Z)^{-1/2}.
$$

改用 $ZZ^{\mathsf T}$ 得到相同数值；补零行或零列也不改变此值。

**引理 6.3（Gram 删除与稳定性）。** 设 $\|Z\|_{\rm op}\le q_*<1$。删除行集 $I$ 和列集 $J$，剩余集合为 $R,T$，则

$$
0\le\log\mathcal G(Z)-\log\mathcal G(Z[R,T])\le\frac{\sum_{i\in I}\|Z_{i,\cdot}\|_2^2+\sum_{j\in J}\|Z_{\cdot,j}\|_2^2}{2(1-q_*^2)}.
$$

对阶数为 $m\ge1$ 的方形余矩阵 $W$，置 $u=\mathbf 1_m/\sqrt m$，则

$$
0\le\log\mathcal G(W)-\log\mathcal G(\Pi_mW\Pi_m)\le\frac{\|W^{\mathsf T}u\|_2^2+\|Wu\|_2^2}{2(1-q_*^2)}.
$$

对于维数相同、算子范数均至多为 $q_*$ 的两个实矩阵，另有

$$
|\log\mathcal G(U)-\log\mathcal G(V)|\le\frac{\|U\|_F+\|V\|_F}{2(1-q_*^2)}\|U-V\|_F.
$$

**证明。** 令 $P_R$ 为投影到保留行坐标的对角投影矩阵。删除行使列侧 Gram 矩阵减少半正定矩阵 $Z^{\mathsf T}(I-P_R)Z$，其迹等于被删行的平方范数之和。对 $F(H)=-\tfrac12\log\det(I-H)$ 和半正定方向 $D$，

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

为明确常数，注意 $1-q_Y^2=n(n-3)/(2(n-1)^2)$。代入并利用 $t\le n/2$ 即可直接验证上述常数。此估计适用于独立选择的行、列删集 $I,J$；反对称性仅用于原全矩阵 $S$。

### 6.3 竞赛图子矩阵的预处理

矩阵 $C=2A/(n-1)$ 的行、列误差符号相反。将第 $i$ 行乘以 $(1+a_i)^{-1}$ 可修正原行和，将第 $i$ 列乘以 $(1-a_i)^{-1}$ 可修正原列和。同时实施两种修正后仍有边际残差，下面将对此估计。其主要作用是使总质量的一阶变化消失，并在恢复乘积中产生比分罚项 $\Gamma$。

固定 $0\le a_0<1$ 和有限正参数 $A_0,B_0$。本小节假设

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

归一化 $\widehat C=nC'/\mathfrak m(C')$。以 $e_i,f_j$ 表示其行、列误差，故 $\sum e_i=\sum f_j=0$。对大小均为 $t$ 的任意删集 $I,J$，记 $R=[n]\setminus I$、$T=[n]\setminus J$、$m=n-t$，并令

$$
X=\frac n m\widehat C[R,T],\qquad \kappa=\mathfrak m(X)-m,\qquad \widetilde X=\frac m{\mathfrak m(X)}X.
$$

精确删行列质量恒等式为

<a id="eq-deletion-mass"></a>

$$
\kappa=\frac n m\left[-\sum_{i\in I}e_i-\sum_{j\in J}f_j+\sum_{i\in I,j\in J}\widehat C_{ij}-\frac{t^2}{n}\right].
\tag{6.1}
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

为应用引理 6.1，下面验证 $\widetilde X$ 的中心核条件。记

$$
\eta=\frac{n^2}{\mathfrak m(C')\mathfrak m(X)}=1+O((t+1)/n),
$$

则

$$
\Pi_m\widetilde X\Pi_m=\eta\left[Z+\Pi_mF[R,T]\Pi_m\right].
$$

由于 $\mathfrak m(C')=n+o(1)$、$\mathfrak m(X)=m+o(1)$，$\eta$ 的主值为 $n/m$。压缩不增大 $Y$ 的算子范数，第二项由已得 Frobenius 界控制。因此，在固定参数下，中心核的算子范数一致至多为 $1/\sqrt2+o(1)$。其元素为 $O(1/m)$，无穷范数边际误差趋于零。由于 $\widetilde X$ 的质量为 $m$，引理 6.1 中的 $E$ 恰为 $\Pi_m\widetilde X\Pi_m$。因此可固定取 $q=3/4$ 及固定的密度界 $C,C_0$。阈值 $\varepsilon_0$ 和逆算子界 $L_0$ 便只依赖 $a_0,A_0,B_0$，与 $n$、竞赛图及删集无关。局部缩放引理对所有充分大的 $n$ 适用，并构造出真正的双随机矩阵 $B_X$；直接给出的谱范数界为 $7/8$。

二范数位移引理给出

$$
\|B_X-\widetilde X\|_F\le K(\sqrt{\tau/n}+t/n).
$$

与较强的中心核界结合，$B_X$ 的中心算子范数仍为 $1/\sqrt2+o(1)$，例如最终至多为 $4/5$。元素继续满足 $K/m$ 的界。

最后，对 $Z$ 应用 Gaussian 删除估计，再对预缩放、归一化和真实缩放扰动应用对数 Lipschitz 估计。由于 $B_X-P_m=\Pi_mB_X\Pi_m$，得到

$$
|\log\mathcal G(B_X-P_m)-\log D_n(S)|\le K\left[\sqrt{\tau/n}+(t+1)/n\right].
$$

中心化产生的 $\tau/n$ 项已吸收入 $\sqrt{\tau/n}$。其中由删除产生的误差与 $t/n$ 成线性关系，正适合对后续子集权重求和。

现在可在固定维度约定下汇总误差。所有常数与最终适用阈值只依赖固定的 $a_0,A_0,B_0$。全阶质量误差在恢复对数中产生 $O(|\nu|)\le K\mathcal M_\tau$；删除引起的质量变化至多为 $K[t\sqrt{\tau/n}+t^2/n]$；Gaussian 对数误差为 $K[\sqrt{\tau/n}+(t+1)/n]$。在阶数 $m\ge n/2$ 使用定理 5.1，增加 $O(1/m)=O(1/n)$。最后的标量恢复贡献 $e^{-1}\exp(O((t+1)/n))$。对于质量为 $m+\kappa$ 的 $X$，容量仅以 $e^{-\theta_X}\le e^\kappa$ 的形式使用，不能断言这种非单位质量下的 $\theta_X$ 非负。第 6.4 节精确恢复这些因子，得到引理 3.1 的误差指数。

### 6.4 非主永久式界的证明

下面证明引理 3.1，以 $n$ 表示全核心阶数 $N$，并取 $a_0=b$。前面的构造已给出缩放矩阵 $B_X$。剩下的工作是恢复全部对角因子和标量因子，再将所得 Gaussian 行列式与 $D_n(S)$ 比较。

**证明。** 已构造的真实缩放满足稠密度与中心核谱隙假设，因此定理 5.1 给出

$$
\operatorname{per}B_X=\frac{m!}{m^m}\mathcal G(B_X-P_m)(1+O(1/m)).
$$

行列缩放因子精确恢复为

$$
\prod_{i\in R}(1+a_i)\prod_{j\in T}(1-a_j)=\Gamma\prod_{i\in I}\ell_i\prod_{j\in J}r_j.
$$

因此，删除行恢复 $\ell$ 因子，删除列恢复 $r$ 因子。完整的标量恒等式为

<a id="eq-exact-restoration"></a>

$$
\operatorname{per}A[R,T]=\Gamma\prod_{i\in I}\ell_i\prod_{j\in J}r_j\left[\frac{m(n-1)\mathfrak m(C')}{2n^2}\right]^m e^{-\theta_X}\operatorname{per}B_X.
\tag{6.2}
$$

将 $m!/m^m$ 代入[式 (6.2)](#eq-exact-restoration)后，剩余标量为

$$
\frac{m!}{2^m}(1-1/n)^m\left[\frac{\mathfrak m(C')}{n}\right]^m.
$$

其对数与 $e^{-1}m!/2^m$ 的对数之差为 $O((t+1)/n+|\nu|)$。容量界给出 $e^{-\theta_X}\le e^\kappa$。代入质量、Gaussian 和零阶永久式误差，即得到所需指数预算。所有常数对竞赛图及两个删集一致，引理 3.1 得证。$\square$

### 6.5 小比分时的双侧估计

当每个比分均为 $o(\sqrt n)$ 时，原始边际已足够接近一，可以直接使用局部缩放。容量界随后从两侧控制恢复因子，得到定理 4.1 所需的近似。

**引理 6.4（小比分永久式近似）。** 设 $d=\|S\mathbf 1_n\|_\infty=o(\sqrt n)$。固定 $0<B_0<\infty$，任删 $t\le B_0\log n$ 行与 $t$ 列，记 $m=n-t$。对这些选择一致地有

<a id="eq-small-score-permanent"></a>

$$
\operatorname{per}A[R,T]=e^{-1}D_n(S)\frac{m!}{2^m}\left[1+O_{B_0}\left(\frac{(d+t+1)^2}{n}\right)\right].
\tag{6.3}
$$

更明确地，对每个固定的 $B_0>0$，存在仅依赖于 $B_0$ 的常数 $C_{\mathrm{err}},\delta>0$ 及整数 $N_0\ge4$，使得对每个 $n\ge N_0$、每个竞赛图符号矩阵 $S$ 及每对满足 $|I|=|J|=t\le B_0\log n$ 的删集 $I,J\subseteq[n]$，均有如下结论：若 $d=\|S\mathbf1_n\|_\infty$ 且 $\eta=(d+t+1)^2/n\le\delta$，则[式 (6.3)](#eq-small-score-permanent)中的绝对相对误差至多为 $C_{\mathrm{err}}\eta$。这里 $R=[n]\setminus I$、$T=[n]\setminus J$、$m=n-t$，且 $I,J$ 可独立选择。这些常数先于阶数、竞赛图和删集选定。在所述渐近范围中，$\eta\to0$。

**证明。** 增大 $N_0$，使整个对数删除窗口内均有 $2t\le n$，于是 $m\ge n/2>0$。此处不需要成对预缩放。令 $C=2A/(n-1)$、$X=(n/m)C[R,T]$。全矩阵 $C$ 的行列误差分别为 $s_i/(n-1)$、$-s_i/(n-1)$。因此，精确质量恒等式[式 (6.1)](#eq-deletion-mass)及第 6.3 节的边际公式给出

$$
|\kappa|=O(t(d+t)/n),\qquad \varepsilon(X)=O((d+t)/n),\qquad \|g(X)\|_2=O((d+t)/\sqrt n).
$$

质量误差满足 $|\kappa|\le K\eta$。必要时缩小 $\delta$，便一致保证 $\mathfrak m(X)=m+\kappa>0$。归一化 $\widetilde X=mX/\mathfrak m(X)$。其稠密度与中心核谱隙固定，局部缩放引理适用。二范数位移和容量估计给出

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

应用统一永久式定理，并使用 $(1-1/n)^m=e^{-1}\exp(O((t+1)/n))$。所有对数误差均由 $\eta=(d+t+1)^2/n$ 的一个固定倍数控制。将 $\delta$ 取得充分小，对这些界取指数，便在前述有限范围内一致得到不超过 $C_{\mathrm{err}}\eta$ 的绝对相对误差。在 $d=o(\sqrt n)$、$t\le B_0\log n$ 的渐近范围中，$\eta\to0$。这就证明了定理 4.1 所用的一致短余矩阵近似。$\square$

## 7. 后续问题

首要问题是能否将上界常数降到 $L$。现有谱论证只使用最大的归一化平方频率及这些频率的总和。若能进一步刻画竞赛图矩阵的可实现谱，就可能改进这一松弛；特别地，若能证明 $\rho_n(S)\le r_n$ 对所有竞赛图成立，其中 $r_n$ 如第 4.2 节所定义，同一归约便会给出 $P(n)=(L+O(n^{-1}))\mu_n$。

本文没有计算出可直接用于有限阶的常数对 $K,n_0$。要做到这一点，需要在三类竞赛图的论证中追踪统一缩放阈值及各项误差。$O(n^{-1})$ 近似也尚未确定圆环图路径数的首个修正项系数及有限阶极值图的结构。

## 附录 A. 形式化与可复现性

### A.1 形式化命题及对应关系

[配套 Lean 工程](https://github.com/LStar404/tournament-hamiltonian-paths/tree/8ea3fcffcc12b6a06294ba7559885b439eda3cac/formalization)使用与本文相同的有限对象：竞赛图是不同标号顶点间每对恰有一个方向的无自环图；Hamilton 路径是所有相邻边均顺向的顶点排列；$P(n)$ 是相应计数的最大值。工程固定使用 Lean 和 Mathlib 4.34.1。

声明 `TournamentHamiltonian.mainBound : TournamentHamiltonian.MainBound` 以精确常数 $L,C_*$ 证明定理 1.1。其结论先选定同一个 $K\ge0$ 和 $n_0\ge2$，再对所有 $n\ge n_0$ 量化。最终定理没有未证明的永久式、缩放、活动量或路径数前提。另一个声明 `small_score_pathCount_spectral_approximation_eventually` 证明定理 4.1：绝对误差常数不依赖比分上包络 $d(n)$，而最终成立的起始阶数可以依赖该函数。

形式化工程同时证明了主要分析输入及上述结论。部分中间论证与正文不同：永久式证明以几何系数矩界代替正文列出的导数常数 $K_G$；高方差与异常顶点情形使用较弱但足够的估计。后者的 $(10/3)4^{-f}(1+o(1))$ 仅控制删除集与 $F$ 不相交的短项，其余项另贡献一致的加性 $o(1)$；完整上界见[式 (3.1)](#eq-exceptional-bound)，三部分相加后在 $f\ge1$ 时最终不超过 $191/200<1$。加权行列式比较使用正主子式矩；小比分恢复复用成对预缩放，局部缩放采用等价的压缩映射估计及不同的固定谱隙。形式化的短删集约定还相差一个边界层，极化和 Gaussian 矩工具则采用有限维实现。这些方法得到相同的误差率与最终界。所附[逐项结论对应表](verification/manuscript_alignment_20261011.md)记录了这些中间差异。

### A.2 核验记录与辅助计算

仓库的[核验记录](https://github.com/LStar404/tournament-hamiltonian-paths/blob/8ea3fcffcc12b6a06294ba7559885b439eda3cac/formalization/VERIFICATION.md)记载了 2026 年 10 月 9 日的一次成功完整运行。命令 `python verify_lean.py --require-main` 执行工程构建、实际 `MainBound` 声明检查、工程源码导入覆盖检查，并将定理的传递公理依赖限制为 `propext`、`Classical.choice` 和 `Quot.sound`。记录包含 3674 个定理常量，其中包括自动生成的引理。已存档的 246 项 Lean 源码及配置哈希均与本次修订所检查的源码一致。这些材料分别提供已记录的构建结果与源码对应检查；本次文字修订没有另行执行 Lean 构建。

后续远端 CI 核验了工作 fork 中已合并的第二轮修订基线提交 `42ee0a1572e9e0cdf88bfc17811c7559b3b2e03c`：[Verify proofs，第 38073718040 次运行](https://github.com/makerY666/tournament-hamiltonian-paths/actions/runs/38073718040)于 2026 年 10 月 10 日成功完成，其中 Lean 构建与审计、四项有限诊断及带符号核心例子测试均成功。这是针对该精确基线的远端证据，并非本地重新构建，也不表示后续文字修订提交已经通过 CI。本次第三轮修订未改变形式化证明源码；其自身提交对应的 CI 结果随拉取请求另行记录。编译与有限检查成功不能替代对正文每一步证明的人工审查。

精确有限计算用于核对归一化、系数恒等式、删除因子及四块展开，与任意阶证明分别记录。存档的有理数计算给出

$$
2.855957892565113<L<2.855957892565114,
$$

$$
2.857401177672316<C_*<2.857401177672317,
$$

并将 $(C_*-L)/L$ 限定在 $0.000505359379058$ 与 $0.000505359379059$ 之间。上界常数的小数区间也已在 Lean 中证明，其他小数区间见有理数计算证书。

叶祥宇完成了配套形式化证明，并通过 [PR 1](https://github.com/LStar404/tournament-hamiltonian-paths/pull/1) 提交。证明重建、交叉检查、翻译及精确算术诊断使用了 AI 工具辅助。

## 参考文献

[1] John Irving and Mohamed Omar. Revisiting the Rédei-Berge Symmetric Functions via Matrix Algebra. The Electronic Journal of Combinatorics 32(4) (2025), Paper P4.43, 23 pp. [DOI: 10.37236/13841](https://doi.org/10.37236/13841).

[2] Noga Alon. The Maximum Number of Hamiltonian Paths in Tournaments. Combinatorica 10(4) (1990), 319–324. [DOI: 10.1007/BF02128667](https://doi.org/10.1007/BF02128667).

[3] Yanjun Han and Jonathan Niles-Weed. Approximate independence of permutation mixtures. The Annals of Statistics, to appear（[作者发表目录](https://yanjunhan2021.github.io/publication.html)）。[arXiv:2408.09341v2](https://arxiv.org/html/2408.09341v2)（2024年9月9日）；正文所引引理编号对应这一版本。

[4] Bo Deng, Xueliang Li, Bryan Shader and Wasin So. On the Maximum Skew Spectral Radius and Minimum Skew Energy of Tournaments. Linear and Multilinear Algebra 66(7) (2018), 1434–1441. [DOI: 10.1080/03081087.2017.1357676](https://doi.org/10.1080/03081087.2017.1357676).

[5] Peter McCullagh. An asymptotic approximation for the permanent of a doubly stochastic matrix. Journal of Statistical Computation and Simulation 84(2) (2014), 404–414. [DOI: 10.1080/00949655.2012.712122](https://doi.org/10.1080/00949655.2012.712122). [arXiv:1205.5723](https://arxiv.org/abs/1205.5723).

[6] N. C. Wormald. Tournaments with many Hamilton cycles. [Undated preprint](https://users.monash.edu.au/~nwormald/papers/hamtourn.pdf), 20 pp. Accessed 10 October 2026.

[7] Ehud Friedgut and Jeff Kahn. On the Number of Hamiltonian Cycles in a Tournament. Combinatorics, Probability and Computing 14(5–6) (2005), 769–781. [DOI: 10.1017/S0963548305006863](https://doi.org/10.1017/S0963548305006863).

[8] Eric Li. The Godsil–McKay Asymptotic for Latin Rectangles in the Sublinear Range of Erdős Problem 725. [arXiv:2608.01671v1](https://arxiv.org/html/2608.01671v1) (2026).

[9] Ilan Adler, Noga Alon and Sheldon M. Ross. On the Maximum Number of Hamiltonian Paths in Tournaments. Random Structures & Algorithms 18(3) (2001), 291–296. [DOI: 10.1002/rsa.1010](https://doi.org/10.1002/rsa.1010).

[10] Tibor Szele. Kombinatorikai vizsgálatok az irányított teljes gráffal kapcsolatban. Matematikai és Fizikai Lapok 50 (1943), 223–256. [Original volume archive](https://real-j.mtak.hu/7300/).
