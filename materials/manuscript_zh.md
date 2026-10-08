# 竞赛图中 Hamilton 路径数的常数因子界

刘星辰

个人研究者

lxc-em5158@outlook.com

2026年10月8日

研究论文稿。本文论证经过 AI 辅助内部证明复核，尚未经过外部同行评审；不声明发表优先权，也不声称已经完整确定极值竞赛图。

## 摘要

设 $P(n)$ 为 $n$ 阶竞赛图中有向 Hamilton 路径数的最大值，记 $\mu_n=n!/2^{n-1}$。本文建立具有固定奇异值谱隙的有界双中心核的统一永久式近似，并给出局部缩放构造及不同行、列删除的线性 Gaussian 行列式误差界。由此，无须预先假定极值图正则或平衡，即可完成全图归约，得到

$$
(L-O(n^{-1}))\mu_n\le P(n)\le(C_*+O(n^{-1}))\mu_n,
$$

其中 $L=\cosh(1)/\cos(1)$，且

$$
C_*=\frac{3\pi^4+4\pi^2-32}{\pi^4+4\pi^2-32}.
$$

数值上，$L=2.855957892565\ldots$，$C_*=2.857401177672\ldots$，首项常数的相对间隙约为 $0.050536\%$。上界常数来自最大反对称奇异值及凸谱松弛；下界由奇偶两类近正则圆环竞赛图获得。本文不确定有限阶精确极值、路径数的首个修正项系数，或极值图的唯一性。

关键词：竞赛图；有向 Hamilton 路径；永久式；矩阵缩放；反对称谱；Gaussian 行列式。

## 1. 引言与主要结果

竞赛图是完全图的一个定向。记 $H(T)$ 为满足全部相邻关系 $v_j\to v_{j+1}$ 的顶点排列 $(v_1,\ldots,v_n)$ 的数量。这里数有向路径，不按反向识别，也不除以二。本文研究

$$
P(n)=\max_{|V(T)|=n}H(T),\qquad \mu_n=\frac{n!}{2^{n-1}}.
$$

随机竞赛图的路径期望为 $\mu_n$，故 $P(n)\ge\mu_n$。Alon 的永久式方法 [2] 给出多项式因子上界；Friedgut 与 Kahn [7] 随后改进相关计数界。Wormald [6] 研究常数因子下界改进，并讨论约为 $2.855958$ 的候选常数。这里引用历史背景，不声称这份简要比较已经完成今日文献中的优先权判断。

稠密永久式的行列式近似已有重要先例，尤其是 McCullagh 的工作 [5]。本文所需的一致性还涉及非对称核及带零支撑的矩阵，因此第 3 节在明确假设下给出完整论证，不直接套用尚未核实适用性的近似。最大反对称谱半径比较也已有文献结果 [4]；本文给出足够用于计数界的短证明，而不引入其取等分类。

**主要定理。** 存在绝对常数 $K<\infty$ 及 $n_0$，使得对每个整数 $n\ge n_0$，

$$
(L-K/n)\mu_n\le P(n)\le(C_*+K/n)\mu_n,
$$

其中

$$
L=\frac{\cosh1}{\cos1},\qquad
a_*=\frac4{\pi^2},\qquad
C_*=\frac{1+a_*}{1-a_*}\frac{3/2-a_*}{1/2+a_*}.
$$

本文尚未将这些常数优化、计算为可实用的有限阶门槛。特别地，$C_*$ 与 $L$ 的数值差不是有限 $n$ 的误差证书。

证明包含三个分析环节。先在系数层面展开集合分划，并独立控制尾项，建立统一零阶永久式公式；再构造定量局部缩放，使公式适用于真实非负矩阵，包括非主余矩阵；最后利用正的行列式—永久式卷积，分别处理高比分方差、异常度数及剩余稠密图类。全部短子集误差求和以前，始终保留比分罚项。证明不假定尚未证明的极值图正则性。

## 2. 记号与精确预备恒等式

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

标准化比分 $a$ 与 $\tau$ 在 $n\ge2$ 时定义。奇阶正则图满足 $s=0$；偶阶平衡图满足 $s_i\in\{-1,1\}$。上界证明中的任意竞赛图均不预设这两个条件。

对顶点集 $U$，$A[U]$ 表示主子矩阵。对可能不同的行、列集 $R,C$，写 $A[R,C]$。空矩阵的行列式和永久式均约定为一。永久式定义为

$$
\operatorname{per}M=\sum_{\pi\in\mathfrak S_m}\prod_{i=1}^m M_{i,\pi(i)}.
$$

记 $S$ 的非零成对特征值为 $\pm i\lambda_j$，必要时补零频率。定义

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

本文的 $D_n$ 始终表示谱因子，而非另外的有限阶计算中使用的整数行列式上界。

### 2.2 正路径卷积

**路径卷积引理。** 对任意竞赛图，

$$
H(T)=\sum_{U\subseteq V(T)}\det(I+A[U])\operatorname{per}A[U^c].
$$

这是 Irving 与 Omar 的 Proposition 2 [1] 在竞赛图上的特化。必须明确补图约定：一般有向图的补邻接矩阵为 $\overline A=J-A$，其中允许对角自环。对竞赛图，有 $\overline A=I+A^{\mathsf T}$，而不是只有 $A^{\mathsf T}$。

也可用生成函数直接核对。令 $X=\operatorname{diag}(z_1,\ldots,z_n)$，每次访问一个顶点即乘上对应变量，则全部游走的生成函数为

$$
1+\mathbf1^{\mathsf T}(I-XA)^{-1}X\mathbf1
=\frac{\det(I+X\overline A)}{\det(I-XA)}.
$$

等号来自秩一行列式引理。取 $z_1\cdots z_n$ 的系数，恰选出全部 Hamilton 路径。分子作主子式展开，分母倒数使用多线性系数恒等式，得到

$$
H(T)=\sum_U\det\overline A[U]\operatorname{per}A[U^c].
$$

代入 $\overline A[U]=I+A[U]^{\mathsf T}$ 即得结论。

令 $k=|U|$。矩阵 $I+A[U]$ 的对称部分为正定矩阵 $(I+J)/2$，所以行列式为正。Hadamard 不等式与平均出度给出

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

Brégman 度数界及度数平衡化 [2]，结合 Stirling 公式，给出统一常数 $C$，使任意 $m$ 阶竞赛图满足

$$
\operatorname{per}A_T\le C\sqrt{m+1}\,\frac{m!}{2^m}.
$$

增大 $C$ 后也覆盖 $m=0$。第 5 节还会证明更强的方差罚项版本。于是路径卷积中 $|U|>k_n$ 的贡献除以 $\mu_n$ 后，至多为

$$
\frac C2\sqrt{n+1}\sum_{k>k_n}w_k
=n^{-3/2+o(1)}=o(n^{-1}).
$$

该界对所有竞赛图一致。

### 2.3 谱上限与凸装填

**谱上限引理。** 任意竞赛符号矩阵满足

$$
\|S\|_{\rm op}\le\cot\left(\frac{\pi}{2n}\right)<\frac{2n}{\pi},
\qquad \rho_n(S)\le C_*.
$$

证明。$iS$ 为谱关于零对称的 Hermitian 矩阵，其最大特征值等于 $\|S\|_{\rm op}$。对任意复向量 $z$，同时对 $z,S$ 作带符号置换，使非零坐标的相位落入 $[0,\pi)$ 并递增排列；零坐标任意安放。于是 $i<j$ 时 $c_{ij}=\operatorname{Im}(\overline z_i z_j)\ge0$。设 $T_n^0$ 为上三角全一的传递符号矩阵，则

$$
z^*iSz=-2\sum_{i<j}S_{ij}c_{ij}
\le2\sum_{i<j}c_{ij}=z^*(-iT_n^0)z.
$$

取 Rayleigh 商最大值得 $\|S\|_{\rm op}\le\|T_n^0\|_{\rm op}$。计算后者时，相邻行的特征方程给出 $(\lambda-1)v_i=(\lambda+1)v_{i+1}$。由首行方程，几何比 $r=(\lambda-1)/(\lambda+1)$ 满足 $r^n=-1$，故全部特征值为 $i\cot((2j-1)\pi/(2n))$，$1\le j\le n$。所述范数由此得出；最后的严格不等式使用 $\tan u>u$。

因此 $0\le x_j\le a_*$ 且 $\sum_jx_j<1/2$。函数

$$
\phi(x)=\log\frac{1+x}{1-x}
$$

在 $[0,1)$ 单调递增且凸。将两个内部坐标的质量移向一个上限坐标和一个余数坐标，不会减小 $\sum_j\phi(x_j)$。必要时补零，并把总质量放宽到 $1/2$。因 $1/4<a_*<1/2$，松弛最大值由 $a_*,1/2-a_*,0,\ldots$ 取得。取指数即得到 $C_*$。此处只是谱松弛，不声称该装填向量可由竞赛图实现。范数比较与已知结果 [4] 一致。引理证毕。

同一特征值计算还给出

$$
\det(I+zT_n^0)=\frac{(1+z)^n+(1-z)^n}{2}.
$$

这些恒等式讨论谱而非路径数；传递竞赛图本身只有一条 Hamilton 路径。

## 3. 统一零阶永久式定理

本节证明适用于一般实矩阵的永久式近似。正规性、反对称性和逐元素非负性均不是假设。谱条件涉及奇异值，而不是特征值的模。因此，在竞赛图矩阵经历不同行列集合的删除与对角缩放之后，只要重新验证本节假设，仍可使用这一结果。

记 $J_n$ 为全一矩阵，$P_n=J_n/n$，$\mathbf1$ 为全一向量。算子范数均指 Euclidean 算子范数。对于复矩阵 $Z$，$Z^*$ 表示共轭转置，并定义

$$
|Z|=(Z^*Z)^{1/2}.
$$

因此，$|Z|$ 是算子绝对值，不是对每个矩阵元素分别取绝对值。

### 3.1. 定理与显式误差预算

**定理（统一零阶永久式近似）。** 固定 $0\le C<\infty$ 和 $0\le q<1$。设 $E\in\mathbb R^{n\times n}$ 满足

$$
E\mathbf1=E^{\mathsf T}\mathbf1=0,\qquad
\max_{i,j}|E_{ij}|\le C,\qquad
\|E/n\|_{\mathrm{op}}\le q.
$$

令 $B=E/n$。对所有满足上述条件的矩阵，一致地有

$$
\frac{\operatorname{per}(J_n+E)}{n!}
=\det(I-BB^{\mathsf T})^{-1/2}+O_{C,q}(n^{-1}).
$$

也可以把误差写成行列式因子乘以相对因子 $1+O_{C,q}(n^{-1})$。

本节所用行列式平方根，在有关实区间上均取正平方根。假设给出 $\|B\|_{\mathrm F}^2\le C^2$。因此，行列式因子不小于一，并且被只依赖 $C,q$ 的常数一致控制。

我们用一个显式但有意保守的误差预算证明定理。定义

$$
f(t)=\frac{\operatorname{per}(J_n+tE)}{n!},
\qquad G(t)=\det(I-t^2BB^{\mathsf T})^{-1/2}.
$$

选取 $1<\sigma<R<1/q$；当 $q=0$ 时不要求最后一个限制。例如可取

$$
R=\frac{3+q}{2(1+q)},\qquad \sigma=\frac{1+R}{2}.
$$

令

$$
W=\max\left\{1,CR+\frac{C^2R^2}{1-Rq}\right\},
\qquad D=710W^3,\qquad
T_1=\frac32W^2+\frac{10}{3}W^3,
$$

$$
\alpha=\min\left\{\frac14,\frac1{16D},\frac{\log\sigma}{2}\right\},
\qquad
\Gamma(r)=\exp\left(\frac{C^2r^2}{2(1-q^2r^2)}\right),
\qquad
\beta=\frac{RC}{1-Rq}.
$$

为控制 Gaussian 系数的阶乘恢复误差，记

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

**显式误差预算。** 对每个整数 $n\ge4/\alpha$，

$$
|f(1)-G(1)|
\le \frac{\Gamma(R)T_1+K_G}{n}
+\frac{8\Gamma(R)D^2}{n^2}
+\frac{R}{R-1}\exp\!\left(\beta\sqrt n-\alpha n\log R\right)
+\sigma\Gamma(\sigma)\exp\!\left(-\alpha n\log\sigma\right).
$$

右侧全部参数只依赖 $C,q$ 及所选半径。两个指数项均为 $o(n^{-1})$。所以，只要证明上述预算，就得到定理所称的一致误差。

### 3.2. 精确系数归一化与中心化展开

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

记 $\Pi_k$ 为 $[k]$ 的集合分划格。“$k$ 个坐标互异”的示性函数具有标准的分划格容斥展开，其中大小为 $d$ 的块带 Möbius 权重 $(-1)^{d-1}(d-1)!$。分别对 $F_k$ 的行坐标和列坐标应用这一展开。每对分划对应一个二部多重图：边带互异标号 $1,\ldots,k$，两侧的顶点分别为行、列分划的块，每个大小为 $d$ 的块带上述权重。

每个顶点的数值标签独立地在 $[n]$ 中求和；不同顶点的数值标签允许相同。如果某个行顶点的度数为一，对其标签求和得到 $B$ 的一个列和，因而为零。度数为一的列顶点同样给出零行和。因此，只有所有顶点度数至少为二的图留下贡献。

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
G(r)\le\Gamma(r)\qquad(0\le r<1/q),
$$

因为 $-\log(1-x)\le x/(1-x)$，且 $\sum_i s_i^2=\|B\|_{\mathrm F}^2\le C^2$；这里 $s_i$ 为 $B$ 的奇异值。

从每个留下贡献的图中删除全部纯二度分量，称剩余部分为核心。核心可以不连通。如果核心有 $h$ 条边、$v$ 个顶点，定义其缺额为 $j=h-v$。非空核心满足 $j\ge1$。带边标号的分量分解给出逐系数恒等式

$$
F(t)=G(t)\left(1+\sum_{j\ge1}C_j(t)\right),
$$

其中 $C_j$ 为缺额 $j$ 的核心生成级数，保留全部 Möbius 符号与矩阵收缩。这是形式恒等式。在固定次数 $k$ 中只有有限个缺额可以出现；事实上，贡献于次数 $k$ 的非空核心满足 $j<k$。我们从不假设对全部 $j$ 的无穷和在非零 $t$ 处收敛。高于 $n$ 次的系数全部抵消为零，因为 $F_k$ 的互异坐标定义在这些次数下为零。

### 3.3. 核心压缩与全缺额活动量界

**引理（压缩核心活动量）。** 在上述记号下，

$$
\|C_j\|_R\le(Dj/n)^j\qquad(j\ge1),
$$

且首缺额满足更精确的界

$$
\|C_1\|_R\le T_1/n.
$$

其中 $\|H\|_R=\sum_{k\ge0}|[t^k]H|R^k$。

*证明。* 压缩所有内部顶点均为二度的极大路径。每条压缩边对应一条两端度数至少为三、长度为正的链。允许自环、重边和非连通压缩图。若 $b$ 为高次顶点数，$e$ 为压缩边数，则压缩不改变缺额，并给出

$$
e=b+j,\qquad
2j=\sum_{i=1}^b(d_i-2),\qquad
1\le b\le2j,\qquad e\le3j.
$$

为避免隐藏的对称因子，下面说明计数补偿。临时为 $b$ 个高次顶点及每个顶点的 $d_i$ 个半边分别加标号，并用这些标号为每条链选择唯一读取方向。每个原始带边标号的核心有 $b!\prod_i d_i!$ 种增饰。反过来，给定增饰后的半边配对及全部正链长，所有链位置均被确定，原始 $h$ 个边标号可以按 $h!$ 种方式分配到这些位置。在满足二部颜色奇偶条件时，内部顶点及其颜色也随之确定。

除去原始指数生成函数的 $h!$ 因子及临时增饰，再乘回高次顶点的绝对 Möbius 权重 $\prod_i(d_i-1)!$，补偿为

$$
\frac1{b!\prod_i d_i}.
$$

这一步包含自环和链反转：它们的两个半边已经带标号，无须另加方向因子。内部二度顶点的绝对 Möbius 权重为一，也没有额外的链长阶乘。

仅在取上界时忽略颜色限制。固定 $j,b$ 后，所得总补偿为

$$
U_{j,b}=
\frac{2^b}{b!}\frac{(2e)!}{2^e e!}
\sum_{\substack{d_1+\cdots+d_b=2e\\d_i\ge3}}
\frac1{d_1\cdots d_b},
\qquad e=b+j.
$$

长度为一的链对应矩阵元素，绝对值不超过 $C/n$。对于长度 $\ell\ge2$ 的链，先求和内部标签，其收缩是由 $B,B^{\mathsf T}$ 交替相乘所得矩阵的一个元素。两端行或列的二范数不超过 $C/\sqrt n$，中间因子的算子范数不超过 $q$。因此，收缩的绝对值不超过

$$
\frac{C^2}{n}q^{\ell-2}.
$$

按 $R$ 加权对长度求和，每条链的总活动量不超过 $W/n$。对 $b$ 个高次顶点标签求和至多给出 $n^b$，故

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

### 3.4. 有限线性窗口与阶乘恢复

采用截断参数

$$
M=\lfloor\alpha n\rfloor.
$$

它与主问题中的 Hamilton 路径常数 $L$ 无关。令 $v_j=(Dj/n)^j$。当 $j+1\le M$ 时，

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

形式核心恒等式中，次数不超过 $M$ 的贡献只能来自缺额 $j\le M$。结合 $G$ 系数非负、活动量引理及加权系数和的卷积不等式，得到

$$
\sum_{k=0}^{M}|F_k-[t^k]G|R^k
\le\Gamma(R)\left(\frac{T_1}n+\frac{8D^2}{n^2}\right).
$$

这只是有限系数窗口的界，不是对全部缺额在 $R$ 处取值。

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

右侧两项分别不超过 $u_\sigma^2$ 与 $v_\sigma$。因此，

$$
\sum_{k=0}^{M}(r_k-1)g_k\le K_G/n.
$$

合并恢复后的两部分，恰得到显式误差预算的前两项。

### 3.5. 极化与解析尾项

还需控制实际永久式多项式的尾部。若尾界丢失 $n!/n^n$ 因子，就不足以完成证明。

**引理（永久式极化）。** 对任意复方阵 $Z$，

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

**引理（半正定永久式界）。** 设 $H$ 为 Hermitian 半正定矩阵，特征值为 $\lambda_1,\ldots,\lambda_n$。则

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

对于实半正定输入，上述 Gaussian 恒等式与 AM–GM 比较正是 Han–Niles-Weed [3，引理 4.3–4.4] 所使用的工具。本节推广到一般非正规永久式的步骤来自前一个极化引理；我们没有把非正规矩阵直接当作半正定定理的输入。

双中心化假设给出 $P_nB=BP_n=0$。在 $|t|=R$ 上，因而有

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

与有限窗口估计结合，恰得到显式误差预算的另外两项，统一定理得证。$\square$

### 3.6. 定理的适用范围

本证明对任意阶数作解析与组合推导，结论不是对有限永久式计算的外推。它也不是有限维精确行列式公式：高缺额核心通常产生非零修正。

每次矩阵变换后，都必须重新核查假设。特别地，竞赛图邻接矩阵不必双中心化。缩放的存在性、缩放后的统一元素界和固定奇异值谱隙，都是另外需要证明的条件。本定理在这些条件成立后提供永久式近似；它本身既不证明全图 Hamilton 路径极值定理，也不确定有限阶极值竞赛图。

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

## 6. 小比分路径公式与下界

**小比分路径定理。** 对满足 $d=\|S\mathbf1\|_\infty=o(\sqrt n)$ 的竞赛图序列，一致地有

$$
\frac{H(T)}{\mu_n}=\rho_n(S)+O\left(\frac{(d+1)^2}{n}\right).
$$

证明。对每个主删集 $|U|=k\le k_n$，应用第 4 节的小比分永久式近似。因 $d+k_n+1=o(\sqrt n)$，其适用性对全部这些子集一致。恢复下降阶乘 $(n)_k$ 后，由正路径卷积得到

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

下降阶乘恢复误差贡献 $O(n^{-1}\sum k^2w_k)$；真实长路径项由第 2 节控制为 $o(n^{-1})$。将上式短生成和扩展到全部 $k$ 的代价为 $n^{-2+o(1)}$，因为系数被 $w_k$ 控制。于是

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

代回即得定理。

对奇数 $n$，在模 $n$ 的剩余类上定义圆环竞赛图 $\mathrm{Car}_n$：当 $1\le j\le(n-1)/2$ 时，令 $i\to i+j$。该图正则，故 $d=0$。对偶数 $n$，令 $\mathrm{Car}_n$ 为 $\mathrm{Car}_{n+1}$ 删去一个顶点所得的图，此时 $d=1$。

奇阶圆环符号矩阵与 $T_n^0$ 带符号置换相似。一个显式构造是：用对角符号 $(-1)^i$，$0\le i<n$，共轭 $T_n^0$，再按 $0,2,\ldots,n-1,1,3,\ldots,n-2$ 重排指标；逐边核对即得圆环方向。将逆向的带符号共轭和重排限制到偶阶的一点删除后，变换所得的矩阵为剩余有序指标上的 $T_n^0$，并非称实际偶阶圆环图为传递图。因此奇偶两类均满足

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

结合第 5 节，主要定理证毕。此处带符号相似只保持谱因子；没有声称它保持 Hamilton 路径数。

## 7. 核验、范围与局限

### 7.1 已完成的核验

正文证明是任意阶分析论证。精确有限检查用于发现归一化、符号与尺度恢复错误，而非从样本外推渐近定理。所附审计档案记录了以下检查的新一轮完成运行：

- 23630 个有理凸装填检查和 276 个整数相位排序检查；1 至 6 阶全部 33867 张标号图的谱比值检查，以及 1 至 5 阶全部 1099 张图的有理算子上限检查。
- 96 个精确核心活动量检查、8381 个下降阶乘检查，以及最大到 384 阶的 16 个非对称、非正规二秩永久式精确例。
- 267 个一般有理矩阵删除比较和 267 个中心化比较；693 个竞赛 Gaussian 比较、635 个尺度恢复检查、56 个精确永久式例及 14 个精确路径例。
- 1111 个图的归约恒等式例，其中有 36746 个比分删点检查、36746 个秩一生成式界、579 个加权生成式、24 个完整四块分解和 112 个异常乘积检查。

四组重跑全部正常结束，退出码为零。另外的浮点缩放例仅作诊断。档案包含原始精确记录、各自范围说明，以及三个组成部分的证明复核报告。

常数的有理包围区间为

$$
2.855957892565113<L<2.855957892565114,
$$

$$
2.857401177672316<C_*<2.857401177672317.
$$

首项常数的相对间隙位于 $0.000505359379058$ 与 $0.000505359379059$ 之间。这些检查均不认证主要定理的有限起始阶数。

### 7.2 没有证明的结论

本文没有证明所有竞赛图都满足 $\rho_n(S)\le r_n$，因此没有证明 $P(n)=(L+O(n^{-1}))\mu_n$。凸装填只用了最大奇异值与平方总质量；其松弛谱未必可实现。

本文也没有证明有限极值图必正则或平衡，没有证明圆环图唯一极值、甚至每个有限阶都极值，亦没有求得任意 $P(n)$ 的精确公式。小比分近似本身不能排除全部其他图，这正是必须另作方差与异常点归约的原因。

$O(n^{-1})$ 路径近似不能确定首个修正项的系数，有限诊断样本也不能把其中常数自动变为有效数值。这些问题有意不列入本文结论。

### 7.3 研究与作者说明

本稿在证明重建、交叉检查、翻译与精确算术诊断方面使用了 AI 辅助。组成部分的审计是在该辅助工作流程内进行的独立重建，不是外部人工同行评审，也不是形式化证明助手认证。投稿前建议作者复核并邀请独立专业审查。已有结果均在下面注明来源；内部复核本身不产生新颖性声明。

## 参考文献

[1] John Irving and Mohamed Omar. Revisiting the Rédei-Berge Symmetric Functions via Matrix Algebra. The Electronic Journal of Combinatorics 32(4) (2025), P4.43. DOI: 10.37236/13841. [原始论文](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v32i4p43/pdf/).

[2] Noga Alon. The Maximum Number of Hamiltonian Paths in Tournaments. [作者手稿](https://web.math.princeton.edu/~nalon/PDFS/hamilton.pdf). 本文使用的 Brégman 永久式界见其中 Lemma 2.1。

[3] Yanjun Han and Jonathan Niles-Weed. Approximate independence of permutation mixtures. arXiv:2408.09341. [第 2 版，含 Lemmas 4.3-4.4](https://arxiv.org/html/2408.09341v2). 此文用于 Gaussian 与半正定永久式工具的对照，不作为任意非对称矩阵近似的黑箱输入。

[4] Bo Deng, Xueliang Li, Bryan Shader and Wasin So. On the Maximum Skew Spectral Radius and Minimum Skew Energy of Tournaments. [作者手稿](https://cfc.nankai.edu.cn/_upload/article/files/09/3a/890a6a5c4660ae2350ac183d2dfa/cb663bb2-4ff4-476f-8047-50514a7780a5.pdf). DOI: 10.1080/03081087.2017.1357676.

[5] Peter McCullagh. An asymptotic approximation for the permanent of a doubly stochastic matrix. Journal of Statistical Computation and Simulation 84(2) (2014), 404-414. DOI: 10.1080/00949655.2012.712122. [arXiv:1205.5723](https://arxiv.org/abs/1205.5723).

[6] N. C. Wormald. Tournaments with many Hamilton cycles. [作者预印本](https://users.monash.edu.au/~nwormald/papers/hamtourn.pdf).

[7] Ehud Friedgut and Jeff Kahn. On the Number of Hamiltonian Cycles in a Tournament. Combinatorics, Probability and Computing 14(5-6) (2005), 769-781. [DOI: 10.1017/S0963548305006863](https://doi.org/10.1017/S0963548305006863).
