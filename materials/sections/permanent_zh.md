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
