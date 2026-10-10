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

$$
H(T)=\sum_{U\subseteq V(T)}\det(I+A[U])\operatorname{per}A[U^c].
$$

邻接矩阵的永久式计算有向圈覆盖数。该恒等式将互补顶点集上的圈覆盖计数转化为路径数。它是 Irving 与 Omar 的 Proposition 2 [1] 在竞赛图上的特化，其中补邻接矩阵为 $\overline A=J-A=I+A^{\mathsf T}$，包含对角元。

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

