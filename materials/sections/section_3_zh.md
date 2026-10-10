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

由于 $P(n)\ge\mu_n$，这个严格小于一的固定间隙说明：对所有充分大的阶数，这类竞赛图不能达到最大值。此处只需 $o(1)$ 误差。

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

$$
\frac{H(T)}{\mu_n}\le
\rho_n(S)\exp\left\{-\tau+
K\left[\frac{1+\tau+\tau^2}{n}
+\frac{\tau^{3/2}+\tau}{\sqrt n}+\sqrt{\tau/n}\right]\right\}
+o(1/n).
$$

当 $\tau\le K_0\log n$ 时，除常数 $1/n$ 外的多项式误差项，在充分大阶数总共至多消耗 $\tau/4$。剩余平方根项由 Young 不等式控制：

$$
K\sqrt{\tau/n}\le\tau/4+K^2/n.
$$

因此总指数至多为 $-\tau/2+K/n$。再使用谱上限，得到

$$
H(T)/\mu_n\le C_*e^{K/n}+o(1/n)=C_*+O(1/n).
$$

### 3.5 完成上界

三类图覆盖全部竞赛图。高方差图的归一化路径数为 $o(1/n)$；低方差但含异常点的图严格低于一；所有剩余图满足刚才的 $C_*+O(1/n)$ 上界。因此

$$
\boxed{P(n)\le\bigl(C_*+O(1/n)\bigr)\mu_n.}
$$

三种情形中的起始阶数均不依赖具体竞赛图，因此取一个共同阈值便得到定理 1.1 的上界。

