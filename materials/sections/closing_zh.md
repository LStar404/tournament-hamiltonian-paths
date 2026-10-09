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

本稿在证明重建、交叉检查、翻译与精确算术诊断方面使用了 AI 辅助。组成部分的审计是在该辅助工作流程内进行的独立重建。第二作者完成的配套 Lean 形式化证明见第 7.4 节。当前没有外部人工同行评审记录。投稿前建议邀请独立专业审查。已有结果均在下面注明来源；内部复核或形式化证明本身不产生新颖性声明。

### 7.4 配套 Lean 形式化证明

[配套 Lean 工程](https://github.com/LStar404/tournament-hamiltonian-paths/tree/2983cd9/formalization)由第二作者叶祥宇以 GitHub 用户 [makerY666 的身份通过 PR #1](https://github.com/LStar404/tournament-hamiltonian-paths/pull/1) 提交，固定使用 Lean 和 Mathlib 4.34.1。工程把竞赛图定义为不同顶点间每对恰有一个方向、无自环的有标号图；Hamilton 路径是所有相邻边均顺向的顶点排列；$P(n)$ 是这类图的路径数最大值。精确常数 $L$ 与 $C_*$ 对应本文主要定理。

工程包含声明 `TournamentHamiltonian.mainBound : TournamentHamiltonian.MainBound`。该命题断言存在同一个实数 $K\ge0$ 和同一个整数 $n_0\ge2$，使得对所有 $n\ge n_0$ 都有

$$
(L-K/n)\mu_n\le P(n)\le(C_*+K/n)\mu_n.
$$

据提交的[核验记录](https://github.com/LStar404/tournament-hamiltonian-paths/blob/2983cd9/formalization/VERIFICATION.md)，运行 `python verify_lean.py --require-main` 的退出码为零：工程构建通过，实际 `MainBound` 类型得到检查，所有工程源码均纳入审计，3674 个工程定理的传递公理审查仅报告 `propext`、`Classical.choice` 和 `Quot.sound`。Lean 证明的部分中间常数与本文展示的估计不同，但结论是同一个最终界。本次修订采纳该 PR 提交的核验记录；本文不声称另行重跑了完整构建。

形式化对象是上述渐近不等式。它没有给出 $K$ 或 $n_0$ 的有效数值，没有求出有限阶 $P(n)$ 的精确公式，也没有证明尖锐全局首项常数或极值图分类。为认可形式化证明的贡献，本修订版将叶祥宇列为第二作者；两位署名作者均为个人研究者。

## 参考文献

[1] John Irving and Mohamed Omar. Revisiting the Rédei-Berge Symmetric Functions via Matrix Algebra. The Electronic Journal of Combinatorics 32(4) (2025), P4.43. DOI: 10.37236/13841. [原始论文](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v32i4p43/pdf/).

[2] Noga Alon. The Maximum Number of Hamiltonian Paths in Tournaments. Combinatorica 10(4) (1990), 319-324. DOI: 10.1007/BF02128667. [作者手稿](https://web.math.princeton.edu/~nalon/PDFS/hamilton.pdf). 本文使用的 Brégman 永久式界见其中 Lemma 2.1。

[3] Yanjun Han and Jonathan Niles-Weed. Approximate independence of permutation mixtures. arXiv:2408.09341. [第 2 版，含 Lemmas 4.3-4.4](https://arxiv.org/html/2408.09341v2). 此文用于 Gaussian 与半正定永久式工具的对照，不作为任意非对称矩阵近似的黑箱输入。

[4] Bo Deng, Xueliang Li, Bryan Shader and Wasin So. On the Maximum Skew Spectral Radius and Minimum Skew Energy of Tournaments. [作者手稿](https://cfc.nankai.edu.cn/_upload/article/files/09/3a/890a6a5c4660ae2350ac183d2dfa/cb663bb2-4ff4-476f-8047-50514a7780a5.pdf). DOI: 10.1080/03081087.2017.1357676.

[5] Peter McCullagh. An asymptotic approximation for the permanent of a doubly stochastic matrix. Journal of Statistical Computation and Simulation 84(2) (2014), 404-414. DOI: 10.1080/00949655.2012.712122. [arXiv:1205.5723](https://arxiv.org/abs/1205.5723).

[6] N. C. Wormald. Tournaments with many Hamilton cycles. [作者预印本](https://users.monash.edu.au/~nwormald/papers/hamtourn.pdf).

[7] Ehud Friedgut and Jeff Kahn. On the Number of Hamiltonian Cycles in a Tournament. Combinatorics, Probability and Computing 14(5-6) (2005), 769-781. [DOI: 10.1017/S0963548305006863](https://doi.org/10.1017/S0963548305006863).
