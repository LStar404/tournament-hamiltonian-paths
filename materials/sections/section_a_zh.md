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
