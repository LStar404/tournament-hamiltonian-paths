# Third-round precision revision

11 October 2026

## Baseline and scope

This narrow revision starts from the working fork's merged second-round commit `42ee0a1572e9e0cdf88bfc17811c7559b3b2e03c`, whose tree is `77713366e6d7759389e72e9dc65bc03e592fe07e`. It corrects the description of one formal intermediate bound and improves cross-referencing and quantifier clarity. It does not change the main theorem, its constants, the deletion range, or any Lean proof source.

The current English and Chinese masters remain authoritative. Generated TeX, reading PDFs and exact section slices are rebuilt together. Historical revision, typesetting and formal-verification receipts retain their original contents and scope.

## Changes

1. Section 3.3, Appendix A.1 and the current manuscript–Lean correspondence now distinguish all three convolution contributions. Only the disjoint short contribution has the multiplicative bound `(10/3)4^(−f)(1+ε_n)`. The short terms meeting the exceptional set and the long terms give a separate additive `δ_n`. Both errors tend to zero uniformly in the relevant low-variance class; the additive error is not absorbed into `4^(−f)` when the exceptional-set size can grow
2. The formal budget is stated explicitly: `(10/3)(1/4)(21/20)+1/25+1/25=191/200<1`. This matches `disjointShortConvolution_le_crude` and `exceptional_pathCount_lt_mean_of_crude_bound` in `CrudeExceptionalExclusion.lean`
3. Eight selected formulas have matching bilingual numbers and readable links: path convolution (2.1), full exceptional bound (3.1), score penalty (3.2), uniform permanent approximation (5.1), core activity (5.2), deletion mass (6.1), exact restoration (6.2), and small-score permanent approximation (6.3)
4. Lemma 6.4 now selects `C_err`, `δ` and `N₀` after fixing `B₀`, before quantifying over the dimension, tournament and independent equal-size deletion sets. The original `t≤B₀ log n` restriction remains. The finite smallness condition gives an explicit relative-error bound, and the proof separates it from the asymptotic conclusion. It also justifies positive retained order and mass before normalization
5. The PDF exporter validates equation anchors, tags, reference numbers, compiled label values and bilingual ID/number maps. Regression tests cover failures as well as a real three-pass XeLaTeX round trip. CI additionally checks the additive-error wording, exact rational budget and matching manuscript equation maps without requiring the optional typesetting toolchain

The 192 pre-existing display formulas in each language retain their mathematical content; only tags and cross-references were added to selected displays. The explicit exceptional bound and rational budget are the two new displays, bringing the total to 194 per language.

## Verification and limits

- The local test suite, fresh finite-diagnostic outcomes, source/output hashes and final page-review scope are recorded in [revision metadata](revision_round3_20261011.json), [typesetting receipt](typesetting_round3_20261011.json) and [finite diagnostics](verification/diagnostics_round3_20261011.json)
- All 246 Lean-source and configuration hashes were rechecked against the archived formal audit and match. This is a source-hash comparison, not a new local Lean kernel build
- The exact baseline passed remote [Verify proofs, run 38073718040](https://github.com/makerY666/tournament-hamiltonian-paths/actions/runs/38073718040), including its Lean build/audit, four finite diagnostics and signed-core tests. A later third-round commit's own CI status belongs to that commit's pull request; it is not inferred from baseline success
- The external review attachment's independent arithmetic-check counts and sandbox links were not imported as newly run evidence. The fresh calculations here are the repository diagnostics and stated regression tests
- These checks do not amount to external human peer review or a guarantee that every proof step is error-free. No upstream merge, release, DOI/archive metadata or journal submission is part of this revision

## 中文摘要

本轮以工作 fork 已合并的第二轮提交 `42ee0a1572e9e0cdf88bfc17811c7559b3b2e03c` 为基线，只做精确性修订与少量阅读优化。

- 第 3.3 节、附录 A.1 和当前 Lean 对应表统一保留加性余项：乘性界只用于删除集避开异常点的短卷积项；另外两部分分别控制，三部分的明确预算为 `191/200<1`
- 中英文同步标注八个关键公式，并在 Markdown、TeX 和 PDF 中建立可核验的引用；原有 192 个显示公式的数学内容不变，新增两个显示公式，总数为 194
- 引理 6.4 明确“先固定 B₀，再统一选取常数及阈值，最后量化阶数、图和删集”的顺序，保留对数删除窗口；证明补明保留阶数和质量为正，并区分有限小量条件与渐近趋零
- 重新运行本仓库四项有限诊断、排版与回归测试，逐项核对 246 个形式化源码及配置哈希；历史记录保持原样。本轮没有在本地重建 Lean，也没有将外部审阅附件的独立计算数目当作本次实跑结果

精确源码、输出哈希、页数及逐页复查范围见本轮机器可读记录。主定理、最终常数、Lean 源码及归档版本信息均未修改。
