# Hamiltonian paths in tournaments / 竞赛图中的 Hamilton 路径

**Author / 作者:** Xingchen Liu / 刘星辰  
**Affiliation / 单位:** Independent Researcher / 个人研究者  
**Contact / 联系:** lxc-em5158@outlook.com  
**Manuscript snapshot / 稿件版本:** 2026-10-08

This repository contains a bilingual research manuscript on constant-factor bounds for the maximum number of directed Hamiltonian paths in an n-vertex tournament, together with proof-audit reports and reproducible finite diagnostics.

本仓库收录 n 阶竞赛图中有向 Hamilton 路径最大数量的常数因子界研究，包括中英文论文、完整证明、内部审查记录和有限核验程序。

## Read the paper / 阅读论文

- [English PDF (25 pages)](papers/tournament_hamilton_paths_en.pdf)
- [中文 PDF（22 页）](papers/tournament_hamilton_paths_zh.pdf)
- [Editable English manuscript](materials/manuscript_en.md) / [可编辑中文主稿](materials/manuscript_zh.md)
- [English LaTeX source](materials/manuscript_en.tex) / [中文 LaTeX 源文件](materials/manuscript_zh.tex)
- [核验结论与未证明事项](materials/audit_summary_zh.md)

## Main result and its scope / 主要结果与范围

Let H(T) count vertex permutations forming a directed Hamiltonian path, and let P(n) be its maximum over n-vertex tournaments. Put

$$
\mu_n=\frac{n!}{2^{n-1}},\qquad L=\frac{\cosh 1}{\cos 1},\qquad C_* = \frac{3\pi^4+4\pi^2-32}{\pi^4+4\pi^2-32}.
$$

The manuscript gives a proof that there are absolute constants K and n_0 such that, for all n at least n_0,

$$
(L-K/n)\mu_n\le P(n)\le(C_*+K/n)\mu_n.
$$

Here L is approximately 2.855957892565114 and C_* approximately 2.857401177672317. Their relative leading-constant gap is about 0.050536%; it is **not** a finite-n error certificate. The constants K and n_0 have not been evaluated to a usable numerical threshold.

The proof uses a uniform zeroth-order permanent approximation, local matrix scaling, Gaussian determinant estimates for nonprincipal deletions, and a full-tournament reduction retaining the score penalty. Existing work is credited in the manuscripts; this repository makes no publication-priority claim.

正文建立上述充分大阶数的上下界，并未求出一般有限 P(n) 的精确值。上下常数的相对间隙不是有限阶误差证书；误差常数和起始阶数尚未给出可实用的有效数值。

### Research status / 研究状态

The arguments were reconstructed and cross-checked in an AI-assisted internal research workflow. They have **not** undergone external human peer review or formal proof-assistant verification. Finite computations are diagnostics, not replacements for the all-order proof. Independent expert review is recommended before relying on the manuscript as a settled result.

证明经过 AI 辅助内部重建和交叉复核，当前未发现致命缺口；这不等于外部人工同行评审或形式化证明认证。建议投稿前由作者和独立专家进一步检查。

Not claimed / 未声称证明：

- The sharp global identity P(n) = (L + O(1/n)) mu_n.
- An exact finite formula for P(n).
- Regularity, balance or uniqueness of finite-order extremal tournaments.
- The first correction coefficient for Hamiltonian path counts.
- Effective numerical values of K and n_0.

## Files and audits / 文件与核验

- `papers/`: final, visually checked PDF manuscripts.
- `materials/`: editable manuscripts, LaTeX exports, component audit reports and diagnostic records.
- `materials/sections/`: modular bilingual manuscript chapters.
- `materials/verification/`: four diagnostic entry points and their local dependency modules.
- [Build/editing notes](materials/README.md): details on manuscript editing and the distinction between exported LaTeX and independently typeset PDFs.
- [Raw diagnostic reruns](materials/audit_computations.json), [delivery checks and hashes](materials/delivery_qa.json).

This is the internally audited manuscript snapshot, not a dump of all exploratory drafts. Earlier speculative or superseded conclusions are not published as established results. Local machine paths and temporary rendering files are excluded; manuscript and PDF contents are unchanged.

本次发布只包含已复核论文版本及必要的核验材料，不将早期探索稿或已被替代的结论作为已证结果上传。本机路径和临时渲染文件不公开，论文与 PDF 内容保持原样。

## Lean formalization in progress / Lean 形式化进展

The [Lean project](formalization/TournamentHamiltonian.lean) pins Lean and Mathlib 4.34.1. Verified components include finite tournament/path definitions and averaging, paired skew spectra and spectral-factor identities, the generic Euclidean operator-norm gap and Gaussian Gram positivity, principal-weight positivity and Hadamard bounds, weighted subset moments and the logarithmic-cutoff scalar tail, the exact transitive determinant formula, actual carousel constructions for both parities and their spectral-factor O(1/n) approximation, unconditional actual spectral packing and the C_* spectral bound, the upper-constant enclosure, exact permanent coefficient normalization and partition expansion with explicit signed-factorial Mobius weights and singleton cancellation, the exact original Hamiltonian-path positive convolution, finite walk interfaces and exact inverse determinant/permanent convolution, the full shifted kernel Gram and norm gap, nonprincipal mass and marginal deletion identities, exact paired preconditioning mass and marginals, and Gaussian deletion/centering loss, the explicit (24t+18tau+11)/n centered-tournament loss, and Frobenius logarithmic Lipschitz bounds, actual preconditioning marginal and displacement bounds, rectangular normalization/deletion budgets, explicit balanced gauge Hessian inverse bounds, finite Wick pairing counts, true Gaussian bilinear integrals and Taylor coefficients, exact Gaussian/nonpairing permanent-coefficient splitting, the complete Brégman permanent bound, actual Banach construction of doubly stochastic scalings with density and gap control, permanent scaling/restoration, and scalar score-penalty estimates. Its [proof ledger](formalization/proof-status.json) records the remaining all-order obligations. **The main asymptotic theorem is not yet formally proved or independently certified.**

Lean 工程已形式化上述有限计数和代数部分，以及一般锦标赛的谱配对、精确配对质量、D_n 与 rho_n 的行列式公式和实/复数算子范数间隙与高斯 Gram 矩阵正定性、任意阶主子矩阵权重的正性与上界、固定加权矩收敛、对数截断的标量尾项、传递矩阵行列式公式、奇偶两种实际轮转锦标赛的构造及 rho_n 的统一 O(1/n) 误差。任意实际锦标赛的强算子谱界及 rho_n <= C_*、实际永久量系数的精确归一化、缩放前核 Y 的有限阶 Gram 和范数间隙、不同删行删列集合的精确质量和边际公式、一般矩形高斯因子的删除损失以及实际永久量系数的递归 Möbius 分划展开与单例消去、配对预处理的精确总质量及边际恒等式、行列式—永久量的全阶逆卷积消去与高斯居中损失、Frobenius 对数 Lipschitz 估计及配对预处理总质量的统一方差误差界也已证明。实际 Hamilton 路径数与正权卷积的全阶等式、一般分划的显式带符号阶乘权重、任意不同删行删列的 (24t+18tau+11)/n 高斯误差界，以及实际预处理矩阵的密度与 Frobenius/算子位移界现已证明。实际预处理边际误差、矩形质量归一化与删除预算、缩放规范 Hessian 的显式逆及范数界、Wick 配对的通用有限计数也已证明。真实 Banach 构造的双随机缩放势、缩放后的密度与谱界、完整 Brégman 永久量上界、真实高斯积分与 Wick/Taylor 系数，以及实际永久量系数的高斯主项/非配对余项分解也已证明。完整永久量近似、轮转锦标赛的实际路径数近似以及完整渐近主定理仍未完成。编译成功不代表全文已得到形式化认证。以下提交检查必须等无条件的 `MainBound` 证明完成后才会通过：

```text
cd formalization
lake exe cache get Mathlib.Analysis.Real.Pi.Bounds Mathlib.Tactic Mathlib.Data.Fintype.Perm Mathlib.Data.Finset.Lattice.Fold Mathlib.LinearAlgebra.Matrix.Permanent Mathlib.LinearAlgebra.Matrix.Adjugate Mathlib.Analysis.InnerProductSpace.Orientation Mathlib.Analysis.MeanInequalities Mathlib.Analysis.SpecificLimits.Normed Mathlib.Analysis.Complex.ExponentialBounds Mathlib.Analysis.SpecialFunctions.Stirling Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics Mathlib.LinearAlgebra.Matrix.SchurComplement Mathlib.LinearAlgebra.Matrix.Block Mathlib.Analysis.SpecialFunctions.Complex.LogBounds Mathlib.Analysis.Matrix.Spectrum Mathlib.Analysis.CStarAlgebra.Matrix Mathlib.Analysis.CStarAlgebra.Basic Mathlib.LinearAlgebra.Matrix.PosDef Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds Mathlib.Data.Finset.Sort Mathlib.Data.Prod.Lex Mathlib.Algebra.Polynomial.BigOperators Mathlib.Algebra.BigOperators.Group.Finset.Powerset Mathlib.Algebra.Order.Star.Real Mathlib.Analysis.Matrix.Order Mathlib.Combinatorics.Enumerative.IncidenceAlgebra Mathlib.Order.Partition.Finpartition Mathlib.Data.Setoid.Partition Mathlib.GroupTheory.Perm.Cycle.Factors Mathlib.GroupTheory.Perm.Sign Mathlib.GroupTheory.Perm.Cycle.Type Mathlib.Algebra.BigOperators.Pi Mathlib.Probability.Distributions.Gaussian.Real Mathlib.Probability.Distributions.Gaussian.Multivariate Mathlib.MeasureTheory.Integral.Pi Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas Mathlib.Data.Nat.Factorial.DoubleFactorial Mathlib.Data.Matrix.Block
python verify_lean.py --require-main
```

For component verification during development, omit `--require-main`. The verifier builds the project, checks transitive axiom dependencies, records hashes of the project sources reached through imports, lists unimported sources separately, and reports the main-theorem status. The submission gate also requires every project Lean source to be imported for audit. `python run_diagnostics.py` reruns the four published finite diagnostics and records their scope and raw output under `formalization/audit/`.

## Reproduce the finite diagnostics / 复现有限检查

Use Python 3.11 or newer. From the repository root:

```text
python -m pip install -r requirements.txt
cd materials/verification
python verify_operator_packing_path_constant.py
python verify_uniform_permanent_zeroth_audit.py
python verify_nonprincipal_gaussian_deletion.py
python verify_standalone_linear_energy_reduction.py
```

These entry points check finite algebraic, arithmetic and floating-point examples within the scopes recorded in their JSON output. They do not establish an effective all-order threshold or perform a new general extremal search. Other modules are included as dependencies; their presence does not assert the validity of every historical exploratory claim.

LaTeX sources target XeLaTeX, using Times New Roman and, for Chinese, SimSun; substitute available fonts when necessary. The exported LaTeX sources were **not compiled locally**. The delivered PDFs were independently typeset and visually checked; formulas are high-resolution rendered glyph images. Edit formulas in the Markdown or LaTeX sources.

## License / 授权

This work is released under [CC BY 4.0 International](LICENSE). Reuse, modification, redistribution, and commercial use are permitted, provided that appropriate credit is given to Xingchen Liu / 刘星辰, a link to the license is provided, and changes are indicated.

本成果采用 [CC BY 4.0 International](LICENSE) 发布；允许再利用、修改、再发布和商业使用，但必须对刘星辰作适当署名、附上许可证链接并说明改动。
