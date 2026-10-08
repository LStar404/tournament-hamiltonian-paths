# Hamiltonian paths in tournaments / 竞赛图中的 Hamilton 路径

**Author / 作者:** Xingchen Liu / 刘星辰  
**Affiliation / 单位:** Independent Researcher / 个人研究者  
**Contact / 联系:** lxc-em5158@outlook.com  
**Manuscript snapshot / 稿件版本:** 2026-10-09 (revised / 修订)

This repository contains a bilingual research manuscript on constant-factor bounds for the maximum number of directed Hamiltonian paths in an n-vertex tournament, together with proof-audit reports and reproducible finite diagnostics.

本仓库收录 n 阶竞赛图中有向 Hamilton 路径最大数量的常数因子界研究，包括中英文论文、完整证明、内部审查记录和有限核验程序。

## Read the paper / 阅读论文

- [English PDF (25 pages)](papers/tournament_hamilton_paths_en.pdf)
- [中文 PDF（23 页）](papers/tournament_hamilton_paths_zh.pdf)
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

The arguments were reconstructed and cross-checked in an AI-assisted internal research workflow. The main theorem now has a complete Lean proof; external human peer review has not been reported. Finite computations are diagnostics, not replacements for the all-order proof. Independent expert review is recommended before relying on the manuscript as a settled result.

证明经过 AI 辅助内部重建和交叉复核，主要渐近定理现已有完整 Lean 形式化证明；这不代表已完成外部人工同行评审。建议投稿前由作者和独立专家进一步检查。

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

This is the internally audited manuscript snapshot, not a dump of all exploratory drafts. Earlier speculative or superseded conclusions are not published as established results. Local machine paths and temporary rendering files are excluded. The manuscripts and PDFs were revised on 9 October 2026 to document the merged Lean formalization.

本次发布只包含已复核论文版本及必要的核验材料，不将早期探索稿或已被替代的结论作为已证结果上传。本机路径和临时渲染文件不公开。中英文论文及 PDF 已于 2026 年 10 月 9 日修订，加入合并后的 Lean 形式化证明说明。

## Lean formalization / Lean 形式化证明

The formalization was contributed in [PR #1](https://github.com/LStar404/tournament-hamiltonian-paths/pull/1) and merged as commit [`2983cd9`](https://github.com/LStar404/tournament-hamiltonian-paths/commit/2983cd984a2698a738a91093060d42f394e64a89). The manuscripts describe the contributor's verification record; this revision did not independently rerun the full Lean build.

The [Lean project](formalization/TournamentHamiltonian.lean) pins Lean and Mathlib 4.34.1. The unconditional theorem [`TournamentHamiltonian.mainBound`](formalization/TournamentHamiltonian/MainBound.lean) proves the displayed maximum-path bounds for the actual finite tournament and Hamiltonian-path definitions, with one absolute constant and one common threshold. It includes both carousel parities and an upper bound for every tournament.

The proof constructs all required permanent, compressed-core activity, local-scaling and Gaussian estimates internally. Its [axiom audit](formalization/Audit.lean) permits only `propext`, `Classical.choice` and `Quot.sound`, and checks transitive dependencies of every imported project theorem. No placeholder or computation axiom is permitted. [The proof ledger](formalization/proof-status.json) records declarations, source coverage and implementation differences. The more conservative Gaussian factorial-recovery constant proves the same uniform rate without claiming the manuscript's displayed derivative constant verbatim. The ancillary whole-path approximation is also proved for every nonnegative score bound d(n) with d(n)/sqrt(n) tending to zero, using one dimension-independent constant and a threshold uniform over all actual tournaments.

无条件定理 `mainBound : MainBound` 已证明原文的真实最大 Hamilton 路径数上下界，使用同一绝对误差常数和同一起始阶数。两种奇偶轮转构造与所有锦标赛的统一上界均已接入。公理审查检查全部传递依赖，仅允许 Lean/Mathlib 的三个标准基础公理。主定理不依赖未证明的永久量、缩放、活动度或高斯前提。部分中间预算采用更保守但充分的常数；对任意非负比分界 d(n)=o(sqrt n)，附属整个路径数双侧近似也已证明，误差常数不依赖阶数，阈值对所有实际锦标赛统一。

To reproduce the final submission gate:

```text
cd formalization
lake exe cache get Mathlib.Analysis.Real.Pi.Bounds Mathlib.Tactic Mathlib.Data.Fintype.Perm Mathlib.Data.Finset.Lattice.Fold Mathlib.LinearAlgebra.Matrix.Permanent Mathlib.LinearAlgebra.Matrix.Adjugate Mathlib.Analysis.InnerProductSpace.Orientation Mathlib.Analysis.MeanInequalities Mathlib.Analysis.SpecificLimits.Normed Mathlib.Analysis.Complex.ExponentialBounds Mathlib.Analysis.SpecialFunctions.Stirling Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics Mathlib.LinearAlgebra.Matrix.SchurComplement Mathlib.LinearAlgebra.Matrix.Block Mathlib.Analysis.SpecialFunctions.Complex.LogBounds Mathlib.Analysis.Matrix.Spectrum Mathlib.Analysis.CStarAlgebra.Matrix Mathlib.Analysis.CStarAlgebra.Basic Mathlib.LinearAlgebra.Matrix.PosDef Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds Mathlib.Data.Finset.Sort Mathlib.Data.Prod.Lex Mathlib.Algebra.Polynomial.BigOperators Mathlib.Algebra.BigOperators.Group.Finset.Powerset Mathlib.Algebra.Order.Star.Real Mathlib.Analysis.Matrix.Order Mathlib.Combinatorics.Enumerative.IncidenceAlgebra Mathlib.Order.Partition.Finpartition Mathlib.Data.Setoid.Partition Mathlib.GroupTheory.Perm.Cycle.Factors Mathlib.GroupTheory.Perm.Sign Mathlib.GroupTheory.Perm.Cycle.Type Mathlib.Algebra.BigOperators.Pi Mathlib.Probability.Distributions.Gaussian.Real Mathlib.Probability.Distributions.Gaussian.Multivariate Mathlib.MeasureTheory.Integral.Pi Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas Mathlib.Data.Nat.Factorial.DoubleFactorial Mathlib.Data.Matrix.Block Mathlib.MeasureTheory.Integral.DominatedConvergence Mathlib.Analysis.Polynomial.Fourier Mathlib.Algebra.Polynomial.Eval.Degree Mathlib.GroupTheory.Perm.DomMulAct Mathlib.Data.Nat.Choose.Multinomial Mathlib.RingTheory.RootsOfUnity.Complex Mathlib.Algebra.Field.GeomSum Mathlib.Probability.Distributions.Exponential Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap Mathlib.Combinatorics.Enumerative.Composition Mathlib.Data.Fin.Tuple.NatAntidiagonal Mathlib.Analysis.SpecificLimits.Basic Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff Mathlib.Data.Matrix.ColumnRowPartitioned Mathlib.Data.Fin.Rev Mathlib.Algebra.Order.Floor.Semiring Mathlib.Analysis.Complex.Exponential
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
