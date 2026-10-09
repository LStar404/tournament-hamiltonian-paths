# Hamiltonian paths in tournaments

[English](#english) · [中文](#中文)

## English

**Constant-factor bounds for Hamiltonian paths in tournaments**
Xingchen Liu and Xiangyu Ye · Independent Researchers
Contact: [lxc-em5158@outlook.com](mailto:lxc-em5158@outlook.com)

This repository contains the English and Chinese manuscripts, a Lean formalization, and computational checks for bounds on the maximum number of directed Hamiltonian paths in a tournament.

**Read the paper:** [English PDF](papers/tournament_hamilton_paths_en.pdf) (25 pages) · [Chinese PDF](papers/tournament_hamilton_paths_zh.pdf) (23 pages)
**Archived manuscript:** [Version 1.1, 9 October 2026, on Zenodo](https://zenodo.org/records/23249802) · DOI: [10.5281/zenodo.23249802](https://doi.org/10.5281/zenodo.23249802)

Repository version: **1.1.1** · [GitHub Releases](https://github.com/LStar404/tournament-hamiltonian-paths/releases)

### Main result

Let $H(T)$ count vertex permutations forming a directed Hamiltonian path, and let $P(n)$ be its maximum over tournaments on $n$ vertices. Write

$$
\mu_n=\frac{n!}{2^{n-1}},\qquad
L=\frac{\cosh 1}{\cos 1},\qquad
C_* = \frac{3\pi^4+4\pi^2-32}{\pi^4+4\pi^2-32}.
$$

There are absolute constants $K\ge0$ and $n_0\ge2$ such that, for every $n\ge n_0$,

$$
(L-K/n)\mu_n\le P(n)\le(C_*+K/n)\mu_n.
$$

The leading constants are $L\approx2.855957892565114$ and $C_*\approx2.857401177672317$, a relative gap of about $0.050536\%$. The theorem is asymptotic; numerical values of $K$ and $n_0$ remain to be evaluated. The exact finite maximum and a sharp common leading constant remain open in this work.

### Guide for reviewers

Start with the main theorem in Section 1. Sections 3 and 4 establish the uniform permanent approximation and the scaling and deletion estimates. Section 5 assembles the upper bound for all tournaments; Section 6 gives the lower bound using carousel tournaments of both parities.

For the formal proof, read the [finite definitions](formalization/TournamentHamiltonian/Definitions.lean) and [final theorem](formalization/TournamentHamiltonian/MainBound.lean), then consult the [verification guide](formalization/VERIFICATION.md) and [proof ledger](formalization/proof-status.json) for the intermediate connections. The declaration is `TournamentHamiltonian.mainBound : TournamentHamiltonian.MainBound`. The ledger explains where Lean uses different intermediate constants to obtain the same final bound.

The manuscript is a preprint awaiting external expert review. AI assistance was used for proof reconstruction, internal cross-checks, translation, typesetting and computational diagnostics; the Lean formalization was contributed by Xiangyu Ye in [PR #1](https://github.com/LStar404/tournament-hamiltonian-paths/pull/1).

### Reproduce the checks

Install [Lean through elan](https://leanprover-community.github.io/get_started.html) and Python 3.11 or newer. The project pins Lean 4.34.1 and the Mathlib revision in `formalization/lake-manifest.json`. From the repository root:

```sh
python -m pip install -r requirements.txt
cd formalization
lake exe cache get
python verify_lean.py --require-main
python run_diagnostics.py
```

The Lean verifier builds the project, checks the main theorem's type, audits transitive axiom dependencies, and checks that all project Lean sources are imported. The allowed axioms are `propext`, `Classical.choice` and `Quot.sound`. The diagnostic runner executes four finite checks and saves their output in `formalization/audit/`.

The [9 October repository review](materials/repository_review_zh.md) includes a fresh complete Lean build, an independent main-theorem type check, an axiom audit of 3,674 project theorems, and all four diagnostics. All checks passed. The [Lean verification record](formalization/audit/lean-verification.json) contains the output and current source hashes. The [CI workflow](.github/workflows/verify.yml) runs the same verification commands on pushes and pull requests and can be started manually in GitHub Actions.

### Repository contents

| Location | Contents |
| --- | --- |
| [`papers/`](papers/) | English and Chinese PDF manuscripts |
| [`materials/`](materials/README.md) | Markdown and LaTeX manuscripts, synchronized sections, and internal audit reports |
| [`formalization/`](formalization/VERIFICATION.md) | Lean proof, verification scripts, proof ledger, and build records |
| [`materials/verification/`](materials/verification/) | Finite diagnostic programs and their supporting modules |

The PDFs are the archived reading copies. Markdown is the editable master; the accompanying XeLaTeX files provide mathematical source. PDF equations are rendered images. See the [source and typesetting notes](materials/README.md) for editing and compilation details.

### Citation and license

For the archived manuscript, cite:

> Liu, Xingchen, and Ye, Xiangyu. *Constant-factor bounds for Hamiltonian paths in tournaments*. Version 1.1, Zenodo, 2026. https://doi.org/10.5281/zenodo.23249802.

Machine-readable citation metadata is in [`CITATION.cff`](CITATION.cff). The version DOI identifies the archived manuscript; subsequent repository edits are recorded in Git history. The work is licensed under [CC BY 4.0](LICENSE).

## 中文

**竞赛图中 Hamilton 路径数的常数因子界**
刘星辰、叶祥宇 · 个人研究者
联系邮箱：[lxc-em5158@outlook.com](mailto:lxc-em5158@outlook.com)

本仓库收录关于竞赛图中有向 Hamilton 路径最大数量的中英文论文、Lean 形式化证明和计算核验程序。

**阅读论文：**[中文 PDF](papers/tournament_hamilton_paths_zh.pdf)（23 页）· [英文 PDF](papers/tournament_hamilton_paths_en.pdf)（25 页）
**论文归档：**[Zenodo v1.1，2026 年 10 月 9 日](https://zenodo.org/records/23249802) · DOI：[10.5281/zenodo.23249802](https://doi.org/10.5281/zenodo.23249802)

仓库版本：**1.1.1** · [GitHub Releases](https://github.com/LStar404/tournament-hamiltonian-paths/releases)

### 主要结果

记 $H(T)$ 为竞赛图 $T$ 中构成有向 Hamilton 路径的顶点排列数，$P(n)$ 为所有 $n$ 阶竞赛图中这一数量的最大值。令

$$
\mu_n=\frac{n!}{2^{n-1}},\qquad
L=\frac{\cosh 1}{\cos 1},\qquad
C_* = \frac{3\pi^4+4\pi^2-32}{\pi^4+4\pi^2-32}.
$$

存在绝对常数 $K\ge0$ 和 $n_0\ge2$，使得对所有 $n\ge n_0$，都有

$$
(L-K/n)\mu_n\le P(n)\le(C_*+K/n)\mu_n.
$$

首项常数分别为 $L\approx2.855957892565114$ 和 $C_*\approx2.857401177672317$，相对间隙约为 $0.050536\%$。这是渐近定理，$K$ 与 $n_0$ 的数值尚待计算。有限阶精确最大值及上下界共同的最优首项常数，仍是本工作的未解问题。

### 专家阅读入口

建议从第 1 节的主定理开始。第 3、4 节建立统一永久式近似以及缩放、删除估计；第 5 节将这些结果组合为所有竞赛图的上界；第 6 节用奇、偶两种轮转竞赛图给出下界。

形式化证明可从[有限对象的定义](formalization/TournamentHamiltonian/Definitions.lean)和[最终定理](formalization/TournamentHamiltonian/MainBound.lean)读起，再通过[核验指南](formalization/VERIFICATION.md)与[证明台账](formalization/proof-status.json)查找中间连接。最终声明为 `TournamentHamiltonian.mainBound : TournamentHamiltonian.MainBound`。台账说明了 Lean 在部分中间估计中采用不同常数、最终得到同一结论的处理方式。

论文目前为预印本，等待外部专家审阅。证明重建、内部交叉检查、翻译、排版和计算诊断使用了 AI 辅助；Lean 形式化证明由叶祥宇通过 [PR #1](https://github.com/LStar404/tournament-hamiltonian-paths/pull/1) 提交。

### 复现核验

安装[由 elan 管理的 Lean](https://leanprover-community.github.io/get_started.html)及 Python 3.11 或更新版本。工程固定 Lean 4.34.1，Mathlib 的具体提交记录在 `formalization/lake-manifest.json` 中。从仓库根目录运行：

```sh
python -m pip install -r requirements.txt
cd formalization
lake exe cache get
python verify_lean.py --require-main
python run_diagnostics.py
```

Lean 核验程序构建工程、检查主定理类型、审查传递公理依赖，并核对所有项目 Lean 源码是否已导入。允许使用的公理为 `propext`、`Classical.choice` 和 `Quot.sound`。计算核验程序运行四项有限检查，将输出保存在 `formalization/audit/` 中。

[10 月 9 日仓库审阅](materials/repository_review_zh.md)已重跑完整 Lean 构建、独立主定理类型检查、3,674 个项目定理的公理审查及四项计算核验，全部通过。[Lean 核验记录](formalization/audit/lean-verification.json)保存运行输出与当前源码哈希。[CI 工作流](.github/workflows/verify.yml)在推送和拉取请求时执行上述核验，也可从 GitHub Actions 手动启动。

### 仓库结构

| 位置 | 内容 |
| --- | --- |
| [`papers/`](papers/) | 中英文 PDF 论文 |
| [`materials/`](materials/README.md) | Markdown、LaTeX 主稿，同步分节稿及内部审查记录 |
| [`formalization/`](formalization/VERIFICATION.md) | Lean 证明、核验脚本、证明台账及构建记录 |
| [`materials/verification/`](materials/verification/) | 有限计算核验程序及其辅助模块 |

PDF 是已归档的阅读版本。Markdown 是可编辑主稿，附带的 XeLaTeX 文件提供数学源代码；PDF 中的公式以图像呈现。编辑与编译方法见[稿件与排版说明](materials/README.md)。

### 引用与许可

引用已归档论文时，请使用：

> Liu, Xingchen, and Ye, Xiangyu. *Constant-factor bounds for Hamiltonian paths in tournaments*. Version 1.1, Zenodo, 2026. https://doi.org/10.5281/zenodo.23249802.

机器可读引用信息见 [`CITATION.cff`](CITATION.cff)。版本 DOI 对应已归档论文，后续仓库修改可在 Git 历史中查询。本成果采用 [CC BY 4.0](LICENSE) 许可。
