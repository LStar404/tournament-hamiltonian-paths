# 数学与形式化核验记录

本记录对应原始稿件提交 `04efafda8f4034a6b59e7def3f07c36151217201` 与最终形式化证明提交 `1b22101c3404aad3d749ad52ac5853b3ba4eb2d5`。形式化证明已在提交 `2983cd9` 合并。其后，2026 年 10 月 9 日的双语主稿与 PDF 增补了第 7.4 节及双作者署名，数学主结论保持相同。原始稿件哈希用于记录证明所依据的版本；归档修订稿哈希见 `../materials/delivery_qa.json`，本轮源码排版与书目修订另见 `../materials/repository-review.json`。

English reading guide: the [main definitions](TournamentHamiltonian/Definitions.lean) specify the finite objects and quantifiers; [MainBound.lean](TournamentHamiltonian/MainBound.lean) assembles the final theorem. The [proof ledger](proof-status.json) maps manuscript sections to declarations and records differences in intermediate constants. This document describes the verification of proof commit `1b22101`; the later manuscript revision adds the formalization account and both authors. The [repository review](../materials/repository_review_zh.md) records a fresh complete build, axiom audit, main-theorem check and diagnostic runs on 9 October, all passing with unchanged Lean sources.

## 已证明的主结论

`TournamentHamiltonian.mainBound : TournamentHamiltonian.MainBound` 是无条件 Lean 定理：

\[
\exists K\ge0,\ \exists n_0\ge2,\ \forall n\ge n_0,\quad
(L-K/n)\mu_n\le P(n)\le(C_*+K/n)\mu_n.
\]

这里 `P(n)` 为所有真实 `n` 阶锦标赛上 Hamilton 路径数的最大值，`mu_n=n!/2^(n-1)`，`L=cosh(1)/cos(1)`，`C_*=(3*pi^4+4*pi^2-32)/(pi^4+4*pi^2-32)`。路径按有向顶点排列计数，不除以反转。最大值在有限锦标赛集合中实际取到。

两侧共用 `K=Cl+Cu` 和 `n0=max Nl Nu`。阈值先于所有锦标赛和删除集合的量词确定。下界覆盖奇、偶两种实际轮转构造；上界覆盖高方差、异常集非空、稠密核心三个互补情形。

## 证明对应

| 稿件部分 | 实际 Lean 连接 |
| --- | --- |
| 计数与谱 | 有限路径计数、精确正权卷积、成对偏斜谱、完整 cotangent 特征向量基、谱松弛与 `C_*` |
| 一般永久量 | 实际分划系数、Gaussian/Wick 矩、真实核心编码单射和权重保持、完整有限计数、无条件活动度、解析尾项 |
| 缩放与删除 | 真实 Banach 缩放势、矩形不同删行删列、同一见证的容量与 Gaussian 比较、真实质量恢复 |
| 全局上界 | 原始异常集的保留和四块永久量、真实非主子永久量界、Hadamard 子集矩、完整比分质量误差及 Gamma 吸收 |
| 实际下界 | 真实短主子永久量双侧近似、生成行列式下界、实际路径卷积下界、两种轮转构造 |
| 最终定理 | `MainBound.lean` 从实际上下界构造同一常数和同一阈值 |

最终主定理没有活动度、编码计数、永久量近似、缩放见证、Gaussian 比较或路径数估计等未解除的前提。

## 独立审查与范围

两路只读审查分别核对了全部英文分节及主定理形式定义与连接，未发现阻断主结论的数学缺口。特别核对了补矩阵的对角线、空子集、不同删除集合、再删点后仍使用原始异常集、比分 cap 的统一阈值，以及最终量词次序。

形式化不逐字复制所有中间常数。稿件 Gaussian 阶乘恢复的显示导数常数 `K_G` 在独立数学复核中成立；Lean 使用较保守的双半径几何二阶矩常数，证明同一无条件统一 `O(C,q)/n` 结论。高方差惩罚、异常点排除和比分吸收也采用较弱但充分的界。稿件的主结论及实际对象没有因此改变。

`C_*` 的小数区间由 Lean 证明；`L` 和相对常数间隙的小数区间来自精确有理数 Python 证书。有限诊断的成功不承担全阶证明义务。一般 `d(n)=o(sqrt n)` 的附属整个路径数近似也已无条件证明：对任意非负函数 `d` 满足 `d(n)/sqrt(n)` 趋于零，存在统一阈值，使所有比分绝对值不超过 `d(n)` 的实际锦标赛都满足 `|H(T)/mu_n-rho_n(T)| <= C(d(n)+1)^2/n`。常数 `C` 不依赖 `d`、阶数或锦标赛；阈值可依赖函数 `d`。方差和原始短子集窗口条件在定理内部解除，不需要更强的 `d(n) log(n)=o(sqrt n)`。该附属定理不作为 `MainBound` 的假设。

## 可复现的检查

工程固定 Lean 与 Mathlib 4.34.1。进入 `formalization` 后运行：

```text
lake exe cache get
python verify_lean.py --require-main
python run_diagnostics.py
```

`Audit.lean` 对每个项目定理的所有传递依赖收集公理，只允许 `propext`、`Classical.choice`、`Quot.sound`。不允许占位证明、计算公理或项目自定义公理。`verify_lean.py` 另外让 Lean 检查实际 `MainBound` 定理类型，记录被导入源码的 SHA-256，并拒绝最终提交中存在未导入的项目源码。

`audit/lean-verification.json` 保存真实构建、公理审查与主定理检查输出；四个有限诊断记录保存在同一目录。`proof-status.json` 保存可在 Lean 中逐项查到的证明台账和准确的覆盖范围。最终提交需全部项目源码都在审查范围内，不能仅凭局部构建成功。

核验程序会更新 `audit/` 下的记录。仓库的 [GitHub Actions 工作流](../.github/workflows/verify.yml) 执行相同入口，并将运行记录作为附件保存。Mathlib 与依赖包的具体提交已固定在 `lake-manifest.json`，复现时使用该清单。

原形式化提交的最终 `--require-main` 检查退出码为零：完整构建、3674 个项目定理的传递公理审查、实际 `MainBound` 类型检查和全部项目源码覆盖均通过。原始英文稿件的 SHA-256 保存在 `audit/manuscript-source-hashes.json`；四项有限诊断均通过。

最终证明与审计对应提交 `1b22101c3404aad3d749ad52ac5853b3ba4eb2d5`，已提交至上游 [PR #1](https://github.com/LStar404/tournament-hamiltonian-paths/pull/1)。后续仅补记提交状态与链接，不改变已审计的 Lean 源码。

2026 年 10 月 9 日的仓库审阅使用官方 Windows Lean 4.34.1 工具链，以 `LEAN_NUM_THREADS=2` 重新运行完整 `--require-main` 入口。构建、3674 个定理的传递公理审查、主定理类型检查和源码覆盖均通过，退出码为零；四项计算入口也已重跑通过。`audit/lean-verification.json` 现保存本轮输出，Lean 源码及配置的 246 项哈希与原记录一致。本轮的稿件与复现检查见 [仓库审阅记录](../materials/repository_review_zh.md)。
