# 仓库审阅与复现记录

审阅日期：2026 年 10 月 9 日。工作区起点：`4ab08a95a0e9bfa6419ea0d73af29865714129a0`。

本轮审阅涵盖论文主稿、分节稿、LaTeX 源文件、阅读版 PDF、Lean 工程、计算核验程序、引用信息和复现说明。以下记录区分已归档论文与本轮工作区修订；逐项运行结果和文件哈希见 [`repository-review.json`](repository-review.json)。

## 数学结论与形式化接口

英文主稿的论证链与中文对应正文已经核对。形式化核对从有限对象定义、路径卷积和最终定理出发，检查了永久式近似、核心编码、阶乘恢复、同一缩放见证下的删除估计、全图归约和轮转下界的连接。

| 检查对象 | 核对结果 |
| --- | --- |
| 有限对象与计数 | `IsTournament` 给出无自环的有限定向；Hamilton 路径由顶点排列的相邻有向边定义，不按反转合并。`maxPaths` 是有限集合上的实际最大值。 |
| 主定理量词 | 存在绝对常数和阈值，再对所有足够大的阶数成立；上下界组合为同一 `K` 和 `n₀`。最终 `mainBound` 不带未解除的分析假设。 |
| 一般永久式近似 | 针对有界、双中心化、具有固定奇异值间隙的一般核；没有把对称核的结论直接用于非对称核。 |
| 缩放与非主子删除 | 删除行集和列集可以不同；容量与 Gaussian 比较沿用同一缩放见证。 |
| 全图上界 | 高比分方差、异常集非空与稠密核心三类均进入最终上界；原始异常集与比分惩罚在后续求和中保留。 |
| 下界 | 最终连接覆盖奇数阶与偶数阶的实际轮转竞赛图。 |
| 附属小比分结论 | 对 `d(n)=o(√n)`，误差常数不依赖函数 `d`；起始阈值可以依赖 `d`。该结论不作为主定理的前提。 |

在上述定义、量词和论证连接中，未发现与主结论相冲突的问题。形式化并不逐项证明论文中所有显示的中间常数：例如 Gaussian 阶乘恢复采用双半径几何二阶矩估计，得到同一统一 `O(1/n)` 结论。对应差异已在 [`proof-status.json`](../formalization/proof-status.json) 和 [`VERIFICATION.md`](../formalization/VERIFICATION.md) 中说明。

这次检查没有给出有限阶精确最大值、最优共同首项常数或可直接使用的数值阈值。README 现已用一句对应说明交代这些问题，避免反复插入否定性声明。

## Lean 复现

工程固定 Lean 4.34.1；Mathlib 和其余依赖固定在 [`lake-manifest.json`](../formalization/lake-manifest.json)。本轮使用官方 Windows 工具链，在取得依赖缓存后运行：

```sh
cd formalization
python verify_lean.py --require-main
```

本轮完整构建、3,674 个项目定理的传递公理审查、独立 `MainBound` 类型检查及全部项目源码覆盖检查均通过，核验入口退出码为 0。允许的传递公理只有 `propext`、`Classical.choice` 和 `Quot.sound`；新运行输出已写入 [`lean-verification.json`](../formalization/audit/lean-verification.json)。

首次默认并发构建在读取 Mathlib 缓存文件时失败；同一模块单独运行通过，将 `LEAN_NUM_THREADS` 设为 `2` 后，全量核验成功。本轮没有修改 Lean 证明源码。

源码核对已确认：242 个项目 Lean 文件全部位于导入闭包中；核验记录的 246 项源码及配置哈希与当前文件相符；证明台账列出的 799 项声明均能在源码中定位。项目源码未发现 `sorry`、`admit`、`native_decide`、自定义 `axiom` 或 `unsafe`。

## 有限计算核验

四个正式入口在本轮均实际运行并以退出码 0 结束。28 个项目 Python 文件通过语法检查。

| 入口 | 本轮覆盖摘要 |
| --- | --- |
| `verify_operator_packing_path_constant.py` | 23,630 项有理数谱装填检查，276 项相位次序检查，1–6 阶共 33,867 项竞赛图谱检查，以及至 5 阶的 1,099 项算子界检查。 |
| `verify_uniform_permanent_zeroth_audit.py` | 96 项活动度检查、8,381 项阶乘权检查及 16 项非正规秩二样例。 |
| `verify_nonprincipal_gaussian_deletion.py` | 267 项一般删除检查、267 项中心化检查、693 项竞赛图比较、635 项标量界、56 项永久式检查和 14 项路径检查。 |
| `verify_standalone_linear_energy_reduction.py` | 1,111 个图、36,746 项比分删除与秩容量检查、579 项加权恒等式、24 项四块检查及 112 项乘积检查。 |

原程序的 `RECORD.date` 是固定的 `2026-10-08` 标签；本轮实际运行日期由新审阅记录的时间字段给出。旧计算记录保留其原始内容。

辅助程序中，`check_higher_coefficient_envelope.py` 需要外部 `rt11.txt`，`verify_regular_catalogue_results.py` 需要 `rt13.txt` 和 `regular13_scan_certificate.json`。这些文件不在仓库内；它们不是上述四个正式入口的依赖。材料说明已区分统一复现入口与需要外部目录数据的独立例程。

## 稿件一致性与排版

- 双语主稿各有 190 个显示公式。逐项比对后，差异仅为公式末尾标点及单字符分子括号写法，未发现数学内容差异。
- 原分节稿仍保留单作者署名，并缺少主稿新增的第 7.4 节。开篇与结尾已同步；两种语言的五份分节稿拼接后均与各自主稿一致。
- 已归档英文 PDF 为 25 页，中文 PDF 为 23 页。全页缩略图及阅读抽查未发现明显裁切、遮挡或缺页；归档 PDF 的哈希保持相同。
- 两份 LaTeX 源稿使用 Tectonic 0.17.0 的 XeTeX 引擎成功编译，同样生成英文 25 页、中文 23 页。原源码中长 URL 和 Lean 声明造成文本越界，现已改用有标签的链接和独立代码排版；最终日志没有 `Overfull \hbox` 或缺字告警。编译稿的全部页面已检查。
- 参考文献 [2] 原来只列出 Alon 的作者手稿链接，现按[普林斯顿大学的出版记录](https://collaborate.princeton.edu/en/publications/the-maximum-number-of-hamiltonian-paths-in-tournaments/)补齐 Combinatorica 10(4) (1990), 319–324 与 DOI `10.1007/BF02128667`，同步更新双语 Markdown、分节稿及 LaTeX。
- 编译稿与归档 PDF 使用不同排版流程，分页不完全一致。本轮源码修改涉及文字排版、分节同步和书目信息，数学正文保持相同；归档 PDF 保持原版本。

[`delivery_qa.json`](delivery_qa.json) 和 [`typesetting_record.json`](typesetting_record.json) 保存归档时的历史记录。本轮 Markdown 和 LaTeX 主稿的新哈希、临时编译文件哈希与排版检查另记于 [`repository-review.json`](repository-review.json)。

## 阅读入口、引用与自动核验

README 已改为先英文、后中文的对应结构，依次介绍结果、专家阅读入口、复现命令、仓库结构和引用许可。主定理、Lean 声明与归档版本直接可见；AI 辅助说明集中保留在作者与审阅状态说明中。

已补齐版本 DOI `10.5281/zenodo.23249802`。[`CITATION.cff`](../CITATION.cff) 的首选论文引用包括两位作者、版本、日期、DOI 和归档地址，并通过 CFF 1.2.0 官方 schema 检查。

新增 [GitHub Actions 工作流](../.github/workflows/verify.yml)，执行完整 Lean 核验及四项计算入口，并保存运行记录。工作流 YAML 和所用 Lean action 的参数已经核对；远端运行结果需在推送后由 GitHub Actions 生成。

审阅开始时，仓库没有 Git 标签或 GitHub Release。本轮仓库修订的版本号为 **1.1.1**，论文归档版本仍为 **Zenodo v1.1**。专家引用论文时可使用上述版本 DOI；仓库快照及发布状态见 [GitHub Releases](https://github.com/LStar404/tournament-hamiltonian-paths/releases)。Release 说明区分仓库修订与既有论文归档，并列出对应提交的核验结果。

## 需要归档维护者处理的一项信息

[Zenodo v1.1](https://zenodo.org/records/23249802) 的结构化作者字段目前写作 **`Liu, Xingxhen`**，而论文、描述及仓库署名均为 **`Xingchen Liu`**。建议将该字段改为 **`Liu, Xingchen`**，以免自动生成的引用沿用拼写错误。仓库中的引用信息已使用正确拼写；外部记录未在本轮修改。
