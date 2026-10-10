# Manuscripts and supporting materials

[English](#english) · [中文](#中文)

## English

The manuscript authors are Xingchen Liu and Xiangyu Ye, both independent researchers. Contact: [lxc-em5158@outlook.com](mailto:lxc-em5158@outlook.com). The working manuscripts are a later editorial revision of the 9 October 2026 manuscript archived as [version 1.1 on Zenodo](https://doi.org/10.5281/zenodo.23249802). The archived DOI identifies that earlier version, not these revised files.

### Sources and editing

- [`manuscript_en.md`](manuscript_en.md) and [`manuscript_zh.md`](manuscript_zh.md) are the complete authoritative, editable masters
- [`sections/`](sections/) contains exact generated slices: numbered sections 1-7 and Appendix A, with front matter in section 1 and references in the appendix slice
- [`manuscript_en.tex`](manuscript_en.tex) and [`manuscript_zh.tex`](manuscript_zh.tex) are generated, self-contained XeLaTeX exports
- [`../papers/`](../papers/) contains the current English and Chinese reading PDFs, compiled from those exports with native mathematical text, linked statements/citations and PDF bookmarks

Do not edit the split sections or TeX exports separately. From the repository root:

```sh
python -m unittest discover -s tools/tests -v
python tools/build_papers.py --render
```

This generates both languages under `build/papers/`, compiles each three times, checks for missing/duplicate labels, numbering mismatches, missing glyphs and overfull boxes, and renders every page to PNG. Inspect all page images. After review, refresh the reading copies and split sections with:

```sh
python tools/build_papers.py --render --publish --sync-sections
```

The build requires Python 3.10+, Pandoc 3+, XeLaTeX with the standard packages listed in [`tools/typesetting/README.md`](../tools/typesetting/README.md), Poppler, Latin Modern fonts and Noto Serif/Sans CJK SC. It installs nothing and performs no network access. The build documentation describes local format initialization for minimal TeX installations, source conventions, deterministic timestamps, and the distinction between compiler checks and visual review. The generated exports can also be compiled directly with XeLaTeX three times on a system with the required fonts and packages.

The v1.1 archived PDFs were produced separately with ReportLab and mathematical images; the archived TeX was compiled during the 9 October review with Tectonic 0.17.0. That historical workflow and its 25 English / 23 Chinese page counts do not describe the current native-math revision. Historical audit receipts below are retained unchanged. The [11 October typesetting record](typesetting_revision_20261011.json) records the first-round source/PDF hashes, all-page visual review, native-formula counts, cross-reference checks and exact section synchronization.

The [second-round record](revision_round2_20261011.md) and [second-round typesetting receipt](typesetting_round2_20261011.json) identify the latest 31-page English and 27-page Chinese reading copies. The new proof examples have exact rational regression tests; all historical receipts continue to describe their original versions.

### Audits and diagnostics

The reports [`audit_summary_zh.md`](audit_summary_zh.md), [`audit_permanent.md`](audit_permanent.md), [`audit_scaling.md`](audit_scaling.md) and [`audit_global.md`](audit_global.md) record the internal mathematical review of 8 October, before the Lean formalization was merged. For the formal proof and its relationship to the manuscript, use [`../formalization/VERIFICATION.md`](../formalization/VERIFICATION.md). The [repository review](repository_review_zh.md) records the later consistency and reproduction checks.

[`audit_computations.json`](audit_computations.json) contains earlier diagnostic output. [`delivery_qa.json`](delivery_qa.json) and [`typesetting_record.json`](typesetting_record.json) record the archived manuscripts' source hashes, page counts and typesetting checks. The later source formatting, bibliographic corrections and compilation checks are recorded in [`repository-review.json`](repository-review.json); the archived PDF hashes remain unchanged.

The four supported diagnostic entry points are:

```sh
python verify_operator_packing_path_constant.py
python verify_uniform_permanent_zeroth_audit.py
python verify_nonprincipal_gaussian_deletion.py
python verify_standalone_linear_energy_reduction.py
```

Run them in `verification/` after installing the root `requirements.txt`, or run `python formalization/run_diagnostics.py` from the repository root to save all four results. Each entry point prints a `RECORD` JSON line. The remaining Python files supply supporting calculations; some standalone routines also expect external catalogue data, as described in their source. The finite checks cover the cases in their output records; the asymptotic proof is in the manuscript and Lean project.

## 中文

论文作者为刘星辰、叶祥宇，两位作者均为个人研究者。联系邮箱：[lxc-em5158@outlook.com](mailto:lxc-em5158@outlook.com)。当前工作稿是在 2026 年 10 月 9 日论文基础上的后续编辑修订；旧稿已在 [Zenodo 以 v1.1 归档](https://doi.org/10.5281/zenodo.23249802)。该 DOI 对应旧归档版本，不对应这里的新修订文件。

### 源文件与编辑

- [`manuscript_en.md`](manuscript_en.md) 与 [`manuscript_zh.md`](manuscript_zh.md) 是完整且唯一权威的可编辑主稿
- [`sections/`](sections/) 是按第 1-7 节与附录 A 生成的精确文本切片；开篇信息包含在第 1 节文件中，参考文献包含在附录文件中
- [`manuscript_en.tex`](manuscript_en.tex) 与 [`manuscript_zh.tex`](manuscript_zh.tex) 是自动生成、可独立编译的 XeLaTeX 导出稿
- [`../papers/`](../papers/) 收录由这些导出稿编译的当前中英文 PDF，公式为原生数学文本，含定理与引用链接及 PDF 书签

不要分别手工修改分节稿或 TeX 导出稿。从仓库根目录运行：

```sh
python -m unittest discover -s tools/tests -v
python tools/build_papers.py --render
```

脚本在 `build/papers/` 下生成两种语言的文件，分别编译三次，检查缺失或重复标签、编号不一致、缺字与行宽溢出，并将每一页渲染为 PNG。逐页检查图像后，运行以下命令更新阅读版与分节稿：

```sh
python tools/build_papers.py --render --publish --sync-sections
```

依赖为 Python 3.10+、Pandoc 3+、XeLaTeX、Poppler、Latin Modern 字体及 Noto Serif/Sans CJK SC 字体；所需常用 TeX 宏包详见[排版说明](../tools/typesetting/README.md)。脚本不安装任何依赖，也不访问网络。说明中同时记载精简 TeX 环境的本地格式初始化、主稿语法、确定性时间戳及编译检查与逐页视觉检查的区别。依赖齐全时，也可直接对导出稿运行三次 XeLaTeX。

v1.1 归档 PDF 使用 ReportLab 与公式图像单独排版；旧 TeX 曾在 10 月 9 日审阅中使用 Tectonic 0.17.0 编译。该历史流程及英文 25 页、中文 23 页的旧页数，不描述当前原生公式修订版。以下历史审查记录原样保留。[10 月 11 日排版核验记录](typesetting_revision_20261011.json)另行保存首轮源码与 PDF 哈希、逐页视觉检查、原生公式数量、交叉引用检查及分节稿精确同步结果。

[第二轮修订记录](revision_round2_20261011.md)及[第二轮排版记录](typesetting_round2_20261011.json)对应最新英文 31 页、中文 27 页阅读版。新增证明例子配有精确有理数回归测试；全部历史核验记录仍只描述各自的原始版本。

### 审查与计算核验

[`audit_summary_zh.md`](audit_summary_zh.md)、[`audit_permanent.md`](audit_permanent.md)、[`audit_scaling.md`](audit_scaling.md) 和 [`audit_global.md`](audit_global.md) 保存 10 月 8 日的内部数学审查，早于 Lean 形式化证明的合并。形式化证明及其与论文的对应关系见 [`../formalization/VERIFICATION.md`](../formalization/VERIFICATION.md)；后续版本一致性和复现检查见[仓库审阅记录](repository_review_zh.md)。

[`audit_computations.json`](audit_computations.json) 保存此前计算输出；[`delivery_qa.json`](delivery_qa.json) 与 [`typesetting_record.json`](typesetting_record.json) 记录归档论文的源码哈希、页数和排版检查。后续源码排版、书目信息修订与编译检查另记于 [`repository-review.json`](repository-review.json)，归档 PDF 的哈希保持相同。

本仓库支持的四个计算核验入口为：

```sh
python verify_operator_packing_path_constant.py
python verify_uniform_permanent_zeroth_audit.py
python verify_nonprincipal_gaussian_deletion.py
python verify_standalone_linear_energy_reduction.py
```

安装仓库根目录 `requirements.txt` 中的依赖后，在 `verification/` 中分别运行；也可在仓库根目录执行 `python formalization/run_diagnostics.py`，统一保存四项结果。每个入口输出一行 `RECORD` JSON。其余 Python 文件提供辅助计算，部分独立例程还需要源码中说明的外部图目录数据。有限检查覆盖输出记录中的案例，渐近证明见论文及 Lean 工程。
