# Manuscripts and supporting materials

[English](#english) · [中文](#中文)

## English

The manuscript authors are Xingchen Liu and Xiangyu Ye, both independent researchers. Contact: [lxc-em5158@outlook.com](mailto:lxc-em5158@outlook.com). The current manuscript is the revision of 9 October 2026, archived as [version 1.1 on Zenodo](https://doi.org/10.5281/zenodo.23249802).

### Sources and editing

- [`manuscript_en.md`](manuscript_en.md) and [`manuscript_zh.md`](manuscript_zh.md) are the complete editable masters.
- [`sections/`](sections/) contains the same text divided into opening, permanent, scaling, global and closing sections. When editing a master, update the corresponding section as well.
- [`manuscript_en.tex`](manuscript_en.tex) and [`manuscript_zh.tex`](manuscript_zh.tex) are XeLaTeX exports.
- [`../papers/`](../papers/) contains the English and Chinese reading PDFs.

The LaTeX files use Times New Roman and, in Chinese, SimSun. With these fonts and XeLaTeX installed, run from this directory:

```sh
xelatex manuscript_en.tex
xelatex manuscript_en.tex
xelatex manuscript_zh.tex
xelatex manuscript_zh.tex
```

On other systems, replace the font settings with available fonts. The archived PDFs were typeset separately with ReportLab and rendered mathematical images, rather than compiled from these LaTeX files. The source files were successfully compiled with Tectonic 0.17.0, using its XeTeX engine, during the 9 October repository review. Long links and Lean identifiers were reformatted to remove text overflow; the mathematical content is unchanged. This build also produced 25 English and 23 Chinese pages, with different page breaks from the archived copies. Use the Markdown or LaTeX sources to copy or edit mathematical notation.

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

论文作者为刘星辰、叶祥宇，两位作者均为个人研究者。联系邮箱：[lxc-em5158@outlook.com](mailto:lxc-em5158@outlook.com)。当前论文为 2026 年 10 月 9 日修订稿，已在 [Zenodo 以 v1.1 归档](https://doi.org/10.5281/zenodo.23249802)。

### 源文件与编辑

- [`manuscript_en.md`](manuscript_en.md) 与 [`manuscript_zh.md`](manuscript_zh.md) 是完整的可编辑主稿。
- [`sections/`](sections/) 按开篇、永久式、缩放、全图归约和结尾拆分相同正文。修改主稿时，请同步相应分节文件。
- [`manuscript_en.tex`](manuscript_en.tex) 与 [`manuscript_zh.tex`](manuscript_zh.tex) 是 XeLaTeX 导出稿。
- [`../papers/`](../papers/) 收录中英文阅读版 PDF。

LaTeX 文件使用 Times New Roman，中文另用 SimSun。安装这些字体及 XeLaTeX 后，在本目录运行：

```sh
xelatex manuscript_en.tex
xelatex manuscript_en.tex
xelatex manuscript_zh.tex
xelatex manuscript_zh.tex
```

其他系统可将字体设置替换为已安装字体。已归档 PDF 使用 ReportLab 与数学公式图像单独排版，并非由这些 LaTeX 文件编译生成。10 月 9 日仓库审阅中，两份源文件已通过 Tectonic 0.17.0 的 XeTeX 引擎编译；长链接及 Lean 标识的排版已修正，消除了文本溢出，数学内容保持相同。此次编译同样生成英文 25 页、中文 23 页，但分页位置与归档稿不同。复制或编辑数学记号时，请使用 Markdown 或 LaTeX 源稿。

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
