# 论文与核验资料 / Manuscripts and audit materials

作者 / Author: 刘星辰 / Xingchen Liu

单位 / Affiliation: 个人研究者 / Independent Researcher

Email: lxc-em5158@outlook.com

Date: 2026-10-08

## 交付内容

- manuscript_en.md：完整英文可编辑主稿。
- manuscript_zh.md：完整中文可编辑主稿；与英文使用同一组显示公式。
- manuscript_en.tex、manuscript_zh.tex：可编辑 LaTeX 源文件。
- 两份 PDF 单独交付；为避免重复体积，源文件包不再包含 PDF。
- audit_summary_zh.md：核验结论、补写细节与未证明事项。
- audit_permanent.md、audit_scaling.md、audit_global.md：组成部分的审查记录。
- audit_computations.json：四组既有检查的本轮重跑原始记录。
- delivery_qa.json：两版公式对照、PDF 页数、署名与范围检查、源文件哈希。
- verification/：源文件包中的检查程序及其本地 Python 依赖模块。

## 数学状态

正文支持当前常数因子界，而非一般精确通式或尖锐首项常数等式。
证明经过 AI 辅助内部重建和交叉复核，未发现致命缺口；不是外部同行评审或形式化证明认证。
未知误差常数和有效起始阶数不能用于直接推断小阶数值。
有限计算只作查错，不替代正文任意阶证明。

## 编辑与复现

Markdown 是排版输入和当前可编辑主稿，数学使用标准 LaTeX 记法。
两份 LaTeX 源文件由主稿作机械格式转换，建议使用 XeLaTeX 编译两遍。
默认使用 Times New Roman；中文另用 SimSun，可在其他系统替换为已安装的相应字体。
本环境没有 TeX 编译器，因此没有声称已本机编译验证 LaTeX 源文件。
所交付 PDF 使用本地数学字形和嵌入中文字体独立排版，并另作完整页面渲染检查。
PDF 中的公式以高分辨率字形图像呈现；需修改公式时请使用 Markdown 或 LaTeX 源稿。

检查程序建议 Python 3.11 或更新版本，部分模块需 NumPy。
在源文件包的 verification/ 目录分别运行四个入口：

~~~text
python verify_operator_packing_path_constant.py
python verify_uniform_permanent_zeroth_audit.py
python verify_nonprincipal_gaussian_deletion.py
python verify_standalone_linear_energy_reduction.py
~~~

程序输出包含 RECORD 的 JSON 行；结果范围在各记录中明确注明。
它们不执行一般极值搜索，不提供全阶误差常数证书。

## English note

The two manuscripts state and prove the current constant-factor result with identical mathematical content. They do not claim an exact finite formula, the sharp constant as a global upper bound, or an extremal classification. Proof checks were conducted within an AI-assisted workflow, not by external human referees.

Editable Markdown and XeLaTeX sources, component audit reports, exact diagnostic records and verification modules are included. The XeLaTeX files have not been compiled locally; the delivered PDFs were independently typeset and visually checked. Their formulas are high-resolution rendered glyphs, so formula edits should be made in the editable sources.
