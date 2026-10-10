# Second-round bilingual revision — 11 October 2026 (UTC+8)

This record describes a second editorial and proof-exposition revision. It does not claim an external mathematical peer review, a newly established priority result, or a usable numerical asymptotic threshold.

## Baseline and version scope

- The fork baseline is `18f6ecd70cdd1217d382e980168ae8ae055663f2` in `makerY666/tournament-hamiltonian-paths`
- The corresponding merged upstream baseline is `e07175db8b9b1df17a2434355953d3a05fbc625b` in `LStar404/tournament-hamiltonian-paths`
- Both have tree `d595883f17a550d82c66bad56ac52c55bb69d5fc`; these were checked before editing
- The prior revision, historical audit records, tagged release and Zenodo archive are preserved. No release or archive metadata is changed

## Changes applied in both languages

1. Introduction: restore the lower-bound progression from Szele to Adler–Alon–Ross and Wormald, alongside the Alon and Friedgut–Kahn upper-bound progression. Cite Adler–Alon–Ross's same-normalization lower bound and constant-factor question. State the contribution as the theorem's uniform upper bound, without an unsupported first-publication claim
2. Section 3.3: write the two independent weighted injection sums explicitly, show why no extra factorial occurs and why row/column images may overlap, and give a deletion-uniform error envelope. Explain the weaker sufficient formal bound nearby
3. Section 5.3: isolate the decorated-count identity, distinguish structural vertices from numerical labels, explain ordered degree sequences and chain orientation, and preserve bipartite parity. Give signed examples with two length-two loops and with three parallel edges. The loop examples have coefficient **negative** three quarters; the activity majorant uses their absolute weights
4. Proposition 5.5: state next to the displayed bound that Lean uses a sufficient alternative factorial-recovery budget, rather than claiming a verbatim formalization of the displayed derivative constant
5. Sections 6.1–6.3: collect the full/retained/generic matrix orders, masses and normalizations; specify the fixed local gap and its later sharpening; summarize all restoration errors and the dependence of constants
6. Appendix A.2: add exact-baseline remote verification evidence and distinguish it from a local rebuild and from CI on future editorial commits
7. Typesetting: bind each proof-ending square to the preceding word; allow a full commit hash to wrap at fixed groups without changing its text. Regenerate the two TeX exports, PDFs and exact section slices

## Reference checks and remaining limits

Adler–Alon–Ross's Theorem 1 and Remark 3 were checked in the [author-hosted published paper](https://adler.ieor.berkeley.edu/ilans_pubs/hamilt_2001.pdf) and [author-hosted preprint](https://web.math.princeton.edu/~nalon/PDFS/aar4.pdf). Szele's title, volume and year are corroborated by the [Hungarian Academy volume archive](https://real-j.mtak.hu/7300/); its page range is also present in Adler–Alon–Ross's bibliography. The original Szele proof was not independently reread.

For Han–Niles-Weed, the exact cited lemma numbering was checked against [arXiv:2408.09341v2](https://arxiv.org/html/2408.09341v2). The [author's publication list](https://yanjunhan2021.github.io/publication.html) lists The Annals of Statistics as forthcoming. The reported final journal volume, issue, pages and DOI were not independently confirmed through accessible primary publisher metadata, so no unverified final bibliographic details were inserted. The optional recent special-tournament enumeration work was not needed for the extremal bound or its proof and was not added from incomplete metadata.

## Verification

- Ten local unit/regression tests pass, including exact rational cubic and fourth-degree coefficient identities for centered matrices of orders 2, 3 and 4
- The signed-core regression test was added as a lightweight CI step; the proof build, theorem audit and four established diagnostic entry points are unchanged
- All four published finite diagnostic programs were rerun successfully; their fresh output is preserved in [the round-two diagnostic receipt](verification/diagnostics_round2_20261011.json)
- All 246 archived Lean-source/configuration SHA-256 values still match. No formal proof source was changed and no new local Lean kernel build is claimed
- [Upstream baseline run 38070905246](https://github.com/LStar404/tournament-hamiltonian-paths/actions/runs/38070905246) and [fork baseline run 38070678338](https://github.com/makerY666/tournament-hamiltonian-paths/actions/runs/38070678338) completed successfully. Exact SHA, event and timestamp metadata are in the machine-readable revision receipt
- The compiler and final visual checks, source/PDF hashes and generated-section checks are recorded in [the round-two typesetting receipt](typesetting_round2_20261011.json). Prior typesetting receipts describe prior versions only

The new commit's remote CI status is established in its pull request after publication, rather than being asserted by a self-referential source receipt. Expert mathematical review, journal-specific affiliations/classification fields, and any future release or archive publication remain separate steps.

## 中文摘要

本轮同步补齐前人下界工作，扩写异常顶点的独立匹配求和、压缩核心的精确增饰计数及矩阵缩放的维度/谱隙/误差依赖。新增自环例子的带符号系数为负的四分之三，活动量上界使用其绝对值，并以精确有理数测试核对三次和四次恒等式。正文明确显示误差常数与 Lean 替代估计的区别，附录补充精确基线提交的远端 CI 证据。两种语言的原生公式 PDF、TeX 与分节稿重新生成，历史记录保持不变。

十项本地测试及四项既有有限诊断通过；246 项形式化源码/配置哈希吻合。未声称本地重新构建 Lean，也未将自动核验视为外部数学同行评审。Han–Niles-Weed 正式期刊最终卷期页码未获可访问的一手来源确认，因此保留明确版本的 arXiv 引理引用与作者目录所列期刊状态。新提交的远端 CI 结果在 PR 中另行记录；本轮未发布新 Release 或修改 Zenodo。
