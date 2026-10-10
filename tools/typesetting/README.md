# Native-math typesetting

The complete Markdown manuscripts under `materials/` are authoritative. Run
`python tools/build_papers.py --render` from the repository root to generate
XeLaTeX source, compile both languages three times, validate cross-references,
and render every page under `build/papers/<language>/pages/`.

Requirements: Python 3.10+, Pandoc 3+, XeLaTeX (TeX Live with the standard
`fontspec`, AMS, `mathtools`, `geometry`, `microtype`, `needspace`, `xurl`,
`hyperref`, `bookmark`, `newunicodechar`, `enumitem`, `booktabs` and `longtable` packages),
Poppler's `pdfinfo` and `pdftoppm`, Latin Modern Roman/Sans/Mono, and Noto
Serif/Sans CJK SC. No separate Chinese TeX package is needed: the template
uses XeTeX's native Chinese line breaking and Unicode OpenType fonts.
The script never installs dependencies or accesses the network.

If a minimal TeX installation contains its distribution files but lacks the
system filename database or XeLaTeX format, the script searches the installed
files and builds a local format under `build/papers/tex-runtime/`. It does not
change the system installation. Otherwise the normal TeX installation is used.

## Source conventions

- The first level-one heading is the title, followed by four paragraphs:
  authors, affiliation, email, and revision date
- Numbered sections use `## 1. Title`, subsections `### 1.1 Title`, and an
  appendix uses `## Appendix A. Title` / `## 附录 A. 标题`
- Statement headings use `**Theorem 1.1 (Title).**` / `**定理 1.1（标题）。**`,
  with one number sequence per section across theorem, lemma, proposition,
  and corollary. They render as upright, bold, numbered heads with true labels
- Ordinary textual statement/section references and bracketed citations link
  to their local destinations. External citations such as `[3, Lemmas 4.3–4.4]`
  link to bibliography entry 3, not to a local statement
- Math remains in dollar delimiters. A small documented set of long displays
  receives layout-only line breaks. No equation is converted to an image
- Bibliography entries retain explicit `[1]` numbers, wording and external links
- Relative repository links become descriptive source-archive footnotes in the
  standalone PDF, while remaining normal links in Markdown
- Do not edit generated `.tex` exports or split sections by hand

### Numbered equations

Give each referenced equation a stable `eq-` ID and an explicit source number:

```markdown
<a id="eq-example"></a>

$$
x^2=1.
\tag{2.1}
$$

See [Equation (2.1)](#eq-example).
```

In the Chinese master use `[式 (2.1)](#eq-example)` with exactly the same equation ID and number.
The empty HTML anchor must stand alone immediately before a standalone display;
the blank line between the anchor and display is optional. The display may be
compact (`$$x=1\tag{2.1}$$`) or multiline. Avoid blank lines inside dollar
delimiters because Pandoc treats them as paragraph boundaries. IDs must match
`eq-[A-Za-z0-9][A-Za-z0-9_-]*`; numbers use a positive section number or one
uppercase appendix letter, a dot, and digits, such as `2.1` or `A.1`. Each ID
and each number must be unique within a master. Keep unreferenced displays
unnumbered unless a number is useful to the reader.

The exporter removes only the source `\tag` command before applying its existing
layout-only rules, then wraps the formula in an AMS `equation` environment with
that `\tag` and a true `\label`. References retain their readable Markdown
captions and become PDF `\hyperref` links to the equation's actual destination.
Do not add raw `\label`, `\tag*`, or a second tag. Tagged displays without
anchors, orphan/malformed/duplicate anchors, missing/duplicate tags, dangling
equation links, and reference captions with the wrong number fail the build.
Anchors and links also work inside lists, quotations and footnotes.

Display counts come from the Markdown AST, including both numbered and
unnumbered displays; fenced code examples are excluded. After three XeLaTeX
passes, every equation's `.aux` label value must equal its declared tag. A
two-language build, including `--tex-only`, requires identical equation
ID/number maps. Single-language builds check only the selected master.

## Checks and publication

`python -m unittest discover -s tools/tests -v` checks converter behavior.
`python tools/build_papers.py --lang en --tex-only` is a quick export check.
The normal build stops on overfull boxes, missing glyphs, unresolved labels,
duplicate statements/equations, and section/statement/equation numbering mismatches. For diagnosis
only, `--allow-layout-warnings` permits layout warnings; this is not a release
check. `build-report.json` captures source/output hashes, page counts, link
counts and compiler findings. A successful build does not assert visual review.

Inspect every rendered PNG, then run
`python tools/build_papers.py --render --publish --sync-sections` to refresh
`materials/manuscript_{en,zh}.tex`, `papers/tournament_hamilton_paths_{en,zh}.pdf`,
and exact split-section copies. Recheck the resulting PNGs if the source or
layout changed between runs. Record final visual review against the precise PDF
hashes in a new dated record; never reuse the historical audit certificates.

The `SOURCE_DATE_EPOCH` environment variable controls deterministic PDF creation
timestamps. By default the script uses 10 October 2026, 00:00 UTC. Reproduction
of byte-identical PDFs also requires the same TeX/Pandoc/font versions.

## Second-round safeguards

The exporter binds an inline proof-ending `\square` to its preceding word and inserts discretionary breaks every eight characters in 40–64-character hexadecimal code literals, so a full commit SHA remains readable without an overfull line. Both behaviors have regression tests. The separate `test_core_examples.py` uses exact rational arithmetic to verify the signed cubic and fourth-degree partition identities used to illustrate compressed cores; CI runs it without requiring the optional typesetting toolchain.
