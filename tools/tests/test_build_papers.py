import importlib.util
from pathlib import Path
import unittest

spec=importlib.util.spec_from_file_location('build_papers',Path(__file__).resolve().parents[1]/'build_papers.py')
b=importlib.util.module_from_spec(spec); spec.loader.exec_module(b)

SOURCE='''# A mathematical test

Author

Affiliation

mail@example.org

10 October 2026

## Abstract

An abstract with $x^2$.

## 1. Introduction

**Theorem 1.1 (Main result).** For $x=1$, we have

$$
x^2=1.
$$

See Theorem 1.1 and Section 1, and [1].

### 1.1 A subsection

An external result [1, Lemma 4.3] is not a local reference.

## Appendix A. Verification

An appendix.

### A.1 Verification details

Details.

## References

[1] An Author. A reference. Lemma 4.3 is used.
'''

class ConverterTests(unittest.TestCase):
    def test_native_math_and_crossrefs(self):
        tex, index=b.prepare('en',SOURCE)
        self.assertIn(r'\[x^2=1.\]',tex)
        self.assertIn(r'\paperstatement{Theorem 1.1 (Main result).}{1.1}{thm-1.1}',tex)
        self.assertIn(r'\paperref{thm-1.1}{Theorem 1.1}',tex)
        self.assertIn(r'\paperref{bib-1}{[1, Lemma 4.3]}',tex)
        self.assertIn(r'\appendix',tex)
        self.assertEqual(list(index['sections']),['sec-1','sec-1.1','sec-A','sec-A.1'])
        self.assertNotIn('includegraphics',tex)
    def test_heading_math_preserved(self):
        tex,index=b.prepare('en',SOURCE.replace('### 1.1 A subsection','### 1.1 The factor $x^2$'))
        self.assertIn(r'\subsection{The factor \(x^2\)}',tex)
    def test_missing_theorem_rejected(self):
        with self.assertRaisesRegex(ValueError,'Unresolved cross-reference'):
            b.prepare('en',SOURCE.replace('See Theorem 1.1','See Theorem 1.2'))
    def test_duplicate_theorem_rejected(self):
        with self.assertRaisesRegex(ValueError,'Duplicate theorem'):
            b.prepare('en',SOURCE.replace('An appendix.','**Lemma 1.1.** Duplicate.'))
    def test_math_layout_preserves_terms(self):
        formula='|f(1)-G(1)|\\le A+\\frac{R}{R-1}B+C'
        result=b.math_layout(formula)
        self.assertIn(r'\\&\quad+\frac{R}',result)
        self.assertIn('B+C',result)
    def test_inline_code_spaces_preserved(self):
        tex,index=b.prepare('en',SOURCE.replace('An appendix.','Run `python verify_lean.py --require-main`.'))
        self.assertIn(r'\texttt{python verify\_\allowbreak{}lean.\allowbreak{}py {-}{-}require{-}main}',tex)
    def test_chinese_template(self):
        tex,index=b.prepare('zh',SOURCE.replace('Theorem 1.1','定理 1.1').replace('Appendix A.','附录 A.'))
        self.assertIn('Noto Serif CJK SC',tex)
        self.assertIn('thm-1.1',tex)

if __name__=='__main__': unittest.main()
