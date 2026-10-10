import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from types import SimpleNamespace
from unittest.mock import patch

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

DISPLAY='$$\nx^2=1.\n$$'
EQUATION='<a id="eq-test"></a>\n\n$$\nx^2=1.\n\\tag{2.1}\n$$'

def equation_source(equation=EQUATION, reference='[Equation (2.1)](#eq-test)'):
    return SOURCE.replace(DISPLAY,equation).replace('See Theorem 1.1','See '+reference+' and Theorem 1.1')

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
    def test_commit_hash_can_wrap(self):
        value='e07175db8b9b1df17a2434355953d3a05fbc625b'
        tex,index=b.prepare('en',SOURCE.replace('An appendix.','Commit `'+value+'`.'))
        self.assertIn(r'\texttt{e07175db\allowbreak{}8b9b1df1',tex)

    def test_qed_binds_to_previous_word(self):
        tex,index=b.prepare('en',SOURCE.replace('An appendix.',r'This proves the claim. $\square$'))
        self.assertIn(r'claim.\nobreak\hspace{.5em}\mbox{$\square$}',tex)
        self.assertNotIn(r'claim. \(\square\)',tex)

    def test_chinese_template(self):
        tex,index=b.prepare('zh',SOURCE.replace('Theorem 1.1','定理 1.1').replace('Appendix A.','附录 A.'))
        self.assertIn('Noto Serif CJK SC',tex)
        self.assertIn('thm-1.1',tex)

class EquationTests(unittest.TestCase):
    def test_native_numbered_equation_and_real_label_link(self):
        tex,index=b.prepare('en',equation_source())
        self.assertIn('\\begin{equation}\nx^2=1.\n\\tag{2.1}\\label{eq-test}\n\\end{equation}',tex)
        self.assertIn(r'\paperref{eq-test}{Equation (2.1)}',tex)
        self.assertEqual(tex.count(r'\tag{2.1}'),1)
        self.assertNotIn(r'\hyperlink{eq-test}',tex)
        self.assertNotIn('<a id=',tex)
        self.assertEqual(index['equations'],{'eq-test':'2.1'})

    def test_anchor_need_not_have_a_blank_line_before_display(self):
        tex,_=b.prepare('en',equation_source(EQUATION.replace('</a>\n\n','</a>\n')))
        self.assertIn(r'\label{eq-test}',tex)

    def test_single_quoted_anchor_and_compact_appendix_display(self):
        equation="<a id='eq-appendix'></a>\n\n$$x=1\\tag{A.7}$$"
        tex,index=b.prepare('en',equation_source(equation,'[Equation (A.7)](#eq-appendix)'))
        self.assertIn(r'\tag{A.7}\label{eq-appendix}',tex)
        self.assertEqual(index['equations'],{'eq-appendix':'A.7'})

    def test_chinese_numbered_equation_reference(self):
        tex,_=b.prepare('zh',equation_source(reference='[式 (2.1)](#eq-test)'))
        self.assertIn(r'\paperref{eq-test}{式 (2.1)}',tex)

    def test_reference_inside_emphasis_and_footnote(self):
        reference='*[Equation (2.1)](#eq-test)* and note^[See [Equation (2.1)](#eq-test).]'
        tex,_=b.prepare('en',equation_source(reference=reference))
        self.assertEqual(tex.count(r'\paperref{eq-test}{Equation (2.1)}'),2)

    def test_equation_inside_block_quote(self):
        equation='\n'.join('> '+line for line in EQUATION.splitlines())
        tex,index=b.prepare('en',equation_source(equation))
        self.assertIn(r'\begin{equation}',tex)
        self.assertEqual(index['equations'],{'eq-test':'2.1'})

    def test_equation_inside_list(self):
        equation='- '+EQUATION.replace('\n','\n  ')
        tex,index=b.prepare('en',equation_source(equation))
        self.assertIn(r'\begin{equation}',tex)
        self.assertEqual(index['equations'],{'eq-test':'2.1'})

    def test_formula_tokens_preserved(self):
        formula=r'\sum_{j=0}^{m}\binom{m}{j}a_jb_{m-j}=\frac{R}{R-1}\,C.'
        tex,_=b.prepare('en',equation_source(EQUATION.replace('x^2=1.',formula)))
        self.assertIn(formula,tex)

    def test_display_count_uses_ast_for_mixed_and_compact_math(self):
        src=equation_source().replace('An appendix.','$$y=2$$\n\n```latex\n$$\nz=3\n$$\n```')
        tex,_=b.prepare('en',src)
        self.assertEqual(b.count_display_math(src),2)
        self.assertEqual(tex.count(r'\[')+tex.count(r'\begin{equation}'),2)

    def test_tag_without_anchor_rejected(self):
        with self.assertRaisesRegex(ValueError,'Missing equation anchor'):
            b.prepare('en',equation_source(EQUATION.replace('<a id="eq-test"></a>\n\n','')))

    def test_anchor_without_tag_rejected(self):
        with self.assertRaisesRegex(ValueError,'Missing equation tag'):
            b.prepare('en',equation_source(EQUATION.replace('\\tag{2.1}\n','')))

    def test_orphan_or_nonstandalone_anchor_rejected(self):
        for equation in ('<a id="eq-test"></a>',EQUATION.replace('</a>','</a> prose'),
                         EQUATION.replace('\n\n$$','\n\nIntervening prose.\n\n$$'),
                         '$$x=1\\tag{2.1}$$\n<a id="eq-test"></a>'):
            with self.subTest(equation=equation), self.assertRaisesRegex(ValueError,'Equation anchor'):
                b.prepare('en',equation_source(equation))

    def test_duplicate_anchor_rejected(self):
        with self.assertRaisesRegex(ValueError,'Duplicate equation anchor'):
            b.prepare('en',equation_source(EQUATION+'\n\n'+EQUATION.replace('2.1','2.2')))

    def test_duplicate_tag_rejected(self):
        with self.assertRaisesRegex(ValueError,'Duplicate equation tag'):
            b.prepare('en',equation_source(EQUATION+'\n\n'+EQUATION.replace('eq-test','eq-other')))

    def test_multiple_tags_in_one_display_rejected(self):
        with self.assertRaisesRegex(ValueError,'Multiple equation tags'):
            b.prepare('en',equation_source(EQUATION.replace(r'\tag{2.1}',r'\tag{2.1}\tag{2.2}')))

    def test_malformed_tags_rejected(self):
        for tag in (r'\tag*{2.1}',r'\tag{two}',r'\tag{2.1.1}',r'\tag{2.1',r'\tag{}'):
            with self.subTest(tag=tag), self.assertRaisesRegex(ValueError,'Malformed equation tag'):
                b.prepare('en',equation_source(EQUATION.replace(r'\tag{2.1}',tag)))

    def test_inline_tag_rejected(self):
        with self.assertRaisesRegex(ValueError,'Missing equation anchor'):
            b.prepare('en',SOURCE.replace('An appendix.',r'$x=1\tag{2.1}$'))

    def test_commented_and_escaped_tags_are_not_equation_metadata(self):
        tag,formula=b.equation_tag('x=1 % \\tag{9.9}\n\\tag{2.1}')
        self.assertEqual(tag,'2.1')
        self.assertEqual(formula,'x=1 % \\tag{9.9}\n')
        self.assertEqual(b.equation_tag(r'x=1\\tag{2.1}'),(None,r'x=1\\tag{2.1}'))
        self.assertEqual(b.equation_tag(r'x=1\%\tag{2.1}'),('2.1',r'x=1\%'))

    def test_raw_label_rejected(self):
        for source in (SOURCE,equation_source()):
            with self.subTest(source=source), self.assertRaisesRegex(ValueError,'raw equation label'):
                b.prepare('en',source.replace('x^2=1.',r'x^2=1.\label{eq-other}'))

    def test_malformed_and_non_html_anchors_rejected(self):
        for anchor in ('<a id="eq-test bad"></a>','<a id=eq-test></a>',
                       '<a id="eq-test" class="equation"></a>','[]{#eq-test}'):
            with self.subTest(anchor=anchor), self.assertRaisesRegex(ValueError,'[Ee]quation anchor'):
                b.prepare('en',equation_source(EQUATION.replace('<a id="eq-test"></a>',anchor)))

    def test_missing_equation_link_destination_rejected(self):
        for reference in ('[Equation (2.1)](#eq-missing)','[Equation (2.1)](#missing)'):
            with self.subTest(reference=reference), self.assertRaisesRegex(ValueError,'Unresolved equation reference'):
                b.prepare('en',equation_source(reference=reference))

    def test_wrong_reference_number_or_caption_rejected(self):
        for reference in ('[Equation (9.9)](#eq-test)','[式 (9.9)](#eq-test)',
                          '[this formula](#eq-test)'):
            with self.subTest(reference=reference), self.assertRaisesRegex(ValueError,'Equation reference number mismatch'):
                b.prepare('en',equation_source(reference=reference))

    def test_compiled_label_values_must_match_source_tags(self):
        index={'sections':{'sec-1':'Introduction'},'statements':{},'equations':{'eq-test':'2.1'}}
        aux='\\newlabel{sec-1}{{1}{1}{}{section.1}{}}\n\\newlabel{eq-test}{{2.1}{1}{}{AMS.1}{}}'
        self.assertEqual(b.validate_label_values(index,aux),{'sec-1':'1','eq-test':'2.1'})
        self.assertEqual(b.validate_label_values(index,aux.replace('{{2.1}','{{{2.1}}'))['eq-test'],'2.1')
        for invalid in (aux.replace('{{2.1}','{{1}'),aux.splitlines()[0],aux+'\n'+aux.splitlines()[1]):
            with self.subTest(aux=invalid), self.assertRaisesRegex(ValueError,'Number mismatch for eq-test'):
                b.validate_label_values(index,invalid)

    def test_bilingual_equation_ids_and_numbers_must_both_match(self):
        base={'sections':{},'statements':{},'references':{},'equations':{'eq-test':'2.1'}}
        b.validate_bilingual_indices(base,dict(base))
        for equations in ({},{'eq-other':'2.1'},{'eq-test':'2.2'}):
            with self.subTest(equations=equations), self.assertRaisesRegex(ValueError,'Bilingual equation'):
                b.validate_bilingual_indices(base,{**base,'equations':equations})

    def test_tex_only_build_counts_numbered_and_unnumbered_displays(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); (root/'materials').mkdir()
            (root/'materials/manuscript_en.md').write_text(equation_source()+'\n\n$$y=2$$\n')
            with patch.object(b,'ROOT',root), patch.object(b,'BUILD',root/'build'):
                result=b.build('en',SimpleNamespace(tex_only=True))
            self.assertTrue((root/result['tex']).is_file())

    def test_tex_only_bilingual_build_still_checks_equation_maps(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            for lang,number in (('en','2.1'),('zh','2.2')):
                (root/lang).mkdir()
                (root/lang/'crossref-index.json').write_text(json.dumps({
                    'sections':{},'statements':{},'references':{},'equations':{'eq-test':number}}))
            with patch.object(b,'BUILD',root), patch.object(b,'build',return_value={}), \
                 patch.object(b.shutil,'which',return_value='/tool'), \
                 patch.object(b.sys,'argv',['build_papers.py','--tex-only']), \
                 self.assertRaisesRegex(ValueError,'Bilingual equation'):
                b.main()

    @unittest.skipUnless(shutil.which('xelatex') and shutil.which('kpsewhich'),'XeLaTeX is optional for converter tests')
    def test_equation_label_round_trips_through_three_latex_passes(self):
        with tempfile.TemporaryDirectory() as tmp:
            work=Path(tmp); tex,index=b.prepare('en',equation_source())
            path=work/'equation.tex'; path.write_text(tex)
            with patch.object(b,'BUILD',work):
                env=b.tex_env(work)
            for _ in range(3):
                b.run(['xelatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error',path.name],cwd=work,env=env)
            values=b.validate_label_values(index,path.with_suffix('.aux').read_text())
            self.assertEqual(values['eq-test'],'2.1')
            self.assertNotRegex(path.with_suffix('.log').read_text(),r'undefined|multiply defined')

if __name__=='__main__': unittest.main()
