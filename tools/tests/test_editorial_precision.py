"""Guard the scope of the third-round exceptional-bound clarification.

These are editorial and exact-arithmetic regressions, not proofs of the
asymptotic statements. Historical receipts intentionally remain untouched.
"""
from fractions import Fraction
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[2]


class EditorialPrecisionTests(unittest.TestCase):
    def test_exact_three_part_budget(self):
        budget = Fraction(10, 3) * Fraction(1, 4) * Fraction(21, 20)
        budget += Fraction(1, 25) + Fraction(1, 25)
        self.assertEqual(budget, Fraction(191, 200))
        self.assertLess(budget, 1)

    def test_exceptional_bound_retains_additive_error_in_both_masters(self):
        for lang in ('en', 'zh'):
            with self.subTest(language=lang):
                text = (ROOT / f'materials/manuscript_{lang}.md').read_text()
                self.assertIn(r'4^{-f}(1+\varepsilon_n)+\delta_n', text)
                self.assertIn(r'\frac{191}{200}<1', text)
                self.assertNotIn(r'4^{-f}(1+o(1))<1', text)
                self.assertEqual(text.count('](#eq-exceptional-bound)'), 2)
                self.assertIn('additive' if lang == 'en' else '加性', text)

    def test_correspondence_distinguishes_all_three_terms(self):
        text = (ROOT / 'materials/verification/manuscript_alignment_20261011.md').read_text()
        item = next(line for line in text.splitlines() if line.startswith('3. Exceptional exclusion'))
        for value in ('disjointShortConvolution / meanPaths', 'short terms meeting F',
                      'long terms', '+δ_n', '191/200<1'):
            self.assertIn(value, item)
        self.assertTrue((ROOT / 'formalization/TournamentHamiltonian/CrudeExceptionalExclusion.lean').is_file())
        self.assertTrue((ROOT / 'formalization/TournamentHamiltonian/UniformSmallScoreMinor.lean').is_file())

    def test_key_equation_source_maps_agree(self):
        expected = {'eq-path-convolution': '2.1', 'eq-exceptional-bound': '3.1',
                    'eq-score-penalty': '3.2', 'eq-uniform-permanent': '5.1',
                    'eq-core-activity': '5.2', 'eq-deletion-mass': '6.1',
                    'eq-exact-restoration': '6.2', 'eq-small-score-permanent': '6.3'}
        for lang in ('en', 'zh'):
            with self.subTest(language=lang):
                text = (ROOT / f'materials/manuscript_{lang}.md').read_text()
                matches = re.findall(r'<a id="(eq-[a-z-]+)"></a>\s*\$\$(.*?)\$\$', text, re.S)
                found = {key: re.search(r'\\tag\{([^}]+)\}', formula).group(1)
                         for key, formula in matches}
                self.assertEqual(found, expected)
                self.assertEqual(len(matches), len(expected))


if __name__ == '__main__':
    unittest.main()
