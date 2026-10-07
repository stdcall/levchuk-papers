"""A product of whole set factors fits the text area without losing factors."""
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

import pymupdf

ROOT = Path(__file__).resolve().parents[2]


class FormulaLayout(unittest.TestCase):
    def test_statement_intro_stays_with_its_first_display(self):
        with tempfile.TemporaryDirectory(dir='/tmp', prefix='levchuk-statement-') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            (root / 'references.bib').write_text('')
            (root / 'articles.json').write_text('[]')
            (root / 'publications.bib').write_text('')
            (root / 'sample.typ').write_text(
                '#import "content/book-style.typ": book-style\n'
                '#import "content/statements.typ": theorem\n'
                '#show: book-style\n'
                '#set page(width: 100mm, height: 100mm, margin: 10mm)\n'
                'Before the statement.\n'
                '#v(60mm)\n'
                '#theorem[The following polynomial is equal to\n'
                '$ f(x) = x^3 + 101. $ <eq:statement-first-display>\n'
                '] <th:statement-display>\n'
                'A following paragraph. See @th:statement-display.\n')
            result = subprocess.run([
                'typst', 'compile', '--root', str(root), '--ignore-system-fonts',
                '--font-path', str(root / 'assets/fonts'),
                str(root / 'sample.typ'), str(root / 'sample.pdf')
            ], capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stderr, '')
            with pymupdf.open(root / 'sample.pdf') as doc:
                pages = [page.get_text() for page in doc]
                intro = next(i for i, value in enumerate(pages)
                             if 'The following polynomial' in value)
                formula = next(i for i, value in enumerate(pages) if '101' in value)
                self.assertEqual(intro, formula, pages)
                self.assertEqual(intro, 1, pages)
                self.assertTrue(any(link.get('page') == intro
                                    for page in doc for link in page.get_links()
                                    if link.get('kind') == pymupdf.LINK_GOTO))

    def test_long_nested_sum_does_not_orphan_the_initial_constant(self):
        with tempfile.TemporaryDirectory(dir='/tmp', prefix='levchuk-sum-layout-') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            (root / 'references.bib').write_text('')
            (root / 'articles.json').write_text('[]')
            (root / 'publications.bib').write_text('')
            (root / 'sample.typ').write_text(
                '#import "content/book-style.typ": book-style\n'
                '#show: book-style\n'
                '$ 1 + 1/n sum_(m=1)^(n-1) binom(n,m) binom(n,m+1) '
                'sum_(t=1)^m sum_(j_1 < j_2 < dots < j_t <= m) '
                '(2^t-1)^(m-j_t) product_(k=2)^(t-1) '
                '(2^k-1)^(j_(k+1)-j_k-1). $\n')
            result = subprocess.run([
                'typst', 'compile', '--root', str(root), '--ignore-system-fonts',
                '--font-path', str(root / 'assets/fonts'),
                str(root / 'sample.typ'), str(root / 'sample.pdf')
            ], capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stderr, '')
            with pymupdf.open(root / 'sample.pdf') as doc:
                spans = [span for page in doc
                         for block in page.get_text('dict')['blocks']
                         for line in block.get('lines', [])
                         for span in line['spans']]
                first = next(span for span in spans if span['text'].startswith('1'))
                self.assertTrue(any('+' in span['text']
                                    and abs(span['origin'][1] - first['origin'][1]) < 2
                                    for span in spans),
                                [(span['text'], span['origin']) for span in spans])
                text = ''.join(page.get_text() for page in doc)
                self.assertEqual(text.count('∑'), 3)
                self.assertEqual(text.count('∏'), 1)
                for span in spans:
                    self.assertGreaterEqual(span['bbox'][0], 55)
                    self.assertLessEqual(span['bbox'][2], doc[0].rect.width - 55)

    def test_long_product_retains_all_factors_inside_the_margins(self):
        with tempfile.TemporaryDirectory(dir='/tmp', prefix='levchuk-math-layout-') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            (root / 'references.bib').write_text('')
            (root / 'articles.json').write_text('[]')
            (root / 'publications.bib').write_text('')
            (root / 'sample.typ').write_text(
                '#import "content/book-style.typ": book-style\n'
                '#show: book-style\n'
                '$ {x_0011 lr((t)) x_1221 lr((c_1 t)) | t in K} '
                '{x_0111 lr((t)) x_1121 lr((c_2 t)) | t in K} '
                '{x_1111 lr((t)) x_0121 lr((c_3 t)) | t in K} '
                'X_1231 T(0122) quad (c_1, c_2, c_3 in K). $\n')
            result = subprocess.run([
                'typst', 'compile', '--root', str(root), '--ignore-system-fonts',
                '--font-path', str(root / 'assets/fonts'),
                str(root / 'sample.typ'), str(root / 'sample.pdf')
            ], capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stderr, '')
            with pymupdf.open(root / 'sample.pdf') as doc:
                text = ''.join(page.get_text() for page in doc)
                for factor in ('0011', '1221', '0111', '1121', '1111', '0121',
                               '1231', '0122'):
                    self.assertIn(factor, text)
                for page in doc:
                    for block in page.get_text('dict')['blocks']:
                        for line in block.get('lines', []):
                            self.assertGreaterEqual(line['bbox'][0], 55)
                            self.assertLessEqual(line['bbox'][2], page.rect.width - 55)


    def test_equation_body_leaves_room_for_its_actual_number(self):
        with tempfile.TemporaryDirectory(dir='/tmp', prefix='levchuk-number-gap-') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            (root / 'references.bib').write_text('')
            (root / 'articles.json').write_text('[]')
            (root / 'publications.bib').write_text('')
            (root / 'sample.typ').write_text(
                '#import "content/book-style.typ": book-style\n'
                '#show: book-style\n'
                '#counter("numbered:eq").update(18)\n'
                '$ A = 〈 x_a lr((t)) x_(2a+b) lr((s t)), '
                'x_(a+b) lr((s)) x_(2a+b) lr((s t)) 〉 U_4 '
                'quad (s,t in K^*), quad |A| = 4 dot |K|^2. $ '
                '<eq:probe-number-gap>\n')
            result = subprocess.run([
                'typst', 'compile', '--root', str(root), '--ignore-system-fonts',
                '--font-path', str(root / 'assets/fonts'),
                str(root / 'sample.typ'), str(root / 'sample.pdf')
            ], capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stderr, '')
            with pymupdf.open(root / 'sample.pdf') as doc:
                spans = [span for page in doc
                         for block in page.get_text('dict')['blocks']
                         for line in block.get('lines', [])
                         for span in line['spans']]
                number = [span for span in spans if span['text'] == '(19)']
                self.assertEqual(len(number), 1)
                x0, y0, _, y1 = number[0]['bbox']
                math = [span for span in spans if 'STIX' in span['font']
                        and span['bbox'][1] < y1 and span['bbox'][3] > y0]
                self.assertTrue(math)
                self.assertTrue(all(span['bbox'][2] + 4 <= x0 for span in math))


if __name__ == '__main__':
    unittest.main()
