"""Check printed data, DOI links and backlinks using the actual compiler."""
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

import pymupdf

ROOT = Path(__file__).resolve().parents[2]


class Bibliography(unittest.TestCase):
    def prepare(self, root):
        shutil.copytree(ROOT / 'content', root / 'content')
        shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
        (root / 'articles.json').write_text('[]')
        (root / 'publications.bib').write_text('')
        (root / 'references.bib').write_text(
            "@article{Dubisch1951,\n"
            "  author={Dubisch, Roy and Perlis, Sam},\n"
            "  title={On total nilpotent algebras},\n"
            "  doi={10.2307/2372186},\n"
            "  annotation={{title}.},\n}\n"
            "@article{Weir1955,\n"
            "  author={Weir, A. J.},\n"
            "  title={Probe B},\n"
            "  annotation={{title}.},\n}\n"
            "@article{Jennings1955,\n"
            "  author={Jennings, S. A.},\n"
            "  title={Probe C},\n"
            "  annotation={{title}.},\n}\n")

    def compile(self, root, stem):
        result = subprocess.run([
            'typst', 'compile', '--root', str(root), '--ignore-system-fonts',
            '--font-path', str(root / 'assets/fonts'), str(root / 'sample.typ'),
            str(root / (stem + '.pdf')),
        ], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stderr, '', result.stderr)
        doc = pymupdf.open(root / (stem + '.pdf'))
        text = ' '.join(' '.join(page.get_text().split()) for page in doc)
        links = [link for page in doc for link in page.get_links()]
        return doc, text, links

    def test_data_changes_reach_printed_text_and_doi(self):
        with tempfile.TemporaryDirectory(dir='/tmp', prefix='levchuk-bib-') as tmp:
            root = Path(tmp)
            self.prepare(root)
            (root / 'sample.typ').write_text(
                '#import "content/book-style.typ": book-style\n'
                '#import "content/statements.typ": bib-item\n'
                '#import "content/bibliography-style.typ": bib-description\n'
                '#show: book-style\n'
                '#bib-item[#bib-description("Dubisch1951")] <bib:Dubisch1951>\n')
            before, text, links = self.compile(root, 'before')
            self.assertIn('On total nilpotent algebras', text)
            self.assertIn('Roy Dubisch', text)
            self.assertIn('https://doi.org/10.2307/2372186',
                          [link.get('uri') for link in links])
            before.close()
            path = root / 'references.bib'
            value = path.read_text().replace(
                'title={On total nilpotent algebras}',
                'title={Bibliography mutation probe}').replace(
                'author={Dubisch, Roy and Perlis, Sam}',
                'author={Changedauthor, A. and Perlis, Sam}').replace(
                'doi={10.2307/2372186}', 'doi={10.1234/mutation-probe}')
            path.write_text(value)
            after, text, links = self.compile(root, 'after')
            self.assertIn('Bibliography mutation probe', text)
            self.assertIn('A. Changedauthor', text)
            self.assertNotIn('On total nilpotent algebras', text)
            self.assertIn('https://doi.org/10.1234/mutation-probe',
                          [link.get('uri') for link in links])
            after.close()

    def test_bibliography_links_do_not_create_mentions(self):
        with tempfile.TemporaryDirectory(dir='/tmp', prefix='levchuk-links-') as tmp:
            root = Path(tmp)
            self.prepare(root)
            (root / 'sample.typ').write_text(
                '#import "content/book-style.typ": book-style\n'
                '#import "content/statements.typ": bib-item\n'
                '#import "content/bibliography-style.typ": bib-description\n'
                '#show: book-style\n'
                'Первое упоминание [@bib:Dubisch1951].\n'
                '#pagebreak()\n'
                'Второе упоминание [@bib:Dubisch1951].\n'
                '#pagebreak()\n'
                '#bib-item[#bib-description("Dubisch1951")] <bib:Dubisch1951>\n'
                '#bib-item[#bib-description("Weir1955"); '
                '@bib:Dubisch1951 и @bib:Jennings1955.] <bib:Weir1955>\n'
                '#bib-item[#bib-description("Jennings1955")] <bib:Jennings1955>\n')
            doc, text, links = self.compile(root, 'links')
            self.assertIn('[1, 2]', text)
            self.assertNotIn('[1, 2, 3]', text)
            self.assertEqual(text.count('[1, 2]'), 1)
            back = [link['page'] for link in doc[2].get_links()
                    if link.get('kind') == pymupdf.LINK_GOTO]
            self.assertIn(0, back)
            self.assertIn(1, back)
            self.assertGreaterEqual(back.count(2), 2)
            doc.close()


if __name__ == '__main__':
    unittest.main()
