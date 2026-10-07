"""Validate correction fields and the correspondence of Lean passages."""
from pathlib import Path
import json
import re
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]


class Edition(unittest.TestCase):
    def test_correction_fields_compile_individually(self):
        entries = json.loads((ROOT / 'corrections.json').read_text())['entries']
        ids = [entry['id'] for entry in entries]
        self.assertEqual(len(ids), len(set(ids)))
        required = {'id', 'printed_page', 'section', 'place', 'original',
                    'corrected', 'reason', 'verified_by'}
        with tempfile.TemporaryDirectory(dir='/tmp', prefix='levchuk-fields-') as tmp:
            for entry in entries:
                self.assertEqual(set(entry), required)
                for field in ('place', 'original', 'corrected', 'reason'):
                    self.assertNotIn('@', entry[field])
                    markup = json.dumps(entry[field], ensure_ascii=False)
                    driver = (
                        '#import "/content/corrections-defs.typ": correction-markup\n'
                        '#import "/content/book-style.typ": formula-rules\n'
                        '#set text(font: "Libertinus Serif", lang: "ru")\n'
                        '#show: formula-rules\n'
                        f'#correction-markup("{entry["id"]}", {markup})\n')
                    result = subprocess.run([
                        'typst', 'compile', '--root', str(ROOT),
                        '--ignore-system-fonts', '--font-path',
                        str(ROOT / 'assets/fonts'), '-', str(Path(tmp) / 'field.pdf'),
                    ], input=driver, capture_output=True, text=True)
                    self.assertEqual(result.returncode, 0,
                                     f'{entry["id"]}/{field}: {result.stderr}')
                    self.assertEqual(result.stderr, '')

    def test_lean_passages_are_present(self):
        records = json.loads((ROOT / 'checks/lean-proofs.json').read_text())
        text = '\n'.join(path.read_text()
                         for path in (ROOT / 'content').rglob('*.typ'))
        labels = set(re.findall(r'<([\w:-]+)>', text))
        for record in records:
            self.assertTrue(record['passages'])
            self.assertTrue(set(record['passages']) <= labels)
            self.assertTrue((ROOT / record['file']).is_file())


if __name__ == '__main__':
    unittest.main()
