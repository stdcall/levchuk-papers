"""Running heads follow article moves and never leak into other sections."""
from pathlib import Path
import subprocess
import tempfile
import unittest

import pymupdf

ROOT = Path(__file__).resolve().parents[2]


class RunningHeaders(unittest.TestCase):
    def compile(self, first, second):
        driver = (
            '#import "/content/book-style.typ": book-style\n'
            '#show: book-style\n'
            '= Предисловие <pass:header-front>\n'
            '#pagebreak()\n'
            '= Первая часть\n'
            '#pagebreak()\n'
            f'== {first[1]} <ch:{first[0]}>\n'
            '#pagebreak()\n'
            'Продолжение первой статьи.\n'
            '#pagebreak()\n'
            '= Вторая часть\n'
            '#pagebreak()\n'
            f'== {second[1]} <ch:{second[0]}>\n'
            '#pagebreak()\n'
            'Продолжение второй статьи.\n'
            '#pagebreak()\n'
            '= Публикации <pass:publications>\n'
            '#pagebreak()\n'
            'Продолжение списка публикаций.\n')
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / 'headers.pdf'
            result = subprocess.run([
                'typst', 'compile', '--root', str(ROOT),
                '--ignore-system-fonts', '--font-path', str(ROOT / 'assets/fonts'),
                '-', str(output),
            ], input=driver, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stderr, '')
            document = pymupdf.open(output)
            self.assertEqual(len(document), 9)
            headers = [page.get_text(clip=pymupdf.Rect(0, 0, page.rect.width, 55))
                       .strip() for page in document]
        return headers

    def test_titles_and_numbers_follow_article_order(self):
        a = ('l1974', 'Название A')
        b = ('l1976', 'Название B')
        for first, second in ((a, b), (b, ('l1974', 'Новое название A'))):
            with self.subTest(first=first, second=second):
                headers = self.compile(first, second)
                self.assertEqual(headers[3], f'I.1 {first[1]}')
                self.assertEqual(headers[6], f'II.2 {second[1]}')
                for index in (0, 1, 2, 4, 5, 7, 8):
                    self.assertEqual(headers[index], '', index + 1)
