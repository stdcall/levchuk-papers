"""Article counters and native links remain correct after another article changes."""
from pathlib import Path
import json
import shutil
import subprocess
import tempfile
import unittest

import pymupdf

ROOT = Path(__file__).resolve().parents[2]


class Collection(unittest.TestCase):
    def build(self, root, extra=False, sectioned=False, grouped=False, conditions=False,
              prefixed=False, introduction=False):
        driver = (
            '#import "content/book-style.typ": book-style\n'
            '#import "content/collection.typ": article-begin\n'
            '#import "content/statements.typ": *\n'
            '#show: book-style\n'
            '#article-begin("probe-a")\n'
            '== Статья A <ch:probe-a>\n'
            + ('#theorem[Дополнительное утверждение.] <th:probe-extra>\n' if extra else '')
            + '#theorem[Первое утверждение.] <th:probe-a>\n'
            '#theorem-corollary[Первое следствие.] <cor:probe-a-first>\n'
            '#theorem(numbered: false, title: [Автор])[Без номера.]\n'
            '#theorem-corollary[Второе следствие.] <cor:probe-a-second>\n'
            '#bib-item[Запись A.] <bib:probe-a-Probe2000>\n'
            '#article-begin("probe-b")\n'
            '== Статья B <ch:probe-b>\n'
            '#theorem[Другое утверждение.] <th:probe-b>\n'
            '#bib-item[Запись B.] <bib:probe-b-Probe2000>\n'
            'Ссылка A: теорема @th:probe-a; '
            'следствие @cor:probe-a-second; [@bib:probe-a-Probe2000].\n'
            'Ссылка B: теорема @th:probe-b; [@bib:probe-b-Probe2000].\n')
        if sectioned:
            driver = (
                '#import "content/book-style.typ": book-style\n'
                '#import "content/collection.typ": article-begin\n'
                '#import "content/statements.typ": *\n'
                '#show: book-style\n'
                '#article-begin("probe-a", depths: (th: 1, lem: 1), '
                'groups: (th: ("th", "lem"), lem: ("th", "lem")))\n'
                '== Статья A <ch:probe-a>\n'
                '=== Первый раздел <sec:probe-first>\n'
                '#lemma[Первое утверждение.] <lem:probe-a>\n'
                '#theorem[Второе утверждение.] <th:probe-a>\n'
                '=== Второй раздел <sec:probe-second>\n'
                '#theorem[Третье утверждение.] <th:probe-a-last>\n'
                '#article-begin("probe-b")\n'
                '== Статья B <ch:probe-b>\n'
                '#theorem[Другое утверждение.] <th:probe-b>\n'
                'Номера: @lem:probe-a, @th:probe-a, @th:probe-a-last, @th:probe-b.\n')
        if grouped:
            driver = (
                '#import "content/book-style.typ": book-style\n'
                '#import "content/collection.typ": article-begin\n'
                '#import "content/statements.typ": *\n'
                '#show: book-style\n'
                '#article-begin("probe-a", groups: '
                '(th: ("th", "lem"), lem: ("th", "lem")))\n'
                '== Статья A <ch:probe-a>\n'
                '#lemma[Первое утверждение.] <lem:probe-a>\n'
                '#lemma[Второе утверждение.] <lem:probe-a-second>\n'
                '#theorem[Третье утверждение.] <th:probe-a>\n'
                '#theorem-corollary[Следствие.] <cor:probe-a>\n'
                '#theorem[Четвёртое утверждение.] <th:probe-a-last>\n'
                '#theorem-corollary[Следствие.] <cor:probe-a-last>\n'
                '#article-begin("probe-b")\n'
                '== Статья B <ch:probe-b>\n'
                '#theorem[Первое утверждение.] <th:probe-b>\n'
                'Номера: @th:probe-a, @cor:probe-a, '
                '@th:probe-a-last, @cor:probe-a-last, @th:probe-b.\n')
        if conditions:
            driver = (
                '#import "content/book-style.typ": book-style\n'
                '#import "content/collection.typ": article-begin\n'
                '#import "content/statements.typ": *\n'
                '#show: book-style\n'
                '#article-begin("probe-a")\n'
                '== Статья A <ch:probe-a>\n'
                '#condition[Начальное условие.] <cond:probe-zero>\n'
                + ('#condition[Вставленное условие.] <cond:probe-extra>\n' if extra else '')
                + '#condition[Базовое условие.] <cond:probe-base>\n'
                '#primed-condition([@cond:probe-base])[Замена условия.] '
                '<cond:probe-prime>\n'
                '#condition[Следующее условие.] <cond:probe-last>\n'
                '#article-begin("probe-b")\n'
                '== Статья B <ch:probe-b>\n'
                '#condition[Новая серия.] <cond:probe-b>\n'
                'Условия: @cond:probe-base, @cond:probe-prime, '
                '@cond:probe-last, @cond:probe-b.\n')
        if prefixed:
            driver = (
                '#import "content/book-style.typ": book-style\n'
                '#import "content/collection.typ": article-begin\n'
                '#show: book-style\n'
                '#article-begin("probe-a", prefixes: (eq: 1))\n'
                '== Статья A <ch:probe-a>\n'
                + ('$ u = v $ <eq:probe-extra>\n' if extra else '')
                + '$ a = b $ <eq:probe-intro>\n'
                '=== Первый раздел <sec:probe-first>\n'
                '$ c = d $ <eq:probe-first>\n'
                '=== Второй раздел <sec:probe-second>\n'
                '==== Первый подраздел <ss:probe-subsection>\n'
                '$ e = f $ <eq:probe-second>\n'
                '#article-begin("probe-b")\n'
                '== Статья B <ch:probe-b>\n'
                '$ g = h $ <eq:probe-b>\n'
                'Формулы: @eq:probe-intro, @eq:probe-first, '
                '@eq:probe-second, @eq:probe-b.\n'
                'Подраздел: @ss:probe-subsection.\n')
        if introduction:
            driver = (
                '#import "content/book-style.typ": book-style\n'
                '#import "content/collection.typ": article-begin, article-introduction\n'
                '#import "content/statements.typ": *\n'
                '#show: book-style\n'
                '#article-begin("probe-a", depths: (th: 1))\n'
                '== Статья A <ch:probe-a>\n'
                '#article-introduction[Introduction] <sec:probe-intro>\n'
                '#theorem(numbered: false)[Основное утверждение.]\n'
                '=== Первый раздел <sec:probe-first>\n'
                '#theorem[Первое утверждение.] <th:probe-first>\n'
                + ('#theorem[Вставленное утверждение.] <th:probe-extra>\n' if extra else '')
                + '=== Второй раздел <sec:probe-second>\n'
                '#theorem[Второе утверждение.] <th:probe-second>\n'
                '#article-begin("probe-b")\n'
                '== Статья B <ch:probe-b>\n'
                '#theorem[Третье утверждение.] <th:probe-b>\n'
                'Разделы: @sec:probe-intro, @sec:probe-first, @sec:probe-second.\n'
                'Теоремы: @th:probe-first, @th:probe-second, @th:probe-b.\n')
        (root / 'sample.typ').write_text(driver)
        command = ['typst', 'compile', '--root', str(root), '--ignore-system-fonts',
                   '--font-path', str(root / 'assets/fonts'),
                   str(root / 'sample.typ'), str(root / 'sample.pdf')]
        result = subprocess.run(command, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stderr, '')
        doc = pymupdf.open(root / 'sample.pdf')
        text = ' '.join(' '.join(page.get_text().split()) for page in doc)
        links = [link for page in doc for link in page.get_links()
                 if link.get('kind') == pymupdf.LINK_GOTO]
        doc.close()
        result = subprocess.run([
            'typst', 'query', '--root', str(root), '--ignore-system-fonts',
            '--font-path', str(root / 'assets/fonts'),
            str(root / 'sample.typ'), '<numbered>',
        ], text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        values = [item['value'] for item in json.loads(result.stdout)]
        return text, links, values

    def test_article_resets_and_cross_article_reference_mutation(self):
        with tempfile.TemporaryDirectory(dir='/tmp', prefix='levchuk-collection-') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            (root / 'references.bib').write_text('')
            (root / 'articles.json').write_text('[]')
            (root / 'publications.bib').write_text('')
            for extra, expected in ((False, 1), (True, 2)):
                text, links, values = self.build(root, extra)
                self.assertIn(f'Ссылка A: теорема {expected}; следствие {expected}.2; [1]', text)
                self.assertIn('Ссылка B: теорема 1; [1]', text)
                numbers = [it['number'] for it in values if it['family'] == 'cor']
                self.assertEqual(numbers, [[expected, 1], [expected, 2]])
                bibliography = [it['number'] for it in values if it['family'] == 'bib']
                self.assertEqual(bibliography, [[1], [1]])
                self.assertTrue(any(it['page'] == 0 for it in links))
                self.assertTrue(any(it['page'] == 1 for it in links))

    def test_shared_section_numbers_do_not_leak_to_next_article(self):
        with tempfile.TemporaryDirectory(dir='/tmp', prefix='levchuk-section-') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            (root / 'references.bib').write_text('')
            (root / 'articles.json').write_text('[]')
            (root / 'publications.bib').write_text('')
            text, links, values = self.build(root, sectioned=True)
            self.assertIn('Номера: 1.1, 1.2, 2.1, 1.', text)
            numbers = [it['number'] for it in values if it['family'] in ('th', 'lem')]
            self.assertEqual(numbers, [[1, 1], [1, 2], [2, 1], [1]])

    def test_corollary_uses_the_shared_number_of_its_theorem(self):
        with tempfile.TemporaryDirectory(dir='/tmp', prefix='levchuk-shared-') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            (root / 'references.bib').write_text('')
            (root / 'articles.json').write_text('[]')
            (root / 'publications.bib').write_text('')
            text, links, values = self.build(root, grouped=True)
            self.assertIn('Номера: 3, 3.1, 4, 4.1, 1.', text)
            numbers = [it['number'] for it in values if it['family'] == 'cor']
            self.assertEqual(numbers, [[3, 1], [4, 1]])

    def test_primed_condition_follows_its_target_after_insertion(self):
        with tempfile.TemporaryDirectory(dir='/tmp', prefix='levchuk-condition-') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            (root / 'references.bib').write_text('')
            (root / 'articles.json').write_text('[]')
            (root / 'publications.bib').write_text('')
            for extra in (False, True):
                text, links, values = self.build(root, extra=extra, conditions=True)
                expected = [[0], [1], ['1′'], [2], [0]]
                if extra:
                    expected = [[0], [1], [2], ['2′'], [3], [0]]
                self.assertEqual([it['number'] for it in values
                                  if it['family'] == 'cond'], expected)
                result = subprocess.run([
                    'typst', 'query', '--root', str(root), '--ignore-system-fonts',
                    '--font-path', str(root / 'assets/fonts'),
                    str(root / 'sample.typ'), '<cross-reference>',
                ], text=True, capture_output=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                printed = [it['value']['printed'] for it in json.loads(result.stdout)]
                self.assertEqual(printed, ['2', '2′', '3', '0'] if extra
                                 else ['1', '1′', '2', '0'])
                self.assertGreaterEqual(len(links), 4)

    def test_numbered_introduction_preserves_later_section_counters(self):
        with tempfile.TemporaryDirectory(dir='/tmp', prefix='levchuk-intro-') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            (root / 'references.bib').write_text('')
            (root / 'articles.json').write_text('[]')
            (root / 'publications.bib').write_text('')
            for extra in (False, True):
                text, links, values = self.build(root, extra=extra, introduction=True)
                self.assertIn('§ 0. Introduction', text)
                self.assertIn('§ 1. Первый раздел', text)
                self.assertIn('Разделы: 0, 1, 2.', text)
                self.assertIn('Теоремы: 1.1, 2.1, 1.', text)
                expected = [[1, 1], [2, 1], [1]]
                if extra:
                    expected.insert(1, [1, 2])
                self.assertEqual([it['number'] for it in values
                                  if it['family'] == 'th' and it['number'] is not None], expected)
                self.assertGreaterEqual(len(links), 6)

    def test_section_prefix_keeps_the_equation_counter_continuous(self):
        with tempfile.TemporaryDirectory(dir='/tmp', prefix='levchuk-prefix-') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            (root / 'references.bib').write_text('')
            (root / 'articles.json').write_text('[]')
            (root / 'publications.bib').write_text('')
            for extra in (False, True):
                text, links, values = self.build(root, extra=extra, prefixed=True)
                delta = int(extra)
                self.assertIn(
                    f'Формулы: (0.{1+delta}), (1.{2+delta}), '
                    f'(2.{3+delta}), (1).', text)
                self.assertIn('2.1. Первый подраздел', text)
                self.assertIn('Подраздел: 2.1.', text)
                for number in (f'(0.{1+delta})', f'(1.{2+delta})',
                               f'(2.{3+delta})'):
                    self.assertGreaterEqual(text.count(number), 2)
                numbers = [it['number'] for it in values if it['family'] == 'eq']
                expected = [[0, 1], [1, 2], [2, 3], [1]]
                if extra:
                    expected = [[0, 1], [0, 2], [1, 3], [2, 4], [1]]
                self.assertEqual(numbers, expected)
                self.assertGreaterEqual(len(links), 5)


if __name__ == '__main__':
    unittest.main()
