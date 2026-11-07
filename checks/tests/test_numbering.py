"""Compile the shared styles and inspect the actual numbered records."""
import json
from pathlib import Path
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[2]


class Numbering(unittest.TestCase):
    def test_book_scheme(self):
        # Theorems and lemmas count separately through a chapter, formulas
        # through a chapter, exercises and examples restart in a section,
        # steps in a statement; chapters are cited in Roman numerals.
        source = '''#import "/content/book-style.typ": book-style
#import "/content/main-defs.typ": *
#import "/content/statements.typ": *
#show: book-style
#chapter[Первая] <ch:first>
#section[Первый] <sec:first>
$ a = a $ <eq:square-zero>
$ b = b $ <eq:anticommutative>
#example[Пример.] <exm:first>
#example[Пример.] <exm:second>
#exercises[
  #exercise[Задание.] <exc:first>
  #exercise[Задание.] <exc:second>
]
#section[Второй] <sec:second>
#theorem[Теорема.] <th:first>
#lemma[Лемма.] <lem:first>
#theorem[Теорема.] <th:second>
#proof[Доказательство.
  #step[Шаг.] <step:first>
  #step[Шаг.] <step:second>
]
$ c = c $ <eq:second>
#exercises[
  #exercise[Задание.] <exc:third>
]
Ссылки: @th:second, @lem:first, @eq:anticommutative, @exc:second, §~@sec:first,
@exm:second, @step:second.
#chapter[Вторая] <ch:second>
#section[Первый] <sec:third>
#theorem[Теорема.] <th:third>
$ d = d $ <eq:third>
#example(format: "1.")[Пример.] <exm:third>
Ссылки: @th:first гл.~@ch:first, @eq:third, §~@sec:second гл.~@ch:second,
@exm:third.
'''
        result = subprocess.run([
            'typst', 'eval', '--root', str(ROOT),
            '--font-path', str(ROOT / 'assets/fonts'),
            '--ignore-system-fonts',
            'query(metadata).map(it => it.value)',
            '--in', '-', '--format', 'json',
        ], input=source, capture_output=True, text=True, cwd=ROOT)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stderr, '')
        records = json.loads(result.stdout)
        numbered = [(r['family'], r['number']) for r in records
                    if isinstance(r, dict) and r.get('kind') == 'numbered']
        self.assertEqual([n for f, n in numbered if f == 'th'],
                         [[1, 1], [1, 2], [2, 1]])
        self.assertEqual([n for f, n in numbered if f == 'lem'], [[1, 1]])
        self.assertEqual([n for f, n in numbered if f == 'eq'],
                         [[1, 1], [1, '1′'], [1, 2], [2, 1]])
        self.assertEqual([n[-1] for f, n in numbered if f == 'exc'], [1, 2, 1])
        self.assertEqual([n[-1] for f, n in numbered if f == 'exm'],
                         ['(a)', '(b)', '1.'])
        self.assertEqual([n[-1] for f, n in numbered if f == 'step'],
                         ['(a)', '(b)'])
        refs = [r for r in records if isinstance(r, dict)
                and r.get('kind') == 'cross-reference']
        printed = [r['printed'] for r in refs]
        self.assertEqual(printed[:2], ['2', '1'])
        self.assertEqual(printed[3:7], ['2', '1', '(b)', '(b)'])
        self.assertEqual(printed[7:], ['1', 'I', '1', '2', 'II', '1'])
        self.assertTrue(all(r['resolved'] for r in refs))

    def test_primes(self):
        source = '''#import "/content/book-style.typ": book-style
#import "/content/main-defs.typ": *
#show: book-style
#chapter[Первая] <ch:first>
#section[Первый] <sec:first>
$ a = a $ <eq:square-zero>
$ b = b $ <eq:jacobi>
$ c = c $ <eq:anticommutative>
$ d = d $ <eq:commutator-square>
$ e = e $ <eq:commutator-jacobi>
$ f = f $ <eq:next>
Ссылки: @eq:anticommutative, @eq:commutator-jacobi, @eq:next.
'''
        result = subprocess.run([
            'typst', 'eval', '--root', str(ROOT),
            '--font-path', str(ROOT / 'assets/fonts'),
            '--ignore-system-fonts',
            'query(metadata).map(it => it.value)',
            '--in', '-', '--format', 'json',
        ], input=source, capture_output=True, text=True, cwd=ROOT)
        self.assertEqual(result.returncode, 0, result.stderr)
        records = json.loads(result.stdout)
        numbers = [r['number'][-1] for r in records if isinstance(r, dict)
                   and r.get('kind') == 'numbered' and r.get('family') == 'eq']
        self.assertEqual(numbers, [1, 2, '1′', '1″', '2″', 3])
        refs = [r['printed'] for r in records if isinstance(r, dict)
                and r.get('kind') == 'cross-reference']
        self.assertEqual(refs, ['1′', '2″', '3'])


if __name__ == '__main__':
    unittest.main()
