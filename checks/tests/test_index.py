"""Abbreviating neighbouring index entries must preserve complete math."""
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]


class Index(unittest.TestCase):
    def test_math_words_with_a_common_initial(self):
        source = '''#import "/content/book-style.typ": book-style
#import "/content/main-defs.typ": idx
#show: book-style
Первая группа.#idx("$R N$-группа")
Вторая группа.#idx("$R N^ast$-группа")
Третья группа.#idx("Группа", "свободная $F$-группа")
Четвёртая группа.#idx("Группа", "свободная $G$-группа")
#include "/content/90-index.typ"
'''
        with tempfile.TemporaryDirectory(prefix='kaplansky-index-', dir='/tmp') as d:
            result = subprocess.run([
                'typst', 'compile', '--root', str(ROOT),
                '--font-path', str(ROOT / 'assets/fonts'),
                '--ignore-system-fonts', '-', str(Path(d) / 'index.pdf'),
            ], input=source, text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stderr, '')


if __name__ == '__main__':
    unittest.main()
