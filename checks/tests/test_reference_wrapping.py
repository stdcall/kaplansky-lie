"""A wrapped descriptive reference must keep its anchor inside the PDF link."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

import pymupdf

ROOT = Path(__file__).resolve().parents[2]


class ReferenceWrapping(unittest.TestCase):
    def test_caption_starts_at_the_next_line(self):
        source = '''#import "/content/book-style.typ": book-style
#import "/content/statements.typ": bib-entry
#show: book-style
#h(274pt) @bib:Example2026[First words of a descriptive citation that
continues on the following line and retains its clickable destination.]
#pagebreak()
#bib-entry[Source.] <bib:Example2026>
'''
        common = ['--root', str(ROOT), '--ignore-system-fonts',
                  '--font-path', str(ROOT / 'assets/fonts')]
        with tempfile.TemporaryDirectory(prefix='kaplansky-ref-', dir='/tmp') as d:
            path = Path(d) / 'sample.pdf'
            compiled = subprocess.run(
                ['typst', 'compile', *common, '-', str(path)], input=source,
                text=True, capture_output=True)
            self.assertEqual(compiled.returncode, 0, compiled.stderr)
            self.assertEqual(compiled.stderr, '')
            queried = subprocess.run([
                'typst', 'eval', *common,
                'query(metadata).map(it => if type(it.value) == dictionary '
                '{ (..it.value, position: it.location().position()) } '
                'else { it.value })', '--in', '-',
                '--format', 'json'], input=source, text=True,
                capture_output=True)
            self.assertEqual(queried.returncode, 0, queried.stderr)
            refs = [r for r in json.loads(queried.stdout)
                    if r.get('kind') == 'cross-reference']
            self.assertEqual(len(refs), 1)
            ref = refs[0]
            self.assertTrue(ref['resolved'])
            pos = ref['position']
            point = pymupdf.Point(float(pos['x'].removesuffix('pt')),
                                  float(pos['y'].removesuffix('pt')))
            with pymupdf.open(path) as pdf:
                all_links = pdf[pos['page'] - 1].get_links()
                self.assertTrue(all(a['from'].width > 0 and a['from'].height > 0
                                    for a in all_links))
                links = [link for link in all_links if 'page' in link and
                         point in link['from'] + (-0.02, -0.02, 0.02, 0.02)]
                self.assertEqual(len(links), 1,
                                 (point, pdf[pos['page'] - 1].get_links()))
                self.assertEqual(links[0]['page'], 1)


if __name__ == '__main__':
    unittest.main()
