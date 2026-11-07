"""The list of literature: the printed order, and data changes in the .bib
files reach the PDF without editing any Typst descriptions."""
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

import pymupdf

ROOT = Path(__file__).resolve().parents[2]

# The printed list [1]–[29] in its order.
PRINTED = '''
Block1960 Block1962 Block1965 Block1964 Bourbaki1960 Winter1968
Gelfand1941 Gleason1952 Glushkov1957 Jacobson1962 Seligman1956
Seligman1957a Seligman1967 Seligman1957b Kaplansky1958 Kreknin1963
Loomis1953 Mills1957 Montgomery1952 Montgomery1955 Serre1966
Chevalley1951 Shoenfield1956 Schue1960 Zassenhaus1959 Jacoby1957
Yamabe1953a Yamabe1953b SeminaireLie1955
'''.split()


def records(text):
    """Key -> {field: value} of the braced one-line fields of a .bib file."""
    found = {}
    for key, body in re.findall(r'^@\w+\{(\w+),\n(.*?)^\}', text, re.M | re.S):
        found[key] = dict(re.findall(r'^  (\w+) = \{(.*)\},$', body, re.M))
    return found


class Bibliography(unittest.TestCase):
    def test_original_list_and_text_references(self):
        bib = ((ROOT / 'references.bib').read_text() +
               (ROOT / 'editorial.bib').read_text())
        keys = re.findall(r'^@\w+\{([^,]+),', bib, re.M)
        listed = re.findall(r'<bib:([^>]+)>',
                            (ROOT / 'content/80-bibliography.typ').read_text())
        self.assertEqual(len(PRINTED), 29)
        self.assertEqual(listed, PRINTED)
        self.assertEqual(len(keys), len(set(keys)))
        self.assertTrue(set(listed).issubset(keys))
        related = set()
        for key in re.findall(r'^  related = \{([^}]+)\}', bib, re.M):
            related.update(key.split(','))
        self.assertTrue(related.issubset(keys))
        self.assertEqual(set(keys), set(listed) | related)
        fields = records(bib)
        self.assertEqual(set(fields), set(keys))
        for key, record in fields.items():
            with self.subTest(key=key):
                self.assertIn(record.get('language'),
                              {'russian', 'english', 'french', 'german'})
                if key in listed:
                    self.assertIn('annotation', record)
                if 'doi' in record:
                    self.assertRegex(record['doi'], r'^10\.\d{4,5}/\S+$')

    def test_mutation_and_backlinks_ignore_the_bibliography_itself(self):
        with tempfile.TemporaryDirectory(prefix='kaplansky-bib-', dir='/tmp') as d:
            root = Path(d)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            original = (ROOT / 'references.bib').read_text()
            (root / 'references.bib').write_text(original)
            shutil.copy(ROOT / 'editorial.bib', root / 'editorial.bib')
            # Two mentions of Jacobson1962 on pages 1 and 2, a reference to it
            # inside the bibliography, and a record without mentions.
            (root / 'sample.typ').write_text('''
#import "content/book-style.typ": book-style
#import "content/main-defs.typ": *
#import "content/statements.typ": bib-entry
#import "content/bibliography-style.typ": bib-description
#show: book-style
Упоминание [@bib:Jacobson1962].
#pagebreak()
Ещё одно упоминание [@bib:Jacobson1962, с.~3].
#pagebreak()
#metadata(none) <bibliography-start>
#bib-entry[#bib-description("Jacobson1962")] <bib:Jacobson1962>
#bib-entry[#bib-description("Yamabe1953a")] <bib:Yamabe1953a>
Ссылка между записями: [@bib:Jacobson1962].
#metadata(none) <bibliography-end>
''')

            def compile(name):
                result = subprocess.run([
                    'typst', 'compile', '--ignore-system-fonts',
                    '--font-path', str(root / 'assets/fonts'),
                    '--root', str(root), str(root / 'sample.typ'),
                    str(root / name),
                ], capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stderr, '')
                with pymupdf.open(root / name) as pdf:
                    text = ' '.join(' '.join(p.get_text().split()) for p in pdf)
                    # The shared line-breaking rule keeps a text hyphen with
                    # its preceding inline formula; it adds no visible glyph.
                    text = text.replace('⁠', '')
                    text = text.replace('\xad ', '')
                    links = {a['uri'] for p in pdf for a in p.get_links()
                             if 'uri' in a}
                query = subprocess.run([
                    'typst', 'eval', '--root', str(root),
                    '--font-path', str(root / 'assets/fonts'),
                    '--ignore-system-fonts',
                    'query(metadata).map(it => it.value)',
                    '--in', str(root / 'sample.typ'), '--format', 'json',
                ], capture_output=True, text=True)
                self.assertEqual(query.returncode, 0, query.stderr)
                values = [x for x in json.loads(query.stdout)
                          if isinstance(x, dict)]
                mentions = [x for x in values
                            if x.get('target') == 'bib-mention:bib:Jacobson1962']
                self.assertEqual([m['description'] for m in mentions],
                                 ['1', '2'])
                self.assertFalse([x for x in values if x.get('target') ==
                                  'bib-mention:bib:Yamabe1953a'])
                return text, links

            before, links = compile('before.pdf')
            self.assertIn(
                '1. ДЖЕКОБСОН (JACOBSON N.), Lie Algebras, Interscience, 1962. '
                '[Русский перевод: Джекобсон Н., Алгебры Ли, «Мир», М., 1964.] '
                '[1, 2]', before)
            self.assertIn('2. ЯМАБЕ (YAMABE H.), On the conjecture', before)

            def mutate(text, key, old, new):
                head = text.index('{' + key + ',')
                end = text.index('\n}\n', head)
                record = text[head:end]
                self.assertIn(old, record)
                return text[:head] + record.replace(old, new, 1) + text[end:]

            changed = original
            for key, old, new in [
                ('Jacobson1962', 'title = {Lie Algebras}',
                 'title = {Bibliography mutation probe}'),
                ('Jacobson1962', 'author = {Jacobson, N.}',
                 'author = {Changedauthor, N.}'),
                ('Jacobson1962', 'nameaddon = {ДЖЕКОБСОН}',
                 'nameaddon = {МУТАЦИЯ}'),
                ('JacobsonRu1964', 'date = {1964}', 'date = {1999}'),
                ('Yamabe1953a', 'userb = {Ann. Math.}', 'userb = {Mutation J.}'),
            ]:
                changed = mutate(changed, key, old, new)
            changed = changed.replace('''  language = {english},
  related = {JacobsonRu1964},''', '''  language = {english},
  doi = {10.1234/mutation-probe},
  related = {JacobsonRu1964},''')
            (root / 'references.bib').write_text(changed)
            after, links = compile('after.pdf')
            self.assertIn(
                '1. МУТАЦИЯ (CHANGEDAUTHOR N.), Bibliography mutation probe, '
                'Interscience, 1962. [Русский перевод: Джекобсон Н., Алгебры '
                'Ли, «Мир», М., 1999.] DOI: 10.1234/mutation-probe [1, 2]',
                after)
            self.assertNotIn('Lie Algebras', after)
            self.assertIn('Mutation J.', after)
            self.assertIn('https://doi.org/10.1234/mutation-probe', links)


if __name__ == '__main__':
    unittest.main()
