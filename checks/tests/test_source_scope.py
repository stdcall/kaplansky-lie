"""An unrelated source cannot invalidate an export of the current entry."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2]/'scripts'))
from project import source_paths


class SourceScope(unittest.TestCase):
    def test_dependencies_in_draft_and_all_sources_in_final(self):
        with tempfile.TemporaryDirectory(dir='/tmp') as directory:
            root = Path(directory)
            (root/'content').mkdir()
            (root/'config').mkdir()
            config = {'entry': 'content/main.typ', 'stage': 'draft'}
            path = root/'config/project.json'
            path.write_text(json.dumps(config))
            (root/'content/main.typ').write_text('#include "chapter.typ"\n')
            (root/'content/chapter.typ').write_text('#import "style.typ": *\n')
            (root/'content/style.typ').write_text('#let identity(x) = x\n')
            (root/'content/unrelated.typ').write_text('Unrelated document.\n')
            self.assertEqual({p.name for p in source_paths(root)},
                             {'main.typ', 'chapter.typ', 'style.typ'})
            config['stage'] = 'final'
            path.write_text(json.dumps(config))
            self.assertEqual({p.name for p in source_paths(root)},
                             {'main.typ', 'chapter.typ', 'style.typ',
                              'unrelated.typ'})
