"""Fail closed on invalid axiom audits and on proofs unbound to the text."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'lean'))
from check_axioms import audit, load_records, passage_problems  # noqa: E402


class CheckerTests(unittest.TestCase):
    def test_axiom_audit(self):
        record = {'declarations': ['Book.lemma']}
        good = "'Book.lemma' depends on axioms: [propext, Classical.choice]"
        self.assertEqual(audit(record, good, 0), [])
        for log, code in [(good, 1), (good + '\nProof.lean:1:1: warning: x', 0),
                          (good.replace('propext', 'sorryAx'), 0),
                          (good.replace('propext', 'Unproved.claim'), 0),
                          (good + '\n' + good, 0), ('', 0)]:
            with self.subTest(log=log, code=code):
                self.assertTrue(audit(record, log, code))

    def test_passages(self):
        record = {'file': 'checks/lean/Proof.lean', 'passages': ['eq:claim']}
        self.assertEqual(passage_problems(record, {'eq:claim'}), [])
        self.assertTrue(passage_problems(record, {'eq:other'}))
        record['passages'] *= 2
        self.assertTrue(passage_problems(record, {'eq:claim'}))

    def test_manifest_matches_sources(self):
        records, problems = load_records()
        self.assertEqual(problems, [])
        self.assertIsInstance(records, list)


if __name__ == '__main__':
    unittest.main()
