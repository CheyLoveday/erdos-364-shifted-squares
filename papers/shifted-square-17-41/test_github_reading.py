"""Focused regression checks for the authorised reading projection boundary."""
import contextlib
import io
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import github_reading as reading


class ReadingTests(unittest.TestCase):
    def test_pandoc_boundaries_and_verifier_are_preserved(self):
        source = (
            '## Result {#result}\n\n::: {.theorem #theorem}\n'
            '**Theorem.** For $x$,\n\n$$\nx^2=1\n\\tag{1}\n$$\n\n:::\n\n'
            '```python\nprint("\\\\tag{literal}")\n  # exact indentation\n```\n'
        )
        view = reading.render('source.md', 'reading/copy.md', source)
        self.assertIn('<a id="theorem"></a>', view)
        self.assertIn('```math\nx^2=1\n\\qquad \\text{(1)}', view)
        self.assertIn('```python\nprint("\\\\tag{literal}")\n  # exact indentation\n```', view)
        self.assertFalse(reading.format_errors(view))
        self.assertEqual(reading.fidelity(source, view), (2, 1))
        with self.assertRaises(ValueError):
            reading.fidelity(source, view.replace(r'\text{(1)}', r'\text{(9)}'))
        with self.assertRaisesRegex(ValueError, 'explicit source anchor'):
            reading.fidelity(source, view.replace('<a id="theorem"></a>', ''))

    def test_backslash_maths_in_lists_and_tables(self):
        source = (
            '# Note\n\n- Let \\(a_b\\) be given.\n\n'
            '  \\[\n  \\begin{aligned}\n  a_b &= 1\\\\[0.4em]\n  c &= 2\n'
            '  \\end{aligned}\n  \\tag{2}\n  \\]\n\n'
            '| Quantity | Value |\n| --- | --- |\n| \\(q\\) | \\(a_b\\) |\n'
        )
        view = reading.render('source.md', 'reading/copy.md', source)
        self.assertIn('\\\\[0.4em]', view)
        self.assertIn('$`a_b`$', view)
        self.assertEqual(reading.fidelity(source, view), (4, 1))

    def test_inline_set_braces_use_github_protected_delimiters(self):
        source = '# Example\n\nLet \\(p\\in\\{17,41\\}\\), then \\(a_b=1\\).\n'
        view = reading.render('source.md', 'reading/copy.md', source)
        self.assertIn('$`p\\in\\{17,41\\}`$', view)
        self.assertEqual(reading.fidelity(source, view), (2, 1))
        with self.assertRaises(ValueError):
            reading.render('source.md', 'reading/copy.md', r'For \(x\tag{1}\).')

    def test_code_labelled_link_is_rebased_but_literal_code_is_not(self):
        source = '[`File.lean`](../Erdos364/File.lean#L2) and `\\(literal\\)`\n'
        view = reading.render('papers/source.md', 'papers/reading/copy.md', source)
        self.assertIn('[`File.lean`](../../Erdos364/File.lean#L2)', view)
        self.assertIn('`\\(literal\\)`', view)
        reading.fidelity(source, view)

    def test_future_unsupported_constructs_fail(self):
        for source in (
            '::: {.unknown}\ntext\n:::\n', '# Heading {.unknown}\n',
            '```{=latex}\nraw\n```\n', '```python\nunclosed\n',
            '\\[\nunclosed math\n', '::: {.theorem}\nunclosed\n',
            '\\begin{theorem}\nraw\n\\end{theorem}\n',
        ):
            with self.subTest(source=source), self.assertRaises(ValueError):
                reading.render('source.md', 'reading/copy.md', source)

    def test_source_to_reading_check_rejects_content_damage(self):
        source = '# Result\n\nStatement $x^2=1$.\n\n```python\nprint(1)\n```\n'
        view = reading.render('source.md', 'reading/copy.md', source)
        for damaged in (
            view.replace('$`x^2=1`$', '$`x^2=2`$'),
            view.replace('Statement', 'Different'),
            view.replace('print(1)', 'print(2)'),
            view.replace('# Result', '## Result'),
        ):
            with self.subTest(damaged=damaged), self.assertRaises(ValueError):
                reading.fidelity(source, damaged)

    def test_manual_drift_and_source_change_require_regeneration(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / 'source.md'
            output = root / 'reading/copy.md'
            source.write_text('# Result\n\nA statement.\n')
            with patch.object(reading, 'ROOT', root), \
                    patch.object(reading, 'PROJECTIONS', {'source.md': 'reading/copy.md'}), \
                    patch.object(reading, 'DIRECT_DOCS', ()), contextlib.redirect_stdout(io.StringIO()):
                with patch('sys.argv', ['github_reading.py', 'generate']):
                    reading.main()
                with patch('sys.argv', ['github_reading.py', 'check']):
                    reading.main()
                    original_bytes = output.read_bytes()
                    output.write_bytes(original_bytes.replace(b'\n', b'\r\n'))
                    with self.assertRaisesRegex(ValueError, 'fresh generation'):
                        reading.main()
                    output.write_bytes(original_bytes + b'Manual change.\n')
                    with self.assertRaisesRegex(ValueError, 'fresh generation'):
                        reading.main()
                with patch('sys.argv', ['github_reading.py', 'generate']):
                    reading.main()
                source.write_text('# Result\n\nChanged source.\n')
                with patch('sys.argv', ['github_reading.py', 'check']):
                    with self.assertRaisesRegex(ValueError, 'fresh generation'):
                        reading.main()
                with patch('sys.argv', ['github_reading.py', 'generate']):
                    reading.main()
                with patch('sys.argv', ['github_reading.py', 'check']):
                    reading.main()

    def test_historical_article_links_retain_their_version(self):
        _, target = reading.reader_link('[article]', 'manuscript/candidate/paper_1_release_candidate.md#thm-main',
                                        f'{reading.PAPER}/PROOF_RECORD.md', f'{reading.PAPER}/reading/PROOF_RECORD.md')
        self.assertEqual(target, '../manuscript/paper_1_final_frozen_portable.md#thm-main')


if __name__ == '__main__':
    unittest.main()
