"""Focused failure controls for the portable Paper I replay coordinator."""

import os
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import run_core as core


class CoreChecks(unittest.TestCase):
    def test_axioms_allow_subsets(self):
        core.validate_axioms("'T' depends on axioms: [propext]\n", {"T"})
        core.validate_axioms("'T' does not depend on any axioms\n", {"T"})

    def test_extra_axiom_rejected(self):
        with self.assertRaisesRegex(ValueError, "unapproved axiom"):
            core.validate_axioms("'T' depends on axioms: [propext, sorryAx]\n", {"T"})

    def test_missing_or_duplicate_declaration_rejected(self):
        with self.assertRaisesRegex(ValueError, "inventory"):
            core.validate_axioms("'T' depends on axioms: [propext]\n", {"T", "U"})
        with self.assertRaisesRegex(ValueError, "duplicate"):
            core.validate_axioms("'T' depends on axioms: []\n" * 2, {"T"})

    def test_private_search_paths_removed(self):
        with patch.dict(
            os.environ,
            {
                "PYTHONPATH": "/private/input",
                "LEAN_PATH": "/private/input",
                "PYTHONHOME": "/private/input",
                "LAKE_HOME": "/private/input",
            },
        ):
            env = core.clean_environment()
        self.assertFalse(set(env) & {"PYTHONPATH", "LEAN_PATH", "PYTHONHOME", "LAKE_HOME"})

    def test_source_symlink_and_escape_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "file").write_text("source")
            (root / "link").symlink_to(root / "file")
            with self.assertRaisesRegex(ValueError, "symlink"):
                core.checked_bytes(root, "link")
            with self.assertRaisesRegex(ValueError, "unsafe"):
                core.checked_bytes(root, "../file")

    def test_imported_source_corruption_rejected(self):
        original = core.checked_bytes

        def altered(root, path):
            raw = original(root, path)
            return raw + b"\n-- corruption\n" if path == core.ENTRY else raw

        with (
            patch.object(core, "checked_bytes", side_effect=altered),
            self.assertRaisesRegex(ValueError, "hash mismatch"),
        ):
            core.source_inventory(core.ROOT)


if __name__ == "__main__":
    unittest.main()
