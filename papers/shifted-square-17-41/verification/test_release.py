"""Focused archive and arithmetic failure controls for the real release path."""

import io
import tempfile
import unittest
from pathlib import Path
from zipfile import ZipFile

import release


class ReleaseChecks(unittest.TestCase):
    def test_copied_dependency_links_stay_within_public_tree(self):
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            public = base / "packages"
            public.mkdir()
            (base / "private").write_text("private source")
            link = public / "link"
            link.symlink_to("../private")
            with self.assertRaisesRegex(ValueError, "escaping public dependency"):
                release.check_dependency_links(public)
            link.unlink()
            (public / "file").write_text("public source")
            link.symlink_to("file")
            release.check_dependency_links(public)

    def test_missing_export_document_link_rejected(self):
        with self.assertRaisesRegex(ValueError, "unexported document link"):
            release.check_document_links({"README.md": b"[proof](proof.md)"})
        release.check_document_links({"README.md": b"[proof](proof.md)", "proof.md": b"proof"})

    def test_archive_escape_and_private_build_rejected(self):
        for name in ("../x", "/x", "a/../../x", ".git/config", ".lake/build/x", "a\\x"):
            with self.subTest(name=name), self.assertRaises(ValueError):
                release.safe_name(name)

    def test_duplicate_zip_member_rejected(self):
        buffer = io.BytesIO()
        with ZipFile(buffer, "w") as archive:
            archive.writestr("x", b"a")
            archive.writestr("x", b"b")
        with self.assertRaisesRegex(ValueError, "duplicate"):
            release.zip_payload(buffer.getvalue())

    def test_checksum_corruption_and_omission_rejected(self):
        files = {"x": b"a", "SHA256SUMS": (release.digest(b"a") + "  x\n").encode()}
        release.verify_sums(files)
        with self.assertRaisesRegex(ValueError, "checksum"):
            release.verify_sums(files | {"x": b"b"})
        with self.assertRaisesRegex(ValueError, "incomplete"):
            release.verify_sums(files | {"unexpected": b"b"})

    def test_actual_ancillary_rejects_changed_detector(self):
        # Execute the actual frozen verifier's function with a corrupted input;
        # no altered manuscript or certificate is written to the source tree.
        payload = release.zip_payload((release.ROOT / release.SOURCE).read_bytes())
        namespace = {"__name__": "paper1_corruption_control"}
        exec(compile(payload["anc/verify_fixed_fields.py"], "frozen-verifier", "exec"), namespace)
        namespace["C17"][0] += 1
        with self.assertRaisesRegex(ArithmeticError, "unit resultant"):
            namespace["verify"](17)


if __name__ == "__main__":
    unittest.main()
