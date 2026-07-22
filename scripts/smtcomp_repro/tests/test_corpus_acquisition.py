"""Unit tests for ADR-0356 S2 safe corpus extraction."""

from __future__ import annotations

import io
import tarfile
import tempfile
import unittest
from pathlib import Path

from scripts.smtcomp_repro.corpus_acquisition import (
    CorpusAcquisitionError,
    extract_tar_stream,
    inventory_logic_tree,
    validate_corpus_roots,
)


def tar_bytes(member: tarfile.TarInfo, payload: bytes = b"") -> bytes:
    output = io.BytesIO()
    with tarfile.open(fileobj=output, mode="w") as archive:
        member.size = len(payload)
        archive.addfile(member, io.BytesIO(payload))
    return output.getvalue()


class CorpusAcquisitionTests(unittest.TestCase):
    def test_regular_member_extracts_with_exact_identity(self) -> None:
        member = tarfile.TarInfo("non-incremental/QF_BV/family/case.smt2")
        payload = b"(set-logic QF_BV)\n(check-sat)\n"
        observed = []
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / "root"
            files, byte_count = extract_tar_stream(
                io.BytesIO(tar_bytes(member, payload)),
                root,
                "QF_BV",
                lambda path, size, sha256: observed.append((path, size, sha256)),
            )
            self.assertEqual(files, 1)
            self.assertEqual(byte_count, len(payload))
            self.assertEqual(observed[0][0], member.name)
            self.assertEqual(observed[0][1], len(payload))
            self.assertEqual((root / member.name).read_bytes(), payload)
            validate_corpus_roots(root, {"QF_BV"})

    def test_traversal_cross_logic_and_link_members_reject(self) -> None:
        members = [
            tarfile.TarInfo("../escape.smt2"),
            tarfile.TarInfo("/non-incremental/QF_BV/absolute.smt2"),
            tarfile.TarInfo("non-incremental/QF_LIA/wrong.smt2"),
        ]
        symlink = tarfile.TarInfo("non-incremental/QF_BV/link.smt2")
        symlink.type = tarfile.SYMTYPE
        symlink.linkname = "case.smt2"
        members.append(symlink)
        hardlink = tarfile.TarInfo("non-incremental/QF_BV/hard.smt2")
        hardlink.type = tarfile.LNKTYPE
        hardlink.linkname = "non-incremental/QF_BV/case.smt2"
        members.append(hardlink)
        for index, member in enumerate(members):
            with self.subTest(member=member.name), tempfile.TemporaryDirectory() as temporary:
                with self.assertRaises(CorpusAcquisitionError):
                    extract_tar_stream(
                        io.BytesIO(tar_bytes(member)),
                        Path(temporary) / f"root-{index}",
                        "QF_BV",
                        lambda _path, _size, _sha256: None,
                    )

    def test_inventory_rejects_symlink_and_extra_logic_root(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / "corpus"
            logic = root / "non-incremental/QF_BV/family"
            logic.mkdir(parents=True)
            target = logic / "case.smt2"
            target.write_bytes(b"(check-sat)\n")
            observed = []
            files, _ = inventory_logic_tree(
                root,
                "QF_BV",
                lambda path, size, sha256: observed.append((path, size, sha256)),
            )
            self.assertEqual(files, 1)
            self.assertEqual(observed[0][0], "non-incremental/QF_BV/family/case.smt2")
            link = logic / "link.smt2"
            link.symlink_to(target)
            with self.assertRaises(CorpusAcquisitionError):
                inventory_logic_tree(root, "QF_BV", lambda _path, _size, _sha256: None)
            link.unlink()
            (root / "non-incremental/QF_LIA").mkdir()
            with self.assertRaises(CorpusAcquisitionError):
                validate_corpus_roots(root, {"QF_BV"})


if __name__ == "__main__":
    unittest.main()
