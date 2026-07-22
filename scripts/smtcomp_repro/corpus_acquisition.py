"""Fail-closed helpers for the ADR-0356 verified corpus acquisition."""

from __future__ import annotations

import hashlib
import os
import stat
import tarfile
from pathlib import Path, PurePosixPath
from typing import BinaryIO, Callable


CHUNK = 1024 * 1024


class CorpusAcquisitionError(ValueError):
    """An archive or extracted corpus violates the frozen S2 contract."""


FileCallback = Callable[[str, int, str], None]


def archive_member_path(member: tarfile.TarInfo, expected_logic: str) -> PurePosixPath | None:
    """Validate one tar member and return its normalized regular-file path."""
    raw = member.name.rstrip("/")
    parts = raw.split("/")
    if (
        not raw
        or member.name.startswith("/")
        or "\\" in member.name
        or any(part in {"", ".", ".."} for part in parts)
    ):
        raise CorpusAcquisitionError(f"unsafe archive member path: {member.name!r}")
    if parts[:2] != ["non-incremental", expected_logic]:
        raise CorpusAcquisitionError(
            f"archive member is outside non-incremental/{expected_logic}: {member.name!r}"
        )
    if member.isdir():
        return None
    if not member.isreg() or len(parts) < 3:
        raise CorpusAcquisitionError(f"archive member is not a benchmark file: {member.name!r}")
    return PurePosixPath(*parts)


def hash_file(path: Path) -> tuple[int, str, str]:
    """Return byte count, MD5, and SHA-256 for one regular non-symlink file."""
    if path.is_symlink() or not path.is_file():
        raise CorpusAcquisitionError(f"not a regular file: {path}")
    size = 0
    md5 = hashlib.md5(usedforsecurity=False)
    sha256 = hashlib.sha256()
    with path.open("rb") as source:
        while data := source.read(CHUNK):
            size += len(data)
            md5.update(data)
            sha256.update(data)
    return size, md5.hexdigest(), sha256.hexdigest()


def extract_tar_stream(
    source: BinaryIO,
    destination: Path,
    expected_logic: str,
    on_file: FileCallback,
) -> tuple[int, int]:
    """Extract one uncompressed tar stream using regular-file-only semantics."""
    destination.mkdir(parents=True, exist_ok=False)
    files = 0
    total_bytes = 0
    with tarfile.open(fileobj=source, mode="r|") as archive:
        for member in archive:
            relative = archive_member_path(member, expected_logic)
            if relative is None:
                continue
            target = destination.joinpath(*relative.parts)
            target.parent.mkdir(parents=True, exist_ok=True)
            extracted = archive.extractfile(member)
            if extracted is None:
                raise CorpusAcquisitionError(f"cannot read archive member: {member.name!r}")
            digest = hashlib.sha256()
            size = 0
            with target.open("xb") as output:
                while data := extracted.read(CHUNK):
                    output.write(data)
                    digest.update(data)
                    size += len(data)
            if size != member.size:
                raise CorpusAcquisitionError(
                    f"archive member size drift: {member.name!r} {size}/{member.size}"
                )
            relative_name = relative.as_posix()
            on_file(relative_name, size, digest.hexdigest())
            files += 1
            total_bytes += size
    return files, total_bytes


def inventory_logic_tree(
    corpus_root: Path,
    expected_logic: str,
    on_file: FileCallback,
) -> tuple[int, int]:
    """Hash one already extracted logic tree without following links."""
    logic_root = corpus_root / "non-incremental" / expected_logic
    if logic_root.is_symlink() or not logic_root.is_dir():
        raise CorpusAcquisitionError(f"missing regular logic directory: {logic_root}")
    files = 0
    total_bytes = 0
    for directory, names, filenames in os.walk(logic_root, followlinks=False):
        base = Path(directory)
        for name in names:
            child = base / name
            if child.is_symlink() or not child.is_dir():
                raise CorpusAcquisitionError(f"non-directory in corpus tree: {child}")
        for name in filenames:
            child = base / name
            mode = child.lstat().st_mode
            if child.is_symlink() or not stat.S_ISREG(mode):
                raise CorpusAcquisitionError(f"non-regular corpus entry: {child}")
            size, _, sha256 = hash_file(child)
            relative = child.relative_to(corpus_root).as_posix()
            on_file(relative, size, sha256)
            files += 1
            total_bytes += size
    return files, total_bytes


def validate_corpus_roots(corpus_root: Path, expected_logics: set[str]) -> None:
    """Require exactly one non-symlink directory for each release logic."""
    if corpus_root.is_symlink() or not corpus_root.is_dir():
        raise CorpusAcquisitionError("corpus root is not a regular directory")
    entries = list(corpus_root.iterdir())
    if len(entries) != 1 or entries[0].name != "non-incremental":
        raise CorpusAcquisitionError("corpus root has unexpected entries")
    non_incremental = entries[0]
    if non_incremental.is_symlink() or not non_incremental.is_dir():
        raise CorpusAcquisitionError("non-incremental root is not a regular directory")
    actual = set()
    for entry in non_incremental.iterdir():
        if entry.is_symlink() or not entry.is_dir():
            raise CorpusAcquisitionError(f"unexpected non-directory corpus entry: {entry}")
        actual.add(entry.name)
    if actual != expected_logics:
        raise CorpusAcquisitionError(
            f"corpus logic roots differ: missing={sorted(expected_logics - actual)!r} "
            f"extra={sorted(actual - expected_logics)!r}"
        )
