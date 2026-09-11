#!/usr/bin/env python3
"""The five Paper I source/build/export operations, using the existing runner.

These operations prepare and check artifacts. They never publish, change Git
refs, select licences, install dependencies or assert mathematical acceptance.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import importlib.metadata
import io
import json
import os
import posixpath
import re
import shutil
import sys
import tarfile
import tempfile
from pathlib import Path, PurePosixPath
from urllib.parse import unquote, urlsplit
from zipfile import ZipFile

import run_core as core

ROOT = core.ROOT
VERIFY = "papers/shifted-square-17-41/verification"
PAPER = "papers/shifted-square-17-41"
CANDIDATE = PAPER + "/manuscript/candidate"
MD = CANDIDATE + "/paper_1_release_candidate.md"
SOURCE = CANDIDATE + "/paper_1_release_candidate_source.zip"
FROZEN_MD = "d27fffb9a760272d44f45d67919d41bd9596fc77e6fdca95ac86ee8266873dd2"
FROZEN_ZIP = "04bd88064b99569332afdc8e3e6678d38bf1e99146c34d2509197922140c8491"
DEPENDENCIES = {
    "sympy": "1.14.0",
    "mpmath": "1.3.0",
    "beautifulsoup4": "4.14.3",
    "soupsieve": "2.8.4",
    "typing_extensions": "4.16.0",
}
require = core.require


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def safe_name(name: str) -> str:
    path = PurePosixPath(name)
    require(bool(name) and not path.is_absolute(), "absolute or empty archive name")
    require(".." not in path.parts and "\\" not in name, "unsafe archive name")
    require(str(path) == name, "noncanonical archive name")
    require(
        not {".git", ".lake", "__pycache__", ".bootstrap"} & set(path.parts),
        "excluded archive path",
    )
    return name


def zip_payload(raw: bytes) -> dict[str, bytes]:
    files: dict[str, bytes] = {}
    with ZipFile(io.BytesIO(raw)) as archive:
        require(len(archive.infolist()) <= 500, "too many ZIP entries")
        for item in archive.infolist():
            name = safe_name(item.filename)
            require(name not in files, "duplicate ZIP entry")
            require(
                not item.is_dir() and item.file_size <= 10 * 1024 * 1024, "unsupported ZIP entry"
            )
            require((item.external_attr >> 16) & 0o170000 != 0o120000, "ZIP symlink")
            files[name] = archive.read(item)
    return files


def verify_sums(files: dict[str, bytes]) -> None:
    listed: dict[str, str] = {}
    for line in files["SHA256SUMS"].decode().splitlines():
        expected, name = line.split(maxsplit=1)
        name = safe_name(name.lstrip("*"))
        require(name not in listed, "duplicate checksum entry")
        listed[name] = expected
        require(name in files and digest(files[name]) == expected, f"checksum: {name}")
    require(set(listed) == set(files) - {"SHA256SUMS"}, "incomplete checksum inventory")


def write_files(files: dict[str, bytes], destination: Path) -> None:
    destination.mkdir(parents=True, exist_ok=False)
    for name, raw in sorted(files.items()):
        target = destination / safe_name(name)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(raw)


def check_dependency_links(base: Path) -> None:
    """Reject links that make a prepared public cache depend on another tree."""
    boundary = base.resolve(strict=True)

    def visit(directory: Path) -> None:
        for path in sorted(directory.iterdir()):
            if path.is_symlink():
                require(
                    path.resolve(strict=True).is_relative_to(boundary),
                    "escaping public dependency symlink: " + str(path.relative_to(base)),
                )
            elif path.is_dir():
                visit(path)

    visit(base)


def check_document_links(files: dict[str, bytes]) -> None:
    for name, raw in files.items():
        if not name.endswith(".md"):
            continue
        for href in re.findall(r"\]\(([^)]+)\)", raw.decode()):
            href = href.strip().strip("<>")
            parsed = urlsplit(href)
            if parsed.scheme or not parsed.path:
                continue
            target = posixpath.normpath(
                posixpath.join(posixpath.dirname(name), unquote(parsed.path))
            )
            require(target in files, f"unexported document link: {name} -> {target}")


def record(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def run(
    argv: list[str],
    output: Path,
    name: str,
    cwd: Path = ROOT,
    timeout: int = 180,
    marker: str | None = None,
) -> bytes:
    runner = core.load_runner()
    runner.REPOSITORY_ROOT = cwd
    result: dict[str, object] = {"argv": argv, "status": "FAIL"}
    try:
        rc, out, err = runner.run_bounded_process(
            argv, timeout=timeout, maximum=10 * 1024 * 1024, context=name
        )
        result.update(exit_code=rc, stdout=core.normalise(out), stderr=core.normalise(err))
        if name == "pandoc-ast":
            result.update(
                stdout_sha256=digest(out),
                stdout_bytes=len(out),
                stdout="<AST bound by hash; its complete Markdown input is exported>",
            )
        require(rc == 0, f"{name}: exit {rc}")
        if marker:
            require((out + err).decode().count(marker) == 1, f"{name}: missing/duplicate marker")
        result["status"] = "PASS"
        return out
    finally:
        # Normalize argv/cwd-related text as well as subprocess output.
        cleaned = core.normalise(json.dumps(result).encode())
        for path, label in (
            (str(output), "<RECORD_ROOT>"),
            (str(cwd), "<WORKING_ROOT>"),
            (sys.prefix, "<PYTHON_ENV>"),
        ):
            if path != str(ROOT):
                cleaned = cleaned.replace(path, label)
        public_cache = os.environ.get("PAPER1_PUBLIC_LAKE_PACKAGES")
        if public_cache:
            cleaned = cleaned.replace(public_cache, "<PUBLIC_LAKE_PACKAGES>")
        (output / (name + ".json")).write_text(json.dumps(json.loads(cleaned), indent=2) + "\n")


def rooted_document(name: str) -> bytes:
    """Re-target a verification-directory document's relative links to the archive root."""
    return (
        core.checked_bytes(ROOT, VERIFY + "/" + name)
        .replace(b"(../", ("(" + PAPER + "/").encode())
        .replace(b"(notices/", ("(" + VERIFY + "/notices/").encode())
    )


def source_files() -> dict[str, bytes]:
    core.source_inventory(ROOT)
    names = (ROOT / VERIFY / "export-files.txt").read_text().splitlines()
    require(len(names) == len(set(names)), "duplicate export allowlist entry")
    files = {safe_name(name): core.checked_bytes(ROOT, name) for name in names}
    files["Erdos364.lean"] = core.checked_bytes(ROOT, VERIFY + "/export-root.lean")
    files["Makefile"] = core.checked_bytes(ROOT, VERIFY + "/export-Makefile")
    files["README.md"] = rooted_document("export-README.md")
    files["LICENSE.md"] = rooted_document("LICENSE.md")
    files["CITATION.cff"] = core.checked_bytes(ROOT, VERIFY + "/CITATION.cff")
    for licence in ("Apache-2.0", "CC-BY-4.0"):
        files["LICENSES/" + licence + ".txt"] = core.checked_bytes(
            ROOT, VERIFY + "/LICENSES/" + licence + ".txt"
        )
    return files


def check(output: Path) -> dict[str, bytes]:
    files = source_files()
    check_document_links(files)
    for item in json.loads(files[VERIFY + "/magma-imports.json"])["sources"]:
        require(digest(files[item["path"]]) == item["sha256"], "historical Magma asset changed")
    manuscript_inputs = json.loads(files[VERIFY + "/manuscript-inputs.json"])["sources"]
    for name, expected_hash in manuscript_inputs.items():
        require(
            name in files and digest(files[name]) == expected_hash,
            f"supplied manuscript asset changed: {name}",
        )
    require(digest(files[MD]) == FROZEN_MD, "frozen Markdown identity")
    require(digest(files[SOURCE]) == FROZEN_ZIP, "frozen source ZIP identity")
    article = zip_payload(files[SOURCE])
    verify_sums(article)
    markdown = files[MD].decode()
    program = re.findall(r"```python\n(.*?)\n```", markdown, re.DOTALL)
    require(len(program) == 1, "one printed Python verifier required")
    require(
        (program[0] + "\n").encode() == article["anc/verify_fixed_fields.py"],
        "printed and standalone verifier differ",
    )
    from bs4 import BeautifulSoup

    html = BeautifulSoup(files[CANDIDATE + "/paper_1_release_candidate.html"], "html.parser")
    require(html.select_one("#markdown-source").get_text() == markdown, "HTML Markdown mismatch")
    require(len(html.select(".math-unit")) == 696, "HTML formula inventory")
    expected = json.loads(files[PAPER + "/manuscript/audit/math-freeze.json"])
    ast = json.loads(
        run(
            ["pandoc", "-f", "markdown+fenced_divs+tex_math_dollars", "-t", "json", str(ROOT / MD)],
            output,
            "pandoc-ast",
        )
    )
    maths: list[object] = []

    def walk(node: object) -> None:
        if isinstance(node, dict):
            if node.get("t") == "Math":
                maths.append(node["c"])
            for value in node.values():
                walk(value)
        elif isinstance(node, list):
            for value in node:
                walk(value)

    walk(ast)
    require(len(maths) == 696, "Markdown formula inventory")
    require(
        digest(json.dumps(maths, separators=(",", ":")).encode())
        == expected["ordered_math_ast_sha256"],
        "mathematical freeze digest",
    )
    require(
        len(re.findall(r"^::: \{\.theorem ", markdown, re.MULTILINE)) == 12,
        "numbered result inventory",
    )
    actual = {name: importlib.metadata.version(name) for name in DEPENDENCIES}
    require(actual == DEPENDENCIES, "Python dependency versions differ")
    record(output / "python-environment.json", {"python": sys.version, "packages": actual})
    record(output / "sources.json", {name: digest(raw) for name, raw in sorted(files.items())})
    return files


def verify(output: Path) -> None:
    article = zip_payload((ROOT / SOURCE).read_bytes())
    work = output / "ancillary"
    write_files(article, work)
    run(
        [sys.executable, "-B", "anc/verify_fixed_fields.py"],
        output,
        "ancillary-verifier",
        cwd=work,
        marker="FIXED_FIELDS_OK",
    )
    run(
        [sys.executable, "-B", "-m", "unittest", "discover", "-s", VERIFY, "-p", "test_*.py", "-v"],
        output,
        "regression-corruption",
    )
    run(
        [sys.executable, "-B", VERIFY + "/run_core.py", "--output", str(output / "core")],
        output,
        "core-verification",
        timeout=2400,
    )


def build_article(article: dict[str, bytes], destination: Path, output: Path) -> None:
    write_files(article, destination)
    # Use the supplied pdfLaTeX recipe where installed. Tectonic is the existing
    # companion's alternative TeX engine, recorded explicitly when used.
    if shutil.which("pdflatex"):
        for i in range(3):
            run(
                [
                    "pdflatex",
                    "-no-shell-escape",
                    "-interaction=nonstopmode",
                    "-halt-on-error",
                    "main.tex",
                ],
                output,
                f"pdflatex-{i + 1}",
                cwd=destination,
            )
    else:
        run(
            [
                "tectonic",
                "--untrusted",
                "--only-cached",
                "--keep-logs",
                "--reruns",
                "2",
                "main.tex",
            ],
            output,
            "tectonic",
            cwd=destination,
        )
    require((destination / "main.pdf").is_file(), "PDF absent after build")
    log = (destination / "main.log").read_text(errors="replace")
    diagnostics = [
        s
        for s in log.splitlines()
        if re.search(
            r"undefined references|LaTeX Warning|Overfull \\[hv]box|Underfull \\[hv]box|^!", s
        )
    ]
    record(output / "latex-diagnostics.json", diagnostics)
    require(not diagnostics, "LaTeX diagnostics need review")
    run(
        ["pdftotext", str(destination / "main.pdf"), str(output / "built-pdf.txt")],
        output,
        "pdf-text",
    )


def build(output: Path) -> None:
    build_article(zip_payload((ROOT / SOURCE).read_bytes()), output / "article", output)
    run(
        [
            sys.executable,
            "-B",
            CANDIDATE + "/rendering/render_html.py",
            MD,
            str(output / "paper_1_release_candidate.html"),
        ],
        output,
        "html-render",
    )
    from bs4 import BeautifulSoup

    result = BeautifulSoup((output / "paper_1_release_candidate.html").read_bytes(), "html.parser")
    require(
        result.select_one("#markdown-source").get_text() == (ROOT / MD).read_text(),
        "rebuilt HTML Markdown mismatch",
    )
    require(len(result.select(".math-unit")) == 696, "rebuilt HTML formula count")
    supplied = BeautifulSoup(
        (ROOT / CANDIDATE / "paper_1_release_candidate.html").read_bytes(), "html.parser"
    )
    parity = {
        "math_units_identical": [str(n) for n in result.select(".math-unit")]
        == [str(n) for n in supplied.select(".math-unit")],
        "visible_text_equal": re.sub(r"\s+", " ", result.select_one("#article").get_text()).strip()
        == re.sub(r"\s+", " ", supplied.select_one("#article").get_text()).strip(),
        "link_targets_equal": [n.get("href") for n in result.select("a")]
        == [n.get("href") for n in supplied.select("a")],
    }
    record(output / "html-parity.json", parity)
    require(all(parity.values()), "rebuilt HTML differs in mathematical geometry, text or links")
    record(
        output / "build-identities.json",
        {
            "pdf_sha256": digest((output / "article/main.pdf").read_bytes()),
            "html_sha256": digest((output / "paper_1_release_candidate.html").read_bytes()),
            "html_equals_supplied": (output / "paper_1_release_candidate.html").read_bytes()
            == (ROOT / CANDIDATE / "paper_1_release_candidate.html").read_bytes(),
        },
    )


def stage(files: dict[str, bytes], output: Path) -> None:
    arxiv = zip_payload(files[SOURCE])
    verify_sums(arxiv)
    (output / "paper1-arxiv-source.zip").write_bytes(files[SOURCE])
    files = dict(files)
    files["SHA256SUMS"] = "".join(
        f"{digest(raw)}  {name}\n" for name, raw in sorted(files.items())
    ).encode()
    with (
        (output / "paper1-evidence-source.tar.gz").open("wb") as target,
        gzip.GzipFile(fileobj=target, mode="wb", filename="", mtime=0) as gz,
        tarfile.open(fileobj=gz, mode="w") as archive,
    ):
        for name, raw in sorted(files.items()):
            item = tarfile.TarInfo(name)
            item.size, item.mode, item.mtime = len(raw), 0o644, 0
            archive.addfile(item, io.BytesIO(raw))
    record(
        output / "packages.json",
        {
            name: digest((output / name).read_bytes())
            for name in ["paper1-arxiv-source.zip", "paper1-evidence-source.tar.gz"]
        },
    )


def check_export(files: dict[str, bytes], output: Path) -> None:
    # Staging here prevents a stale archive elsewhere being credited to this run.
    stage(files, output)
    with tempfile.TemporaryDirectory(prefix="paper1-extracted-") as temporary:
        work = Path(temporary)
        require(not (work / ".git").exists(), "extraction inside Git")
        article = zip_payload((output / "paper1-arxiv-source.zip").read_bytes())
        verify_sums(article)
        build_article(article, work / "arxiv", output)
        run(
            [sys.executable, "-B", "anc/verify_fixed_fields.py"],
            output,
            "extracted-ancillary",
            cwd=work / "arxiv",
            marker="FIXED_FIELDS_OK",
        )
        extracted: dict[str, bytes] = {}
        with tarfile.open(output / "paper1-evidence-source.tar.gz", "r:gz") as archive:
            for item in archive:
                name = safe_name(item.name)
                require(
                    item.isfile() and name not in extracted and item.size <= 10 * 1024 * 1024,
                    "unsupported TAR entry",
                )
                extracted[name] = archive.extractfile(item).read()
        verify_sums(extracted)
        require(
            {k: v for k, v in extracted.items() if k != "SHA256SUMS"} == files,
            "evidence package differs from explicit source allowlist",
        )
        evidence = work / "evidence"
        write_files(extracted, evidence)
        require(not (evidence / ".lake").exists(), "private build artifacts in evidence")
        cache = os.environ.get("PAPER1_PUBLIC_LAKE_PACKAGES")
        require(
            cache is not None,
            "set PAPER1_PUBLIC_LAKE_PACKAGES to separately prepared public dependencies",
        )
        dependencies = json.loads(files["lake-manifest.json"])["packages"]
        check_dependency_links(Path(cache))
        (evidence / ".lake/packages").mkdir(parents=True)
        for item in dependencies:
            package = Path(cache) / item["name"]
            require(
                item["url"].startswith(
                    ("https://github.com/leanprover-community/", "https://github.com/leanprover/")
                ),
                "private dependency",
            )
            revision = run(
                ["git", "rev-parse", "HEAD"], output, "dependency-" + item["name"], cwd=package
            )
            require(revision.decode().strip() == item["rev"], "dependency revision differs")
            dirty = run(
                ["git", "status", "--porcelain", "--untracked-files=no"],
                output,
                "dependency-clean-" + item["name"],
                cwd=package,
            )
            require(not dirty.strip(), "modified public dependency")
            destination = evidence / ".lake/packages" / item["name"]
            if sys.platform == "darwin":
                run(
                    ["cp", "-cR", str(package), str(destination)],
                    output,
                    "dependency-copy-" + item["name"],
                    timeout=300,
                )
            else:
                shutil.copytree(package, destination, symlinks=False)
        check_dependency_links(evidence / ".lake/packages")
        try:
            for operation in ("check", "verify", "build"):
                run(
                    [
                        sys.executable,
                        "-B",
                        VERIFY + "/release.py",
                        operation,
                        "--output",
                        str(work / "checks"),
                    ],
                    output,
                    "extracted-" + operation,
                    cwd=evidence,
                    timeout=3000,
                )
        finally:
            if (work / "checks").is_dir():
                shutil.copytree(work / "checks", output / "extracted-records")
        run(
            ["lake", "--no-cache", "build"],
            output,
            "extracted-default-lean-root",
            cwd=evidence,
            timeout=1800,
        )
        check_dependency_links(evidence / ".lake/packages")
        record(
            output / "extraction.json",
            {"status": "PASS", "private_git_required": False, "local_Lean_sources_rebuilt": 60},
        )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("operation", choices=["check", "verify", "build", "stage", "check-export"])
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve() / args.operation
    output.mkdir(parents=True, exist_ok=False)
    status: dict[str, object] = {"operation": args.operation, "status": "FAIL"}
    try:
        files = check(output)
        identity = {k: digest(v) for k, v in sorted(files.items())}
        status["source_sha256"] = digest(json.dumps(identity, sort_keys=True).encode())
        if args.operation == "verify":
            verify(output)
        elif args.operation == "build":
            build(output)
        elif args.operation == "stage":
            stage(files, output)
        elif args.operation == "check-export":
            check_export(files, output)
        require(source_files() == files, "inputs changed during operation")
        status["status"] = "PASS"
        print("PAPER1_" + args.operation.upper().replace("-", "_") + "_OK")
        return 0
    except (
        ValueError,
        OSError,
        KeyError,
        RuntimeError,
        importlib.metadata.PackageNotFoundError,
    ) as error:
        status["error"] = str(error)
        print(f"PAPER1_{args.operation}: {error}", file=sys.stderr)
        return 1
    finally:
        record(output / "result.json", status)


if __name__ == "__main__":
    raise SystemExit(main())
