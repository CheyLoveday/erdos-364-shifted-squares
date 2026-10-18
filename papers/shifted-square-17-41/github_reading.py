"""Generate/check only Paper I's explicitly selected GitHub reading surfaces.

Run from any directory: python3 papers/shifted-square-17-41/github_reading.py generate|check
Original manuscripts, evidence records and historical editions are never written.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import posixpath
import re
import subprocess
from pathlib import Path
from urllib.parse import unquote, urlsplit

PAPER = 'papers/shifted-square-17-41'
REVISION = f'{PAPER}/manuscript/revision'
SCRIPT = f'{PAPER}/github_reading.py'
ROOT = Path(__file__).resolve().parents[2]
PROJECTIONS = {
    f'{REVISION}/paper_1.md': f'{REVISION}/paper_1_github.md',
    f'{PAPER}/PROOF_RECORD.md': f'{PAPER}/reading/PROOF_RECORD.md',
    f'{PAPER}/hilbert-jacobi-crosswalk.md': f'{PAPER}/reading/hilbert-jacobi-crosswalk.md',
    f'{PAPER}/hilbert-obstruction-lamport.md': f'{PAPER}/reading/hilbert-obstruction-lamport.md',
    f'{PAPER}/theorem-formal-crosswalk.md': f'{PAPER}/reading/theorem-formal-crosswalk.md',
    f'{PAPER}/source-theorem.md': f'{PAPER}/reading/source-theorem.md',
    f'{PAPER}/fixed-field-obligation-table.md': f'{PAPER}/reading/fixed-field-obligation-table.md',
    'problems/square-middle/sm2-lower-square/shifted-square-propagation-lamport.md':
        f'{PAPER}/reading/shifted-square-propagation-lamport.md',
    'experiments/paper1_validation_20260909/magma-17-41-comparison.md':
        f'{PAPER}/reading/magma-17-41-comparison.md',
    f'{PAPER}/verification/export-README.md': f'{PAPER}/reading/verification-guide.md',
}
DIRECT_DOCS = (
    'README.md', f'{PAPER}/conceptual-proof-map.md', f'{REVISION}/README.md',
    'LICENSE.md', f'{PAPER}/verification/LICENSE.md',
    f'{PAPER}/verification/notices/README.md',
)
HISTORICAL_ARTICLE = f'{PAPER}/manuscript/candidate/paper_1_release_candidate.md'
HISTORICAL_READING = f'{PAPER}/manuscript/paper_1_final_frozen_portable.md'
EXPLANATION = f'{PAPER}/manuscript/explanation/paper_1_explained.md'
BODY_MARKER = '<!-- reading-body -->\n\n'
FENCE = re.compile(r'^( *)(`{3,}|~{3,})([^\n]*)\n', re.M)
LINK = re.compile(r'(!?\[[^\]\n]*\])\(([^\s)]+)\)')


def chunks(text: str) -> list[tuple[str, str]]:
    """Separate fenced code byte-for-byte; reject unclosed/attributed fences."""
    result = []
    start = 0
    while match := FENCE.search(text, start):
        result.append(('text', text[start:match.start()]))
        indent, fence, info = match.groups()
        if '{' in info:
            raise ValueError('unsupported attributed/raw Pandoc code fence')
        closing = re.compile(r'^' + indent + re.escape(fence[0]) +
                             '{' + str(len(fence)) + r',}[ \t]*$', re.M)
        end = closing.search(text, match.end())
        if end is None:
            raise ValueError('unclosed fenced block')
        stop = end.end() + (text[end.end():end.end()+1] == '\n')
        result.append(('math' if info.strip() == 'math' else 'code', text[match.start():stop]))
        start = stop
    result.append(('text', text[start:]))
    return result


def relative(target: str, output: str) -> str:
    return posixpath.relpath(target, posixpath.dirname(output))


def reader_link(label: str, url: str, source: str, output: str) -> tuple[str, str]:
    parsed = urlsplit(url)
    if parsed.scheme or parsed.netloc:
        return label, url
    target = posixpath.normpath(posixpath.join(posixpath.dirname(source), unquote(parsed.path))) if parsed.path else source
    if source == f'{PAPER}/verification/export-README.md' and url == 'CITATION.cff':
        target = 'CITATION.cff'  # Original frozen guide's root citation link.
    if target == EXPLANATION:
        label = '[Pandoc explanation source]'
    elif target == HISTORICAL_ARTICLE:
        target = HISTORICAL_READING  # Keep the proof record's v1.0.0 correspondence.
    elif target in PROJECTIONS:
        target = PROJECTIONS[target]
    if parsed.path.endswith('.html'):
        label = label[:-1] + ' (download and open locally)]'
    url = relative(target, output)
    if parsed.fragment:
        url += '#' + parsed.fragment
    return label, url


def transform_text(text: str, source: str, output: str) -> str:
    divs = []
    lines = []
    for line in text.splitlines(keepends=True):
        heading = re.fullmatch(r'(#{1,6} .+?) \{#([\w-]+)\}\n?', line)
        opening = re.fullmatch(r'::: \{([^}]+)\}\n?', line)
        if heading:
            lines.append(f'<a id="{heading[2]}"></a>\n\n{heading[1]}\n')
        elif opening:
            tokens = opening[1].split()
            if not all(token in {'.theorem', '.reference', '.table-caption'} or
                       re.fullmatch(r'#[\w-]+', token) for token in tokens):
                raise ValueError('unsupported Pandoc division: ' + line.strip())
            divs.append(tokens)
            ids = [token[1:] for token in tokens if token.startswith('#')]
            if len(ids) > 1:
                raise ValueError('multiple division IDs')
            lines.append(f'<a id="{ids[0]}"></a>\n\n' if ids else '\n')
        elif line.strip() == ':::':
            if not divs:
                raise ValueError('unmatched division close')
            divs.pop()
            lines.append('\n')
        else:
            lines.append(line)
    if divs:
        raise ValueError('unclosed Pandoc division')
    text = ''.join(lines)
    # Protect literal inline code while adapting math and links in ordinary prose.
    parts = re.split(r'(!?\[[^\]\n]*\]\([^\s)]+\)|`+[^`\n]+`+)', text)
    for index in range(1, len(parts), 2):
        if match := LINK.fullmatch(parts[index]):
            label, url = reader_link(match[1], match[2], source, output)
            parts[index] = label + '(' + url + ')'
    for index in range(0, len(parts), 2):
        part = parts[index]
        def display(match: re.Match[str]) -> str:
            indent, tex = match[1], match[2]
            tex = re.sub(r'\\tag\{([^}]+)\}', lambda m: r'\qquad \text{(' + m[1] + ')}', tex)
            if indent:
                # GitHub leaves indented math fences as literal code inside lists.
                if re.search(r'(?<!\\)%', tex):
                    raise ValueError('unsupported TeX comment in nested display')
                return indent + '$`' + r'\displaystyle ' + re.sub(r'\s+', ' ', tex).strip() + '`$'
            # A top-level math fence protects TeX from prose parsing.
            return '```math\n' + tex + '```'
        part = re.sub(r'(?<![\\$])\$(?![`$])([^$]+?)\$(?!\$)',
                      lambda m: '$`' + re.sub(r'\s+', ' ', m[1]) + '`$', part, flags=re.S)
        part = re.sub(r'(?m)^( *)(?:\$\$|\\\[)\s*\n(.*?)(?:^\1(?:\$\$|\\\]))[ \t]*$', display, part, flags=re.S)
        part = re.sub(r'\\\((.*?)\\\)', lambda m: '$`' + re.sub(r'\s+', ' ', m[1]) + '`$', part, flags=re.S)
        parts[index] = part
    result = ''.join(parts)
    if format_errors(result):
        raise ValueError(f'unsupported presentation syntax in {source}: {format_errors(result)}')
    return result


def format_errors(text: str) -> list[str]:
    errors = []
    for kind, block in chunks(text):
        if kind == 'code':
            continue
        if any(r'\tag{' in tex for tex in re.findall(r'\$`(.*?)`\$', block, re.S)):
            errors.append('equation tag in inline maths')
        block = re.sub(r'`+[^`\n]+`+', '', block)
        if kind == 'text' and re.search(r'^\s*\\begin\{', block, re.M):
            errors.append('raw LaTeX block outside maths')
        for pattern in (r'^\s*:::', r'^#{1,6} .*\{[^}]*[#.]', r'\\tag\{', r'(?<!\\)\\[\[\]()]'):
            if re.search(pattern, block, re.M):
                errors.append(pattern)
    return errors


def render(source: str, output: str, text: str) -> str:
    digest = hashlib.sha256(text.encode()).hexdigest()
    title = ''
    if text.startswith('---\n'):
        metadata, text = text[4:].split('\n---\n', 1)
        fields = dict(line.split(': ', 1) for line in metadata.splitlines())
        if set(fields) != {'title', 'author', 'affiliation', 'date', 'lang'}:
            raise ValueError('unsupported manuscript metadata')
        fields = {k: v.strip('"') for k, v in fields.items()}
        title = f'# {fields["title"]}\n\n{fields["author"]} · {fields["affiliation"]} · {fields["date"]}.\n\n'
    body = ''.join(block if kind == 'code' else transform_text(block, source, output)
                   for kind, block in chunks(text))
    header = (
        '> [!NOTE]\n> Generated GitHub reading copy. **Do not edit directly.**\n'
        f'> Source: [{Path(source).name}]({relative(source, output)}). '
        'Only presentation syntax and reader links are adapted.\n'
        '> Original version, historical claims and evidence identities remain unchanged.\n\n'
        '<!--\nGENERATED FILE. DO NOT EDIT.\n'
        f'Source: {source}\nGenerator: python3 {SCRIPT} generate\nSource SHA-256: {digest}\n-->\n\n'
    )
    return (header + BODY_MARKER + title + body.lstrip('\n')).rstrip('\n') + '\n'


def ast(text: str, source: bool = False) -> dict:
    reader = 'markdown+fenced_divs+tex_math_dollars+tex_math_single_backslash-smart' if source else 'gfm+tex_math_dollars'
    return json.loads(subprocess.check_output(['pandoc', '-f', reader, '-t', 'json'], input=text.encode()))


def nodes(node: object, kind: str):
    if isinstance(node, dict):
        if node.get('t') == kind:
            yield node['c']
        for value in node.values():
            yield from nodes(value, kind)
    elif isinstance(node, list):
        for value in node:
            yield from nodes(value, kind)


def math_inventory(node: object) -> list[tuple[str, str, tuple[str, ...]]]:
    if isinstance(node, dict):
        kind, value = node.get('t'), node.get('c')
        if kind == 'Math':
            tex = value[1]
            name = value[0]['t']
            if name == 'InlineMath' and tex.startswith(r'\displaystyle '):
                name, tex = 'DisplayMath', tex.removeprefix(r'\displaystyle ')
        elif kind == 'CodeBlock' and 'math' in value[0][1]:
            name, tex = 'DisplayMath', value[1]
        else:
            return [item for child in node.values() for item in math_inventory(child)]
        labels = tuple(re.findall(r'\\tag\{([^}]+)\}', tex) or
                       re.findall(r'\\qquad\s*\\text\{\(([\w.]+)\)\}', tex))
        tex = re.sub(r'\\tag\{[^}]+\}|\\qquad\s*\\text\{\([\w.]+\)\}', '', tex)
        return [(name, re.sub(r'\s+', '', tex), labels)]
    if isinstance(node, list):
        return [item for child in node for item in math_inventory(child)]
    return []


def narrative(node: object) -> list[str]:
    if isinstance(node, dict):
        if node.get('t') in {'Link', 'Math', 'CodeBlock', 'RawBlock', 'RawInline'}:
            return []  # Link-label changes are limited to reader_link; bytes bind regeneration.
        if node.get('t') == 'Str':
            return [node['c']]
        return [word for child in node.values() for word in narrative(child)]
    if isinstance(node, list):
        return [word for child in node for word in narrative(child)]
    return []


def fidelity(original: str, generated: str) -> tuple[int, int]:
    manuscript = original.startswith('---\n')
    body = generated.split(BODY_MARKER, 1)[1]
    def raw_code(text):
        return [block for kind, block in chunks(text) if kind == 'code']
    if raw_code(original) != raw_code(body):
        raise ValueError('fenced code bytes differ')
    for anchor in re.findall(r'\{[^}]*#([\w-]+)[^}]*\}', original):
        if f'<a id="{anchor}"></a>' not in body:
            raise ValueError(f'missing explicit source anchor {anchor}')
    original = ast(original, True)['blocks']
    # The article's title/author metadata are promoted into a visible title above its body.
    if manuscript:
        body = body.split('\n\n', 2)[2]
    reading = ast(body)['blocks']
    if math_inventory(original) != math_inventory(reading):
        raise ValueError('ordered mathematical expressions differ')
    if narrative(original) != narrative(reading):
        raise ValueError('non-link prose differs')
    def code(tree):
        return [c for c in nodes(tree, 'CodeBlock') if 'math' not in c[0][1]]
    if list(nodes(original, 'Code')) != list(nodes(reading, 'Code')):
        raise ValueError('inline code differs')
    if code(original) != code(reading):
        raise ValueError('embedded code differs')
    if [h[0] for h in nodes(original, 'Header')] != [h[0] for h in nodes(reading, 'Header')]:
        raise ValueError('section structure differs')
    return len(math_inventory(original)), len(list(nodes(original, 'Header')))


def check_links(root: Path, path: str, text: str) -> int:
    tree = ast(text)['blocks']
    count = 0
    for _, _, (url, _) in nodes(tree, 'Link'):
        target = urlsplit(url)
        if target.scheme or target.netloc:
            continue
        dest = (root / path).parent / unquote(target.path) if target.path else root / path
        if not dest.exists():
            raise ValueError(f'{path}: missing destination {url}')
        if target.fragment and dest.suffix == '.md':
            raw = dest.read_text()
            headings = ast(raw)['blocks']
            ids = {h[1][0] for h in nodes(headings, 'Header')}
            ids.update(re.findall(r'<(?:a|h[1-6])\s+id="([^"]+)"', raw))
            if target.fragment not in ids:
                raise ValueError(f'{path}: missing anchor {url}')
        count += 1
    return count


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('operation', choices=('generate', 'check'))
    args = parser.parse_args()
    sources = {source: (ROOT / source).read_bytes().decode('utf-8') for source in PROJECTIONS}
    rendered = {output: render(source, output, sources[source]) for source, output in PROJECTIONS.items()}
    if args.operation == 'generate':
        for output, text in rendered.items():
            (ROOT / output).parent.mkdir(parents=True, exist_ok=True)
            (ROOT / output).write_bytes(text.encode('utf-8'))
        print(f'Generated {len(rendered)} reading copies; no source file written.')
        return
    maths = links = 0
    for source, output in PROJECTIONS.items():
        actual = (ROOT / output).read_bytes().decode('utf-8')
        if actual != rendered[output]:
            raise ValueError(f'{output}: differs from fresh generation')
        try:
            maths += fidelity(sources[source], actual)[0]
        except ValueError as error:
            raise ValueError(f'{output}: {error}') from error
        links += check_links(ROOT, output, actual)
    for path in DIRECT_DOCS:
        text = (ROOT / path).read_text()
        if format_errors(text):
            raise ValueError(f'{path}: unsupported GitHub presentation syntax')
        links += check_links(ROOT, path, text)
    print(f'GITHUB_READING_OK: {len(rendered)} fresh projections, {len(DIRECT_DOCS)} direct documents, {maths} maths, {links} local links.')


if __name__ == '__main__':
    main()
