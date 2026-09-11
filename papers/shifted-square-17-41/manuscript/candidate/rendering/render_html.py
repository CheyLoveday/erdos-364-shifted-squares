#!/usr/bin/env python3
"""Render the frozen Paper I mathematics without network or font dependencies.

Requires Pandoc and beautifulsoup4. The cached SVG/MathML is the unchanged
mathematics from the baseline HTML. Unknown formulae fail rather than rendering
unverified replacements. Usage: python render_html.py manuscript.md output.html
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
import re
import subprocess
from pathlib import Path
from bs4 import BeautifulSoup, NavigableString


def normalise(tex: str) -> str:
    return re.sub(r'\s+', ' ', tex).strip()


def render(source: Path, output: Path) -> dict[str, object]:
    base = Path(__file__).resolve().parent
    md = source.read_text(encoding='utf-8')
    result = subprocess.run(
        ['pandoc', '-f', 'markdown+fenced_divs+tex_math_dollars',
         '-t', 'html5', '--mathjax'], input=md, text=True,
        capture_output=True, check=True)
    fragment = BeautifulSoup(result.stdout, 'html.parser')
    cache = json.loads((base / 'math-cache.json').read_text(encoding='utf-8'))
    template = BeautifulSoup((base / 'template.html').read_text(encoding='utf-8'), 'html.parser')
    formulae = list(fragment.select('span.math'))
    eqids: set[str] = set()
    for number, span in enumerate(formulae):
        display = 'display' in span.get('class', [])
        tex = span.get_text()[2:-2].strip()
        tag = re.search(r'\\tag\{([^}]+)\}', tex)
        label = tag.group(1) if tag else None
        tex = re.sub(r'\\tag\{[^}]+\}', '', tex).strip()
        key = ('display:' if display else 'inline:') + normalise(tex)
        if key not in cache:
            raise ValueError(f'Formula outside the frozen cache: {key!r}')
        unit = BeautifulSoup(cache[key], 'html.parser').select_one('.math-unit')
        assert unit is not None
        unit['id'] = f'math-{number:04}'
        if display:
            eq = fragment.new_tag('div', attrs={'class': 'equation' if label else 'equation unnumbered'})
            main = fragment.new_tag('div', attrs={'class':'equation-main', 'tabindex':'0'})
            main.append(unit)
            eq.append(main)
            if label:
                eid = 'eq-' + label.replace('.', '-')
                if eid in eqids:
                    raise ValueError(f'Duplicate equation ID: {eid}')
                eqids.add(eid)
                eq['id'] = eid
                link = fragment.new_tag('a', href='#'+eid, attrs={'class':'equation-number'})
                link.string = '('+label+')'
                eq.append(link)
            parent = span.parent
            if parent.name == 'p' and len([c for c in parent.contents if str(c).strip()]) == 1:
                parent.replace_with(eq)
            else:
                span.replace_with(eq)
        else:
            span.replace_with(unit)
    for table in list(fragment.find_all('table')):
        wrapper = fragment.new_tag('div', attrs={'class':'table-wrap', 'tabindex':'0'})
        table.wrap(wrapper)
    abstract = fragment.find(id='abstract')
    if abstract:
        abstract.find_next_sibling('p')['class'] = 'abstract-text'
    ids = {n['id'] for n in fragment.select('[id]')}
    token = re.compile(r'\[(\d+)\]|\(([1-8A-C])\.(\d+)\)')
    for node in list(fragment.find_all(string=True)):
        if not isinstance(node, NavigableString):
            continue
        if any(p.name in {'a','code','pre','script','style'} or
               'math-unit' in p.get('class',[]) or 'reference' in p.get('class',[])
               for p in node.parents):
            continue
        text = str(node)
        matches = list(token.finditer(text))
        if not matches:
            continue
        contents = []; position = 0
        for m in matches:
            target = f'ref-{m[1]}' if m[1] else f'eq-{m[2]}-{m[3]}'
            if target not in ids:
                continue
            contents.append(NavigableString(text[position:m.start()]))
            link = fragment.new_tag('a',href='#'+target,attrs={'class':'cite' if m[1] else 'xref'})
            link.string = m[0]; contents.append(link); position = m.end()
        if contents:
            contents.append(NavigableString(text[position:]))
            for c in contents: node.insert_before(c)
            node.extract()
    article = template.select_one('#article')
    article.clear()
    for child in list(fragment.contents):
        article.append(child.extract())
    template.select_one('#markdown-source').string = md
    html = str(template)
    all_ids=[x.get('id') for x in template.select('[id]')]
    if len(all_ids)!=len(set(all_ids)):
        raise ValueError('Duplicate HTML IDs')
    missing=sorted({a['href'][1:] for a in template.select('a[href^="#"]')
                    if a['href'][1:] and a['href'][1:] not in all_ids})
    if missing:
        raise ValueError(f'Broken internal references: {missing}')
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(html, encoding='utf-8')
    return {'expressions':len(formulae),'numbered_equations':len(eqids),
            'html_sha256':hashlib.sha256(output.read_bytes()).hexdigest()}

if __name__ == '__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('source',type=Path);p.add_argument('output',type=Path)
    args=p.parse_args()
    print(json.dumps(render(args.source,args.output),sort_keys=True))
