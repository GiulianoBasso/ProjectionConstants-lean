"""Build diagram/dependency-tree.html from scripts/diagram/template.html and .lake/diagram/tree.json."""
import json, pathlib, subprocess
ROOT = pathlib.Path(__file__).resolve().parents[2]
OUT = ROOT / '.lake' / 'diagram'
tree = json.load(open(OUT / 'tree.json'))
nodes = json.load(open(OUT / 'depgraph.json'))
files = sorted(list((ROOT / 'ProjectionConstants').rglob('*.lean')) + [ROOT / 'ProjectionConstants.lean'])
lines = sum(len(f.read_text().splitlines()) for f in files)
lean = (ROOT / 'lean-toolchain').read_text().strip().split(':v')[-1]
stats = {'decls': len(nodes), 'files': len(files), 'lines': lines, 'lean': lean}
tpl = (ROOT / 'scripts' / 'diagram' / 'template.html').read_text()
page = tpl.replace('/*__DATA__*/null', json.dumps(tree, ensure_ascii=False, separators=(',', ':'))) \
          .replace('/*__STATS__*/null', json.dumps(stats))
html = ('<!doctype html>\n<html lang="en">\n<head>\n<meta charset="utf-8">\n'
        '<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">\n'
        '</head>\n<body>\n' + page + '\n</body>\n</html>\n')
(ROOT / 'diagram').mkdir(exist_ok=True)
(ROOT / 'diagram' / 'dependency-tree.html').write_text(html)
print(stats)
