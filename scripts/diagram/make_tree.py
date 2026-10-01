"""Turn the declaration graph (.lake/diagram/depgraph.json) into the radial tree shown in the diagram.

Each part of the library (folder) is a branch; inside a branch, every declaration hangs off a
declaration of the same part that uses it (breadth-first from the part's exported results)."""
import json, collections, sys, pathlib
from collections import deque
ROOT = pathlib.Path(__file__).resolve().parents[2]
OUT = ROOT / '.lake' / 'diagram'
nodes = json.load(open(OUT / 'depgraph.json'))
byname = {n['name']: n for n in nodes}
BR = [('found', 'Foundations'), ('cl', 'Chalmers–Lewicki formula'), ('dl', 'Bounds and exact values'),
      ('etf', 'Equiangular tight frames'), ('jfa', 'Π₂ = 4/3 ([JFA], [JFA-E])'),
      ('amop', 'Almost minimal projections'), ('foursix', 'Π(4, 6) = 5/3 ([JFA], [JFA-E])'),
      ('eucl', 'λ(ℓ₂ⁿ): Grünbaum, Rutovitz'), ('grun', 'Grünbaum (1960)'), ('rudin', 'Rudin (1962)'),
      ('stab', 'Stabilization ([KMMP])'),
      ('compl', 'Complementary dimensions ([DL26])')]
def branch_of(mod):
    m = mod.replace('ProjectionConstants.', '')
    if m.startswith(('ForMathlib', 'Matrix')) or m in ('Basic', 'Linfty', 'L1', 'Reduction'):
        return 'found'
    if m == 'Invariant.Rudin' or m.startswith('Fourier'): return 'rudin'
    if m == 'Injective' or m.startswith('Invariant'): return 'grun'
    if m.startswith('ChalmersLewicki'): return 'cl'
    if m in ('Bounds.Welch', 'Bounds.FrameBound') or m.startswith('Complementary'): return 'compl'
    if m.startswith('Bounds') or m in ('Quasimaximal', 'Values'): return 'dl'
    if m.startswith('ETF'): return 'etf'
    if m.startswith('GrunbaumConjecture'): return 'jfa'
    if m.startswith('AlmostMinimal'): return 'amop'
    if m.startswith('FourSix'): return 'foursix'
    if m.startswith('Euclidean'): return 'eucl'
    if m.startswith('Stabilization'): return 'stab'
    if m == 'MainResults': return 'main'
    raise ValueError(mod)
for n in nodes: n['branch'] = branch_of(n['module'])
users = collections.defaultdict(set)
for n in nodes:
    for d in n['deps']:
        if d in byname and d != n['name']: users[d].add(n['name'])
parent = {}
for b, _ in BR:
    members = [n['name'] for n in nodes if n['branch'] == b]
    mset = set(members)
    # entry points: used from outside the branch, or unused
    entries = [m for m in members if not users[m] or any(u not in mset for u in users[m])]
    # keep only entries that are not used inside the branch? (maximal ones)
    top = [m for m in entries if not any(u in mset for u in users[m])]
    # BFS from the top nodes (not used inside the branch) following deps inside the branch
    dist = {}
    q = deque()
    # sort tops by module order and line for determinism
    top.sort(key=lambda m: (byname[m]['module'], byname[m]['line']))
    for t in top:
        dist[t] = 0; parent[t] = 'hub:' + b; q.append(t)
    while q:
        u = q.popleft()
        # deps of u inside the branch, in source order
        ds = sorted([d for d in byname[u]['deps'] if d in mset and d != u],
                    key=lambda m: (byname[m]['module'], byname[m]['line']))
        for d in ds:
            if d not in dist:
                dist[d] = dist[u] + 1; parent[d] = u; q.append(d)
    missing = [m for m in members if m not in dist]
    for m in missing: parent[m] = 'hub:' + b
children = collections.defaultdict(list)
for k, p in parent.items(): children[p].append(k)
import functools
@functools.lru_cache(None)
def size(x): return 1 + sum(size(c) for c in children[x])
def short(name):
    for pre in ('ProjectionConstants.',):
        if name.startswith(pre): return name[len(pre):]
    return name
def firstsent(doc):
    doc = ' '.join(doc.split())
    return doc[:420]
def build(x):
    n = byname[x]
    kids = sorted(children[x], key=lambda c: (byname[c]['module'], byname[c]['line']))
    d = {'n': short(x), 'f': n['module'].replace('ProjectionConstants.', ''), 'l': n['line'], 'k': n['kind'][0], 'd': firstsent(n['doc'])}
    if kids: d['c'] = [build(c) for c in kids]
    return d
main_nodes = [n for n in nodes if n['branch'] == 'main']
root = {'n': 'Main results', 'root': True, 'f': 'MainResults', 'l': 0, 'k': 'r',
        'd': 'The main theorems of the library, restated in elementary terms (MainResults.lean): the results of Deręgowska–Lewandowska [DL] (the formula of Chalmers and Lewicki, the bounds of König–Lewis–Lin and Bukh–Cox, λ = μ, exact values), Π₂ = 4/3 and Π(4, 6) = 5/3 from [JFA] and its erratum, almost minimal orthogonal projections [AMOP] and the (folklore) strict monotonicity of λ_ℝ(n), the stabilization λ_ℝ(r, n) = λ_ℝ(r) for n ≥ 2^r C(r+1, 2) [KMMP], complementary dimensions [DL26], the projection constants of ℓ₂ⁿ(ℝ) and ℓ₂ⁿ(ℂ) (Grünbaum, Rutovitz), Grünbaum’s projection constants of ℓ₁ⁿ and of the regular polygons, and Rudin’s averaging theorem with its applications on the circle (Lozinskiĭ–Kharshiladze λ(𝒯ₙ, C(𝕋)) = Lₙ, the growth of the Lebesgue constants, the disc algebra is not complemented).',
        'main': [{'n': short(m['name']).replace('MainResults.', ''), 'd': firstsent(m['doc']), 'l': m['line'],
                  'u': [short(d) for d in m['deps'] if d in byname and byname[d]['branch'] != 'main']}
                 for m in sorted(main_nodes, key=lambda m: m['line'])],
        'c': []}
for b, title in BR:
    kids = sorted(children['hub:' + b], key=lambda c: (byname[c]['module'], byname[c]['line']))
    root['c'].append({'n': title, 'hub': b, 'k': 'h', 'c': [build(c) for c in kids]})
json.dump(root, open(OUT / 'tree.json', 'w'), ensure_ascii=False, separators=(',', ':'))
# stats
depth = {}
def dep(x, d):
    depth[x] = d
    for c in children[x]: dep(c, d + 1)
for b, _ in BR:
    for c in children['hub:' + b]: dep(c, 2)
print(sorted(collections.Counter(depth.values()).items()))
for b, _ in BR:
    kids = sorted(children['hub:' + b], key=lambda c: -size(c))
    print(b, len(kids), [ (short(c), size(c)) for c in kids[:6]])
