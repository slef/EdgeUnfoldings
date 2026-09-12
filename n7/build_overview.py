"""Build a self-contained local seven-vertex overview and readable proof pages."""
from __future__ import annotations
import html
import itertools as it
import json
import math
from pathlib import Path
import random
import shutil
import subprocess
import networkx as nx
from n7.catalogue import face_edges, pair_audit
ROOT=Path(__file__).resolve().parent

def solve(a,b):
    a=[list(row)+[val] for row,val in zip(a,b)]
    for k in range(len(a)):
        p=max(range(k,len(a)),key=lambda i:abs(a[i][k]));a[k],a[p]=a[p],a[k]
        t=a[k][k]
        a[k]=[x/t for x in a[k]]
        for i in range(len(a)):
            if i!=k:
                t=a[i][k];a[i]=[x-t*y for x,y in zip(a[i],a[k])]
    return [r[-1] for r in a]

def distance_to_edge(p,a,b):
    dx,dy=b[0]-a[0],b[1]-a[1]
    t=max(0,min(1,((p[0]-a[0])*dx+(p[1]-a[1])*dy)/(dx*dx+dy*dy)))
    return math.hypot(p[0]-a[0]-t*dx,p[1]-a[1]-t*dy)

def graph_positions(row, cand=None):
    g=nx.Graph(row['edges']);rng=random.Random(row['atlas_index']);best=None
    excluded=set() if row['universal_vertices'] else set(row['dome_bases'][:1]) if row['dome_bases'] else set((cand or {}).get('changed_faces',[]))
    for fi,outer in enumerate(row['facets']):
        if fi in excluded:continue
        for trial in range(96):
            pos={v:(math.cos(-math.pi/2+2*math.pi*i/len(outer)),math.sin(-math.pi/2+2*math.pi*i/len(outer))) for i,v in enumerate(outer)}
            inside=[v for v in sorted(g) if v not in pos];idx={v:i for i,v in enumerate(inside)}
            a=[[0.0]*len(inside) for v in inside];bx=[0.0]*len(inside);by=bx.copy()
            for v in inside:
                i=idx[v];weights={u:(1.0 if trial==0 else math.exp(rng.uniform(-1.1,1.1))) for u in g[v]}
                a[i][i]=sum(weights.values())
                for u,w in weights.items():
                    if u in idx:a[i][idx[u]]-=w
                    else:bx[i]+=w*pos[u][0];by[i]+=w*pos[u][1]
            xs,ys=solve(a,bx),solve(a,by)
            pos.update({v:(xs[idx[v]],ys[idx[v]]) for v in inside})
            xmin,xmax=min(x for x,y in pos.values()),max(x for x,y in pos.values())
            ymin,ymax=min(y for x,y in pos.values()),max(y for x,y in pos.values())
            pos={v:(26+308*(x-xmin)/(xmax-xmin),24+214*(y-ymin)/(ymax-ymin)) for v,(x,y) in pos.items()}
            distances=[math.dist(pos[u],pos[v]) for u,v in it.combinations(g,2)]
            clearance=[distance_to_edge(pos[v],pos[a],pos[b]) for a,b in g.edges() for v in g if v not in (a,b)]
            score=min(min(distances)/2,min(clearance))
            if best is None or score>best[0]:best=(score,pos)
    return best[1]

def group(row):
    if row['universal_vertices']:return 'A'
    if row['dome_bases']:return 'B'
    if row['degree_five_cofacial_sources']:return 'C'
    if row['cofacial_sources']:return 'D'
    return 'E'

def candidate(row):
    if row['universal_vertices']:
        return next(c for c in row['cofacial_candidates'] if c['source']==row['universal_vertices'][0])
    if row['dome_bases']:
        base=row['dome_bases'][0];keep=face_edges(row['facets'][base])
        cut=[e for e in row['edges'] if tuple(e) not in keep]
        return {'source':None,'cut':cut,'changed_faces':[], 'audit':pair_audit(nx.Graph(row['edges']),row['facets'],cut)}
    if row['degree_five_cofacial_sources']:
        return next(c for c in row['cofacial_candidates'] if c['source'] in row['degree_five_cofacial_sources'])
    if row['cofacial_candidates']:return row['cofacial_candidates'][0]
    return dict(row['all_tree_scan']['best'],source=None,changed_faces=[])

def svg_graph(row, cand):
    pos=graph_positions(row,cand);cut={tuple(e) for e in cand['cut']}
    pieces=[f'<svg viewBox="0 0 360 265" role="img" aria-label="Planar graph {row["id"]}, seven labelled vertices"><title>{row["id"]}: seven-vertex graph</title>']
    fillfaces=[] if row['universal_vertices'] else [(i,'#e4f1eb') for i in row['dome_bases'][:1]] if row['dome_bases'] else [(i,'#fff0d6') for i in cand.get('changed_faces',[])]
    for i,color in fillfaces:
        pts=' '.join(f'{pos[v][0]:.2f},{pos[v][1]:.2f}' for v in row['facets'][i])
        pieces.append(f'<polygon points="{pts}" fill="{color}"/>')
    for a,b in row['edges']:
        x,y=pos[a];xx,yy=pos[b];flag='true' if tuple((a,b)) in cut else 'false'
        pieces.append(f'<line x1="{x:.2f}" y1="{y:.2f}" x2="{xx:.2f}" y2="{yy:.2f}" data-cut="{flag}"/>')
    for v,(x,y) in sorted(pos.items()):
        cl='source' if v==cand.get('source') else ''
        pieces.append(f'<g class="{cl}"><circle cx="{x:.2f}" cy="{y:.2f}" r="11.5"/><text x="{x:.2f}" y="{y+3.8:.2f}">{v}</text></g>')
    pieces.append('</svg>');return ''.join(pieces)

def names(row):
    return {875:'Dome with a pentagonal base',992:'Pentagonal base + one extra triangle',1008:'Hexagonal pyramid',1205:'Capped octahedron',1212:'Pentagonal bipyramid',1167:'Core with one quadrilateral',1104:'Core with two quadrilaterals'}.get(row['atlas_index'],f'{row["edge_count"]} edges · {row["face_count"]} faces')

def card(row):
    cand=candidate(row);a=cand['audit'];r=len(a['unresolved']);gid=group(row)
    theorem='Edge-star theorem' if gid=='A' else 'Dome theorem' if gid=='B' else 'One movable quadrilateral' if gid=='C' else 'Movable-face reduction' if gid=='D' else 'Core graph: open'
    proof='ARGUMENTS.html#edge-star' if gid=='A' else 'ARGUMENTS.html#dome' if gid=='B' else 'ARGUMENTS.html#cofacial-core' if gid in 'CD' else 'ARGUMENTS.html#core-graphs'
    status='Solved' if row['status']=='solved' else 'Open'
    detail='Whole graph covered for every convex realization.' if status=='Solved' else f'<strong>{a["safe_count"]}/{a["total_pairs"]} pairs settled</strong> for the candidate shown; {r} unresolved.'
    a992=row['atlas_index']==992
    if a992:
        proof='A992_BASE_EDGES.html';theorem='A second R0 obligation has a proved subcase'
        detail='<strong>One complete obligation; a second now has a proved subcase.</strong> With converging or parallel hinges in R0, Right has only E/Q left to settle. The divergent case and R6 retain open obligations. <a href="A992.html#next-lemma">See the exact remaining cases →</a>'
    facets=''.join(f'<li><b>F{i}</b> = '+ '–'.join(map(str,f))+'</li>' for i,f in enumerate(row['facets']))
    residual=''.join('<li>F'+str(x['faces'][0])+' / F'+str(x['faces'][1])+' <span>via '+ ' → '.join('F'+str(i) for i in x['path'])+'</span></li>' for x in a['unresolved']) or '<li>None under the stated theorem.</li>'
    cuts=', '.join(f'{u}–{v}' for u,v in cand['cut'])
    source=f'Source vertex {cand["source"]}. ' if cand.get('source') is not None else ''
    return f'''<article class="graph-card {row['status']}" id="{row['id']}" data-status="{row['status']}" data-group="{gid}">
<div class="card-heading"><a href="#{row['id']}">{row['id']}</a><span class="badge {row['status']}">{status}</span></div>
<h3>{names(row)}</h3>{svg_graph(row,cand)}<p class="rule"><a href="{proof}">{theorem} ↗</a></p>
<p class="pair-count">{detail}</p><p class="degrees">Degrees: {', '.join(map(str,row['degrees']))}</p>
<details><summary>Candidate cuts and remaining pairs</summary><div class="card-detail"><p>{source}Cut {cuts}.</p><p>Green shading marks a dome base; amber shading marks movable polygons. Blue marks the source.</p>
<h4>{"Certified failing pair in the original candidate" if a992 else "Still needs a proof"}</h4><ul>{residual}</ul><h4>Original faces</h4><ol class="facets">{facets}</ol><p class="small">{"This original candidate has a certified failure. A different attachment is needed; see the dedicated case page." if a992 else "These are pair obligations for this one tree. Missing witnesses do not mean actual overlap. The numbers do not measure how much of the shape space is covered."}</p></div></details></article>'''

GROUPS=[('A','Nine complete cases: cut an edge star','A vertex joined to all six others gives a shortest-path star made entirely of original edges.'),
('B','One more complete case: unfold a dome','The hexagonal pyramid is already counted above. This is the other graph with a face adjacent to every other face.'),
('C','Eleven open cases: one movable quadrilateral','A degree-five source sees its sole nonneighbor through one face. The rest of the net inherits a known nonoverlapping placement.'),
('D','Nine open cases: move a few polygons','A source shares a face with every vertex. The same comparison fixes the rest of the net; these candidates still have residual pairs.'),
('E','Four core graphs','The two graphs with quadrilaterals triangulate to the pentagonal bipyramid or the capped octahedron. Any inserted diagonal must remain uncut.')]

def build():
    data=json.loads((ROOT/'results/catalogue.json').read_text());patterns=json.loads((ROOT/'results/patch-patterns.json').read_text())
    nav=''.join(f'<a href="#group-{k}"><span>{k}</span>{sum(group(r)==k for r in data["graphs"])} graph types</a>' for k,title,desc in GROUPS)
    sections=''.join(f'<section id="group-{k}" class="graph-group" data-group="{k}"><div class="section-heading"><span class="letter">{k}</span><div><h2>{title}</h2><p>{desc}</p></div></div><div class="graph-grid">'+''.join(card(r) for r in data['graphs'] if group(r)==k)+'</div></section>' for k,title,desc in GROUPS)
    patternrows=''.join(f'<tr><td><code>{p["representative"]}</code></td><td>{p["inward_count"]}</td><td>{p["labelled_count"]}</td><td>'+ (f'<a href="BIPYRAMID_PATCHES.html#theorem-{p["theorem"].lower()}">Proved: {p["theorem"]}</a>' if p['theorem'] else '<a href="BIPYRAMID_PATCHES.html#theorem-gap">Open; half-turn part proved</a>' if p['extra_partial_theorem'] else 'Open')+'</td></tr>' for p in patterns['classes'])
    page=f'''<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Seven vertices — unfolding case map</title><link rel="stylesheet" href="style.css"></head><body>
<div class="layout"><aside><a class="brand" href="#top">Edge unfoldings<span>Seven-vertex notebook</span></a><nav aria-label="Page sections"><a href="#progress">Current results</a><a href="#case-map">All 34 graphs</a>{nav}<a href="#bipyramid">Bipyramid patterns</a><a href="#next">Next proof targets</a><a href="#history">Progress history</a></nav><div class="sidebar-note">Separate from the six-vertex proof and its Lean formalization.<a href="ARGUMENTS.html">Read the arguments ↗</a></div></aside>
<main id="top"><header><p class="eyebrow">RESEARCH NOTEBOOK · 12 SEPTEMBER 2026</p><h1>Seven vertices</h1><p class="lead">A complete graph map, with the first proof reductions.</p><p>Each graph stands for every convex polytope with that edge structure. A green status means its entire graph case is covered; amber means an existence proof is still missing.</p></header>
<section id="progress"><div class="totals"><div><strong>34</strong><span>graph types, all enumerated</span></div><div class="green"><strong>10</strong><span>covered by established theorems</span></div><div class="amber"><strong>24</strong><span>whole graph cases still open</span></div></div>
<div class="progress-track" role="img" aria-label="Ten of thirty-four graph types covered; twenty-four open"><span></span></div><p class="small">Graph counts, not percentages of shapes or proof effort. No numerical experiment is treated as a proof.</p>
<div class="finding"><h2>New: one pair remains in a further A992 family</h2><p>Right now avoids both 135 and 235 in R0 when its two relevant base hinges converge or are parallel. <strong>Only E/Q remains in that family.</strong> The new proof extends the base to a triangle and applies the obtuse-petal lemma. Divergent hinges still need E/235, and the three R6 obligations remain open. The whole graph is still open.</p><p><a href="A992_BASE_EDGES.html">See the three hinge cases and read the proof →</a></p></div><div class="finding"><h2>What carries over already</h2><p>The edge-star and dome arguments settle ten types. A generalization of the six-vertex star comparison gives <strong>a known safe core in twenty more</strong>: any overlap must involve a small set of movable faces. Twelve displayed candidates move one face, seven move two, and one moves three. Four graphs need a different starting point.</p><p>For the pentagonal bipyramid, three of fifteen necessary patch-pattern classes now have conditional existence proofs. The whole graph remains open.</p><a href="ARGUMENTS.html">Read the separate seven-vertex arguments →</a></div></section>
<section id="case-map"><h2>The complete decomposition</h2><p>The list includes triangular and nontriangular faces. Graphs with identical degree lists can still be different cases.</p><div class="case-map">{''.join(f'<a href="#group-{k}"><b>{k}</b><strong>{sum(group(r)==k for r in data["graphs"])}</strong><span>'+ {'A':'Universal vertex','B':'Additional dome','C':'One quadrilateral','D':'Other movable faces','E':'Core graphs'}[k]+'</span></a>' for k,t,d in GROUPS)}</div>
<div class="toolbar"><div class="filters" aria-label="Filter graph status"><button data-filter="all" aria-pressed="true">All graphs</button><button data-filter="open" aria-pressed="false">Open</button><button data-filter="solved" aria-pressed="false">Solved</button></div><label><input type="checkbox" id="show-cuts"> Show candidate cuts in red</label></div><p class="small" id="visible-count" aria-live="polite">Showing all 34 graphs.</p><p class="small">Diagrams show planar graphs, not metric shapes or 3D models. Vertex numbers agree with the cut trees and face lists.</p></section>
{sections}
<section id="bipyramid"><h2>A closer look at the pentagonal bipyramid</h2><p>Flatten the ten triangles into five two-face patches. <b>C</b> means a convex patch; <b>B</b> and <b>F</b> mean an inward corner at its first or second equator vertex. These describe shapes inside one graph case.</p>
<div class="proof-list"><a href="BIPYRAMID_PATCHES.html#theorem-c"><b>All five patches convex</b><span>Every slit works at either pole.</span></a><a href="BIPYRAMID_PATCHES.html#theorem-one"><b>Exactly one inward patch</b><span>Choose between the two poles; no curvature order is needed.</span></a><a href="BIPYRAMID_PATCHES.html#theorem-toward"><b>Two inward patches facing one convex patch</b><span>An exact angle identity selects a safe pole.</span></a><a href="BIPYRAMID_PATCHES.html#lemma-l7"><b>Lemma L: a local extension</b><span>The same three local pairs are safe under an explicit curvature threshold.</span></a></div>
<p><strong>3 of 15 symbolic classes covered.</strong> Twelve retain open parts. The list is a necessary partition; it does not assert that every remaining symbolic pattern is realizable.</p><details><summary>See all 15 pattern classes and their status</summary><div class="table-wrap"><table><thead><tr><th>Pattern</th><th>Inward patches</th><th>Labelled versions</th><th>Whole conditional family</th></tr></thead><tbody>{patternrows}</tbody></table></div></details><p><a href="BIPYRAMID_PATCHES.html">Read the patch proofs and what remains →</a></p></section>
<section id="next"><h2>Where I would push next</h2><div class="next-grid"><div><span class="eyebrow">SMALLEST RESIDUAL TARGET</span><h3><a href="A992.html#next-lemma">N7-A992: choose between two attachments</a></h3><p>If the original placement fails, move only triangle 036. One R0 pair implication is proved throughout; a second is proved for converging and parallel hinges. E/Q, divergent E/235, and the three R6 implications remain open. The first obstruction localizes to a five-vertex pyramid and can now occur only in two explicit curvature regimes.</p></div><div><span class="eyebrow">MAIN STRUCTURAL TARGET</span><h3><a href="#N7-A1212">The five-patch bipyramid</a></h3><p>Start with the remaining two-inward-patch patterns. This most closely extends the octahedron methods, while exposing exactly where the four-patch proof stops working.</p></div></div><p>The capped octahedron needs a cap-attachment argument. A successful net for the six old vertices does not automatically stay safe after adding the seventh.</p></section>
<section id="history"><h2>Progress history</h2><details open><summary>12 September · A992: E/235 with converging or parallel hinges</summary><div class="history-body"><ul><li>Extended the two base hinges to a new fan center and proved the auxiliary hull is convex.</li><li>Applied the obtuse-petal theorem to larger triangles containing the actual faces.</li><li>Included parallel hinges by continuity with the petal angle fixed.</li><li>Certified exact examples with actual Left overlap in both new branches.</li><li>Only E/Q remains in this R0 family; divergent E/235 and all three R6 obligations remain open.</li><li>One of six cells completely proved; a second partially proved. Whole-graph count unchanged.</li></ul><p><a href="A992_BASE_EDGES.html">Read the proof and exact remaining cases →</a></p></div></details><details><summary>12 September · A992: E/135 is proved safe in R0</summary><div class="history-body"><ul><li>Localized the pair to a convex triangular bipyramid on five vertices.</li><li>Proved the stronger obtuse-petal statement: an angle of at least 90° at 0 suffices.</li><li>Closed the narrow-fan branch by trapping an auxiliary face and comparing equal edge lengths.</li><li>Verified the contradiction identity with exact integer coefficients.</li><li>One of six conditional repair statements closed; five remain open. Whole-graph count unchanged.</li></ul><p><a href="A992_R0.html">Read the proof and its precise scope →</a></p></div></details><details><summary>12 September · A992: a proved cone split of the remaining obstruction</summary><div class="history-body"><ul><li>Convex two-face patches settled; inward patches settled under explicit angle and curvature inequalities.</li><li>Every possible Left failure is confined to R0 or R6, which force opposite sides of the curvature-180° threshold at vertex 4.</li><li>New exact R6 example establishes that the sharp-4 regime is real and that Right repairs that example.</li><li>Three repair implications remain open in each regime; the whole-graph count remains 10 covered and 24 open.</li></ul><p><a href="A992_CONES.html">Read the full proof and the exact scope →</a></p></div></details><details><summary>12 September · A992: certified failures and a two-attachment conjecture</summary><div class="history-body"><ul><li>Original fixed rule refuted on an exact 11-parameter family; moving triangle 036 repairs the same family.</li><li>Both source-3 hinge choices can fail together; the longer-edge shortcut is also refuted exactly.</li><li>Initial obstruction localized to five vertices and seven metric parameters.</li><li>Three conditional pair implications identified for a possible complete proof.</li><li>Whole-graph count remains 10 covered and 24 open.</li></ul><p><a href="A992.html">Read the case, with figures, 3D, and certificates →</a></p></div></details><details><summary>12 September · Initial census and transferred lemmas</summary><div class="history-body"><ul><li>All 34 graphs enumerated; independently matched against plantri.</li><li>10 full graph cases covered; 24 open.</li><li>20 open types given a cofacial-core reduction and explicit residual pairs.</li><li>25,942 cut trees checked for the two elementary pair reductions.</li><li>Three complete conditional bipyramid patterns, one further curvature-restricted family, and a local Lemma L extension written.</li><li>A rational interval certificate covers a 21-coordinate open neighborhood of an acute bipyramid.</li></ul><p>New arguments are under self-review. Independent mathematical review and formal verification remain separate tasks.</p></div></details></section>
<footer><a href="ARGUMENTS.html">Full arguments</a><a href="BIPYRAMID_PATCHES.html">Bipyramid proofs</a><a href="results/catalogue.json">Graph data</a><a href="results/validation.json">Finite checks</a><a href="results/plantri-comparison.json">Independent census comparison</a><a href="results/acute-bipyramid-box.json">Exact example family</a><p>This notebook contains only the seven-vertex investigation. The shared six-vertex files are unchanged.</p></footer></main></div><script src="overview.js"></script></body></html>'''
    (ROOT/'index.html').write_text(page)
    pandoc=shutil.which('pandoc')
    if not pandoc:raise RuntimeError('pandoc is needed to render the mathematical reading pages')
    for name in ('ARGUMENTS','BIPYRAMID_PATCHES','A992','A992_CONES','A992_R0','A992_BASE_EDGES'):
        subprocess.run([pandoc,str(ROOT/(name+'.md')),'--standalone','--mathml','--css=style.css','--metadata','title='+{'ARGUMENTS':'Seven-vertex arguments','BIPYRAMID_PATCHES':'Five-patch bipyramid proofs','A992':'N7-A992: two attachments','A992_CONES':'N7-A992: the cone proof','A992_R0':'N7-A992: the R0 repair lemma','A992_BASE_EDGES':'N7-A992: converging and parallel hinges'}[name], '-o',str(ROOT/(name+'.html'))],check=True)
        p=ROOT/(name+'.html');s=p.read_text().replace('<body>','<body class="reading"><p class="back"><a href="index.html">← Seven-vertex overview</a></p>');p.write_text(s)
    print('Built overview with',len(data['graphs']),'graphs and six mathematical reading pages.')

if __name__=='__main__':build()
