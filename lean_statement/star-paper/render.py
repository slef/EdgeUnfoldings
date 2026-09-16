from pathlib import Path
import json,html,re
from math_typesetting import MathTypesetter
site=Path(__file__).resolve().parent; dist=site/'dist'
P=json.loads((site/'paper.json').read_text()); A=json.loads((site/'annotations.json').read_text()); F=json.loads((site/'figures.json').read_text())
ann={b:a for a in A for b in a['blocks']}
def annotation_texts(value):
    if isinstance(value,str):return [value]
    if isinstance(value,list):return [text for item in value for text in annotation_texts(item)]
    if isinstance(value,dict):return annotation_texts(list(value.values()))
    return []
math_typesetter=MathTypesetter([b['text'] for b in P]+list(F.values())+annotation_texts(A)+[r'\(n \le 6\)',r'\(\frac{\pi}{2}\)'])
esc=html.escape
D=json.loads((dist/'data.js').read_text().removeprefix('window.PAPER_DATA = ').rstrip(';\n'))
H=json.loads((site/'hover-index.json').read_text())
V=json.loads((site/'verification.json').read_text())
assert V['revision']==D['revision'] and V['result']=='passed'
assert V['declarations']==len(D['declarations'])
assert V['theorems']==sum(d['kind']=='theorem' for d in D['declarations'].values())
coverage={'proved':'Formalized','restricted':'Partial coverage','defined':'Formalized','missing':'Correspondence incomplete','outside':'Not formalized here'}
work_labels={'complete':'Complete component','todo':'Still to do','beyond':'Outside milestone'}
by_id={a['id']:a for a in A}
definition_blocks={'definition-1','definition-2','geodesic','curve-images','wedge-definition'}
primary={
    'main':'UniversalStarEmbedding:universal_star_embedding',
    'budget':'SmallPolyhedronSourceBudget:universal_half_source_angle_sum_lt_pi',
    'leaf':'SmallPolyhedronUniqueRouteLeaves:small_cofacial_source_original_is_leaf',
    'tree':'SmallPolyhedronCutTree:small_exists_regular_cut_tree',
    'kite-partition':'CutEdgeTriangles:CutEdgeTriangles',
    'path':'CutTreeChainSeparation:end_kites_nonoverlap',
    'invariant':'ExpandingRegionChains:finite_chain_separation',
    'rotation':'WedgeRotation:rotate_arms',
}
names={
    'universal_star_embedding':'The completed universal-source star theorem',
    'hasEdgeUnfolding_of_universal_vertex':'Its whole-face edge-unfolding consequence',
    'universal_half_source_angle_sum_lt_pi':'The complete source-angle budget',
    'small_cofacial_source_original_is_leaf':'Every original cut vertex is a leaf',
    'ConvexPolyhedron':'Convex polyhedron', 'ConvexPolyhedron.body':'Its solid body',
    'starCuts':'The star cuts', 'UncutSurface':'The surface after cutting',
    'multipleRouteLocus':'Points with multiple shortest routes', 'cutSet':'The cut set',
    'EmbeddedCutGraph':'An embedded cut graph', 'CutLocusTree':'The cut tree',
    'CutEdgeTriangles':'Two radial triangles', 'CutEdgeMetricModel':'The metric kite',
    'sourceAngle':'Source angle', 'totalAngle':'Total surface angle',
    'polarRegion':'The W-wedge', 'region':'Cartesian wedge coordinates',
    'gapKite':'The planar kite', 'cofacial_star_embedding':'The checked star-embedding theorem',
    'small_exists_regular_cut_tree':'Existence of the small-polyhedron cut tree',
    'finite_chain_separation':'The finite induction', 'RegionStep':'One induction step',
    'rotate_arms':'Rotate the wedge arms', 'move_root':'Move the wedge center',
    'initial_kite_in_wedge':'Enclose the first kite',
}
def lean_code(key, field):
    """Keep the exact excerpt text; add only contextual definition controls."""
    d=D['declarations'][key]; text=d[field]
    # The declaration being introduced is already fully visible here.
    head=re.match(r'(?:noncomputable\s+)?'+re.escape(d['kind'])+r'\s+('+re.escape(d['name'])+r')(?=\s|:)', text) if field=='signature' else None
    assert field!='signature' or head, key
    introductions=[head.span(1)] if head else []
    if field=='signature' and d['kind']=='structure':
        introductions.extend(m.span(1) for m in re.finditer(r"^  ([^\W\d][\w']*)[ \t]*:",text,re.M))
    if field=='signature' and d['kind']=='inductive':
        introductions.extend(m.span(1) for m in re.finditer(r"^  \| ([^\W\d][\w']*)",text,re.M))
    pieces=[]; cursor=0
    for token in H['references'][key][field]:
        start,end=token['start'],token['end']
        assert cursor <= start < end <= len(text)
        pieces.append(esc(text[cursor:start]))
        if any(left<=start<end<=right for left,right in introductions):
            pieces.append(esc(text[start:end]))
            cursor=end
            continue
        pieces.append(f'<button type="button" class="lean-symbol" data-symbol="{token["symbol"]}" aria-label="Definition of {esc(text[start:end])}" aria-haspopup="dialog" aria-controls="lean-hover" aria-expanded="false">{esc(text[start:end])}</button>')
        cursor=end
    pieces.append(esc(text[cursor:]))
    return ''.join(pieces)

def declaration(ref, block_id, opened=False):
    key=':'.join(ref); d=D['declarations'][key]
    anchor='decl-'+block_id+'-'+key.replace(':','-').replace('.','-')
    path=D['sources'][d['module']]['path']; end_line=d['line']+len(d['signature'].splitlines())-1
    theorem=d['kind']=='theorem'
    kind='Theorem' if theorem else 'Definition'
    state='Proof checked' if theorem else 'Formalized'
    context=(f'<details class="context"><summary>Hypotheses and surrounding Lean context</summary><pre data-excerpt="{key}:context"><code>{lean_code(key,"context")}</code></pre></details>' if d['context'] else '')
    return (f'<details class="declaration" id="{anchor}" data-source-path="{esc(path)}" data-source-start="{d["line"]}" data-source-end="{end_line}" {"open" if opened else ""}>'
      f'<summary><span class="declaration-title">{esc(names.get(d["name"],d["name"]))}</span>'
      f'<span class="declaration-meta">{kind} · {state}</span></summary>'
      f'<div class="decl-content"><p class="code-path">{esc(d["qualified"])}</p>'
      f'{context}<pre class="signature" data-excerpt="{key}:signature"><code>{lean_code(key,"signature")}</code></pre>'
      f'<div class="source-links"><a href="sources/{d["module"]}.html#L{d["line"]}" target="_blank" rel="noopener">Full source{" & proof" if theorem else ""} ↗</a>'
      f'<a href="sources/{d["module"]}.lean" download>Download Lean</a></div>'
      f'<p class="fine">{"Checked under the displayed statement’s hypotheses, including its surrounding context. This does not assert the paper’s full scope." if theorem else "This defines a mathematical object; it makes no claim that a theorem has been proved."}</p></div></details>')
def work_badge(a):
    state=a['work']['status']
    return f'<span class="work-status {state}">{work_labels[state]}</span>'

def work_details(a):
    work=a['work']
    result=f'<div class="work-note"><strong>{work_labels[work["status"]]}:</strong> {typeset(work["reason"])}</div>'
    if work['depends_on']:
        links=[f'<a href="#{by_id[key]["blocks"][0]}">{esc(by_id[key]["title"])}</a>' for key in work['depends_on']]
        result+='<p class="work-dependencies">Related work: '+ ' · '.join(links)+'</p>'
    return result

def remaining_details(a):
    result=''
    for field,label,style in [('remaining','Remaining for this milestone','gap'),('beyond','Beyond this milestone — not claimed complete','beyond-note')]:
        items=a['work'][field]
        if items:
            result+=f'<div class="{style}"><strong>{label}</strong><ul>'+''.join(f'<li>{typeset(item)}</li>' for item in items)+'</ul></div>'
    return result

def inline_note(b,a):
    is_definition=b['id'] in definition_blocks
    label='Definitions' if is_definition else ('Statement' if b['kind']=='claim' else 'Formalization')
    status=coverage[a['status']]
    refs=list(a['refs'])
    if a['id'] in primary:
        refs.sort(key=lambda r: ':'.join(r)!=primary[a['id']])
    proof=(f'<div><dt>Proof status</dt><dd>{esc(a["proof"])}</dd></div>' if not is_definition else '')
    gap=remaining_details(a)
    steps=('<h4>How the proof is split</h4><ol class="steps">'+''.join(f'<li>{typeset(t)}</li>' for t in a['steps'])+'</ol>' if a['steps'] else '')
    explanation=f'<details class="correspondence"><summary>Explanation, scope and remaining work</summary><p>{typeset(a["note"])}</p>{steps}{gap}</details>'
    code=(''.join(declaration(r, b["id"], i==0) for i,r in enumerate(refs)) if refs else '<p class="no-declaration">There is no matching Lean declaration yet.</p>')
    return (f'<details class="lean-note" id="lean-{b["id"]}" data-annotation="{a["id"]}">'
      f'<summary><img class="lean-logo" src="assets/lean-logo.svg" alt="Lean"><span>{label}</span>{work_badge(a)}<span class="coverage paper-coverage">Paper: {status.lower()}</span><span class="disclosure" aria-hidden="true">+</span></summary>'
      f'<div class="lean-content">{work_details(a)}<dl class="status-grid"><div><dt>Formalization</dt><dd>{esc(a["statement"])}</dd></div>{proof}</dl>'
      f'<p class="scope"><strong>Scope of this correspondence:</strong> {esc(a["scope"])}</p>'
      f'{explanation}<h4>{"Existing components" if a["status"]=="missing" else "Lean definitions" if is_definition else "Related Lean declarations"}</h4>{code}</div></details>')
def figure(n):
    return f'<figure id="figure-{n}" class="figure {"fig-small" if n in (3,5) else ""}"><a href="assets/figure-{n}.png" target="_blank" aria-label="Enlarge original Figure {n}"><img src="assets/figure-{n}.png" alt="Original Figure {n} from the paper" aria-describedby="caption-{n}" loading="lazy"></a><figcaption id="caption-{n}"><strong>Fig. {n}</strong> {typeset(F[str(n)])}</figcaption></figure>'
def prose(t):
    t=esc(t)
    t=re.sub(r'\s+([,.])',r'\1',t)
    t=re.sub(r'^(Definition \d|Lemma \d|Theorem \d|Proof)',r'<span class="claim-label">\1</span>',t)
    t=re.sub(r'Fig\. ([2345])([ab]?)',r'<a href="#figure-\1">Fig. \1\2</a>',t)
    t=t.replace('Sect. 2','<a href="#section-2">Sect. 2</a>')
    t=re.sub(r'\[(1|3|4|9|12|13)([^\]]*)\]',r'<a href="#references">[\1\2]</a>',t)
    return t
def typeset(t):
    return math_typesetter.render(t, prose)

sections={'1.1':'Preliminaries and Definitions for the Point Star Unfolding','1.2':'Preliminaries and Definitions for the Geodesic Star Unfolding','2':'New Proof for the Point Star Unfolding'}
article=''
for section,title in sections.items():
    article+=f'<section class="paper-section" id="section-{section.replace(".","-")}"><div class="section-head"><span class="section-no">{section}</span><h2>{title}</h2></div>'
    if section=='1.1': article+=figure(2)
    if section=='1.2':article+='<p class="section-note">Lean annotation: included for completeness; curve-source unfolding is outside this point-star formalization. <a href="#section-2">Continue to the point proof →</a></p>'
    for b in (b for b in P if b['section']==section):
        a=ann.get(b['id'])
        note=inline_note(b,a) if a else ''
        article+=f'<div class="passage {b["kind"]}" id="{b["id"]}"><p class="paper-text">{typeset(b["text"])}</p>{note}</div>'
        if b['id']=='lemma-2-proof':article+=figure(3)+figure(4)
        if b['id']=='empty-regions':article+=figure(5)
    article+='</section>'
template='''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><meta name="description" content="Kiazyk and Lubiw’s point star-unfolding proof, Sections 1.1–2, annotated with exact Lean statements, checked scope, and remaining obligations."><title>Star Unfolding — Paper & Lean</title><link rel="stylesheet" href="assets/katex/katex.min.css"><link rel="stylesheet" href="style.css"><script src="hovers.js" defer></script><script src="app.js" defer></script></head>
<body><a class="skip" href="#paper">Skip to paper</a><header class="topbar"><a class="brand" href="#paper">Star unfolding / Lean</a><nav class="topnav" aria-label="Paper navigation"><a href="#section-1-1">§1.1</a><a href="#section-1-2">§1.2</a><a href="#section-2">§2 · Proof</a><a href="#proof-map-section">Proof map</a><label class="toggle"><input id="annotations-toggle" type="checkbox" checked>Lean annotations</label></nav></header>
<main class="workspace"><article class="paper" id="paper"><header class="paper-header"><p class="eyebrow">KIAZYK–LUBIW · SECTIONS 1.1–2</p><h1>Star Unfolding from<br>a Geodesic Curve</h1><p class="authors">Stephen Kiazyk · Anna Lubiw</p><p class="citation"><i>Discrete & Computational Geometry</i> 56, 1018–1036 (2016).<br><a href="https://doi.org/10.1007/s00454-016-9795-1" target="_blank" rel="noopener">Journal article ↗</a> · excerpt pp. 1021–1026</p><p class="intro-note">Open a Lean insert beneath a passage to read its formalization in place. Definitions and proof status are labelled separately.</p><p class="hover-help">Hover over a name in the Lean code to see its type, definition and source. Click to keep the card open; keyboard users can Tab to a name and press Enter to explore its card. Escape closes it. Follow “View definition on this page” to open the corresponding insert; its full-source link remains there.</p></header>
<div class="checkpoint"><strong><!--MILESTONE-STATE--></strong><p>The scope is six vertices, triangular or quadrilateral faces, and a source vertex adjacent to every other vertex. The theorem constructs the planar development from the solid, including the angle budget and nonoverlap. The unrestricted paper theorem, for arbitrary sources and polyhedra, remains unfinished.</p><a href="#theorem-1">Read the checked theorem</a> · <a href="#source-budget">Source-angle proof</a> · <a href="#lemma-3-leaf">Leaf proof</a></div>
<div class="milestone"><strong>Work status refers to this universal-source milestone.</strong><p><!--WORK-COUNTS-->. “Outside milestone” means a broader paper claim remains unformalized but is not needed by this completed proof. “Partial coverage” describes that difference in scope; it does not by itself mean work is left.</p></div>
<details class="legend"><summary>How to read the two status labels</summary><p>The first label answers whether work remains for the milestone above:</p><ul><li><span class="work-status complete">Complete component</span> The needed definition or conditional lemma is checked. The related-work links identify the components supplying its inputs.</li><li><span class="work-status todo">Still to do</span> A required construction, proof or transfer remains unfinished.</li><li><span class="work-status beyond">Outside milestone</span> Not required for this milestone. This does not mean the paper claim is proved or that every broader extension is abandoned.</li></ul><p>The second label describes the correspondence with the paper: <strong>formalized</strong>, <strong>partial coverage</strong>, <strong>correspondence incomplete</strong> or <strong>not formalized here</strong>. For example, a cut-tree result may be <strong>Complete component · Paper: partial coverage</strong>: it is sufficient for the milestone despite the paper’s greater generality.</p><p>Inside an insert, <strong>Definition · Formalized</strong> identifies a formal object; <strong>Theorem · Proof checked</strong> identifies a checked theorem under its displayed hypotheses. No displayed declaration contains a <code>sorry</code>. Missing statements and broader proof obligations remain identified separately.</p></details>
<!--ARTICLE-->
<p class="end-mark">End of Section 2. Sections 3 onward are not reproduced.</p>
<section class="map" id="proof-map-section"><h2>The proof, with its Lean decomposition</h2><p>Navigate to a passage or inspect its formal counterpart. Work status is relative to the universal-source milestone; paper coverage is separate. These groups are not a percentage of proof completion.</p><ol id="proof-map"><!--PROOFMAP--></ol></section>
<section class="editorial" id="editorial"><h2>Source and verification notes</h2><p>This reading edition is based on the PDF supplied by the user. The paper’s wording, theorem numbering and mathematical claims are retained, with line breaks and notation normalized. Figures 2–5 are cropped from that PDF and moved next to the relevant text. Annotation labels and all material in the Lean inserts are editorial additions.</p><p>The wording “surface area” and the missing <!--HALF-PI--> offset in the root-movement paragraph are retained from the paper; the adjacent annotations explain them. References to Figure 6 and later sections are original forward references outside this excerpt.</p><details><summary>Compare with the original pages</summary><div class="page-links"><a href="assets/page-1021.png" target="_blank">1021</a><a href="assets/page-1022.png" target="_blank">1022</a><a href="assets/page-1023.png" target="_blank">1023</a><a href="assets/page-1024.png" target="_blank">1024</a><a href="assets/page-1025.png" target="_blank">1025</a><a href="assets/page-1026.png" target="_blank">1026 (end of §2)</a></div></details>
<details><summary>Lean snapshot and audit</summary><p>Proof snapshot: <code><!--REVISION--></code>, exported <!--SNAPSHOT-DATE-->. The source excerpts are bundled with this page and carry file hashes in the source manifest. They are a fixed snapshot, not a live build monitor.</p><p>All <!--DECLARATIONS--> declarations displayed here have been checked against the compiled library; their <!--THEOREMS--> theorem declarations use only <code>propext</code>, <code>Classical.choice</code> and <code>Quot.sound</code>. No theorem uses <code>sorryAx</code>.</p><p>The official Lean logo is from <a href="https://lean-lang.org/" target="_blank" rel="noopener">lean-lang.org</a>. Definition cards capture Lean 4.29.1’s language-server hover information for these exact excerpts, with source files bundled locally. The source badge distinguishes this project, Mathlib and Lean core. Local variables point to their binding; inherited fields point to their parent declaration. Library snapshot: Mathlib <code>5e932f97dd25535344f80f9dd8da3aab83df0fe6</code>.</p><p>Work labels, scope labels and paper-to-code correspondence are reviewed editorial judgments; the kernel checks Lean declarations, not that correspondence.</p><p><a href="source-manifest.json">Source manifest</a> · <a href="verification.txt">Excerpt verification record</a></p></details>
<details id="references"><summary>References cited in this excerpt (original numbering)</summary><ol><li value="1">Agarwal, P.K., Aronov, B., Schevon, C.A.: Star unfolding of a polytope with applications. SIAM J. Comput. 26, 1689–1713 (1997).</li><li value="3">Aronov, B., O’Rourke, J.: Nonoverlap of the star unfolding. Discrete Comput. Geom. 8(3), 219–250 (1992).</li><li value="4">Demaine, E.D., Lubiw, A.: A generalization of the source unfolding of convex polyhedra. LNCS 7579, 185–199 (2012).</li><li value="9">Itoh, J., O’Rourke, J., Vîlcu, C.: Star unfolding convex polyhedra via quasigeodesic loops. Discrete Comput. Geom. 44(1), 35–54 (2010).</li><li value="12">Sharir, M., Schorr, A.: On shortest paths in polyhedral spaces. SIAM J. Comput. 15(1), 193–215 (1986).</li><li value="13">Shiohama, K., Tanaka, M.: Cut loci and distance spheres on Alexandrov surfaces. Actes Table Ronde Géom. Différ. (Luminy, 1992) 1, 531–559 (1996).</li></ol></details><p class="fine">Paper and figures: Stephen Kiazyk and Anna Lubiw, journal version © Springer Science+Business Media New York 2016. This private annotated reading copy does not assert a new license for the original material.</p></section></article>
</main><div id="lean-hover" class="lean-hover" role="dialog" aria-labelledby="lean-hover-title" hidden><div class="lean-hover-top"><strong id="lean-hover-title">Lean definition</strong><button type="button" id="lean-hover-close" aria-label="Close definition">×</button></div><div id="lean-hover-body"></div></div></body></html>'''
proof_map=''.join(f'<li><a href="#{a["blocks"][0]}">{esc(a["title"])}</a>{work_badge(a)} <span class="coverage paper-coverage">Paper: {coverage[a["status"]].lower()}</span></li>' for a in A if a['id']!='curve')
counts={state:sum(a['work']['status']==state for a in A) for state in work_labels}
assert by_id['main']['work']['status']!='complete' or counts['todo']==0
replacements={
    '<!--MILESTONE-STATE-->': 'The universal-source star milestone is complete.' if by_id['main']['work']['status']=='complete' else 'The universal-source star milestone is in progress.',
    '<!--WORK-COUNTS-->': f"{counts['complete']} complete components · {counts['todo']} required items still to do · {counts['beyond']} items outside this milestone",
    '<!--REVISION-->':D['revision'], '<!--SNAPSHOT-DATE-->':D['date'],
    '<!--DECLARATIONS-->':str(V['declarations']), '<!--THEOREMS-->':str(V['theorems']),
}
for marker,value in replacements.items():template=template.replace(marker,esc(value))
(dist/'index.html').write_text(template.replace('<!--SMALL-POLYHEDRA-->',typeset(r'\(n \le 6\)')).replace('<!--HALF-PI-->',typeset(r'\(\frac{\pi}{2}\)')).replace('<!--ARTICLE-->',article).replace('<!--PROOFMAP-->',proof_map))
print('Rendered complete annotated paper.')
