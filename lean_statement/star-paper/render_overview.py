"""Render the complete proof narrative using the shared checked Lean excerpt renderer."""
import html,json,re
from math_typesetting import MathTypesetter

def render_overview(site,D,H,V,declaration):
    O=D['overview']; esc=html.escape
    def texts(value):
        if isinstance(value,str):return [value]
        if isinstance(value,list):return [s for item in value for s in texts(item)]
        if isinstance(value,dict):return texts(list(value.values()))
        return []
    math=MathTypesetter(texts(O))
    fmt=math.render
    states={'proved':'Proved in Lean','partial':'Partially formalized','open':'Not yet proved in Lean','definitions':'Definitions formalized'}
    styles={'proved':'complete','partial':'todo','open':'todo','definitions':'complete'}
    def badge(state):return f'<span class="work-status {styles[state]}">{states[state]}</span>'
    def note(p):
        a=p['lean']; refs=a['refs']; content=''
        content+=f'<p class="route-note"><strong>{esc(a["relation"])}</strong></p>'
        content+=''.join('<p>'+fmt(t)+'</p>' for t in a['explanation'])
        if a['steps']:content+='<h4>How the Lean proof is split</h4><ol class="steps">'+''.join('<li>'+fmt(t)+'</li>' for t in a['steps'])+'</ol>'
        if a['remaining']:content+='<div class="gap"><strong>Still required for this step</strong><ul>'+''.join('<li>'+fmt(t)+'</li>' for t in a['remaining'])+'</ul></div>'
        if refs:
            content+='<h4>'+('The target statement — proof unfinished' if p['id']=='target' else 'Lean definitions' if a['state']=='definitions' else 'Lean statements and hypotheses')+'</h4>'
            content+=''.join(declaration(ref,'proof-'+p['id'],i==0) for i,ref in enumerate(refs))
        else:content+='<p class="no-declaration">No theorem for this step has been declared yet.</p>'
        return f'<details class="lean-note" id="lean-proof-{p["id"]}" data-proof-passage="{p["id"]}"><summary><img class="lean-logo" src="assets/lean-logo.svg" alt="Lean"><span>Formalization</span>{badge(a["state"])}<span class="disclosure" aria-hidden="true">+</span></summary><div class="lean-content">{content}</div></details>'
    case_rows=''.join(f'<tr><th scope="row"><a href="#{c["target"]}">{esc(c["title"])}</a></th><td>{badge(c["state"])}</td><td>{esc(c["note"])}</td></tr>' for c in O['cases'])
    toc=''.join(f'<li><a href="#{s["id"]}">{esc(s["title"])}</a></li>' for s in O['sections'])
    article=''
    for n,s in enumerate(O['sections'],1):
        article+=f'<section class="paper-section" id="{s["id"]}"><div class="section-head"><span class="section-no">{n:02}</span><h2>{esc(s["title"])}</h2></div>'
        for p in s['passages']:
            article+=f'<div class="passage" id="{p["id"]}"><h3>{esc(p["title"])}</h3>'
            for text in p['paragraphs']:
                formula=bool(re.fullmatch(r'\\\(.*\\\)\.?',text))
                article+=f'<p class="paper-text{" formula-row" if formula else ""}">{fmt(text)}</p>'
            if 'table' in p:
                t=p['table'];article+='<div class="table-scroll"><table class="proof-table"><thead><tr>'+''.join('<th scope="col">'+esc(c)+'</th>' for c in t['columns'])+'</tr></thead><tbody>'
                article+=''.join('<tr>'+''.join('<td>'+fmt(c)+'</td>' for c in row)+'</tr>' for row in t['rows'])+'</tbody></table></div>'
            if p['links']:article+='<p class="chapter-links">'+ ' · '.join(f'<a href="{esc(url)}">{esc(label)} →</a>' for label,url in p['links'])+'</p>'
            article+=note(p)+'</div>'
        article+='</section>'
    keyset={':'.join(r) for s in O['sections'] for p in s['passages'] for r in p['lean']['refs']}
    proved=sum(D['declarations'][k]['kind']=='theorem' and not D['declarations'][k]['proofHole'] for k in keyset)
    # The published manuscript and the formal proof have independent provenance.
    audit=f'''<section class="editorial" id="proof-audit"><h2>What this page certifies</h2>
<p>This is an edited reading version of the <a href="{esc(O['source']['url'])}">streamlined proof</a>. Its case structure and prism argument are retained; explanatory passages identify where the Lean proof uses another route. The source manuscript has not been edited.</p>
<p>Every green theorem label refers to the displayed Lean statement under its exact hypotheses. A checked algebraic lemma does not certify a geometric application whose hypotheses have not been supplied. Definitions are labelled separately, and the main target is explicitly unfinished.</p>
<details><summary>Proof snapshot and verification</summary><p>Source revision <code>{D['revision']}</code>, exported {D['date']}. This page displays {len(keyset)} declarations, including {proved} proved theorems and one unfinished target. Across both chapters, {V['proved_theorems']} proved theorem dependency reports use only <code>propext</code>, <code>Classical.choice</code> and <code>Quot.sound</code>. The main target alone records <code>sorryAx</code>.</p>
<p>The declarations and source locations are exported from the checked files. Hover definitions come from the Lean language server. The manuscript correspondence is an editorial assessment; the Lean kernel checks the formal statements and proofs.</p><p>Manuscript source: <code>{esc(O['source']['path'])}</code>; SHA-256 <code>{O['source']['sha256']}</code>.</p><p><a href="source-manifest.json">Source manifest</a> · <a href="verification.txt">Lean verification record</a></p></details>
<p><a href="index.html">Star-unfolding chapter</a> · <a href="#overview">Return to the case overview</a></p></section>'''
    page=f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><meta name="description" content="The six-vertex edge-unfolding proof, with an overview of every case, expandable Lean statements and the precise remaining prism obligations."><title>Six-vertex edge unfolding — Proof & Lean</title><link rel="stylesheet" href="assets/katex/katex.min.css"><link rel="stylesheet" href="style.css"><link rel="stylesheet" href="overview.css"><script src="hovers.js" defer></script><script src="declaration-links.js" defer></script><script src="app.js" defer></script></head>
<body class="full-proof"><a class="skip" href="#overview">Skip to proof overview</a><header class="topbar"><a class="brand" href="proof.html">Edge unfolding / Lean</a><nav class="topnav" aria-label="Proof navigation"><a href="#overview">Overview</a><a href="#statement">The proof</a><a href="#prism-setup">Remaining case</a><a href="index.html">Star chapter</a><label class="toggle"><input id="annotations-toggle" type="checkbox" checked>Lean annotations</label></nav></header>
<main class="workspace"><article class="paper"><header class="paper-header"><p class="eyebrow">THE COMPLETE PROOF MAP</p><h1>{esc(O['title'])}</h1><p class="overview-subtitle">{esc(O['subtitle'])}</p></header>
<section id="overview" class="overview"><div class="overview-status"><strong>One geometric family remains in Lean.</strong><p>The universal-source star proof is complete. The prism-with-diagonal case still needs its remaining geometric constructions and switches.</p></div><h2>The cases at a glance</h2><p class="overview-intro">First remove the smaller solids and pyramids. For the remaining six-vertex solids, split on a universal vertex; otherwise the four graph types below exhaust the possibilities.</p>
<div class="table-scroll"><table class="proof-table case-table"><thead><tr><th scope="col">Case or reduction</th><th scope="col">Lean status</th><th scope="col">Argument</th></tr></thead><tbody>{case_rows}</tbody></table></div>
<details class="contents"><summary>Contents — follow the full argument</summary><ol>{toc}</ol></details>
<details class="legend"><summary>How to read the annotations</summary><p>Expand the Lean logo below a passage to see its statements and hypotheses without leaving the text. Hover over an identifier for its definition and origin.</p><p><strong>Proved in Lean</strong> means the stated result is checked. The insert says when its proof follows a different argument. <strong>Partially formalized</strong> identifies proved components and explicitly lists what is still needed. <strong>Not yet proved in Lean</strong> means this step remains open; it does not necessarily have a Lean declaration containing sorry. The main target has the one actual sorry.</p><p>The status table counts cases, not a percentage of remaining effort. Some reductions overlap. The general arbitrary-source star theorem and stronger every-slit claims are outside this route.</p></details></section>
{article}{audit}</article></main><div id="lean-hover" class="lean-hover" role="dialog" aria-labelledby="lean-hover-title" hidden><div class="lean-hover-top"><strong id="lean-hover-title">Lean definition</strong><button type="button" id="lean-hover-close" aria-label="Close definition">×</button></div><div id="lean-hover-body"></div></div></body></html>'''
    (site/'dist/proof.html').write_text(page)
    print(f'Rendered full proof: {len(O["sections"])} sections, {len(keyset)} displayed declarations.')
