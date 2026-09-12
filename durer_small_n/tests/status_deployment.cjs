// Check links in every rendered article, including links generated from data.
const fs = require('node:fs'), path = require('node:path');
const vm = require('node:vm'), assert = require('node:assert/strict');
const site = path.resolve(process.argv[2]);
const html = fs.readFileSync(path.join(site, 'index.html'), 'utf8');
const script = html.match(/<script>([\s\S]*?)<\/script>/)[1];
const ctx = vm.createContext({document:{addEventListener(){}}, console});
vm.runInContext(script.slice(0,script.indexOf('let showAll = false;')), ctx);
const rendered = vm.runInContext(
  "NODES.map(n=>article(n,true)).join('') + progressHistory() + progressDashboard()", ctx);
let count = 0;
for (const m of rendered.matchAll(/(?:href|src)="([^\"]+)"/g)) {
  const link = m[1];
  if (/^(#|https?:|data:)/.test(link)) continue;
  const target = path.resolve(site, decodeURIComponent(link.split('#')[0]));
  assert(target.startsWith(site + path.sep), `Link escapes deployed site: ${link}`);
  assert(fs.statSync(target).isFile(), `Missing deployed file: ${link}`);
  count++;
}
assert(count > 20, 'Exercise evidence links as well as in-page navigation');
assert(rendered.includes('thesis scan available in the local project'));
assert(!html.includes('../../n6/'));
console.log(`Deployment: all ${count} rendered evidence links resolve inside the site.`);

// The new reading pages contain proof-to-proof links and native heading
// anchors, independently of the overview's JavaScript navigation.
const proofPages = ['TIDY_PROOF', 'TIDY_CORE', 'PRISM_CAP_RULE',
  'CASE_A_CAP_BUDGET', 'SHARPEST_COFACIAL_FAILURE', 'OCTA_FACE_CAP_RULE', 'TIDY_PROOF_FIRST_REVIEW'];
let proofLinkCount = 0;
for (const name of proofPages) {
  const file = path.join(site, 'n6', `${name}.html`);
  const source = fs.readFileSync(file, 'utf8');
  for (const match of source.matchAll(/(?:href|src)="([^\"]+)"/g)) {
    const link = match[1];
    if (/^(https?:|\/\/|data:|mailto:)/.test(link)) continue;
    const [relative, anchor] = link.split('#');
    const target = relative ? path.resolve(path.dirname(file), decodeURIComponent(relative)) : file;
    assert(target.startsWith(site + path.sep), `Proof link escapes deployed site: ${name}: ${link}`);
    assert(fs.statSync(target).isFile(), `Missing proof evidence: ${name}: ${link}`);
    if (anchor && target.endsWith('.html')) {
      const destination = target === file ? source : fs.readFileSync(target, 'utf8');
      assert(destination.includes(`id="${decodeURIComponent(anchor)}"`),
        `Missing reading-page heading: ${name}: ${link}`);
    }
    proofLinkCount++;
  }
}
console.log(`Reading pages: all ${proofLinkCount} evidence links and heading anchors resolve.`);
