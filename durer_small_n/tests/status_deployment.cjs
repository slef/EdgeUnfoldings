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
