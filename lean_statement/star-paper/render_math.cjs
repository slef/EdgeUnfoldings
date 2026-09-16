// Render the explicitly marked formulas once, at build time.
const fs = require('node:fs');
const katex = require('./vendor/katex/katex.min.js');
const formulas = JSON.parse(fs.readFileSync(0, 'utf8'));
const rendered = Object.fromEntries(formulas.map(tex => [tex, katex.renderToString(tex, {
  output: 'htmlAndMathml', displayMode: false, throwOnError: true,
  strict: 'error', trust: false,
})]));
process.stdout.write(JSON.stringify(rendered));
