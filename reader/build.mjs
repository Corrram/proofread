#!/usr/bin/env node
// Build the single-text reader of a certified article:
//
//   node reader/build.mjs path/to/article.tex [--bbl article.bbl] [--title "…"] [--out dir]
//
// reads `article.tex` and the report `article.proofread.json` that
// `#proofread_certify` wrote next to it, and writes `dir/index.html` (default
// `article-reader/` next to the article) with its stylesheets, script and KaTeX
// fonts. The page renders the article from its source, with the status of every
// sentence; nothing in it is written by hand.
import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {renderCompiledReader} from './reader.mjs';

const here = path.dirname(fileURLToPath(import.meta.url));
const args = process.argv.slice(2);
const option = name => {
  const i = args.indexOf(name);
  return i >= 0 ? args[i + 1] : undefined;
};
const texPath = args.find((a, i) => !a.startsWith('--') && (i === 0 || !args[i - 1].startsWith('--')));
if (!texPath) {
  console.error('usage: node reader/build.mjs ARTICLE.tex [--bbl FILE.bbl] [--title TITLE] [--date YYYY-MM-DD] [--out DIR]');
  process.exit(2);
}
const source = fs.readFileSync(texPath, 'utf8');
const reportPath = texPath.replace(/\.tex$/, '.proofread.json');
if (!fs.existsSync(reportPath)) {
  console.error(`${reportPath} not found: build the module with #proofread_certify first`);
  process.exit(1);
}
const report = JSON.parse(fs.readFileSync(reportPath, 'utf8'));
const bblPath = option('--bbl') ?? texPath.replace(/\.tex$/, '.bbl');
const bibliography = fs.existsSync(bblPath) ? fs.readFileSync(bblPath, 'utf8') : '';
const title = option('--title') ?? (source.match(/\\title\{([^}]*)\}/)?.[1] ?? path.basename(texPath));
const out = option('--out') ?? path.join(path.dirname(texPath), 'article-reader');

const html = renderCompiledReader({
  title, source, bibliography, report, config: {}, sourceDate: option('--date') ?? '',
  figureURL: image => image, sourceURL: path.basename(texPath),
  assets: {styles: ['katex/katex.min.css', 'reader.css'], script: 'reader.js'},
  links: [{href: path.basename(texPath), label: 'Source'}, {href: path.basename(reportPath), label: 'Report'}],
  declarationURL: () => null,
  intro: `This page renders <code>${path.basename(texPath)}</code>, the text that the Lean kernel compiled. ` +
    'Each marker reports what the certificate checked for its sentence.',
});

fs.mkdirSync(path.join(out, 'katex'), {recursive: true});
fs.writeFileSync(path.join(out, 'index.html'), html);
fs.copyFileSync(texPath, path.join(out, path.basename(texPath)));
fs.copyFileSync(reportPath, path.join(out, path.basename(reportPath)));
fs.copyFileSync(path.join(here, 'reader.css'), path.join(out, 'reader.css'));
fs.copyFileSync(path.join(here, 'reader.js'), path.join(out, 'reader.js'));
const katex = path.join(here, '..', 'node_modules', 'katex', 'dist');
fs.copyFileSync(path.join(katex, 'katex.min.css'), path.join(out, 'katex', 'katex.min.css'));
fs.cpSync(path.join(katex, 'fonts'), path.join(out, 'katex', 'fonts'), {recursive: true});
console.log(`wrote ${path.join(out, 'index.html')}`);
