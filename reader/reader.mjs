import katex from 'katex';
import {parseArticle, renderArticle} from './article.mjs';

/* The single-text reader: the article is rendered from the very source the
   Lean kernel compiled, and every sentence carries the status that
   `#proofread_certify` recorded for it in `<article>.proofread.json`. Nothing in the
   reading column is written by hand; the inspector only shows data from the
   report (formal readings, Lean statements, premises). */

export const escape = s => String(s).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const standardAxioms = new Set(['propext', 'Classical.choice', 'Quot.sound']);
const claimStatuses = new Set(['text', 'companion', 'unverified']);

export const statusText = {
  text: 'Derived from its citations',
  companion: 'Checked by the companion development',
  definition: 'Definition, well defined',
  binder: 'Binds a variable',
  unverified: 'Compiled, not yet verified',
  failed: 'Not compiled',
  prose: 'Prose, not compiled',
};

/** FNV-1a (64 bit) of the UTF-8 bytes with CRLF normalized, as `Proofread.sourcePin`. */
export function sourcePin(source) {
  let h = 0xcbf29ce484222325n;
  for (const b of new TextEncoder().encode(source.replace(/\r\n/g, '\n'))) h = ((h ^ BigInt(b)) * 0x100000001b3n) & 0xffffffffffffffffn;
  return 'fnv1a64:' + h.toString(16).padStart(16, '0');
}

export function validateReport(report, source) {
  if (!report || !Array.isArray(report.sentences) || !Array.isArray(report.claims) || !Array.isArray(report.definitions))
    throw new Error('Invalid Proofread report');
  if (report.sourceHash !== sourcePin(source))
    throw new Error('The article changed after its report was written: update the pin of #proofread_article and rebuild');
  if (!Array.isArray(report.axioms) || report.axioms.some(a => !standardAxioms.has(a)))
    throw new Error('The certificate uses a nonstandard axiom');
  const length = [...source.replace(/\r\n/g, '\n')].length;
  report.sentences.forEach((s, i) => {
    if (s.index !== i || !Number.isSafeInteger(s.start) || !Number.isSafeInteger(s.stop) || s.start > s.stop || s.stop > length)
      throw new Error(`Invalid sentence ${i}`);
    if (!['prose', 'failed', 'compiled'].includes(s.outcome)) throw new Error(`Invalid outcome of sentence ${i}`);
  });
  report.claims.forEach((c, k) => {
    if (c.index !== k || !claimStatuses.has(c.status) || !report.sentences[c.sentence]) throw new Error(`Invalid claim ${k}`);
    if (c.premises.some(j => !report.claims[j])) throw new Error(`Claim ${k} has an unknown premise`);
    if (c.status !== 'unverified' && c.premises.some(j => report.claims[j].status === 'unverified'))
      throw new Error(`Claim ${k} is verified from an unverified premise`);
  });
  const verified = new Set(report.verified);
  report.claims.forEach(c => { if ((c.status !== 'unverified') !== verified.has(c.index)) throw new Error(`Claim ${c.index}: status disagrees with the certificate`); });
  return report;
}

/** Status of a sentence, from the claims and definitions it compiled to. */
export function sentenceStatus(report, s) {
  if (s.outcome === 'failed') return 'failed';
  if (s.outcome === 'prose') return 'prose';
  const statuses = (s.claims ?? []).map(k => report.claims[k].status);
  if (statuses.includes('unverified')) return 'unverified';
  if (statuses.includes('companion')) return 'companion';
  if (statuses.includes('text')) return 'text';
  // `fix $b\in B$.`, `Let $w\in A$.`: no definition and no claim
  if (!(s.definitions ?? []).length && !(s.claims ?? []).length) return 'binder';
  return 'definition';
}

/** Sentences that get a marker: everything compiled or failed, and prose inside
    results and proofs (so that uncompiled mathematics stays visible). */
const marked = (report, s) => s.outcome !== 'prose' || s.environment !== 'text';

// UTF-16 index of each code point offset (the report counts code points).
function utf16Index(source) {
  const map = [];
  let i = 0;
  for (const ch of source) { map.push(i); i += ch.length; }
  map.push(i);
  return cp => map[cp];
}

const displayEnvs = /^(?:equation|align|gather|multline|eqnarray|displaymath|math|flalign|alignat)\*?$/;

/** Formula regions [from, to) of the source, so markers never enter mathematics. */
export function mathRegions(src) {
  const out = [];
  let i = 0;
  while (i < src.length) {
    const c = src[i];
    if (c === '%' && src[i - 1] !== '\\') { const e = src.indexOf('\n', i); i = e < 0 ? src.length : e + 1; continue; }
    if (c === '\\' && (src[i + 1] === '$' || src[i + 1] === '\\')) { i += 2; continue; }
    let close = null, open = 0;
    if (src.startsWith('$$', i)) { close = '$$'; open = 2; }
    else if (c === '$') { close = '$'; open = 1; }
    else if (src.startsWith('\\(', i)) { close = '\\)'; open = 2; }
    else if (src.startsWith('\\[', i)) { close = '\\]'; open = 2; }
    else {
      const m = src.slice(i, i + 40).match(/^\\begin\{([A-Za-z*]+)\}/);
      if (m && displayEnvs.test(m[1])) { close = `\\end{${m[1]}}`; open = m[0].length; }
    }
    if (close) {
      const e = src.indexOf(close, i + open);
      const to = e < 0 ? src.length : e + close.length;
      out.push([i, to]);
      i = to;
      continue;
    }
    i++;
  }
  return out;
}

/** The source with private-use markers at the start and end of each marked sentence. */
export function markSentences(source, report) {
  const src = source.replace(/\r\n/g, '\n');
  const at = utf16Index(src);
  const regions = mathRegions(src);
  const outside = pos => {
    for (const [a, b] of regions) if (a < pos && pos < b) return b;
    return pos;
  };
  // a sentence ends one character into its last token; finish a control word it cut
  const wordEnd = pos => {
    const m = src.slice(Math.max(0, pos - 40), pos).match(/\\[A-Za-z]*$/);
    if (!m) return pos;
    if (m[0] === '\\') pos++;
    while (pos < src.length && /[A-Za-z]/.test(src[pos])) pos++;
    return pos;
  };
  const inserts = [];
  for (const s of report.sentences) {
    if (!marked(report, s)) continue;
    const start = at(s.start), stop = outside(wordEnd(at(s.stop)));
    inserts.push([start, 0, `${s.index}`]);
    inserts.push([stop, 1, `${s.index}`]);
  }
  // later positions first; at equal positions, ends before starts
  inserts.sort((x, y) => y[0] - x[0] || x[1] - y[1]);
  let out = src;
  for (const [pos, , text] of inserts) out = out.slice(0, pos) + text + out.slice(pos);
  return out;
}

function renderReading(tex) {
  // inline mode, so that long readings wrap after relations and operators
  return katex.renderToString(tex, {displayMode: false, throwOnError: false, strict: 'ignore',
    macros: {'\\CC': '\\mathcal{C}'}, output: 'htmlAndMathml'});
}

/** Operators written around their argument (`C^\top`, `\widehat C`) display with a placeholder. */
const symbolTex = s => s.startsWith('^') ? '(\\cdot)' + s : s === '\\widehat' ? '\\widehat{\\cdot}' : s;

/** Inspector data for every marked sentence. */
export function inspectorData(report, {declarationURL = () => null} = {}) {
  const sentenceOfClaim = k => report.claims[k].sentence;
  const data = {};
  for (const s of report.sentences) {
    if (!marked(report, s)) continue;
    const status = sentenceStatus(report, s);
    data[s.index] = {
      status, label: statusText[status], line: s.line, environment: s.environment, message: s.message ?? null,
      claims: (s.claims ?? []).map(k => {
        const c = report.claims[k];
        return {index: k, role: c.role, status: c.status, statusText: statusText[c.status],
          reading: renderReading(c.reading), lean: c.lean, meaningful: c.meaningful,
          justification: c.justification, justificationURL: declarationURL(c.justification, c.module),
          premises: c.premises.map(j => ({claim: j, sentence: sentenceOfClaim(j), status: report.claims[j].status})),
          cites: c.cites};
      }),
      definitions: (s.definitions ?? []).map(i => {
        const d = report.definitions[i];
        return {index: i, name: d.name, symbol: katex.renderToString(symbolTex(d.symbol || d.name), {throwOnError: false}),
          lean: d.lean, wellDefined: d.wellDefined, justification: d.justification,
          justificationURL: declarationURL(d.justification, d.module)};
      }),
    };
  }
  return data;
}

export function coverage(report) {
  const count = f => report.sentences.filter(f).length;
  const claims = st => report.claims.filter(c => c.status === st).length;
  return {
    sentences: report.sentences.length,
    compiled: count(s => s.outcome === 'compiled'),
    failed: count(s => s.outcome === 'failed'),
    proseMath: count(s => s.outcome === 'prose' && s.environment !== 'text'),
    claims: report.claims.length, text: claims('text'), companion: claims('companion'), unverified: claims('unverified'),
    definitions: report.definitions.length,
  };
}

/** The reading column: the compiled source, with sentence markers. */
export function renderCompiledArticle({source, bibliography = '', report, config = {}, figureURL = x => x, sourceURL = '', sourceDate = ''}) {
  validateReport(report, source);
  const article = parseArticle(markSentences(source, report), bibliography, {referenceChoices: config.referenceChoices ?? {}});
  let html = renderArticle(article, {definitions: config.definitions ?? {}, figureURL, sourceURL, sourceDate,
    pageReferences: config.pageReferences ?? {}});
  // markers never belong inside attributes (titles, contents links)
  html = html.replace(/="([^"]*)"/g, (m, v) => /[-]/.test(v) ? `="${v.replace(/\d+|\d+/g, '')}"` : m);
  const statusOf = k => sentenceStatus(report, report.sentences[k]);
  html = html.replace(/(\d+)/g, (_, k) => {
    const st = statusOf(Number(k));
    return `<button type="button" class="lm-dot lm-${st}" data-sentence="${k}" aria-label="Sentence ${Number(k) + 1}: ${escape(statusText[st])}"></button>`;
  });
  html = html.replace(/(\d+)/g, (_, k) => `<span class="lm-end" data-sentence="${k}"></span>`);
  // a paragraph that holds only markers (beside a display) needs no box of its own
  html = html.replace(/<div class="article-paragraph"[^>]*><p>((?:\s|<button type="button" class="lm-dot[^>]*><\/button>|<span class="lm-end"[^>]*><\/span>)*)<\/p><\/div>/g, '$1');
  if (/[-]/.test(html)) throw new Error('A sentence marker was not placed');
  return html;
}

/** A complete reader page. `assets` gives the stylesheet and script URLs. */
export function renderCompiledReader({title, source, bibliography, report, config, figureURL, sourceURL, sourceDate,
    assets, links = [], declarationURL, intro = ''}) {
  const body = renderCompiledArticle({source, bibliography, report, config, figureURL, sourceURL, sourceDate});
  const data = JSON.stringify(inspectorData(report, {declarationURL})).replaceAll('<', '\\u003c');
  const c = coverage(report);
  const n = (k, word) => `${k} ${word}${k === 1 ? '' : 's'}`;
  // results closed by a compiled proof: their first statement sentence
  const proved = [...new Map(report.claims.filter(cl => cl.role === 'statement' && cl.premises.length)
    .map(cl => [report.sentences[cl.sentence].env, cl.sentence])).values()]
    .map(k => `<button type="button" class="lm-jump" data-sentence="${k}"><span class="lm-dot lm-text" aria-hidden="true"></span>${escape(report.sentences[k].environment)} · line ${report.sentences[k].line}</button>`);
  const legend = ['text', 'companion', 'definition', 'binder', 'unverified', 'failed', 'prose'].map(st =>
    `<label class="lm-filter"><input type="checkbox" data-filter="${st}" checked><span class="lm-dot lm-${st}" aria-hidden="true"></span>${escape(statusText[st])}</label>`).join('');
  return `<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>${escape(title)} · Proofread</title>
${assets.icon ? `<link rel="icon" href="${escape(assets.icon)}" type="image/svg+xml">` : ''}${assets.styles.map(href => `<link rel="stylesheet" href="${escape(href)}">`).join('')}
<script defer src="${escape(assets.script)}"></script></head>
<body class="lm-compiled"><a class="lm-skip" href="#lm-article">Skip to article</a>
<header class="lm-bar"><span class="lm-brand">Proofread</span><span class="lm-title">${escape(title)}</span>
<nav class="lm-links">${links.map(l => `<a href="${escape(l.href)}">${escape(l.label)}</a>`).join('')}</nav></header>
<div class="lm-layout"><main id="lm-article" tabindex="-1">
<section class="lm-summary" id="lm-summary"><p class="lm-kicker">Single source · compiled by the Lean kernel</p>
<p>${intro}</p>
<p>${n(c.sentences, 'sentence')}. ${c.compiled} compiled into ${n(c.claims, 'claim')} and ${n(c.definitions, 'definition')}. Of the claims, <strong>${c.text} ${c.text === 1 ? 'is' : 'are'} derived from the results they cite</strong>, ${c.companion} ${c.companion === 1 ? 'is' : 'are'} checked by the companion Lean development, and ${c.unverified} ${c.unverified === 1 ? 'is' : 'are'} unverified. ${n(c.failed, 'sentence')} failed to compile, and ${n(c.proseMath, 'sentence')} in results and proofs ${c.proseMath === 1 ? 'is' : 'are'} prose the grammar does not read yet.</p>
${proved.length ? `<p class="lm-proved">Results whose proof is compiled sentence by sentence: ${proved.join(' · ')}</p>` : ''}
<fieldset class="lm-legend"><legend>Show markers</legend>${legend}</fieldset></section>
${body}</main>
<aside class="lm-inspector" aria-label="Sentence inspector" aria-live="polite"><div class="lm-inspector-empty"><p>Select a marker <span class="lm-dot lm-text" aria-hidden="true"></span> at the start of a sentence to see what Lean checked for it.</p></div></aside></div>
<script id="lm-data" type="application/json">${data}</script></body></html>`;
}
