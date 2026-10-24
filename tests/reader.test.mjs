import test from 'node:test';
import assert from 'node:assert/strict';
import {sourcePin, mathRegions, markSentences, sentenceStatus, validateReport, renderCompiledArticle, inspectorData} from '../reader/reader.mjs';

const source = String.raw`\title{A compiled note}
\author{A mathematician}
\begin{document}
\maketitle
\section{Squares}
For a real number $x$, let $q(x)\coloneqq x^2$.
\begin{theorem}\label{thm:q}
Every real number $x$ satisfies $q(x)\ge0$.
\end{theorem}
\begin{proof}
Squares are nonnegative, so
\[ q(x)\ge0. \]
\end{proof}
\leavevmode
\end{document}`;

const cp = s => [...s];
const at = (needle, from = 0) => cp(source).join('').indexOf(needle, from);

function report() {
  const s1 = at('For a real'), e1 = at('x^2$.') + 5;
  const s2 = at('Every real'), e2 = at('ge0$.') + 5;
  const s3 = at('Squares are'), e3 = at('ge0. \\]') + 4; // ends inside the display
  const s4 = at('\\leavevmode');
  const sentence = (index, start, stop, environment, extra) => ({index, start, stop, line: 1, column: 1, environment, env: 0, label: '', ...extra});
  return {
    article: 'note.tex', sourceHash: sourcePin(source), verified: [0, 1], axioms: ['propext', 'Quot.sound'],
    definitions: [{index: 0, name: 'q', symbol: 'q', key: 'q', sentence: 0, lean: 'fun x => x ^ 2', wellDefined: 'True', justification: 'J.defined0', module: 'M'}],
    claims: [
      {index: 0, sentence: 1, role: 'statement', cites: [], premises: [1], status: 'text', rank: 1, reading: '\\forall x, q(x)\\ge 0', lean: '∀ x, 0 ≤ q x', meaningful: 'True', justification: 'J.proof0', module: 'M'},
      {index: 1, sentence: 2, role: 'proof step', cites: [], premises: [], status: 'text', rank: 0, reading: 'q(x)\\ge0', lean: '0 ≤ q x', meaningful: 'True', justification: 'J.proof1', module: 'M'},
    ],
    sentences: [
      sentence(0, s1, e1, 'text', {outcome: 'compiled', definitions: [0], claims: []}),
      sentence(1, s2, e2, 'theorem', {outcome: 'compiled', definitions: [], claims: [0]}),
      sentence(2, s3, e3, 'proof', {outcome: 'compiled', definitions: [], claims: [1]}),
      sentence(3, s4, s4 + 1, 'proof', {outcome: 'prose'}),
    ],
  };
}

test('the source pin is FNV-1a over UTF-8 with CRLF normalized', () => {
  assert.equal(sourcePin(''), 'fnv1a64:cbf29ce484222325');
  assert.equal(sourcePin('a\r\nb'), sourcePin('a\nb'));
  assert.notEqual(sourcePin('a'), sourcePin('b'));
});

test('markers stay outside formulas and control words', () => {
  const r = report();
  assert.deepEqual(mathRegions('a $x$ b \\[y\\] c').map(([a, b]) => b - a), [3, 5]);
  const marked = markSentences(source, r);
  // the end of sentence 2 moves past the display that contains its period
  assert.match(marked, /ge0\. \\\]2/);
  // a sentence that ends one character into \leavevmode keeps the command whole
  assert.match(marked, /\\leavevmode3/);
  for (const [a, b] of mathRegions(marked)) assert.doesNotMatch(marked.slice(a, b), /[-]/);
});

test('sentence status follows the certificate', () => {
  const r = report();
  assert.equal(sentenceStatus(r, r.sentences[0]), 'definition');
  assert.equal(sentenceStatus(r, r.sentences[1]), 'text');
  assert.equal(sentenceStatus(r, r.sentences[3]), 'prose');
  const data = inspectorData(r);
  assert.equal(data[1].claims[0].premises[0].sentence, 2);
  assert.equal(data[0].definitions[0].name, 'q');
});

test('the reader renders the compiled source with one marker per sentence', () => {
  const html = renderCompiledArticle({source, report: report()});
  for (const k of [0, 1, 2, 3]) assert.match(html, new RegExp(`class="lm-dot lm-\\w+" data-sentence="${k}"`));
  assert.equal((html.match(/class="lm-end"/g) ?? []).length, 4);
  assert.doesNotMatch(html, /[-]/);
});

test('stale or inconsistent reports are rejected', () => {
  assert.throws(() => validateReport(report(), source + ' '), /changed after its report/);
  const r = report();
  r.axioms.push('sorryAx');
  assert.throws(() => validateReport(r, source), /nonstandard axiom/);
  const u = report();
  u.claims[1].status = 'unverified';
  u.verified = [0];
  assert.throws(() => validateReport(u, source), /unverified premise/);
});
