// Client side of the single-text reader: select a sentence marker to highlight
// the sentence and inspect what the certificate checked for it.
(() => {
  const data = JSON.parse(document.getElementById('lm-data').textContent);
  const panel = document.querySelector('.lm-inspector');
  const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
  const highlights = typeof CSS !== 'undefined' && CSS.highlights && typeof Highlight === 'function';

  function range(k) {
    const start = document.querySelector(`.lm-dot[data-sentence="${k}"]`);
    const end = document.querySelector(`.lm-end[data-sentence="${k}"]`);
    if (!start || !end) return null;
    const r = document.createRange();
    r.setStartAfter(start);
    r.setEndBefore(end);
    return r;
  }
  function mark(name, k) {
    if (!highlights) return;
    if (k === null) { CSS.highlights.delete(name); return; }
    const r = range(k);
    if (r) CSS.highlights.set(name, new Highlight(r));
  }

  const premise = p => `<li><button type="button" class="lm-jump" data-sentence="${p.sentence}"><span class="lm-dot lm-${p.status}" aria-hidden="true"></span>Claim ${p.claim + 1} · sentence ${p.sentence + 1}</button></li>`;
  const declaration = (name, url) => url ? `<a href="${esc(url)}"><code>${esc(name)}</code></a>` : `<code>${esc(name)}</code>`;

  function claimHTML(c) {
    return `<section class="lm-claim"><h3>Claim ${c.index + 1} <span class="lm-role">${esc(c.role)}</span></h3>
      <p class="lm-status lm-${c.status}">${esc(c.statusText)}</p>
      <div class="lm-reading">${c.reading}</div>
      ${c.premises.length ? `<details open><summary>Uses ${c.premises.length} premise${c.premises.length > 1 ? 's' : ''}${c.cites.length ? ' (cites ' + c.cites.map(esc).join(', ') + ')' : ''}</summary><ul class="lm-premises">${c.premises.map(premise).join('')}</ul></details>`
        : `<p class="lm-small">${c.status === 'companion' ? 'Stated without a compiled proof in the text; proved in Lean from the companion development.' : 'No premises.'}</p>`}
      <details><summary>Lean statement</summary><pre><code>${esc(c.lean)}</code></pre></details>
      <details><summary>Definedness condition</summary><pre><code>${esc(c.meaningful)}</code></pre></details>
      ${c.justification ? `<p class="lm-small">Justification: ${declaration(c.justification, c.justificationURL)}</p>` : ''}</section>`;
  }
  function definitionHTML(d) {
    return `<section class="lm-claim"><h3>Definition of <span class="lm-symbol">${d.symbol}</span></h3>
      <p class="lm-status lm-definition">Well defined</p>
      <details open><summary>Lean value</summary><pre><code>${esc(d.lean)}</code></pre></details>
      <details><summary>Well-definedness condition</summary><pre><code>${esc(d.wellDefined)}</code></pre></details>
      <p class="lm-small">Justification: ${declaration(d.justification, d.justificationURL)}</p></section>`;
  }

  let selected = null;
  function select(k, scroll = false) {
    const d = data[k];
    if (!d) return;
    selected = k;
    document.querySelectorAll('.lm-dot[aria-pressed]').forEach(b => b.removeAttribute('aria-pressed'));
    const dot = document.querySelector(`.lm-dot[data-sentence="${k}"]`);
    if (dot) { dot.setAttribute('aria-pressed', 'true'); if (scroll) { const go = () => dot.scrollIntoView({block: matchMedia('(max-width: 900px)').matches ? 'start' : 'center', behavior: 'instant'}); go(); setTimeout(go, 500); } }
    mark('lm-active', k);
    panel.innerHTML = `<header class="lm-inspector-head"><p class="lm-kicker">Sentence ${Number(k) + 1} · line ${d.line} · ${esc(d.environment)}</p>
      <p class="lm-status lm-${d.status}">${esc(d.label)}</p><button type="button" class="lm-close" aria-label="Close">×</button></header>
      ${d.message ? `<p class="lm-message">${esc(d.message)}</p>` : ''}
      ${d.status === 'prose' ? '<p class="lm-small">The fixed grammar does not read this sentence yet, so it makes no checked claim.</p>' : ''}
      ${d.definitions.map(definitionHTML).join('')}${d.claims.map(claimHTML).join('')}`;
    panel.classList.add('lm-open');
    history.replaceState(null, '', '#sentence-' + (Number(k) + 1));
  }

  document.addEventListener('click', e => {
    const b = e.target.closest('.lm-dot[data-sentence], .lm-jump');
    if (b) { select(b.dataset.sentence, b.classList.contains('lm-jump')); return; }
    if (e.target.closest('.lm-close')) {
      panel.classList.remove('lm-open'); mark('lm-active', null); selected = null;
      panel.innerHTML = '<div class="lm-inspector-empty"><p>Select a sentence marker.</p></div>';
    }
  });
  document.addEventListener('mouseover', e => {
    const b = e.target.closest('.lm-dot[data-sentence]');
    mark('lm-hover', b ? b.dataset.sentence : null);
  });
  document.querySelectorAll('[data-filter]').forEach(box => box.addEventListener('change', () => {
    document.body.classList.toggle('lm-hide-' + box.dataset.filter, !box.checked);
  }));
  const m = location.hash.match(/^#sentence-(\d+)$/);
  // select after images and fonts have settled, so the sentence stays in view
  if (m) window.addEventListener('load', () => select(String(Number(m[1]) - 1), true));
})();
