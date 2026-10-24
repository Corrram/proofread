import test from 'node:test';
import assert from 'node:assert/strict';
import {parseArticle} from '../reader/article.mjs';
import {resolveFigureAssets} from '../reader/figures.mjs';
const article=raw=>parseArticle(String.raw`\documentclass{article}\begin{document}\begin{figure}\includegraphics{`+raw+String.raw`}\caption{Original figure}\end{figure}\end{document}`);
const sha='a'.repeat(64),png='b'.repeat(64),raw=String.raw`\assetroot figures/original.pdf`;
const entry={source:'source/figures/original.pdf',rendered:'rendered-figures/original.png',sourceSha256:sha,renderedSha256:png,page:1,dpi:144,renderer:'pdftoppm 26.07.0'};
const assets={[entry.source]:sha,[entry.rendered]:png};

test('figure overrides pin the original PDF and its browser rendering without rewriting the source argument',()=>{
  const parsed=article(raw),resolved=resolveFigureAssets(parsed,{[raw]:entry},assets);
  assert.equal(parsed.blocks[0].images[0].image,raw);
  assert.deepEqual(resolved[raw],{source:entry.source,rendered:entry.rendered,filename:'original.png'});
  assert.throws(()=>resolveFigureAssets(parsed,{},assets),/explicit rendering/);
  for(const patch of [{source:'../original.pdf'},{rendered:'C:/image.png'},{rendered:'rendered/image.pdf'},{sourceSha256:png},{renderedSha256:sha},{page:0},{dpi:0},{renderer:''}]){
    assert.throws(()=>resolveFigureAssets(parsed,{[raw]:{...entry,...patch}},assets),/figure rendering/);
  }
  assert.throws(()=>resolveFigureAssets(parsed,{[raw]:entry,unused:entry},assets),/Unused/);
  assert.throws(()=>resolveFigureAssets(parsed,{[raw]:entry},{[entry.source]:sha}),/Unpinned/);
});

test('browser image originals remain directly pinned and output filenames cannot collide',()=>{
  assert.equal(resolveFigureAssets(article('figures/original.png'),{}, {'source/figures/original.png':png})['figures/original.png'].rendered,'source/figures/original.png');
  assert.throws(()=>resolveFigureAssets(article('figures/original.png')),/Unpinned/);
  const source=String.raw`\documentclass{article}\begin{document}\begin{figure}\includegraphics{one/x.png}\includegraphics{two/x.png}\caption{Two}\end{figure}\end{document}`;
  assert.throws(()=>resolveFigureAssets(parseArticle(source),{}, {'source/one/x.png':sha,'source/two/x.png':png}),/Colliding/);
});
