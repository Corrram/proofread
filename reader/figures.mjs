import {articleBlocks} from './article.mjs';

const safePath=value=>typeof value==='string'&&!value.startsWith('/')&&!value.includes('\\')&&!value.includes(':')&&value.split('/').every(p=>p&&p!=='.'&&p!=='..');
const digest=value=>typeof value==='string'&&/^[a-f0-9]{64}$/.test(value);
const browserImage=value=>/\.(png|jpe?g|svg)$/i.test(value);

// Original graphic arguments stay in the parsed source. Explicit overrides
// select browser renderings and bind both files to the compiled asset manifest.
export function resolveFigureAssets(article,overrides={},assets={}) {
  const resolved={},used=new Set(),names=new Map();
  for(const block of articleBlocks(article).filter(b=>b.kind==='figure'))for(const image of block.images){
    const raw=image.image,entry=overrides[raw];
    let source,rendered;
    if(entry!==undefined){
      if(!entry||!safePath(entry.source)||!safePath(entry.rendered)||!entry.source.startsWith('source/')||!browserImage(entry.rendered))throw new Error('Unsafe figure rendering: '+raw);
      if(!digest(entry.sourceSha256)||!digest(entry.renderedSha256)||assets[entry.source]!==entry.sourceSha256||assets[entry.rendered]!==entry.renderedSha256)throw new Error('Unpinned figure rendering: '+raw);
      if(!Number.isSafeInteger(entry.page)||entry.page<1||!Number.isSafeInteger(entry.dpi)||entry.dpi<1||typeof entry.renderer!=='string'||!entry.renderer.trim())throw new Error('Missing figure rendering provenance: '+raw);
      source=entry.source;rendered=entry.rendered;used.add(raw);
    }else{
      if(!safePath(raw)||!browserImage(raw))throw new Error('Figure needs an explicit rendering: '+raw);
      source=rendered='source/'+raw;
      if(!digest(assets[source]))throw new Error('Unpinned source figure: '+raw);
    }
    const filename=rendered.split('/').at(-1);
    if(names.has(filename)&&names.get(filename)!==rendered)throw new Error('Colliding figure rendering filename: '+filename);
    names.set(filename,rendered);
    resolved[raw]={source,rendered,filename};
  }
  for(const key of Object.keys(overrides))if(!used.has(key))throw new Error('Unused figure rendering: '+key);
  return resolved;
}
