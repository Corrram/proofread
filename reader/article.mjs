// A source-preserving LaTeX article reader. Mathematical evidence is an overlay,
// never a replacement for the manuscript, and unchecked spans stay visible.
import katex from 'katex';
export const escape = s => String(s).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));

const envPattern = /\\(begin|end)\{([^}]+)\}/g;
const mathEnvs = new Set(['equation','equation*','align','align*','gather','gather*','gathering','multline','multline*']);
const results = new Set(['theorem','lemma','proposition','corollary','remark','definition','example','optimizationproblem','optimisationproblem']);
export function brace(text, offset) {
  if(text[offset] !== '{') throw new Error(`Expected brace at ${offset}`);
  let depth=1, at=offset+1;
  for(; at<text.length; at++) {
    if(text[at]==='\\') {at++;continue;}
    if(text[at]==='{') depth++;
    else if(text[at]==='}' && --depth===0) return {value:text.slice(offset+1,at),end:at+1};
  }
  throw new Error('Unclosed LaTeX argument');
}

function argument(text,at) {
  while(/\s/.test(text[at]??'') && at<text.length) at++;
  return brace(text,at);
}
function optional(text,at) {
  if(text[at]!=='[') return {value:'',end:at};
  let depth=0;
  for(let i=at+1;i<text.length;i++) {
    if(text[i]==='{') depth++;
    else if(text[i]==='}') depth--;
    else if(text[i]===']' && depth===0) return {value:text.slice(at+1,i),end:i+1};
  }
  throw new Error('Unclosed LaTeX option');
}
const uncomment = text => text.replace(/(?<!\\)%[^\n]*/g,m=>' '.repeat(m.length));
const labels = text => [...uncomment(text).matchAll(/\\label\{([^}]+)\}/g)].map(m=>m[1]);
const anchor = label => 'article-'+label.replace(/[^a-zA-Z0-9-]/g,'-');

// Paragraph boundaries must not split an environment inside inline mathematics.
function paragraphEnd(text,start) {
  for(let i=start;i<text.length;i++) {
    if(text[i]==='%'){const end=text.indexOf('\n',i);if(end<0)return text.length;i=end;}
    if(text[i]==='$') {
      const delimiter=text[i+1]==='$'?'$$':'$';
      const end=text.indexOf(delimiter,i+delimiter.length);
      if(end<0)throw new Error('Unclosed source mathematics');
      i=end+delimiter.length-1;continue;
    }
    if(text[i]==='\\') {
      if(text[i+1]==='\\'){i++;continue;}
      if(text.startsWith('\\(',i)) {
        const end=text.indexOf('\\)',i+2);if(end<0)throw new Error('Unclosed source mathematics');
        i=end+1;continue;
      }
      if(text.startsWith('\\[',i)||text.startsWith('\\begin{',i)||/^\\(?:subsub|sub)?section\*?\{|^\\paragraph\*?\{|^\\appendix\b/.test(text.slice(i)))return i;
      i++;continue;
    }
    if(text[i]==='\n'&&/^\n\s*\n/.test(text.slice(i)))return i;
  }
  return text.length;
}

function tableRows(tex) {
  tex=uncomment(tex).replace(/\\(?:toprule|midrule|bottomrule|hline|addlinespace)(?:\[[^\]]*\])?/g,'').replace(/\\cline\{[^}]+\}/g,'');
  const rows=[];let row=[],start=0,depth=0,math='';
  for(let i=0;i<tex.length;i++) {
    if(tex[i]==='$'){math=math?'':'$';continue;}
    if(tex.startsWith('\\(',i)){math='\\)';i++;continue;}
    if(tex.startsWith('\\)',i)){math='';i++;continue;}
    if(math)continue;
    if(tex[i]==='{')depth++;
    if(tex[i]==='}')depth--;
    if(depth)continue;
    if(tex[i]==='&'){row.push(tex.slice(start,i).trim());start=i+1;}
    else if(tex.startsWith('\\\\',i)){
      row.push(tex.slice(start,i).trim());if(row.some(Boolean))rows.push(row);
      row=[];i=optional(tex,i+2).end-1;start=i+1;
    }
  }
  const final=tex.slice(start).trim();if(final){row.push(final);rows.push(row);}
  if(!rows.length)throw new Error('Empty source table');
  return rows;
}

function listItems(text) {
  const starts=[];
  for(let i=0;i<text.length;i++) {
    if(text[i]==='%'){const end=text.indexOf('\n',i);if(end<0)break;i=end;continue;}
    if(text.startsWith('\\begin{',i)){i=environment(text,i).end-1;continue;}
    if(/^\\item\b/.test(text.slice(i))){const option=optional(text,i+5);starts.push({itemStart:i,start:option.end,label:option.value});i=option.end-1;}
  }
  if(!starts.length)throw new Error('Empty source list');
  return starts.map((item,i)=>({...item,body:text.slice(item.start,starts[i+1]?.itemStart??text.length)}));
}

function roman(n) {
  let out='';for(const [value,digit] of [[1000,'m'],[900,'cm'],[500,'d'],[400,'cd'],[100,'c'],[90,'xc'],[50,'l'],[40,'xl'],[10,'x'],[9,'ix'],[5,'v'],[4,'iv'],[1,'i']])while(n>=value){out+=digit;n-=value;}return out;
}

// A row in a nested cases/aligned environment is part of its outer equation.
function equationRows(body) {
  const text=uncomment(body),rows=[];let start=0,depth=0,environments=0;
  for(let i=0;i<text.length;i++) {
    if(text.startsWith('\\begin{',i)){const arg=brace(text,i+6);environments++;i=arg.end-1;continue;}
    if(text.startsWith('\\end{',i)){const arg=brace(text,i+4);environments--;i=arg.end-1;continue;}
    if(text.startsWith('\\\\',i)&&!depth&&!environments){rows.push(text.slice(start,i));i=optional(text,i+2).end-1;start=i+1;continue;}
    if(text[i]==='\\'){i++;continue;}
    if(text[i]==='{')depth++;
    if(text[i]==='}')depth--;
  }
  rows.push(text.slice(start));return rows.filter(row=>row.trim());
}

export function articleBlocks(article) {
  const all=[];
  function walk(blocks){for(const b of blocks){all.push(b);if(b.children)walk(b.children);if(b.items)b.items.forEach(walk);}}
  walk(article.blocks);return all;
}

/** Bind by exact labels or a unique literal quotation; fuzzy matching is rejected. */
export function resolveBindings(article,bindings) {
  const blocks=articleBlocks(article),annotations={};
  for(const binding of bindings) {
    if(binding.role&&!['counterpart','refutation'].includes(binding.role))throw new Error(`Unknown source binding role: ${binding.role}`);
    let candidates=blocks.filter(b=>binding.label?b.labels.includes(binding.label):b.kind===binding.kind&&b.latex.includes(binding.quote));
    if(binding.occurrence!==undefined){
      if(!binding.label||!Number.isSafeInteger(binding.occurrence)||binding.occurrence<1)throw new Error('Invalid binding occurrence');
      candidates=candidates.slice().sort((a,b)=>a.start-b.start).filter((_,i)=>i===binding.occurrence-1);
    }
    if(candidates.length!==1)throw new Error(`Source binding must match exactly once: ${binding.label??binding.quote} (${candidates.length})`);
    const b=candidates[0];
    annotations[b.id]??=[];
    for(const declaration of binding.declarations)annotations[b.id].push({declaration,title:binding.title,note:binding.note,role:binding.role??'counterpart'});
  }
  return annotations;
}

function environment(text,at) {
  const visible=uncomment(text);
  envPattern.lastIndex=at;
  const first=envPattern.exec(visible);
  if(first?.index!==at || first[1]!=='begin') throw new Error('Expected environment');
  const title=optional(text,envPattern.lastIndex);
  const contentStart=title.end;
  if(first[2]==='comment') {
    const close=text.indexOf('\\end{comment}',contentStart);
    if(close<0)throw new Error('Unclosed comment environment');
    return {kind:'comment',title:'',body:text.slice(contentStart,close),end:close+13};
  }
  const stack=[first[2]];
  envPattern.lastIndex=contentStart;
  for(let token; (token=envPattern.exec(visible));) {
    if(token[1]==='begin'&&token[2]==='comment') {
      const close=text.indexOf('\\end{comment}',envPattern.lastIndex);
      if(close<0)throw new Error('Unclosed comment environment');
      envPattern.lastIndex=close+13;continue;
    }
    if(token[1]==='begin') stack.push(token[2]);
    else if(stack.pop()!==token[2]) throw new Error(`Mismatched environment: ${token[2]}`);
    if(!stack.length) return {kind:first[2],title:title.value,body:text.slice(contentStart,token.index),end:envPattern.lastIndex};
  }
  throw new Error(`Unclosed environment ${first[2]}`);
}

export function parseArticle(source,bibliography='',{referenceChoices={}}={}) {
  const begin=source.indexOf('\\begin{document}'),end=source.lastIndexOf('\\end{document}');
  if(begin<0||end<begin) throw new Error('Missing article document');
  const macros={};
  const preamble=uncomment(source.slice(0,begin));
  const equationWithin=preamble.match(/\\numberwithin\{equation\}\{(section|subsection)\}/)?.[1];
  function defineMacro(name,count,body) {
    const used=Math.max(0,...[...body.matchAll(/(?<!\\)#([1-9])/g)].map(m=>Number(m[1])));
    if(used!==count)throw new Error(`Unsupported unused or mismatched macro parameters: ${name}`);
    macros[name]=body;
  }
  // Both braced and unbraced control sequences are legal LaTeX declarations.
  for(const match of preamble.matchAll(/\\(?:newcommand|providecommand|renewcommand)\*?\s*(?:\{(\\[A-Za-z]+|\\\d)\}|(\\[A-Za-z]+|\\\d))/g)) {
    let at=match.index+match[0].length;
    while(/\s/.test(preamble[at]??'')&&at<preamble.length)at++;
    const count=optional(preamble,at);
    if(count.value&&!/^[1-9]$/.test(count.value))throw new Error('Unsupported macro arguments');
    defineMacro(match[1]??match[2],Number(count.value||0),argument(preamble,count.end).value);
  }
  // Simple undelimited TeX definitions: \def\name#1#2{...} and \def\1{...}.
  for(const match of preamble.matchAll(/\\def\s*(\\[A-Za-z]+|\\\d)((?:\s*#[1-9])*)\s*(?=\{)/g)) {
    const parameters=match[2].replace(/\s/g,''),count=parameters.length/2;
    if(parameters!==Array.from({length:count},(_,i)=>'#'+(i+1)).join(''))throw new Error('Unsupported delimited macro parameters');
    defineMacro(match[1],count,argument(preamble,match.index+match[0].length).value);
  }
  for(const match of preamble.matchAll(/\\DeclareMathOperator(\*)?\{(\\[A-Za-z]+)\}/g))macros[match[2]]='\\operatorname'+(match[1]??'')+'{'+argument(source,match.index+match[0].length).value+'}';
  const declarations={},counters={};
  for(const match of preamble.matchAll(/\\newtheorem(\*)?\{([A-Za-z]+)\}(?:\[([A-Za-z]+)\])?\{([^}]+)\}(?:\[([A-Za-z]+)\])?/g))declarations[match[2]]={title:match[4],counter:match[1]?null:match[3]??match[2],within:match[5]};
  const resultKinds=new Set([...results,...Object.keys(declarations)]);
  function resultNumber(kind) {
    const declaration=declarations[kind]??{counter:'theorem',within:'section'};
    if(declaration.counter===null)return '';
    const parent=declarations[declaration.counter]??declaration;
    const within=parent.within??declaration.within;
    const sectionNumber=appendix?String.fromCharCode(64+section):String(section);
    const prefix=within==='section'?sectionNumber:within==='subsection'?`${sectionNumber}.${subsection}`:'';
    counters[declaration.counter]=(counters[declaration.counter]??0)+1;
    return [prefix,String(counters[declaration.counter])].filter(Boolean).join('.');
  }
  const getMeta=command=>{const m=source.match(new RegExp('\\\\'+command+'\\{'));return m?brace(source,m.index+m[0].length-1).value:'';};
  const article={title:getMeta('title'),author:getMeta('author'),date:getMeta('date'),implicitDate:/\\documentclass(?:\[[^\]]*\])?\{article\}/.test(preamble)&&!/\\date\s*\{/.test(preamble),macros,blocks:[],references:{},bibliography:[]};
  let section=0,subsection=0,subsubsection=0,equation=0,figure=0,table=0,serial=0,appendix=false;
  function equationNumber(){
    const prefix=equationWithin?(appendix?String.fromCharCode(64+section):String(section))+(equationWithin==='subsection'?'.'+subsection:''):'';
    return [prefix,String(++equation)].filter(Boolean).join('.');
  }
  function parse(text,base=0) {
    let at=0; const blocks=[];
    while(at<text.length) {
      if(/\s/.test(text[at])) {at++;continue;}
      if(text[at]==='%') {at=text.indexOf('\n',at);if(at<0)break;continue;}
      const start=at;
      const sectionMatch=text.slice(at).match(/^\\(section|subsection|subsubsection)(\*)?\{/);
      let block;
      if(text.startsWith('\\twocolumn',at)) {
        at+='\\twocolumn'.length;
        while(/\s/.test(text[at]??'')&&at<text.length)at++;
        if(text[at]==='[') {
          const option=optional(text,at),innerStart=at+1;
          const visible=uncomment(option.value),groupStart=visible.search(/\S/);
          let body=option.value,offset=innerStart;
          if(visible[groupStart]==='{') {
            const group=brace(option.value,groupStart);
            if(visible.slice(group.end).trim())throw new Error('Unsupported column-title wrapper');
            body=group.value;offset+=groupStart+1;
          }
          block={kind:'wide',children:parse(body,base+offset)};at=option.end;
        } else block={kind:'layout'};
      } else if(text.startsWith('\\appendix',at)) {
        at+='\\appendix'.length;appendix=true;section=0;subsection=0;subsubsection=0;block={kind:'layout'};
      } else if(/^\\paragraph\*?\{/.test(text.slice(at))) {
        const match=text.slice(at).match(/^\\paragraph\*?\{/),arg=brace(text,at+match[0].length-1);
        at=arg.end;block={kind:'heading',level:5,number:'',title:arg.value};
      } else if(sectionMatch) {
        const arg=brace(text,at+sectionMatch[0].length-1); at=arg.end;
        const labelMatch=text.slice(at).match(/^\s*\\label\{[^}]+\}/);
        if(labelMatch)at+=labelMatch[0].length;
        if(!sectionMatch[2]){if(sectionMatch[1]==='section'){section++;subsection=0;subsubsection=0;}else if(sectionMatch[1]==='subsection'){subsection++;subsubsection=0;}else subsubsection++;}
        if(!sectionMatch[2]&&equationWithin&&(sectionMatch[1]==='section'||equationWithin==='subsection'))equation=0;
        for(const [kind,d] of Object.entries(declarations))if(!sectionMatch[2]&&kind===d.counter&&((sectionMatch[1]==='section'&&['section','subsection'].includes(d.within))||(sectionMatch[1]==='subsection'&&d.within==='subsection')))counters[kind]=0;
        if(!Object.keys(declarations).length&&sectionMatch[1]==='section')counters.theorem=0;
        const sectionNumber=appendix?String.fromCharCode(64+section):String(section);
        block={kind:'heading',level:sectionMatch[1]==='section'?2:sectionMatch[1]==='subsection'?3:4,number:sectionMatch[2]?'':sectionMatch[1]==='section'?sectionNumber:sectionMatch[1]==='subsection'?`${sectionNumber}.${subsection}`:`${sectionNumber}.${subsection}.${subsubsection}`,title:arg.value};
      } else if(text.startsWith('\\begin{',at)) {
        const env=environment(text,at);at=env.end;
        if(mathEnvs.has(env.kind)) {
          const rows=['align','gather'].includes(env.kind)?equationRows(env.body):[env.body];
          const numbers=[],labelNumbers={};
          for(const row of rows){const numbered=!env.kind.endsWith('*')&&!/\\(?:notag|nonumber)\b/.test(row);const number=numbered?equationNumber():'';if(number)numbers.push(number);for(const label of labels(row))labelNumbers[label]=number;}
          block={kind:'math',environment:env.kind,body:env.body,numbers,labelNumbers};
        } else if(resultKinds.has(env.kind)) {
          const prefix=env.body.match(/^\s*(?:\\label\{[^}]+\}\s*)*/)[0];
          const name=declarations[env.kind]?.title??env.kind[0].toUpperCase()+env.kind.slice(1);
          const normalized=name.toLowerCase().replace(/\s/g,'');
          block={kind:results.has(normalized)?normalized:'result',isResult:true,resultName:name,title:env.title,number:resultNumber(env.kind),ownLabels:labels(prefix),children:parse(env.body.slice(prefix.length),base+start+text.slice(start,at).indexOf(env.body)+prefix.length)};
        } else if(['proof','abstract','center','samepage','centering'].includes(env.kind)) {
          block={kind:env.kind,title:env.title,children:parse(env.body,base+start+text.slice(start,at).indexOf(env.body))};
        } else if(env.kind==='minipage') {
          const width=argument(env.body,0);
          block={kind:'minipage',children:parse(env.body.slice(width.end),base+start+text.slice(start,at).indexOf(env.body)+width.end)};
        } else if(env.kind==='figure'||env.kind==='figure*') {
          const visible=uncomment(env.body),captions=[...visible.matchAll(/\\caption\{/g)];
          if(!captions.length)throw new Error('Incomplete figure');
          const bodyOffset=base+start+text.slice(start,at).indexOf(env.body);
          const children=[];let segmentStart=0;
          for(let ci=0;ci<captions.length;ci++){
            const caption=captions[ci],arg=brace(env.body,caption.index+caption[0].length-1);
            const nextImage=visible.slice(arg.end).search(/\\includegraphics(?:\[[^\]]*\])?\{/);
            const segmentEnd=ci===captions.length-1?env.body.length:arg.end+nextImage;
            if(ci<captions.length-1&&(nextImage<0||segmentEnd>=captions[ci+1].index))throw new Error('Each caption must have its own figure images');
            const segment=env.body.slice(segmentStart,segmentEnd),segmentVisible=visible.slice(segmentStart,segmentEnd);
            let imageRow=0,imageEnd=0;
            const images=[...segmentVisible.matchAll(/\\includegraphics(?:\[([^\]]*)\])?\{([^}]+)\}/g)].map(m=>{
              if(/\\\\/.test(segmentVisible.slice(imageEnd,m.index)))imageRow++;
              imageEnd=m.index+m[0].length;
              return {image:m[2],options:m[1]??'',row:imageRow};
            });
            if(!images.length)throw new Error('Incomplete figure');
            const childStart=ci===0?base+start:bodyOffset+segmentStart;
            const childEnd=ci===captions.length-1?base+at:bodyOffset+segmentEnd;
            children.push({kind:'figure',number:String(++figure),image:images[0].image,images,caption:arg.value,
              id:`passage-${++serial}`,start:childStart,end:childEnd,latex:source.slice(childStart,childEnd),labels:labels(segment)});
            segmentStart=segmentEnd;
          }
          if(children.length===1){block=children[0];serial--;}
          else block={kind:'figureGroup',children};
        } else if(env.kind==='table'||env.kind==='table*') {
          const tabularStart=env.body.indexOf('\\begin{tabular');
          if(tabularStart<0)throw new Error('Unsupported table body');
          const tabular=environment(env.body,tabularStart);
          let args=argument(tabular.body,0);
          if(tabular.kind==='tabular*')args=argument(tabular.body,args.end);
          const caption=env.body.match(/\\caption\{/);
          block={kind:'table',number:String(++table),rows:tableRows(tabular.body.slice(args.end)),
            caption:caption?brace(env.body,caption.index+caption[0].length-1).value:''};
        } else if(env.kind==='comment') {
          block={kind:'comment'};
        } else if(env.kind==='enumerate'||env.kind==='itemize') {
          const parts=listItems(env.body);
          block={kind:'list',style:env.kind==='itemize'?'bullet':env.title.includes('alph')?'alpha':env.title.includes('roman')?'roman':env.title.includes('Q')?'question':'decimal',itemLabels:parts.map(p=>p.label),items:parts.map(p=>parse(p.body,base+start+text.slice(start,at).indexOf(env.body)+p.start))};
        } else throw new Error(`Unsupported article environment ${env.kind}`);
      } else if(text.startsWith('$$',at)) {
        const close=text.indexOf('$$',at+2);if(close<0)throw new Error('Unclosed display');
        at=close+2;block={kind:'math',body:text.slice(start+2,close),numbers:[]};
      } else if(text.startsWith('\\[',at)) {
        const close=text.indexOf('\\]',at+2);if(close<0)throw new Error('Unclosed display');
        at=close+2;block={kind:'math',body:text.slice(start+2,close),numbers:[]};
      } else {
        at=paragraphEnd(text,at);
        if(at===start)throw new Error(`Unrecognized source block at ${base+at}`);
        block={kind:'paragraph',body:text.slice(start,at)};
      }
      block.id=`passage-${++serial}`;
      block.start=base+start;block.end=base+at;
      block.latex=text.slice(start,at);block.labels=block.ownLabels??((block.children||block.items)?[]:labels(block.latex));
      blocks.push(block);
    }
    return blocks;
  }
  const embeddedBib=source.indexOf('\\begin{thebibliography}',begin+16);
  if(embeddedBib>=0){bibliography=source.slice(embeddedBib,end);article.blocks=parse(source.slice(begin+16,embeddedBib),begin+16);}
  else article.blocks=parse(source.slice(begin+16,end),begin+16);
  const referenceEntries=[];
  function putReference(label,number,block) {referenceEntries.push({label,number,block});}
  function referenceWalk(blocks) {
    for(const b of blocks) {
      // Label equations within results separately from their containing result.
      if(b.kind==='math') b.labels.forEach((l,i)=>putReference(l,b.labelNumbers?.[l]??b.numbers[i]??'',b));
      else if(b.number) for(const l of b.labels.filter(l=>!b.children?.some(c=>c.labels.includes(l))))putReference(l,b.number,b);
      if(b.kind==='list')b.items.forEach((item,i)=>{for(const p of item)if(p.kind==='paragraph')for(const l of p.labels)putReference(l,b.style==='question'?`(Q${i+1})`:b.style==='alpha'?`(${String.fromCharCode(97+i)})`:b.style==='roman'?`(${roman(i+1)})`:String(i+1),p);referenceWalk(item);});
      if(b.children)referenceWalk(b.children);
    }
  }
  referenceWalk(article.blocks);
  // Proof labels need anchors even without a theorem/equation number.
  const numberedLabels=new Set(referenceEntries.map(e=>e.label));
  for(const block of articleBlocks(article))for(const label of block.labels)
    if(!numberedLabels.has(label))putReference(label,'',block);
  article.referenceOccurrences={};
  article.duplicateReferences=[];
  const usedAnchors=new Set();
  for(const [label,entries] of Object.entries(Object.groupBy(referenceEntries,e=>e.label))){
    const choice=referenceChoices[label];
    if(new Set(entries.map(e=>e.block.id)).size!==entries.length)throw new Error(`Repeated label within one source block ${label}`);
    if(entries.length>1 && choice===undefined)throw new Error(`Duplicate source label ${label}: choose an explicit reference occurrence`);
    if(choice!==undefined && (entries.length<2||!Number.isSafeInteger(choice)||choice<1||choice>entries.length))throw new Error(`Invalid reference occurrence for ${label}`);
    const occurrences=entries.map((entry,i)=>{
      const id=anchor(label)+(entries.length>1?`-occurrence-${i+1}`:'');
      if(usedAnchors.has(id))throw new Error(`Colliding source anchor ${label}`);
      usedAnchors.add(id);
      entry.block.referenceIds??={};entry.block.referenceIds[label]=id;
      return {id,number:entry.number,blockId:entry.block.id,occurrence:i+1};
    });
    article.referenceOccurrences[label]=occurrences;
    article.references[label]=occurrences[(choice??1)-1];
    if(entries.length>1)article.duplicateReferences.push({label,choice,occurrences});
  }
  for(const label of Object.keys(referenceChoices))if(!article.referenceOccurrences[label])throw new Error(`Unknown reference choice ${label}`);

  const bibStart=/\\bibitem(?:\[[\s\S]*?\])?\{([^}]+)\}/g;
  const matches=[...bibliography.matchAll(bibStart)];
  article.bibliography=matches.map((m,i)=>({key:m[1],number:i+1,body:bibliography.slice(m.index+m[0].length,matches[i+1]?.index??bibliography.length).replace(/\\end\{thebibliography\}[\s\S]*/,'')}));
  return article;
}

export function renderArticle(article,{annotations={},evidence={},definitions={},figureURL=x=>x,sourceURL='',sourceDate='',pageReferences={},proofDetails=()=>'',certificateURL=()=>'',verificationAnchor='article-verification'}={}) {
  const pageLabels=new Set(articleBlocks(article).flatMap(b=>[...uncomment(b.latex).matchAll(/\\pageref\{([^}]+)\}/g)].map(m=>m[1])));
  for(const label of pageLabels)if(!article.references[label]||!Number.isSafeInteger(pageReferences[label])||pageReferences[label]<1)throw new Error('Missing pinned page reference '+label);
  for(const label of Object.keys(pageReferences))if(!pageLabels.has(label))throw new Error('Unused page reference '+label);
  const knownAnchors=new Set(Object.values(article.references).map(r=>r.id));
  for(const d of Object.values(definitions)) {
    if(!article.references[d.label])throw new Error(`Unknown definition label ${d.label}`);
  }
  function m(tex,display=false) {
    tex=uncomment(tex).replace(/\\label\{[^}]+\}/g,'').replace(/\\allowdisplaybreaks(?:\[[0-4]\])?|\\qedhere\b/g,'');
    tex=tex.replace(/\\begin\{multlined\}/g,'\\begin{gathered}').replace(/\\end\{multlined\}/g,'\\end{gathered}');
    if(/\\(?:href|url|html[A-Za-z]*|includegraphics)\b/.test(tex))throw new Error('Source math cannot supply presentation links or HTML');
    tex=tex.replace(/\\(eqref|ref)\{([^}]+)\}/g,(_match,kind,label)=>{
      const ref=article.references[label];if(!ref)throw new Error('Unknown reference '+label);
      const number=kind==='eqref'?'('+ref.number+')':ref.number;
      return '{\\href{#'+ref.id+'}{\\text{'+number+'}}}';
    });
    // Link lexical symbols; never nest links around their arguments.
    const commandMap=Object.entries(definitions).sort((a,b)=>b[0].length-a[0].length);
    const escaped=s=>s.replace(/[.*+?^${}()|[\]\\]/g,'\\$&');
    const patterns=commandMap.map(([key])=>{
      if(/^\\[A-Za-z]+$/.test(key))return escaped(key);
      const decorated=key.match(/^\\(check|hat|widehat|tilde|widetilde|bar|overline|underline|vec|dot|ddot|breve|acute|grave)\{(\\[A-Za-z]+)\}$/);
      if(decorated)return escaped('\\'+decorated[1])+'\\s*(?:\\{\\s*'+escaped(decorated[2])+'\\s*\\}|'+escaped(decorated[2])+'(?![A-Za-z]))';
      if(!/^[A-Za-z]+(?:_[A-Za-z0-9]+)?$/.test(key))throw new Error('Unsupported definition notation '+key);
      const [name,subscript]=key.split('_');
      return escaped(name)+(subscript?'_(?:'+escaped(subscript)+'|\\{'+escaped(subscript)+'\\})':'');
    });
    const accent=/^(?:\\(?:check|hat|widehat|tilde|widetilde|bar|overline|underline|vec|dot|ddot|breve|acute|grave)\s*)*/;
    const re=patterns.length?new RegExp(accent.source.slice(1)+'(?:'+patterns.join('|')+')','g'):null;
    if(re)tex=tex.replace(re,(symbol,offset,input)=>{
      if(/[A-Za-z]/.test(input[offset+symbol.length]??''))return symbol;
      if(!symbol.startsWith('\\')&&/[A-Za-z\\]/.test(input[offset-1]??''))return symbol;
      const key=symbol.replace(accent,'').replace(/_\{([A-Za-z0-9]+)\}$/,'_$1');
      const decorated=symbol.replace(/\s+/g,'').match(/^\\(check|hat|widehat|tilde|widetilde|bar|overline|underline|vec|dot|ddot|breve|acute|grave)(?:\{(\\[A-Za-z]+)\}|(\\[A-Za-z]+))$/);
      const decoratedKey=decorated?'\\'+decorated[1]+'{'+(decorated[2]??decorated[3])+'}':null;
      const def=(decoratedKey&&definitions[decoratedKey])||definitions[key],id=article.references[def.label]?.id??def.id;
      return `{\\href{#${id}}{${symbol}}}`;
    });
    return katex.renderToString(tex,{displayMode:display,throwOnError:true,strict:'ignore',macros:{'\\mathds':'\\mathbb{#1}','\\scalebox':'\\@secondoftwo',
        '\\ding':context=>{const tokens=context.consumeArgs(1)[0],code=[...tokens].reverse().map(t=>t.text).join('');
          const marker={'51':'✓','55':'✗'}[code];if(!marker)throw new Error('Unsupported dingbat '+code);return context.mode==='text'?(code==='51'?'$\\checkmark$':'$\\times$'):(code==='51'?'\\checkmark':'\\times');},...article.macros},trust:ctx=>ctx.command==='\\href'&&knownAnchors.has(ctx.url?.slice(1))});
  }
  const authorNotes=[];let inAuthor=false;
  function inline(tex) {
    let out='',at=0;
    const simple={'maketitle':'','tableofcontents':'','@':'','centering':'','small':'','normalsize':'','footnotesize':'','scriptsize':'','large':'','Large':'','LARGE':'','huge':'','Huge':'','bfseries':'','raggedright':'','itshape':'','upshape':'','em':'','par':'<br>','noindent':'','smallskip':'','medskip':'','bigskip':'','nopagebreakhere':'','leavevmode':'', 'qedhere':'','newblock':' ','DOIprefix':'doi:','URLprefix':'URL: ','ArXivprefix':'arXiv:','newpage':'<span class="article-page-break" style="break-after:page"></span>','ss':'ß','SS':'ẞ','ae':'æ','AE':'Æ','oe':'œ','OE':'Œ','o':'ø','O':'Ø','l':'ł','L':'Ł','clearpage':'<span class="article-page-break" style="break-after:page"></span>' };
    while(at<tex.length) {
      if(tex[at]==='$') {const delimiter=tex.startsWith('$$',at)?'$$':'$';const end=tex.indexOf(delimiter,at+delimiter.length);if(end<0)throw new Error('Unclosed inline math');out+=m(tex.slice(at+delimiter.length,end),delimiter==='$$');at=end+delimiter.length;continue;}
      if(tex.startsWith('\\(',at)){const end=tex.indexOf('\\)',at+2);if(end<0)throw new Error('Unclosed inline math');out+=m(tex.slice(at+2,end));at=end+2;continue;}
      if(tex[at]==='{'){
        const group=brace(tex,at),font=group.value.match(/^\\(LARGE|Large|large|Huge|huge|small|normalsize)\b/);
        if(font){
          const sizes={LARGE:'1.5em',Large:'1.3em',large:'1.1em',Huge:'1.8em',huge:'1.7em',small:'.85em',normalsize:'1em'};
          const declarations=group.value.match(/^(?:\\(?:LARGE|Large|large|Huge|huge|small|normalsize|bfseries|itshape)\s*)+/)?.[0]??'';
          out+=`<span style="font-size:${sizes[font[1]]}${declarations.includes('\\bfseries')?';font-weight:bold':''}${declarations.includes('\\itshape')?';font-style:italic':''}">${inline(group.value)}</span>`;
          at=group.end;continue;
        }
      }
      if(tex[at]==='%'&&(at===0||tex[at-1]!=='\\')){const end=tex.indexOf('\n',at);at=end<0?tex.length:end+1;continue;}
      if(tex[at]==='\\') {
        const match=tex.slice(at).match(/^\\([A-Za-z]+\*?|[^A-Za-z])/);const cmd=match[1];at+=match[0].length;
        if(Object.hasOwn(simple,cmd)){out+=simple[cmd];if(['ss','SS','ae','AE','oe','OE','o','O','l','L'].includes(cmd))while(/\s/.test(tex[at]??'')&&at<tex.length)at++;continue;}
        if(cmd==='today'){
          if(!/^\d{4}-\d{2}-\d{2}$/.test(sourceDate)||Number.isNaN(Date.parse(sourceDate+'T00:00:00Z'))||new Date(sourceDate+'T00:00:00Z').toISOString().slice(0,10)!==sourceDate)throw new Error('A pinned sourceDate is required for \\today');
          out+=escape(new Date(sourceDate+'T00:00:00Z').toLocaleDateString('en-GB',{day:'numeric',month:'long',year:'numeric',timeZone:'UTC'}));continue;
        }
        if(cmd==='textsuperscript'||cmd==='textsubscript'){const arg=argument(tex,at),tag=cmd==='textsuperscript'?'sup':'sub';out+=`<${tag}${cmd==='textsf'?' style="font-family:ui-sans-serif,system-ui,sans-serif"':cmd==='textsc'?' style="font-variant:small-caps"':cmd==='underline'?' style="text-decoration:underline"':''}>${inline(arg.value)}</${tag}>`;at=arg.end;continue;}
        if(cmd==='\\'){out+='<br>';at=optional(tex,at).end;continue;}
        if([';',',','!',' ','\n','\r'].includes(cmd)){out+=' ';continue;}
        if(cmd==='quad'||cmd==='qquad'){out+=' ';continue;}
        if(cmd==='penalty'){const number=tex.slice(at).match(/^[+-]?\d+/);if(!number)throw new Error('Invalid penalty');at+=number[0].length;continue;}
        if(['Needspace','vspace','hspace','bibliographystyle'].includes(cmd)){at=argument(tex,at).end;continue;}
        if(cmd==='label'){at=argument(tex,at).end;continue;}
        if(cmd==='pageref'){const arg=argument(tex,at),r=article.references[arg.value];out+=`<a href="#${r.id}" title="Page in the published PDF">${pageReferences[arg.value]}</a>`;at=arg.end;continue;}
        if(cmd==='ref'||cmd==='eqref'){const arg=argument(tex,at),r=article.references[arg.value];if(!r)throw new Error(`Unknown reference ${arg.value}`);out+=`<a href="#${r.id}">${cmd==='eqref'?'('+escape(r.number)+')':escape(r.number)}</a>`;at=arg.end;continue;}
        if(['emph','textbf','textit','textup','textnormal','textsf','textsc','underline','texttt','path','mbox','mathrm','nolinkurl','natexlab'].includes(cmd)){const arg=argument(tex,at);const tag=cmd==='emph'||cmd==='textit'?'em':cmd==='textbf'?'strong':cmd==='texttt'?'code':'span';out+=`<${tag}${cmd==='textsf'?' style="font-family:ui-sans-serif,system-ui,sans-serif"':cmd==='textsc'?' style="font-variant:small-caps"':cmd==='underline'?' style="text-decoration:underline"':''}>${inline(arg.value)}</${tag}>`;at=arg.end;continue;}
        if(cmd==='bibinfo'){const field=argument(tex,at),body=argument(tex,field.end);out+=inline(body.value);at=body.end;continue;}
        if(cmd==='enquote'){const arg=argument(tex,at);out+='“'+inline(arg.value)+'”';at=arg.end;continue;}
        if(cmd==='texorpdfstring'){const first=argument(tex,at),second=argument(tex,first.end);out+=inline(first.value);at=second.end;continue;}
        if(cmd==='href'){const href=argument(tex,at),label=argument(tex,href.end);if(!/^(https?:|mailto:)/.test(href.value))throw new Error('Invalid source hyperlink');out+=`<a href="${escape(href.value)}">${inline(label.value)}</a>`;at=label.end;continue;}
        if(cmd==='url'){const arg=argument(tex,at);if(!/^https?:/.test(arg.value))throw new Error('Invalid source URL');out+=`<a href="${escape(arg.value)}">${escape(arg.value)}</a>`;at=arg.end;continue;}
        if(cmd==='doi'){const arg=argument(tex,at);out+=`<a href="https://doi.org/${escape(arg.value)}">doi: ${escape(arg.value)}</a>`;at=arg.end;continue;}
        if(cmd.startsWith('cite')){const first=optional(tex,at),second=optional(tex,first.end),arg=argument(tex,second.end);out+='['+arg.value.split(',').map(key=>{const b=article.bibliography.find(b=>b.key===key.trim());if(!b)throw new Error(`Missing citation ${key}`);return `<a href="#bib-${escape(b.key)}">${b.number}</a>`;}).join(', ')+(first.value?', '+inline(first.value):'')+(second.value?', '+inline(second.value):'')+']';at=arg.end;continue;}
        if(cmd==='bibliography'){at=argument(tex,at).end;continue;}
        if(cmd==='phantom'||cmd==='hphantom'){const arg=argument(tex,at);out+='<span aria-hidden="true" style="visibility:hidden">'+inline(arg.value)+'</span>';at=arg.end;continue;}
        if(cmd==='keywords'){const arg=argument(tex,at);out+='<strong>Keywords:</strong> '+inline(arg.value);at=arg.end;continue;}
        if(cmd==='thanks'){
          if(!inAuthor)throw new Error('Author note outside the author field');
          const arg=argument(tex,at),marker=['*','†','‡','§','¶','‖'][authorNotes.length]??String(authorNotes.length+1);
          const note={id:'article-author-note-'+(authorNotes.length+1),marker,body:arg.value};
          authorNotes.push(note);out+=`<sup><a href="#${note.id}">${marker}</a></sup>`;at=arg.end;continue;
        }
        if(cmd==='footnotemark'){
          const number=optional(tex,at),index=Number(number.value);
          if(!inAuthor||!/^\d+$/.test(number.value)||index<1||index>authorNotes.length)throw new Error('Unresolved author footnote mark');
          const note=authorNotes[index-1];out+=`<sup><a href="#${note.id}">${note.marker}</a></sup>`;at=number.end;continue;
        }
        if(cmd==='footnote'){const arg=argument(tex,at);out+=`<span class="article-footnote">(${inline(arg.value)})</span>`;at=arg.end;continue;}
        if(['%','&','_','#','$','{','}'].includes(cmd)){out+=escape(cmd);continue;}
        if(['\'','`','"','^','~','c','v','H'].includes(cmd)){const arg=tex[at]==='{'?brace(tex,at):{value:tex[at],end:at+1};const marks={"'":'\u0301','`':'\u0300','"':'\u0308','^':'\u0302','~':'\u0303',c:'\u0327',v:'\u030c',H:'\u030b'};out+=escape((arg.value+marks[cmd]).normalize('NFC'));at=arg.end;continue;}
        if(cmd==='textendash'||cmd==='textemdash'){out+=cmd==='textendash'?'–':'—';continue;}
        if(cmd==='and'){out+=' and ';continue;}
        if(Object.hasOwn(article.macros,'\\'+cmd)&&!/#\d/.test(article.macros['\\'+cmd])){out+=m('\\'+cmd);continue;}
        throw new Error(`Unsupported article prose command \\${cmd}: ${tex.slice(at-30,at+45)}`);
      }
      const char=tex[at++];if(char==='{'||char==='}')continue;
      out+=char==='~'?'&nbsp;':escape(char);
    }
    return out.replace(/---/g,'—').replace(/--/g,'–').replace(/``/g,'“').replace(/''/g,'”').replace(/\s+/g,' ');
  }
  function checked(b) {
    const items=annotations[b.id]??b.labels.flatMap(l=>annotations[l]??[]);
    if(!items.length)return '';
    const refutation=items.some(item=>item.role==='refutation');
    const precise=proofDetails(b,items,m);
    const native=items.map(item=>{
      const record=evidence[item.declaration];if(!record)throw new Error(`Missing compiled evidence ${item.declaration}`);
      return `<section><h4>${escape(item.title??'Checked mathematical counterpart')}</h4><p><a href="${escape(certificateURL(record))}">${escape(record.declaration)}</a></p><pre><code>${escape(record.type)}</code></pre>${item.note?`<p>${escape(item.note)}</p>`:''}</section>`;
    }).join('');
    return `<details class="article-evidence${refutation?' article-refutation':''}"><summary>${refutation?'Printed claim refuted · Open checked correction':'Open verification'} (${items.length})</summary>${precise}${precise?'<details class="article-native-types"><summary>Inspect the compiled Lean theorem types</summary>'+native+'</details>':native}</details>`;
  }
  function blocksHTML(blocks) {return blocks.map(b=>{
    const contentId=b.labels.find(l=>article.references[l])??b.id;
    const attrs=`id="${contentId===b.id?b.id:(b.referenceIds?.[contentId]??anchor(contentId))}" data-passage="${b.id}"`;
    const extraAnchors=b.labels.filter(l=>l!==contentId&&!b.children?.some(c=>c.labels.includes(l))).map(l=>`<span id="${b.referenceIds?.[l]??anchor(l)}"></span>`).join('');
    if(b.kind==='heading')return `<h${b.level} ${attrs}>${b.number?b.number+'. ':''}${inline(b.title)}</h${b.level}>${extraAnchors}`;
    if(b.kind==='comment'||b.kind==='layout')return '';
    if(b.kind==='table')return `<figure class="article-table" ${attrs}>${extraAnchors}<div style="overflow-x:auto"><table>${b.rows.map(row=>`<tr>${row.map(cell=>{
      if(cell.startsWith('\\multicolumn')){const n=argument(cell,12),format=argument(cell,n.end),body=argument(cell,format.end);if(!/^\d+$/.test(n.value)||Number(n.value)>100)throw new Error('Invalid table span');return `<td colspan="${n.value}">${inline(body.value+cell.slice(body.end))}</td>`;}
      return `<td>${inline(cell)}</td>`;
    }).join('')}</tr>`).join('')}</table></div><figcaption><strong>Table ${b.number}.</strong> ${inline(b.caption)}</figcaption>${checked(b)}</figure>`;
    if(b.kind==='paragraph')return `<div class="article-paragraph" ${attrs}><p>${inline(b.body)}</p>${checked(b)}</div>`;
    if(b.kind==='math') {
      let tex=b.body;
      if(b.environment?.startsWith('align'))tex=`\\begin{aligned}${tex}\\end{aligned}`;
      if(b.environment?.startsWith('gather'))tex=`\\begin{gathered}${tex}\\end{gathered}`;
      if(b.environment?.startsWith('multline'))tex=`\\begin{gathered}${tex}\\end{gathered}`;
      return `<div class="article-equation" ${attrs}>${extraAnchors}<div class="article-math">${m(tex,true)}</div>${b.numbers.length?`<span class="equation-number">(${b.numbers.join(', ')})</span>`:''}${checked(b)}</div>`;
    }
    if(b.isResult)return `<section class="article-result" data-result-kind="${b.kind}" ${attrs}>${extraAnchors}<h3>${inline(b.resultName)}${b.number?' '+b.number:''}${b.title?' ('+inline(b.title)+')':''}.</h3>${blocksHTML(b.children)}${checked(b)}</section>`;
    if(b.kind==='proof')return `<section class="article-proof" ${attrs}><h4>${b.title?inline(b.title):'Proof.'}</h4>${blocksHTML(b.children)}<span class="article-qed">□</span>${checked(b)}</section>`;
    if(b.kind==='abstract')return `<section class="article-abstract" ${attrs}><h2>Abstract</h2>${blocksHTML(b.children)}</section>`;
    if(b.kind==='center')return `<div class="article-affiliation" ${attrs}>${blocksHTML(b.children)}</div>`;
    if(b.kind==='wide'||b.kind==='figureGroup')return `<div class="article-wide-title" ${attrs}>${blocksHTML(b.children)}</div>`;
    if(['samepage','centering','minipage'].includes(b.kind))return `<div ${attrs}>${blocksHTML(b.children)}</div>`;
    if(b.kind==='figure') {
      const rows=Object.values(Object.groupBy(b.images,image=>image.row??0));
      return `<figure ${attrs}>${extraAnchors}<div class="article-figure-images">${rows.map(row=>`<div class="article-figure-row" style="display:flex;justify-content:center;gap:8px">${row.map(image=>{const width=image.options.match(/width\s*=\s*([.\d]+)\\(?:textwidth|linewidth)/);const percent=width?Math.min(100,Number(width[1])*100):100/row.length;return `<img src="${escape(figureURL(image.image))}" alt="Figure ${b.number}${b.images.length>1?' panel '+(b.images.indexOf(image)+1):''}" loading="lazy" style="width:${percent}%;min-width:0">`;}).join('')}</div>`).join('')}</div><figcaption><strong>Figure ${b.number}.</strong> ${inline(b.caption)}</figcaption>${checked(b)}</figure>`;
    }
    if(b.kind==='list')return `<${b.style==='bullet'?'ul':'ol'} class="article-list ${b.style}"${b.style==='roman'?' style="list-style-type:lower-roman"':''} ${attrs}>${b.items.map((item,i)=>`<li${b.itemLabels[i]?' style="list-style-type:none"':''}>${b.itemLabels[i]?'<span class="article-item-label">'+inline(b.itemLabels[i])+'</span> ':''}${blocksHTML(item)}</li>`).join('')}</${b.style==='bullet'?'ul':'ol'}>`;
    throw new Error(`Unsupported block ${b.kind}`);
  }).join('\n');}
  // A contents entry is one link; references inside its title retain their text.
  const contentsTitle=tex=>inline(tex).replace(/<a\b[^>]*>|<\/a>/g,'').replace(/\shref="[^"]*"/g,'');
  const toc=article.blocks.filter(b=>b.kind==='heading').map(b=>`<li class="level-${b.level}"><a href="#${b.labels[0]?(b.referenceIds?.[b.labels[0]]??anchor(b.labels[0])):b.id}">${b.number?b.number+'. ':''}${contentsTitle(b.title)}</a></li>`).join('');
  inAuthor=true;const authorHTML=inline(article.author);inAuthor=false;
  const authorNoteHTML=authorNotes.map(n=>`<p id="${n.id}"><sup>${n.marker}</sup> ${inline(n.body)}</p>`).join('');
  const referenceNotice=article.duplicateReferences.length?`<aside class="article-reference-notice"><strong>Source cross-reference notice.</strong> ${article.duplicateReferences.map(d=>`The source label <code>${escape(d.label)}</code> occurs ${d.occurrences.length} times. Cross-references explicitly use occurrence ${d.choice}, numbered (${escape(d.occurrences[d.choice-1].number)}); verification links distinguish each occurrence.`).join(' ')}</aside>`:'';
  return `<article class="mirror-full-article">${referenceNotice}<header class="article-title">${article.title?'<h1>'+inline(article.title)+'</h1>':''}${article.author?'<p class="article-author">'+authorHTML+'</p>':''}${article.date||(article.implicitDate&&sourceDate)?'<p class="article-date">'+inline(article.date||'\\today')+'</p>':''}<p><a href="${escape(sourceURL)}">Published source</a> · <a href="#${escape(verificationAnchor)}">Verification map</a></p></header>${authorNoteHTML?'<div class="article-affiliation">'+authorNoteHTML+'</div>':''}<details class="article-contents"><summary>Contents</summary><ol>${toc}</ol></details>${blocksHTML(article.blocks)}<section class="article-bibliography"><h2>References</h2><ol>${article.bibliography.map(b=>`<li id="bib-${escape(b.key)}">${inline(b.body)}</li>`).join('')}</ol></section></article>`;
}
