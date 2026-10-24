import test from 'node:test';
import assert from 'node:assert/strict';
import {parseArticle,articleBlocks,resolveBindings,renderArticle} from '../reader/article.mjs';

const manuscript=String.raw`\title{A classical calculation}
\author{A mathematician}
\begin{document}
\maketitle
\section{Real numbers}\label{sec:reals}
For $x\in\mathbb R$, put
\begin{equation}\label{eq:alpha}\alpha(x)=x^2.\end{equation}
\begin{theorem}[Nonnegativity]\label{thm:positive}
Every $x\in\mathbb R$ satisfies $\alpha(x)\ge0$.
\end{theorem}
\begin{proof}
Since $x^2\ge0$, the assertion follows from \eqref{eq:alpha}.
\end{proof}
\begin{remark}\label{rem:zero} Equality holds at zero.\end{remark}
\end{document}`;

test('retains exact source spans, original result order and references',()=>{
  const article=parseArticle(manuscript);
  for(const b of articleBlocks(article))assert.equal(manuscript.slice(b.start,b.end),b.latex);
  assert.equal(article.references['thm:positive'].number,'1.1');
  assert.equal(article.references['rem:zero'].number,'1.2');
  const html=renderArticle(article);
  assert.match(html,/Nonnegativity/);
  assert.match(html,/Equality holds at zero/);
  assert.match(html,/data-result-kind="remark"/);
  assert.match(html,/href="#article-eq-alpha">\(1\)/);
  assert.doesNotMatch(html,/Open verification|checked mathematical/i);
});

test('bindings must identify exactly one original source passage',()=>{
  const article=parseArticle(manuscript);
  const bindings=[{label:'thm:positive',declarations:['Example.square_nonneg']}];
  assert.equal(Object.values(resolveBindings(article,bindings))[0][0].declaration,'Example.square_nonneg');
  assert.throws(()=>resolveBindings(article,[{label:'missing',declarations:[]}]),/exactly once/);
  assert.throws(()=>resolveBindings(article,[{quote:'x',kind:'paragraph',declarations:[]}]),/exactly once/);
  assert.throws(()=>resolveBindings(article,[{label:'thm:positive',role:'certified-original',declarations:[]}]),/Unknown source binding role/);
});

test('a compiled counterexample is visibly distinguished from a source theorem link',()=>{
  const article=parseArticle(manuscript);
  const annotations=resolveBindings(article,[{label:'thm:positive',role:'refutation',declarations:['Example.counterexample']}]);
  const html=renderArticle(article,{annotations,evidence:{'Example.counterexample':{declaration:'Example.counterexample',type:'¬ PrintedClaim'}}});
  assert.match(html,/class="article-evidence article-refutation"/);assert.match(html,/Printed claim refuted · Open checked correction/);
});

test('a readable checked proof precedes folded native theorem types',()=>{
  const article=parseArticle(manuscript);
  const annotations=resolveBindings(article,[{label:'thm:positive',declarations:['Example.proof']}]);
  const html=renderArticle(article,{annotations,evidence:{'Example.proof':{declaration:'Example.proof',type:'NativeProposition'}},proofDetails:()=>'<p>Readable checked proof</p>'});
  assert(html.indexOf('Readable checked proof')<html.indexOf('NativeProposition'));
  assert.match(html,/class="article-native-types"/);
});

test('duplicate labels and anchor collisions cannot hide a passage',()=>{
  assert.throws(()=>parseArticle(manuscript.replace('rem:zero','thm:positive')),/Duplicate/);
  assert.throws(()=>parseArticle(manuscript.replace('rem:zero','thm-positive')),/Colliding/);
});

test('notation links resolve only to definitions actually present in the article',()=>{
  const article=parseArticle(manuscript);
  assert.match(renderArticle(article,{definitions:{'\\alpha':{label:'eq:alpha'}}}),/href="#article-eq-alpha"/);
  assert.throws(()=>renderArticle(article,{definitions:{'\\alpha':{label:'missing'}}}),/Unknown definition/);
  assert.throws(()=>renderArticle(parseArticle(manuscript.replace('x^2.',String.raw`\href{https://example.com}{x}.`))),/presentation links/);
});

test('unsupported content, missing references, and missing evidence fail visibly',()=>{
  assert.throws(()=>parseArticle(manuscript.replace('begin{remark}','begin{unknown}').replace('end{remark}','end{unknown}')),/Unsupported/);
  assert.throws(()=>renderArticle(parseArticle(manuscript.replace('eqref{eq:alpha}','eqref{missing}'))),/Unknown reference/);
  const article=parseArticle(manuscript),annotations=resolveBindings(article,[{label:'thm:positive',declarations:['Missing.proof']}]);
  assert.throws(()=>renderArticle(article,{annotations}),/Missing compiled evidence/);
});

const document=body=>String.raw`\title{Source fidelity}\begin{document}`+body+String.raw`\end{document}`;

test('comments and inline environments preserve real proof text and source offsets',()=>{
  const source=document(String.raw`\begin{proof}
% \begin{invalid}
A matrix $\begin{pmatrix}1&0\\0&1\end{pmatrix}$ is invertible.
\begin{comment}\begin{unclosed}This is not published.\end{comment}
The conclusion remains visible.\end{proof}`);
  const article=parseArticle(source),html=renderArticle(article);
  for(const b of articleBlocks(article))assert.equal(source.slice(b.start,b.end),b.latex);
  assert.match(html,/invertible/);assert.match(html,/conclusion remains visible/);
  assert.doesNotMatch(html,/not published|unclosed|invalid/);
});

test('nested lists retain all items and explicit labels without moving source spans',()=>{
  const source=document(String.raw`\begin{enumerate}[label=(\roman*)]
\item[(A)] First outer claim.\begin{itemize}\item Inner one.\item Inner two.\end{itemize}
\item Second outer claim.\end{enumerate}`);
  const article=parseArticle(source),lists=articleBlocks(article).filter(b=>b.kind==='list');
  assert.equal(lists.length,2);assert.equal(lists[0].items.length,2);assert.equal(lists[1].items.length,2);
  for(const b of articleBlocks(article))assert.equal(source.slice(b.start,b.end),b.latex);
  const html=renderArticle(article);assert.match(html,/>\(A\)<\/span>/);assert.match(html,/Inner two/);assert.match(html,/Second outer claim/);
});

test('all figure panels and numerical table cells remain visible',()=>{
  const article=parseArticle(document(String.raw`\begin{figure}
\includegraphics[width=.32\textwidth]{left.png}\includegraphics[width=.32\textwidth]{right.png}
\caption{Both panels.}\label{fig:panels}\end{figure}
\begin{table}\begin{tabular}{lrr}\toprule Name & $x$ & $x^2$\\\midrule
A & $2$ & $4$\\\multicolumn{3}{c}{A spanning row}\\\bottomrule\end{tabular}
\caption{Exact entries.}\label{tab:entries}\end{table}`));
  const html=renderArticle(article);
  assert.equal((html.match(/<img /g)??[]).length,2);assert.match(html,/left.png/);assert.match(html,/right.png/);
  assert.match(html,/width:32%/);assert.match(html,/colspan="3"/);assert.match(html,/spanning row/);
  assert.equal(article.references['fig:panels'].number,'1');assert.equal(article.references['tab:entries'].number,'1');
});

test('declared theorem counters, parameterized notation and embedded bibliography are retained',()=>{
  const source=String.raw`\title{Counters}\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}\newtheorem{example}{Example}[subsection]
\newcommand{\square}[1]{#1^2}\DeclareMathOperator{\rank}{rank}
\begin{document}\section{First}\subsection{Subsection}
\begin{theorem}\label{thm:first}$\square{x}\ge0$.\end{theorem}
\begin{lemma}\label{lem:next}The next result.\end{lemma}
\begin{example}\label{ex:first}An example.\end{example}
See \cite{classic}.
\begin{thebibliography}{1}\bibitem{classic} A. Author. A classic theorem.\end{thebibliography}
\end{document}`;
  const article=parseArticle(source);
  assert.equal(article.references['thm:first'].number,'1.1');assert.equal(article.references['lem:next'].number,'1.2');
  assert.equal(article.references['ex:first'].number,'1.1.1');
  assert.match(renderArticle(article),/href="#bib-classic"/);assert.equal(article.bibliography.length,1);
});

test('starred headings, appendix headings and double-dollar mathematics are not discarded',()=>{
  const article=parseArticle(document(String.raw`\section{First}Text $$x^2\ge0$$ continues.
\section*{Acknowledgments}Thanks.\appendix\section{Calculation}$$1+1=2$$`));
  const headings=article.blocks.filter(b=>b.kind==='heading');
  assert.deepEqual(headings.map(b=>b.number),['1','','A']);
  const html=renderArticle(article);assert.match(html,/Acknowledgments/);assert.match(html,/A\. Calculation/);
  assert.equal((html.match(/class="katex-display"/g)??[]).length,2);
});

test('numbered outer rows count even without labels; nested cases and notag do not add numbers',()=>{
  const article=parseArticle(document(String.raw`\begin{align}
x &= \begin{cases}0&x<0\\1&x\ge0\end{cases}\label{eq:first}\\
y &= 2\\
z &= 3\notag\\
w &= 4\label{eq:last}\end{align}
\begin{equation}\label{eq:next}1=1\end{equation}`));
  assert.equal(article.references['eq:first'].number,'1');assert.equal(article.references['eq:last'].number,'3');
  assert.equal(article.references['eq:next'].number,'4');
});

test('a two-column title wrapper retains its content, source spans and pinned date',()=>{
  const source=document(String.raw`\twocolumn[{%
\begin{center}{\LARGE\bfseries A readable title\par}
An Author\textsuperscript{1}\par
An affiliation\par\today\end{center}
\begin{minipage}{.8\textwidth}An abstract with $x^2\ge0$.\end{minipage}
}]\section{The result}Original body. A citation dated 1980{\natexlab{a}}.`);
  const article=parseArticle(source);
  for(const b of articleBlocks(article))assert.equal(source.slice(b.start,b.end),b.latex);
  assert.throws(()=>renderArticle(article),/pinned sourceDate/);
  assert.throws(()=>renderArticle(article,{sourceDate:'2026-02-31'}),/pinned sourceDate/);
  const html=renderArticle(article,{sourceDate:'2026-09-29'});
  assert.match(html,/A readable title/);assert.match(html,/<sup>1<\/sup>/);
  assert.match(html,/29 September 2026/);assert.match(html,/An abstract/);assert.match(html,/Original body/);
  assert.match(html,/1980<span>a<\/span>/);
  assert.doesNotMatch(html,/\}\]/);
});

test('section equation numbering resets and appendix prefixes are preserved',()=>{
  const source=String.raw`\numberwithin{equation}{section}\begin{document}
\section{One}\begin{equation}\label{eq:first}1=1\end{equation}
\section*{Aside}\begin{equation}\label{eq:aside}2=2\end{equation}
\section{Two}\begin{equation}\label{eq:second}3=3\end{equation}
\appendix\section{Appendix}\begin{equation}\label{eq:appendix}4=4\end{equation}
\end{document}`;
  const article=parseArticle(source);
  assert.deepEqual(['eq:first','eq:aside','eq:second','eq:appendix'].map(k=>article.references[k].number),['1.1','1.2','2.1','A.1']);
});

test('ordinary subscripted names link to definitions in both TeX spellings',()=>{
  const article=parseArticle(document(String.raw`\begin{equation}\label{eq:L}L_b(x)=x\end{equation}
Use $L_b(u)$ and $L_{b}(v)$; $XL_b$ is a different name.`));
  const html=renderArticle(article,{definitions:{L_b:{label:'eq:L'}}});
  assert.equal((html.match(/<a href="#article-eq-L"/g)??[]).length,3);
  assert.throws(()=>renderArticle(article,{definitions:{'L+X':{label:'eq:L'}}}),/Unsupported definition notation/);
});


test('definition links preserve unbraced accents and single-token operands',()=>{
  const source=String.raw`\documentclass{article}
\begin{document}
\begin{equation}\label{def:L}L_b(u,v)=uv\end{equation}
$\check L_b$, $\hat{L_b}$, $x^{L_b}$ and $x^\xi$.
\begin{equation}\label{def:xi}\xi(C)=0\end{equation}
\end{document}`;
  const article=parseArticle(source);
  const html=renderArticle(article,{definitions:{L_b:{label:'def:L'},'\\xi':{label:'def:xi'}}});
  assert.match(html,/href="#article-def-L"/);
  assert.match(html,/href="#article-def-xi"/);
  assert.match(html,/class="accent/);
});


test('dsfont blackboard notation remains readable without editing the original source',()=>{
  const source=String.raw`\newcommand{\1}{\mathds{1}}\begin{document}
$\1_{\{x\le y\}}$ and $\mathds{R}$.\end{document}`;
  const article=parseArticle(source),html=renderArticle(article);
  assert.match(html,/mathvariant="double-struck"/);
  assert.match(html,/class="katex"/);
  assert.equal(article.macros['\\1'],String.raw`\mathds{1}`);
});


test('mathtools multiline subexpressions retain each original mathematical row',()=>{
  const source=String.raw`\begin{document}\begin{equation}\label{eq:split}
\begin{multlined}f(x)=x^2+1\\+x^3\end{multlined}\end{equation}\end{document}`;
  const article=parseArticle(source),html=renderArticle(article);
  assert.equal(article.references['eq:split'].number,'1');
  assert.equal(article.blocks[0].body.includes('\\begin{multlined}'),true);
  assert.match(html,/class="mtable"/);assert.match(html,/>3</);
});


test('quoted proof directions retain their mathematical content and quotation marks',()=>{
  const source=String.raw`\begin{document}\enquote{\emph{$\Rightarrow$}}. An argument.\end{document}`;
  const html=renderArticle(parseArticle(source));
  assert.match(html,/“<em>/);assert.match(html,/<\/em>”/);
  assert.match(html,/An argument/);assert.match(html,/⇒/);
});


test('ordinary title pages retain their explicit or source-pinned date',()=>{
  const pinned=String.raw`\title{The theorem}\author{An Author}\date{\today}
\begin{document}\maketitle Original body.\end{document}`;
  assert.throws(()=>renderArticle(parseArticle(pinned)),/pinned sourceDate/);
  assert.match(renderArticle(parseArticle(pinned),{sourceDate:'2025-09-08'}),/8 September 2025/);
  const literal=pinned.replace('\\today','A literal manuscript date');
  assert.match(renderArticle(parseArticle(literal)),/A literal manuscript date/);
});


test('explicit figure row breaks retain the original panel grid',()=>{
  const source=String.raw`\begin{document}\begin{figure}
\includegraphics[width=.32\textwidth]{one.png}
\includegraphics[width=.32\textwidth]{two.png}
\includegraphics[width=.32\textwidth]{three.png}\vspace{-.5em}\\
\includegraphics[width=.32\textwidth]{four.png}
\includegraphics[width=.32\textwidth]{five.png}
\includegraphics[width=.32\textwidth]{six.png}\\
\caption{Two rows, in source order.}\end{figure}\end{document}`;
  const article=parseArticle(source),html=renderArticle(article);
  assert.deepEqual(article.blocks[0].images.map(i=>i.row),[0,0,0,1,1,1]);
  assert.equal((html.match(/class="article-figure-row"/g)??[]).length,2);
  assert.equal((html.match(/<img /g)??[]).length,6);
  assert(html.indexOf('three.png')<html.indexOf('four.png'));
});

test('simple TeX definitions and unbraced LaTeX declarations retain parameters',()=>{
  const source=String.raw`\def\1{\mathds{1}}
\def\abs#1{\left\lvert#1\right\rvert}
\def\of#1{\left(#1\right)}
\newcommand\pair[2]{#1+#2}
\providecommand{\tr}{\operatorname{tr}}
\renewcommand\pair[2]{#1-#2}
\begin{document}$\1_{\{t\le v\}},\abs{x},f\of{y},\pair{u}{v},\tr(A)$\end{document}`;
  const article=parseArticle(source),html=renderArticle(article);
  assert.equal(article.macros['\\pair'],'#1-#2');
  assert.equal(article.macros['\\abs'],'\\left\\lvert#1\\right\\rvert');
  assert.match(html,/class="katex"/);
  for(const block of articleBlocks(article))assert.equal(source.slice(block.start,block.end),block.latex);
  assert.throws(()=>parseArticle(String.raw`\newcommand\unused[2]{#1}\begin{document}x\end{document}`),/Unsupported unused/);
});

test('sans-serif prose retains software names and embedded mathematics',()=>{
  const article=parseArticle(String.raw`\begin{document}The \textsf{R} package and \textsf{$x^2$}.\end{document}`);
  const html=renderArticle(article);
  assert.match(html,/font-family:ui-sans-serif,system-ui,sans-serif/);
  assert.match(html,/>R<\/span>/);
  assert.match(html,/class="katex"/);
});

test('explicit page breaks retain following results in the continuous reader',()=>{
  const source=String.raw`\begin{document}Before.\newpage After.\clearpage\begin{theorem}Still present.\end{theorem}\end{document}`;
  const article=parseArticle(source),html=renderArticle(article);
  assert.equal((html.match(/class="article-page-break"/g)||[]).length,2);
  assert.match(html,/After\./);
  assert.match(html,/Still present\./);
  for(const block of articleBlocks(article))assert.equal(source.slice(block.start,block.end),block.latex);
});

test('paragraph headings retain proof order without changing equation counters',()=>{
  const source=String.raw`\begin{document}\begin{proof}First.\paragraph{1. A calculation}Then $x^2$.\begin{equation}\label{eq:x}x=x\end{equation}\paragraph*{2. Finish}Done.\end{proof}\end{document}`;
  const article=parseArticle(source),html=renderArticle(article);
  const headings=articleBlocks(article).filter(b=>b.kind==='heading');
  assert.deepEqual(headings.map(b=>[b.level,b.number,b.title]),[[5,'','1. A calculation'],[5,'','2. Finish']]);
  assert.equal(article.references['eq:x'].number,'1');
  assert(html.indexOf('First.')<html.indexOf('1. A calculation'));
  assert(html.indexOf('1. A calculation')<html.indexOf('2. Finish'));
  for(const block of articleBlocks(article))assert.equal(source.slice(block.start,block.end),block.latex);
});

test('bibliography metadata preserves printed authors, mathematical titles and links',()=>{
  const bib=String.raw`\begin{thebibliography}{1}\bibitem{one}\bibinfo{author}{A. Author}, \bibinfo{year}{2026}. \bibinfo{title}{A bound for $\rho$}. \URLprefix\url{https://example.org/} \DOIprefix\doi{10.1/test}.\end{thebibliography}`;
  const article=parseArticle(String.raw`\begin{document}See \cite{one}.\end{document}`,bib),html=renderArticle(article);
  assert.match(html,/A\. Author/);
  assert.match(html,/2026/);
  assert.match(html,/A bound for/);
  assert.match(html,/class="katex"/);
  assert.match(html,/href="https:\/\/doi.org\/10.1\/test"/);
});


test('contents links with theorem references and clickable notation do not nest anchors',()=>{
  const source=String.raw`\begin{document}\begin{theorem}\label{thm:t}$\xi=\xi$\end{theorem}\begin{equation}\label{eq:xi}\xi=x\end{equation}\section{Proof of Theorem~\ref{thm:t} for $\xi$}\label{sec:proof}Done.\end{document}`;
  const html=renderArticle(parseArticle(source),{definitions:{'\\xi':{label:'eq:xi'}}});
  const contents=html.match(/<details class="article-contents">([\s\S]*?)<\/details>/)[1];
  assert.equal((contents.match(/<a\b/g)||[]).length,1);
  assert.match(contents,/href="#article-sec-proof"/);
  assert.match(contents,/Theorem&nbsp;0\.1/);
  assert.match(contents,/class="katex"/);
  assert.match(html,/<h2[^>]*>[^]*?<a href="#article-thm-t">0\.1<\/a>/);
});


test('duplicate source labels require explicit reference choices and separately bindable occurrences',()=>{
  const source=String.raw`\begin{document}\begin{equation}\label{eq:same}x=x\end{equation}\begin{equation}\label{eq:same}y=y\end{equation}See \eqref{eq:same}.\end{document}`;
  assert.throws(()=>parseArticle(source),/Duplicate source label/);
  for(const choice of [0,3,1.5,'2'])assert.throws(()=>parseArticle(source,'',{referenceChoices:{'eq:same':choice}}),/Invalid reference occurrence/);
  assert.throws(()=>parseArticle(source,'',{referenceChoices:{'eq:missing':1,'eq:same':2}}),/Unknown reference choice/);
  const article=parseArticle(source,'',{referenceChoices:{'eq:same':2}}),html=renderArticle(article);
  assert.equal(article.references['eq:same'].number,'2');
  assert.equal(article.referenceOccurrences['eq:same'][0].number,'1');
  assert.match(html,/id="article-eq-same-occurrence-1"/);
  assert.match(html,/id="article-eq-same-occurrence-2"/);
  assert.match(html,/href="#article-eq-same-occurrence-2">\(2\)<\/a>/);
  assert.match(html,/Source cross-reference notice/);
  assert.throws(()=>resolveBindings(article,[{label:'eq:same',declarations:['A']}]),/exactly once/);
  const blocks=articleBlocks(article),bindings=resolveBindings(article,[{label:'eq:same',occurrence:1,declarations:['A']},{label:'eq:same',occurrence:2,declarations:['B']}]);
  assert.deepEqual(bindings[blocks[0].id].map(b=>b.declaration),['A']);
  assert.deepEqual(bindings[blocks[1].id].map(b=>b.declaration),['B']);
  assert.throws(()=>resolveBindings(article,[{label:'eq:same',occurrence:3,declarations:['A']}]),/exactly once/);
  assert.throws(()=>resolveBindings(article,[{kind:'math',quote:'x=x',occurrence:1,declarations:['A']}]),/Invalid binding occurrence/);
  for(const block of blocks)assert.equal(source.slice(block.start,block.end),block.latex);
});


test('author thanks preserve affiliation notes and native letters',()=>{
  const source=String.raw`\author{A\thanks{Universit\"at A, Stra\ss e 1.}\and B\thanks{Universit\"at B.}}\begin{document}\maketitle Text.\end{document}`;
  const html=renderArticle(parseArticle(source));
  assert.match(html,/href="#article-author-note-1">\*<\/a>/);
  assert.match(html,/href="#article-author-note-2">†<\/a>/);
  assert.match(html,/Universität A, Straße 1\./);
  assert.match(html,/Universität B\./);
  assert(html.indexOf('article-author-note-1"')<html.indexOf('class="article-contents"'));
  assert.throws(()=>renderArticle(parseArticle(document(String.raw`\thanks{Unplaced note}`))),/outside the author field/);
});


test('decorated coefficient definitions take precedence over the underlying coefficient',()=>{
  const source=String.raw`\documentclass{article}
\begin{document}
\begin{equation}\label{rho}\rho(C)=0\end{equation}
\begin{equation}\label{upper}\overline{\rho}(x)=1\end{equation}
\begin{equation}\label{lower}\underline{\rho}(x)=-1\end{equation}
$\rho(C)$, $\overline\rho(x)$ and $\underline{\rho}(x)$.
\end{document}`;
  const html=renderArticle(parseArticle(source),{definitions:{'\\rho':{label:'rho'},'\\overline{\\rho}':{label:'upper'},'\\underline{\\rho}':{label:'lower'}}});
  assert.match(html,/href="#article-upper"/);assert.match(html,/href="#article-lower"/);
  const paragraph=html;
  assert.equal((paragraph.match(/href="#article-rho"/g)||[]).length,4);
  assert.equal((paragraph.match(/href="#article-upper"/g)||[]).length,4);
  assert.equal((paragraph.match(/href="#article-lower"/g)||[]).length,4);
});


test('shared author footnote marks reuse an existing affiliation explicitly',()=>{
  const source=String.raw`\documentclass{article}\author{A\thanks{Department one}\and B\thanks{Department two}\and C\footnotemark[1]}\begin{document}\maketitle Text.\end{document}`;
  const html=renderArticle(parseArticle(source));
  assert.equal((html.match(/href="#article-author-note-1"/g)||[]).length,2);
  assert.equal((html.match(/id="article-author-note-1"/g)||[]).length,1);
  for(const mark of ['3','0','x',''])assert.throws(()=>renderArticle(parseArticle(source.replace('[1]','['+mark+']'))),/Unresolved author footnote/);
  assert.throws(()=>renderArticle(parseArticle(String.raw`\documentclass{article}\begin{document}\footnotemark[1]\end{document}`)),/Unresolved author footnote/);
});


test('source figure widths respect both line width and text width fractions',()=>{
  const source=String.raw`\documentclass{article}\begin{document}\begin{figure}\includegraphics[width=0.72\linewidth]{figure.png}\caption{Original}\end{figure}\end{document}`;
  for(const tex of [source,source.replace('linewidth','textwidth')])assert.match(renderArticle(parseArticle(tex)),/style="width:72%;min-width:0"/);
});


test('unnumbered proof labels retain pinned published page references and small caps',()=>{
  const source=String.raw`\documentclass{article}\begin{document}See page \pageref{proof:one}. \textsc{CheckAvg}.\begin{proof}\label{proof:one}An argument.\end{proof}\end{document}`;
  const article=parseArticle(source),html=renderArticle(article,{pageReferences:{'proof:one':18}});
  assert.equal(article.references['proof:one'].number,'');
  assert.match(html,/href="#article-proof-one" title="Page in the published PDF">18/);
  assert.match(html,/id="article-proof-one"/);assert.match(html,/font-variant:small-caps/);
  assert.throws(()=>renderArticle(article),/Missing pinned page reference/);
  for(const value of [0,-1,'18',1.5])assert.throws(()=>renderArticle(article,{pageReferences:{'proof:one':value}}),/Missing pinned page/);
  assert.throws(()=>renderArticle(article,{pageReferences:{'proof:one':18,unknown:2}}),/Unused page/);
  assert.throws(()=>renderArticle(parseArticle(source.replace('proof:one}.','unknown}.')),{pageReferences:{unknown:18}}),/Missing pinned page/);
});


test('underlined prose retains its proof heading and embedded mathematics',()=>{
  const source=String.raw`\documentclass{article}\begin{document}\underline{Case $x>0$:} A calculation.\end{document}`;
  const html=renderArticle(parseArticle(source));
  assert.match(html,/text-decoration:underline/);assert.match(html,/Case/);assert.match(html,/katex/);assert.match(html,/A calculation/);
});


test('the standard article title uses the inspected pinned date when LaTeX defaults to today',()=>{
  const source=String.raw`\documentclass{article}\title{A theorem}\begin{document}\maketitle Text.\end{document}`;
  assert.match(renderArticle(parseArticle(source),{sourceDate:'2026-05-25'}),/class="article-date">25 May 2026/);
  const empty=source.replace('\\title','\\date{}\\title');
  assert(!renderArticle(parseArticle(empty),{sourceDate:'2026-05-25'}).includes('class="article-date"'));
  // Without an inspected source date the reader must not invent today's date.
  assert(!renderArticle(parseArticle(source)).includes('class="article-date"'));
});


test('third-level headings preserve their counters and reset within sections',()=>{
  const source=String.raw`\begin{document}\section{Main}\subsection{A}\subsubsection{First}\label{first}Body.\subsubsection{Second}More.\subsection{B}\subsubsection{Third}Done.\appendix\section{Proofs}\subsection{Cases}\subsubsection{End}\end{document}`;
  const article=parseArticle(source),heads=articleBlocks(article).filter(b=>b.kind==='heading');
  assert.deepEqual(heads.map(b=>b.number),['1','1.1','1.1.1','1.1.2','1.2','1.2.1','A','A.1','A.1.1']);
  assert.equal(article.references.first.number,'1.1.1');
  assert.match(renderArticle(article),/<h4[^>]*>1\.1\.1\. First<\/h4>/);
  for(const b of articleBlocks(article))assert.equal(source.slice(b.start,b.end),b.latex);
});

test('multiple captions in a float keep separate figures and ignore commented image commands',()=>{
  const source=String.raw`\begin{document}\tableofcontents\begin{figure}\centering\includegraphics{a.png}
%\includegraphics{hidden.png}
\caption{First}\label{fig:a}\\[1em]\includegraphics{b.png}\includegraphics{c.png}\caption{Second}\label{fig:b}\end{figure}\begin{figure}\includegraphics{d.png}\caption{Third}\label{fig:d}\end{figure}\end{document}`;
  const article=parseArticle(source),figures=articleBlocks(article).filter(b=>b.kind==='figure');
  assert.deepEqual(figures.map(b=>[b.number,b.caption,b.images.map(i=>i.image)]),[['1','First',['a.png']],['2','Second',['b.png','c.png']],['3','Third',['d.png']]]);
  assert.equal(article.references['fig:b'].number,'2');assert.equal(article.references['fig:d'].number,'3');
  const html=renderArticle(article);assert.equal((html.match(/<img /g)||[]).length,4);assert.match(html,/Figure 2\./);assert.match(html,/Second/);
  assert(!html.includes('hidden.png'));
  for(const b of articleBlocks(article))assert.equal(source.slice(b.start,b.end),b.latex);
});


test('table markers retain check and cross meanings in prose and math without becoming verification claims',()=>{
  const source=String.raw`\newcommand{\yes}{\color{green}{\ding{51}}\color{black}}\newcommand{\no}{\color{red}{\ding{55}}\color{black}}\newcommand{\conv}{{\scalebox{1.5}{\raisebox{-0.2ex}{$\ast$}}}}\begin{document}w.l.o.g.\@ $A\conv B$.\begin{table}\begin{tabular}{ll}\yes & $\text{\no}^*$\\\end{tabular}\caption{Numerical markers}\end{table}\end{document}`;
  const html=renderArticle(parseArticle(source));assert.match(html,/✓/);assert.match(html,/×/);assert.match(html,/Numerical markers/);assert.match(html,/class="katex"/);
  assert(!html.includes('Open verification'));assert(!html.includes('undefined'));
  assert.throws(()=>renderArticle(parseArticle(document('$\\ding{99}$'))),/Unsupported dingbat/);
});


test('equation references inside mathematics retain their printed numbers and local links',()=>{
  const source=String.raw`\begin{document}\begin{align}a=a\label{first}\\b=b\label{second}\end{align}\[\eqref{second}\geq\eqref{first},\quad\text{by }\ref{first}\]\end{document}`;
  const html=renderArticle(parseArticle(source));assert.match(html,/href="#article-second"/);assert.match(html,/\\text\{\(2\)\}/);assert.match(html,/\\text\{\(1\)\}/);
  assert.throws(()=>renderArticle(parseArticle(document('$\\eqref{unknown}$'))),/Unknown reference unknown/);
});
