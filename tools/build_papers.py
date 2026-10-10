#!/usr/bin/env python3
"""Build native-math PDFs from the two authoritative Markdown masters.

Requires Python >=3.10, Pandoc >=3, XeLaTeX, Poppler, and fonts listed in
materials/README.md. No network access or package installation is performed.
Generated outputs are checked before replacing reading copies.
"""
from __future__ import annotations
import argparse, copy, hashlib, json, os, re, shutil, subprocess, sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TEMPLATE = ROOT / 'tools/typesetting/paper.tex'
BUILD = ROOT / 'build/papers'
LABEL_RE = r'(?:Theorem|Lemma|Proposition|Corollary|定理|引理|命题|推论)\s*([1-9]\d*\.\d+)'

def run(args, *, cwd=ROOT, env=None, input=None):
    p = subprocess.run([str(a) for a in args], cwd=cwd, env=env, input=input,
                       text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if p.returncode:
        raise RuntimeError(f"Command failed ({p.returncode}): {' '.join(map(str,args))}\n{p.stdout[-6000:]}")
    return p.stdout

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def text_of(inlines):
    out = []
    for x in inlines:
        t, c = x['t'], x.get('c')
        if t in ('Str', 'Code'): out.append(c if t == 'Str' else c[1])
        elif t in ('Space', 'SoftBreak', 'LineBreak'): out.append(' ')
        elif t == 'Math': out.append(c[1])
        elif t in ('Strong','Emph','SmallCaps','Strikeout','Superscript','Subscript'): out.append(text_of(c))
        elif t in ('Link','Image'): out.append(text_of(c[1]))
    return ''.join(out)

def raw(s, block=False): return {'t':'RawBlock' if block else 'RawInline', 'c':['latex',s]}

def to_tex(inlines, version):
    doc = {'pandoc-api-version':version,'meta':{},'blocks':[{'t':'Plain','c':inlines}]}
    return run(['pandoc','-f','json','-t','latex','--wrap=none'],input=json.dumps(doc)).strip()

def strip_text_prefix(inlines, count):
    result=copy.deepcopy(inlines)
    while count and result:
        node=result.pop(0)
        if node['t']=='Str':
            if len(node['c'])>count:
                node['c']=node['c'][count:]; result.insert(0,node); count=0
            else: count-=len(node['c'])
        elif node['t'] in ('Space','SoftBreak'): count-=1
        else: raise ValueError('Unexpected formatted content in a heading number')
    if count: raise ValueError('Heading prefix exceeds inline length')
    return result

def math_layout(s):
    """Line breaks only; these rules never change a mathematical token."""
    s=s.strip()
    # Separate long lists of independent definitions at explicit source separators.
    if '\\begin{' not in s and len(s)>145 and '\\qquad' in s:
        return '\\begin{gathered}\n' + s.replace('\\qquad', '\\\\\n') + '\n\\end{gathered}'
    if s.startswith('|f(1)-G(1)|'):
        return '\\begin{aligned}\n' + s.replace('\\le ', '&\\le ',1).replace('+\\frac{R}', '\\\\&\\quad+\\frac{R}',1) + '\n\\end{aligned}'
    if s.startswith('\\operatorname{per}A_T\n=\\sum'):
        s=s.replace('\n=', '\n&=',1).replace('\\operatorname{per}A[R,C]\\,', '\\\\&\\quad\\operatorname{per}A[R,C]\\,',1)
        s=s.replace('\\operatorname{per}A[I,F\\setminus C]\\,','\\\\&\\quad\\operatorname{per}A[I,F\\setminus C]\\,',1)
        return '\\begin{aligned}\n'+s+'\n\\end{aligned}'
    return s

def rewrite_inlines(inlines, labels, sections, refs, lang="en"):
    # Link only prose text; math, code and existing link destinations stay intact.
    result=[]
    for x in inlines:
        if x['t']=='Math' and x['c'][0]['t']=='InlineMath' and x['c'][1].strip()==r'\square':
            # Bind the end-of-proof marker to the preceding word so it cannot
            # become the sole item on a new line or page.
            while result and result[-1]['t'] in ('Space','SoftBreak'):
                result.pop()
            result.append(raw(r'\nobreak\hspace{.5em}\mbox{$\square$}'))
            continue
        if x['t']=='Math':
            x=copy.deepcopy(x)
            if x['c'][0]['t']=='DisplayMath': x['c'][1]=re.sub(r'\n[ \t]*\n+', '\n', math_layout(x['c'][1]))
        elif x['t']=='Code':
            escapes={'\\':r'\textbackslash{}','{':r'\{','}':r'\}','_':r'\_\allowbreak{}','.':r'.\allowbreak{}','/':r'/\allowbreak{}','-':'{-}','&':r'\&','%':r'\%','$':r'\$','#':r'\#','~':r'\textasciitilde{}','^':r'\textasciicircum{}'}
            code=x['c'][1]
            escaped=''.join(escapes.get(ch,ch)+(r'\allowbreak{}' if ch.islower() and i+1<len(code) and code[i+1].isupper() else '') for i,ch in enumerate(code))
            if re.fullmatch(r'[0-9a-f]{40,64}',code):
                escaped=r'\allowbreak{}'.join(code[i:i+8] for i in range(0,len(code),8))
            x=raw(r'\texttt{'+escaped+'}')
        elif x['t']=='Link':
            x=copy.deepcopy(x)
            label=text_of(x['c'][1])
            target=x['c'][2][0]
            if not re.match(r'[A-Za-z][A-Za-z0-9+.-]*:',target) and not target.startswith('#'):
                source_path=(ROOT/'materials'/target).resolve()
                if not source_path.is_file() or not source_path.is_relative_to(ROOT):
                    raise ValueError('Missing relative source link: '+target)
                archive_path=str(source_path.relative_to(ROOT))
                note=[{'t':'Str','c':'源码包：' if lang=='zh' else 'Source archive: '},raw(r'\path|'+archive_path+'|')]
                x={'t':'Span','c':[['',[],[]],x['c'][1]+[{'t':'Note','c':[{'t':'Para','c':note}]}]]}
            elif re.match(r'(?:DOI: )?10\.\d{4,}/',label):
                x['c'][1]=[raw(r'\nolinkurl{'+label+'}')]
        elif x['t'] in ('Emph','Strong','SmallCaps','Strikeout'):
            x=copy.deepcopy(x); x['c']=rewrite_inlines(x['c'],labels,sections,refs,lang)
        result.append(x)
    # Match across Pandoc's separate word/space nodes while leaving semantic spans.
    out=[]; i=0
    while i<len(result):
        if result[i]['t'] not in ('Str','Space','SoftBreak'):
            out.append(result[i]); i+=1; continue
        j=i
        while j<len(result) and result[j]['t'] in ('Str','Space','SoftBreak'): j+=1
        text=text_of(result[i:j])
        pattern = r'('+LABEL_RE+r'|(?:Section|Sections|Appendix|附录)\s+([A-Z](?:\.\d+)*|\d+(?:\.\d+)*)|第\s*([A-Z](?:\.\d+)*|\d+(?:\.\d+)*)\s*节|\[(\d+)(?:[,，][^\]]*)?\])'
        last=0
        for m in re.finditer(pattern,text):
            ident=m.group(2) or m.group(3) or m.group(4) or m.group(5)
            key=('thm-'+ident if m.group(2) else 'bib-'+ident if m.group(5) else 'sec-'+ident)
            exists=key in labels or key in sections or key in refs
            if not exists:
                if m.group(2) or m.group(5): raise ValueError(f'Unresolved cross-reference: {m.group(0)}')
                continue
            if m.start()>last: out.append({'t':'Str','c':text[last:m.start()]})
            out.append(raw(r'\paperref{'+key+'}{'+m.group(0)+'}'))
            last=m.end()
        if last<len(text): out.append({'t':'Str','c':text[last:]})
        i=j
    return out

def prepare(lang, src):
    ast=json.loads(run(['pandoc','--from=markdown+tex_math_dollars+raw_tex-smart','--to=json'],input=src))
    version=ast['pandoc-api-version']; blocks=ast['blocks']
    if blocks[0]['t']!='Header' or blocks[0]['c'][0]!=1: raise ValueError('Master must start with one title')
    title=blocks.pop(0)['c'][2]
    # The established master format has four front-matter paragraphs.
    front=[]
    while blocks and blocks[0]['t'] in ('Para','Plain') and len(front)<4: front.append(blocks.pop(0)['c'])
    if len(front)!=4: raise ValueError('Expected author, affiliation, email and revision date before abstract')
    author=front[0]+[raw(r'\\')]+front[1]+[raw(r'\\')]+front[2]
    ast['meta']={'title':{'t':'MetaInlines','c':title},'author':{'t':'MetaInlines','c':author},
                 'pdfauthor':{'t':'MetaInlines','c':front[0]},'date':{'t':'MetaInlines','c':front[3]}}
    if lang=='zh': ast['meta']['chinese']={'t':'MetaBool','c':True}
    labels={}; sections={}; refs={}
    for b in blocks:
        if b['t']=='Header':
            heading=text_of(b['c'][2]); m=re.match(r'(?:(?:Appendix|附录)\s+)?([A-Z](?:\.\d+)*|\d+(?:\.\d+)*)[.．]?\s+',heading)
            if m:
                ident=m.group(1)
                if 'sec-'+ident in sections: raise ValueError('Duplicate section number: '+ident)
                sections['sec-'+ident]=heading
        elif b['t'] in ('Para','Plain') and b['c']:
            first=b['c'][0]
            if first['t']=='Strong':
                m=re.match(LABEL_RE,text_of(first['c']))
                if m:
                    key='thm-'+m.group(1)
                    if key in labels: raise ValueError('Duplicate theorem number: '+key)
                    labels[key]=text_of(first['c'])
            m=re.match(r'^\[(\d+)\]\s',text_of(b['c']))
            if m: refs['bib-'+m.group(1)]=text_of(b['c'])
    transformed=[]; appendix=False
    for b in blocks:
        if b['t']=='Header':
            level, attr, content=b['c']; heading=text_of(content)
            m=re.match(r'(?:(?:Appendix|附录)\s+)?([A-Z](?:\.\d+)*|\d+(?:\.\d+)*)[.．]?\s+(.*)',heading)
            if m:
                number,name=m.groups()
                if number[0].isalpha() and not appendix:
                    transformed.append(raw(r'\appendix',True)); appendix=True
                command={2:'section',3:'subsection',4:'subsubsection'}[level]
                # Strip plain-text numbering so LaTeX provides true counter labels.
                title_tex=to_tex(strip_text_prefix(content,m.start(2)),version)
                transformed.append(raw(r'\Needspace{'+('9' if level==2 else '7')+r'\baselineskip}'+'\n'+'\\'+command+'{'+title_tex+'}\\label{sec-'+number+'}',True))
            else:
                title_tex=to_tex(content,version)
                ident='abstract' if heading in ('Abstract','摘要') else 'references' if heading in ('References','参考文献') else attr[0]
                transformed.append(raw((r'\Needspace{6\baselineskip}' if ident=='references' else '')+r'\section*{'+title_tex+'}\n'+r'\phantomsection\addcontentsline{toc}{section}{'+title_tex+'}\\label{sec-'+ident+'}'+(r'\small' if ident=='references' else ''),True))
            continue
        if b['t'] in ('Para','Plain'):
            b=copy.deepcopy(b); ins=b['c']
            if ins and ins[0]['t']=='Strong':
                heading=text_of(ins[0]['c']); m=re.match(LABEL_RE,heading)
                if m:
                    ins[0]=raw((r'\Needspace{12\baselineskip}' if m.group(1)=='1.1' else '')+r'\paperstatement{'+to_tex(ins[0]['c'],version)+'}{'+m.group(1)+'}{thm-'+m.group(1)+'}')
            m=re.match(r'^\[(\d+)\]\s',text_of(ins))
            if m:
                # Hanging bibliography with linkable entries and preserved source wording.
                n=m.group(1)
                for node in ins:
                    if node['t']=='Link' and re.match(r'DOI: 10\.\d{4,}/',text_of(node['c'][1])):
                        node['c'][1]=[raw(r'\nolinkurl{'+text_of(node['c'][1])+'}')]
                b['c']=[raw(r'\hypertarget{bib-'+n+'}{}\\phantomsection\\label{bib-'+n+'}\\noindent ')] + ins
            else: b['c']=rewrite_inlines(ins,labels,sections,refs,lang)
        elif b['t'] in ('BulletList','OrderedList'):
            lists=b['c'] if b['t']=='BulletList' else b['c'][1]
            for item in lists:
                for para in item:
                    if para['t'] in ('Para','Plain'): para['c']=rewrite_inlines(para['c'],labels,sections,refs,lang)
        transformed.append(b)
    ast['blocks']=transformed
    tex=run(['pandoc','-f','json','-t','latex','--standalone','--wrap=none','--no-highlight','--template',TEMPLATE],input=json.dumps(ast))
    # Keep a prose lead-in in the same TeX paragraph as its following display,
    # enabling amsmath's predisplay penalty to prevent stranded introductions.
    tex=tex.replace('\n\n'+r'\[','\n'+r'\[')
    tex=tex.replace(r'\]'+ '\n'+r'\[',r'\]'+ '\n'+r'\nopagebreak[3]'+r'\[')
    return tex, {'sections':sections,'statements':labels,'references':refs}

def tex_env(work):
    env=os.environ.copy()
    env.setdefault('SOURCE_DATE_EPOCH','1791590400')
    env['FORCE_SOURCE_DATE']='1'
    runtime=BUILD/'tex-runtime'; runtime.mkdir(parents=True,exist_ok=True)
    # Some minimal distributions ship TeX files but no filename DB or formats.
    # A local, network-free format build avoids changing system configuration.
    if not subprocess.run(['kpsewhich','article.cls'],stdout=subprocess.DEVNULL).returncode:
        return env
    trees=[Path('/usr/share/texlive/texmf-dist'),Path('/usr/share/texmf'),Path('/etc/texmf')]
    if not trees[0].exists(): raise RuntimeError('TeX installation has no article.cls')
    env['TEXMF']='{'+','.join(str(p) for p in trees if p.exists())+'}'
    env['TEXMFVAR']=str(runtime); env['TEXMFCONFIG']=str(runtime)
    env['TEXFORMATS']=str(runtime)+'//:'
    env['XDG_CACHE_HOME']=str(runtime/'cache')
    (runtime/'cache').mkdir(exist_ok=True)
    if not (runtime/'xelatex.fmt').exists():
        log=run(['xetex','-ini','-etex','-interaction=nonstopmode','-halt-on-error','-jobname=xelatex','xelatex.ini'],cwd=runtime,env=env)
        (runtime/'format-build.log').write_text(log)
    return env

def synchronize_sections(lang, src, *, check=False):
    # New reader-first structure. Each slice preserves exact master bytes.
    headings=list(re.finditer(r'^## (?:([1-9]\d*)\.\s+|(?:Appendix|附录)\s+([A-Z])(?:\.|\s))',src,re.M))
    if not headings: raise ValueError('No numbered sections found')
    pieces={}
    for i,m in enumerate(headings):
        key=m.group(1) or m.group(2); start=0 if i==0 else m.start(); end=headings[i+1].start() if i+1<len(headings) else len(src)
        pieces['section_'+key.lower()+'_'+lang+'.md']=src[start:end]
    dest=ROOT/'materials/sections'; dest.mkdir(exist_ok=True)
    for name,content in pieces.items():
        path=dest/name
        if check:
            if not path.exists() or path.read_text()!=content: raise ValueError('Unsynchronized section '+name)
        else: path.write_text(content)
    if ''.join(pieces.values())!=src: raise ValueError('Section slices do not reconstruct the master')
    if not check:
        for old in ('opening','permanent','scaling','global','closing'):
            stale=dest/f'{old}_{lang}.md'
            if stale.exists(): stale.unlink()
    return [str(Path('materials/sections')/x) for x in pieces]

def build(lang, args):
    source=ROOT/f'materials/manuscript_{lang}.md'; src=source.read_text()
    work=BUILD/lang; work.mkdir(parents=True,exist_ok=True)
    tex,index=prepare(lang,src)
    display_count=len(re.findall(r'^\$\$\s*$',src,re.M))//2
    if tex.count(r'\[')!=display_count:
        raise ValueError(f'{lang}: display-math count changed during export')
    texpath=work/f'manuscript_{lang}.tex'; texpath.write_text(tex)
    (work/'crossref-index.json').write_text(json.dumps(index,ensure_ascii=False,indent=2)+'\n')
    if args.tex_only: return {'language':lang,'tex':str(texpath.relative_to(ROOT))}
    env=tex_env(work)
    for iteration in range(3):
        out=run(['xelatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-file-line-error',texpath.name],cwd=work,env=env)
        (work/f'pass-{iteration+1}.stdout.log').write_text(out)
    log=texpath.with_suffix('.log').read_text(errors='replace')
    aux=texpath.with_suffix('.aux').read_text(errors='replace')
    label_values={}
    for key in list(index['sections'])+list(index['statements']):
        hit=re.search(r'\\newlabel\{'+re.escape(key)+r'\}\{\{([^}]*)\}',aux)
        expected=key.split('-',1)[1]
        if not hit or hit.group(1)!=expected:
            raise ValueError(f'Number mismatch for {key}: expected {expected}; got {hit.group(1) if hit else None}')
        label_values[key]=hit.group(1)
    problems=[line for line in log.splitlines() if re.search(r'Overfull|Missing character|undefined|multiply defined',line)]
    pdf=texpath.with_suffix('.pdf')
    info=run(['pdfinfo',pdf]); pages=int(re.search(r'^Pages:\s+(\d+)',info,re.M).group(1))
    if args.render:
        render=work/'pages'; render.mkdir(exist_ok=True)
        for p in render.glob('page-*.png'): p.unlink()
        run(['pdftoppm','-r','110','-png',pdf,render/'page'])
    report={'language':lang,'display_math_blocks':display_count,'master_sha256':sha(source),'tex_sha256':sha(texpath),'pdf_sha256':sha(pdf),'pages':pages,
            'crossrefs':{k:len(v) for k,v in index.items()},'compiler_problems':problems,
            'compiler_notes':[x for x in log.splitlines() if 'Warning' in x or 'Underfull' in x],
            'toolchain':{tool:run([tool,'--version']).splitlines()[0] for tool in ('pandoc','xelatex')},
            'source_date_epoch':env['SOURCE_DATE_EPOCH'],
            'label_values':label_values,'rendered':args.render,'visual_review':'pending','compiled_at':datetime.now(timezone.utc).isoformat()}
    (work/'build-report.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    if problems and not args.allow_layout_warnings: raise RuntimeError(f'{lang}: compiler quality checks failed:\n'+'\n'.join(problems))
    if source.read_text()!=src: raise ValueError(f'{lang}: master changed during build; rerun after editing finishes')
    return report

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lang',choices=['en','zh','both'],default='both')
    p.add_argument('--tex-only',action='store_true')
    p.add_argument('--render',action='store_true',help='Render every PDF page to PNG at 110 dpi for visual inspection')
    p.add_argument('--publish',action='store_true',help='Replace generated TeX and reading PDFs after compiler checks')
    p.add_argument('--sync-sections',action='store_true')
    p.add_argument('--allow-layout-warnings',action='store_true',help='For investigation only; not for release')
    args=p.parse_args()
    for tool in ['pandoc','xelatex','kpsewhich','pdfinfo','pdftoppm']:
        if not shutil.which(tool): raise SystemExit('Required executable not found: '+tool)
    result=[build(lang,args) for lang in (['en','zh'] if args.lang=='both' else [args.lang])]
    if args.lang=='both' and not args.tex_only:
        en=json.loads((BUILD/'en/crossref-index.json').read_text())
        zh=json.loads((BUILD/'zh/crossref-index.json').read_text())
        for category in ('sections','statements','references'):
            if set(en[category])!=set(zh[category]):
                raise ValueError('Bilingual '+category+' numbering differs: '+str(set(en[category])^set(zh[category])))
    if not args.tex_only:
        for report in result:
            lang=report['language']; source=ROOT/f'materials/manuscript_{lang}.md'
            if sha(source)!=report['master_sha256']: raise ValueError(f'{lang}: master changed before publication')
        for report in result:
            lang=report['language']
            if args.publish:
                shutil.copyfile(BUILD/lang/f'manuscript_{lang}.tex',ROOT/f'materials/manuscript_{lang}.tex')
                shutil.copyfile(BUILD/lang/f'manuscript_{lang}.pdf',ROOT/f'papers/tournament_hamilton_paths_{lang}.pdf')
            if args.sync_sections:
                report['section_files']=synchronize_sections(lang,(ROOT/f'materials/manuscript_{lang}.md').read_text())
    print(json.dumps(result,ensure_ascii=False,indent=2))

if __name__=='__main__':
    try: main()
    except (RuntimeError,ValueError) as exc: print(str(exc),file=sys.stderr); sys.exit(1)
