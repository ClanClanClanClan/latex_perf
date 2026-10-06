#!/usr/bin/env python3
# AI-scoping (OPEN-129) census of sample 2: classes, packages, vendored .cls/.sty, and a coarse
# "\\emph-relevant" configuration signature. Regex instrument over every .tex of each paper
# (comments stripped per line); see docs/v27/spike/AI-scoping.md §3.
import json,re,os,collections,glob
ROOT=os.environ["LP_REAL_CORPUS"]  # the arXiv corpus (not in the repo)
REPO=os.environ.get("LP_REPO", os.path.join(os.path.dirname(os.path.abspath(__file__)),"../../../../.."))
d=json.load(open(REPO+"/corpora/real_roots/results_sample2.json"))
docs=d['docs']
pk=collections.Counter(); cls=collections.Counter(); cfg=set(); privcls=0; privsty=0; missing=0; per=[]
for r in docs:
    p=os.path.join(ROOT,r['arxiv_id'])
    if not os.path.isdir(p): missing+=1; continue
    src=""
    for f in glob.glob(p+"/**/*.tex",recursive=True):
        try: src+=open(f,errors='replace').read()+"\n"
        except: pass
    src="\n".join(l.split('%')[0] if not l.lstrip().startswith('%') else '' for l in src.splitlines())
    c=re.findall(r'\\documentclass\s*(?:\[[^\]]*\])?\s*\{([^}]*)\}',src)
    c=c[0].strip() if c else '?'
    pkgs=set()
    for m in re.findall(r'\\(?:usepackage|RequirePackage)\s*(?:\[[^\]]*\])?\s*\{([^}]*)\}',src):
        for x in m.split(','):
            x=x.strip()
            if x: pkgs.add(x)
    local={os.path.splitext(os.path.basename(f))[0]:os.path.splitext(f)[1] for f in glob.glob(p+"/**/*.cls",recursive=True)+glob.glob(p+"/**/*.sty",recursive=True)}
    if any(e=='.cls' for e in local.values()): privcls+=1
    if any(e=='.sty' for e in local.values()): privsty+=1
    cls[c]+=1
    for x in pkgs: pk[x]+=1
    cfg.add((c,frozenset(pkgs)))
    per.append((c,pkgs,local))
n=len(per)
print("papers",n,"missing",missing,"distinct pkgs",len(pk),"distinct (class,pkgset)",len(cfg),"priv cls",privcls,"priv sty",privsty)
print("top pkgs",[(k,v) for k,v in pk.most_common(25)])
print("top classes",cls.most_common(12))
# papers whose package set is within the top-K most common packages, no private cls/sty
for K in (10,20,40,80):
    top={k for k,_ in pk.most_common(K)}
    ok=sum(1 for c,s,l in per if s<=top and c in ('article','amsart') and not l)
    print("K",K,"papers with article/amsart, no local cls/sty, all pkgs in topK:",ok)
sing=sum(1 for k,v in pk.items() if v==1)
print("packages used by exactly one paper:",sing)
FONT={'fontenc','lmodern','times','mathptmx','newtxtext','newtxmath','txfonts','pxfonts','palatino','mathpazo','microtype','helvet','courier','charter','libertine','kpfonts','fourier','bera','tgtermes','newpxtext','newpxmath','cmbright','sourcesanspro','fontspec','ebgaramond','stix','stix2','XCharter','mlmodern','cm-super','ae','pslatex','bookman','utopia','fbb','lato','inconsolata','beramono','tgpagella','libertinus','amsfonts','eucal','bm','ulem','babel','hyperref','soul','emph'}
EMPH={'fontenc','lmodern','times','mathptmx','newtxtext','txfonts','pxfonts','palatino','mathpazo','microtype','helvet','charter','libertine','kpfonts','fourier','tgtermes','newpxtext','cmbright','fontspec','ebgaramond','stix','stix2','XCharter','mlmodern','ae','pslatex','bookman','utopia','fbb','libertinus','ulem','tgpagella','courier','bera','beramono','inconsolata','sourcesanspro','lato','cm-super'}
sig=collections.Counter()
for c,s,l in per:
    key=(c if not any(e=='.cls' for e in l.values()) else 'PRIVATE-CLS', frozenset(s&EMPH), bool([k for k,e in l.items() if e=='.sty']))
    sig[key]+=1
print("distinct emph-relevant signatures",len(sig))
tot=0
for k,v in sig.most_common(12): print(v,k[0],sorted(k[1]),'localsty' if k[2] else '')
rep=sum(v-1 for v in sig.values()); print("papers that share a signature with an earlier one (upper bound on \\emph reuse):",rep)
import hashlib
sig2=collections.Counter(); hashes=collections.Counter()
for r,(c,s,l) in zip(docs,per):
    p=os.path.join(ROOT,r['arxiv_id'])
    hs=[]
    for f in glob.glob(p+"/**/*.cls",recursive=True)+glob.glob(p+"/**/*.sty",recursive=True):
        h=hashlib.sha256(open(f,'rb').read()).hexdigest()[:12]; hs.append(h); hashes[h]+=1
    sig2[(c,frozenset(s&EMPH),frozenset(hs))]+=1
print("signatures with local files by content hash:",len(sig2),"; papers sharing with an earlier one:",sum(v-1 for v in sig2.values()))
print("local files shared by >1 paper:",sum(1 for h,v in hashes.items() if v>1),"of",len(hashes))
