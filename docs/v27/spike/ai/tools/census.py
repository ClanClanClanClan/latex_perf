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
# Revision (2026-10-06, C-152): the reuse figure depends on the key, so it is reported for several
# keys, as a crude two-sided estimate. \emph reads \f@size, which the class's size option sets,
# and fontenc's option sets the encoding: keys F and H include them. A key with every class option
# (G) also splits on options \emph never reads (a4paper, twocolumn), so it is not a lower bound.
OPT=[]; EOPT=[]; H=[]
for r,(c,s,l) in zip(docs,per):
    p=os.path.join(ROOT,r['arxiv_id'])
    H.append(frozenset(hashlib.sha256(open(f,'rb').read()).hexdigest()[:12]
                       for f in glob.glob(p+"/**/*.cls",recursive=True)+glob.glob(p+"/**/*.sty",recursive=True)))
    t="".join(open(f,errors='replace').read() for f in glob.glob(p+"/**/*.tex",recursive=True))
    t="\n".join(x.split('%')[0] for x in t.splitlines())
    m=re.search(r'\\documentclass\s*(?:\[([^\]]*)\])?',t); o=m.group(1) if m and m.group(1) else ''
    OPT.append(frozenset(x.strip() for x in o.split(',') if x.strip()))
    eo=set()
    for mm in re.finditer(r'\\(?:usepackage|RequirePackage)\s*(?:\[([^\]]*)\])?\s*\{([^}]*)\}',t):
        for x in mm.group(2).split(','):
            if x.strip() in EMPH: eo.add((x.strip(),(mm.group(1) or '').replace(' ','')))
    EOPT.append(frozenset(eo))
def share(keys):
    cnt=collections.Counter(keys); return len(cnt), sum(v-1 for v in cnt.values())
size=lambda o: frozenset(x for x in o if re.fullmatch(r'\d+pt',x))
priv=lambda c,l: c if not any(e=='.cls' for e in l.values()) else 'PRIVATE-CLS'
hassty=lambda l: bool([k for k,e in l.items() if e=='.sty'])
for name,keys in [
    ("A (class or PRIVATE-CLS, emph pkgs, has a local .sty)", [(priv(c,l),frozenset(s&EMPH),hassty(l)) for c,s,l in per]),
    ("B (class, emph pkgs, local files by hash)", [(c,frozenset(s&EMPH),h) for (c,s,l),h in zip(per,H)]),
    ("F (B + the class's size option)", [(c,size(o),frozenset(s&EMPH),h) for (c,s,l),h,o in zip(per,H,OPT)]),
    ("H (F + the emph packages' options)", [(c,size(o),eo,h) for (c,s,l),h,o,eo in zip(per,H,OPT,EOPT)]),
    ("G (B + every class option)", [(c,o,frozenset(s&EMPH),h) for (c,s,l),h,o in zip(per,H,OPT)])]:
    k,sh=share(keys); print(f"key {name}: {k} distinct; papers sharing with an earlier one: {sh}")
