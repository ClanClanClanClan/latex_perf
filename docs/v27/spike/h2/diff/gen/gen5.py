# Review A's (spike H.2 fidelity review, 2026-09-30) random-document generator, kept
# verbatim except for the output path. usage: python3 gen5.py FIRST LAST OUTDIR
# writes OUTDIR/eFIRST.tex .. e(LAST-1).tex; the committed inputs/e*.tex are
# seeds 100-123 (diff/README.md).
import random, sys
P=r'*\scrollmode \catcode`\{=1 \catcode`\}=2 \catcode`\#=6 \catcode`\^=7 '
def dim(r, lo=-5, hi=60):
    return f"{r.randint(lo,hi)}.{r.randint(0,99999):05d}pt"
def glue(r):
    s=dim(r,0,20)
    if r.random()<0.7:
        o=r.choice(['pt','pt','pt','fil','fill','filll'])
        s+=f" plus {r.randint(0,30)}.{r.randint(0,999)}{o}"
    if r.random()<0.5:
        o=r.choice(['pt','pt','pt','pt','fil'])
        s+=f" minus {r.randint(0,10)}.{r.randint(0,999)}{o}"
    return s
def item(r):
    k=r.random()
    if k<0.35: return rf"\hbox to {dim(r,0,40)}{{}}"
    if k<0.6: return rf"\hskip {glue(r)}"
    if k<0.7: return rf"\penalty{r.choice([-10000,10000,r.randint(-200,200)])} "
    if k<0.78: return rf"\kern{dim(r,-3,5)}"
    if k<0.86: return rf"\discretionary{{\hbox to {dim(r,0,5)}{{}}}}{{\hbox to {dim(r,0,5)}{{}}}}{{\hbox to {dim(r,0,8)}{{}}}}"
    if k<0.92: return rf"\vrule width {dim(r,0,3)} height {dim(r,0,9)} depth {dim(r,0,3)}"
    return rf"\hbox{{\vrule height {dim(r,0,12)} depth {dim(r,0,4)} width 1pt}}"
def para(r):
    s=rf"\hsize={dim(r,40,200)} \tolerance={r.choice([100,200,1000,10000])} \pretolerance={r.choice([-1,100,10000])} \looseness={r.choice([0,0,1,-1])} \emergencystretch={dim(r,0,20)} \linepenalty={r.randint(0,100)} \adjdemerits={r.randint(0,10000)} \doublehyphendemerits={r.randint(0,10000)} \finalhyphendemerits={r.randint(0,10000)} \hyphenpenalty={r.randint(-100,100)} \exhyphenpenalty={r.randint(-100,100)} "
    if r.random()<0.3: s+=rf"\hangindent={dim(r,-20,20)} \hangafter={r.randint(-3,3)} "
    if r.random()<0.3: s+=rf"\parshape 3 {dim(r,0,10)} {dim(r,30,120)} {dim(r,0,10)} {dim(r,30,120)} {dim(r,0,10)} {dim(r,30,120)} "
    if r.random()<0.3: s+=rf"\lastlinefit={r.randint(0,1000)} "
    s+=rf"\leftskip={glue(r)} \rightskip={glue(r)} \parfillskip={glue(r) if r.random()<0.3 else '0pt plus 1fil'} \parindent={dim(r,0,20)} "
    s+=r"\noindent " if r.random()<0.5 else r"\indent "
    s+="".join(item(r) for _ in range(r.randint(5,40)))
    return s
def test(seed):
    r=random.Random(seed)
    s=P+r"\hbadness=10000 \vbadness=10000 \hfuzz=16383pt \vfuzz=16383pt \baselineskip=12pt plus 1pt \lineskip=1pt \lineskiplimit=0pt "
    s+=r"\setbox0\vbox{"+para(r)+r"\par\xdef\pg{\the\prevgraf}\setbox2\lastbox\xdef\a{\the\wd2,\the\ht2,\the\dp2}\unskip\unpenalty\setbox2\lastbox\xdef\b{\the\wd2,\the\ht2}}"
    s+=r"\message{[\pg][\a][\b][\the\wd0,\the\ht0,\the\dp0]}"
    # page builder
    s+=r"\output={\message{OUT[\the\ht255,\the\dp255,\the\outputpenalty,\the\insertpenalties,\the\badness]}\setbox9\box255 \deadcycles=0 }"
    s+=rf"\vsize={dim(r,20,200)} \maxdepth={dim(r,0,5)} \topskip={glue(r)} \count100=1000 \dimen100={dim(r,0,100)} \skip100={glue(r)} "
    for _ in range(r.randint(3,20)):
        k=r.random()
        if k<0.4: s+=rf"\hrule height {dim(r,0,30)} depth {dim(r,0,5)} "
        elif k<0.6: s+=rf"\vskip {glue(r)} "
        elif k<0.75: s+=rf"\penalty{r.choice([-10000,10000,r.randint(-500,500)])} "
        elif k<0.85: s+=rf"\insert100{{\hrule height {dim(r,0,20)}}}"
        elif k<0.92: s+=rf"\kern{dim(r,-5,10)} "
        else: s+=rf"\mark{{m}}"
    s+=r"\penalty-10000 \message{[\the\pagetotal,\the\pagegoal]}"
    return s+"\n\\end\n"
for i in range(int(sys.argv[1]), int(sys.argv[2])):
    open(f"{sys.argv[3]}/e{i}.tex","w").write(test(i))
