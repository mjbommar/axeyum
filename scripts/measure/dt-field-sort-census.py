"""Classify every declared datatype in a list of SMT-LIB files by field sort.

Answers the ADR-1935 sizing question: for how many files does ADR-1920's
"restricted to datatypes whose fields are all scalar" precondition actually
hold?  Each declared datatype is scored `scalar-only` (Bool/Int/Real/BitVec
fields only -- what `register_datatype` admits today), `expandable-with-array-
or-uf` (no field sort mentions a datatype, but some field is an array or an
uninterpreted sort), or `dt-field` (a datatype-sorted field, or an array whose
element sort mentions one).  Each file is then scored by the WORST datatype
that appears as a parameter of a `declare-fun`, because a file only decides if
every application it makes is handled.

Static and deliberately over-approximating: a declared UF parameter need not be
applied, and the score is per declaration rather than per use site.  Both errors
raise the eligible counts, never lower them.

Usage:
    tr '\n' ' ' < bench-results/parity-lists/UFDT.txt | python3 scripts/measure/dt-field-sort-census.py

Measurement:
    docs/research/03-measurements/the-adr-1920-slice-is-6-of-600-files-2026-09-12.md
"""
import re, sys, collections
def toks(s):
    s = re.sub(r';[^\n]*', ' ', s)
    return re.findall(r'\(|\)|\|[^|]*\||[^\s()]+', s)
def parse(t,i):
    if t[i]=='(':
        out=[];i+=1
        while t[i]!=')':
            v,i=parse(t,i);out.append(v)
        return out,i+1
    return t[i],i+1
def render(s):
    if isinstance(s,str): return s
    return '('+' '.join(render(x) for x in s)+')'
def mentions_dt(s,dtn):
    if isinstance(s,str): return s in dtn
    return any(mentions_dt(x,dtn) for x in s)
def kind(s,dtn):
    if isinstance(s,str):
        if s in dtn: return 'datatype'
        if s in ('Int','Real','Bool'): return 'scalar'
        return 'uninterp'
    if s and s[0]=='Array': return 'array'
    if s and s[0]=='_': return 'scalar'
    return 'other'

fieldsorts=collections.Counter()
agg=collections.Counter()
per_div_files=0
for path in sys.stdin.read().split():
    per_div_files+=1
    src=open(path,errors='replace').read()
    t=toks(src); i=0; top=[]
    while i<len(t):
        try: v,i=parse(t,i)
        except Exception: break
        top.append(v)
    dtn=set(); bodies={}
    for v in top:
        if isinstance(v,list) and v and v[0]=='declare-datatypes':
            names=[n[0] if isinstance(n,list) else n for n in v[1]]
            dtn.update(names)
            for nm,body in zip(names,v[2]): bodies[nm]=body
    if not dtn: agg['no-datatype-decl']+=1; continue
    agg['files-with-dt']+=1
    cls={}
    for nm,body in bodies.items():
        ks=collections.Counter(); bad=False
        for ctor in body:
            if isinstance(ctor,str): continue
            for fld in ctor[1:]:
                if isinstance(fld,list) and len(fld)==2:
                    srt=fld[1]; k=kind(srt,dtn); ks[k]+=1
                    fieldsorts[render(srt) if k in ('array','other','uninterp') else k]+=1
                    if mentions_dt(srt,dtn): bad=True
        if bad or ks['datatype']: cls[nm]='dt-field'
        elif ks['array'] or ks['uninterp'] or ks['other']: cls[nm]='expandable-with-array-or-uf'
        else: cls[nm]='scalar-only'
    seen_arg=set(); seen_res=set()
    for v in top:
        if isinstance(v,list) and v and v[0]=='declare-fun' and len(v)>=4:
            params=v[2] if isinstance(v[2],list) else []
            for p in params:
                if isinstance(p,str) and p in dtn: seen_arg.add(p)
            if params and isinstance(v[3],str) and v[3] in dtn: seen_res.add(v[3])
    if seen_arg:
        agg['files with a UF dt-PARAM']+=1
        kinds={cls[a] for a in seen_arg}
        if kinds=={'scalar-only'}: agg['  every such param dt is SCALAR-ONLY (ADR-1920 slice applies)']+=1
        elif kinds <= {'scalar-only','expandable-with-array-or-uf'}: agg['  every such param dt expandable IF array/UF fields land']+=1
        else: agg['  at least one param dt has a DATATYPE field (neither half helps)']+=1
    for nm,c in cls.items(): agg['dt-decls: '+c]+=1
print(f'files scanned: {per_div_files}')
for k,v in sorted(agg.items()): print(f'{v:6d}  {k}')
print('-- top non-scalar field sorts --')
for k,v in fieldsorts.most_common(12): print(f'{v:7d}  {k}')
