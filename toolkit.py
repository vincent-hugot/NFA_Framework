# Copyright 2019-2022,  Vincent Hugot <vincent.hugot@insa-cvl.fr>
#
# Permission is hereby granted, free of charge, to any person obtaining a copy of
# this software and associated documentation files (the "Software"), to deal in
# the Software without restriction, including without limitation the rights to
# use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
# the Software, and to permit persons to whom the Software is furnished to do so,
# subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
# FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
# COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
# IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
# CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
import random
from itertools import *
from more_itertools import set_partitions
from functools import reduce
import subprocess as sp
import math
from math import sqrt
import os
import tempfile, shutil as sh
from shutil import copy
from collections import defaultdict
import random as rand
from contextlib import contextmanager
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from time import sleep
from threading import Lock

term_reset= "\u001b[0m"
term_visu_style= "\u001b[1m\u001b[31m"
term_bold_yellow= "\u001b[1m\u001b[33m"
term_bold= "\u001b[1m"
term_light_blue = "\u001b[94m"
term_light_green = "\u001b[92m"
erase_line = "\r\033[2K"
# erase_line = "\r"+" "*79+"\r"

# print a set in order
# can need a renum if mixing incomparable types
def sortstr(aset,l="{",r="}"):
    return f"{l}{str(sort_states(aset))[1:-1]}{r}"

def sort_states(Q):
    """
    :param Q: set of states
    :return: same, ordered in a "nice" way
    """
    try:
        return sorted(Q,key=lambda x:(len(x), str(x)))
    except TypeError:
        return sorted(Q,key=lambda x:( (0 if isinstance(x,int) else 1), str(x)  ))


def inputint(prompt="? ", default=0, upper=None):
    n = None
    while n is None:
        try:
            n = int(input(prompt) or default)
            if upper is not None and n > upper:
                print("Number out of range. Retry.")
                n = None
        except ValueError:
            print("Invalid number. Retry.")
    return n


def fresh_gen(s=(), trans=lambda x:x):
    """return generator of states not in s (at next() time).
    States are 0, 1,... or trans(0), trans(1),... """
    # s = set(s) # local copy in case s modified during lifespan of gen
    # that would not work as expected, as this is executed at time of first next(),
    # not actually at time of fresh_gen() call...
    k=0
    while True:
        x = trans(k)
        if x not in s: yield x
        k+=1

def base_case_gen(g,b):
    """prefixes g with b if g is empty, without consuming g"""
    try:
        gi = iter(g)
        i = next(gi)
        return chain([i],gi)
    except StopIteration:
        return iter([b])

if __debug__:
    __g = fresh_gen((1, 3, 5))
    assert [next(__g) for _ in range(5)] == [0, 2, 4, 6, 7]
    __Q = set()
    __g = fresh_gen(__Q)
    next(__g)
    __Q.add(1)
    assert next(__g) == 2

def try_eval(s):
    try:
        r = eval(s)
        assert type(r) in (str, int, float)
        return r
    except: return s

class fset(frozenset): # less ugly writing in subset constructions
    def __init__(s,*args): super().__init__()
    def __repr__(s): return s.__str__()
    # Python str is fucked: str calls repr in container structures,
    # so I can't really separate the two; if I put a true repr here,
    # then tuples containing sets will call it and mess the display...
    def repr(s): return super().__repr__()
    def __str__(s): return f"{{{', '.join(map(str,s))}}}"
    def __or__(s,o): return fset(frozenset.__or__(s,o))
    def __and__(s, o): return fset(frozenset.__and__(s, o))
    def __sub__(s, o): return fset(frozenset.__sub__(s, o))

class ffset(fset): # only for converting into something with a correct repr
    def __repr__(s): return f"fset({{{', '.join(map(repr,s))}}})"

# def deep_freeze(s):
#     """deeply change structure to convert all sets into fsets"""
#     try:
#         i = iter(s)
#     except TypeError:
#         return s
#     return type(s)(deep_freeze(x) for x in i)


assert str(fset({1,2,3})) == '{1, 2, 3}'

def __DEPRECATED_do_dot(pdfname,pdfprepend=False, pdfoverwrite=False, store=None, renderer="dot", renderer_options = [],
           pdfcrop=False):
    assert sh.which("pdftk")
    assert sh.which(renderer)
    r = sp.run([renderer] + renderer_options + ["-Tpdf", pdfname + ".dot", f"-o{pdfname}_fig.pdf"],capture_output=True)
    if r.returncode: print(r)
    assert not r.returncode if renderer == "dot" else True
    # sfdp bad build Error: remove_overlap: Graphviz not built with triangulation library
    if store: copy(f"{pdfname}_fig.pdf", f"{store}.pdf")
    if pdfcrop and sh.which("pdfcrop"):
        r = sp.run(["pdfcrop", f"{pdfname}_fig.pdf", f"{pdfname}_figc.pdf"],capture_output=True)
        if r.returncode: print(r)
        sh.move(f"{pdfname}_figc.pdf",f"{pdfname}_fig.pdf")
    if os.path.isfile(pdfname + ".pdf"):
        if pdfoverwrite:
            sh.move(f"{pdfname}_fig.pdf", f"{pdfname}.pdf")
        else:
            sp.run(["cp", pdfname + ".pdf", pdfname + "_copy.pdf"])
            if pdfprepend:
                sp.run(["pdftk", pdfname + "_fig.pdf", pdfname + "_copy.pdf", "cat", "output", pdfname + ".pdf"])
            else:
                sp.run(["pdftk", pdfname + "_copy.pdf", pdfname + "_fig.pdf", "cat", "output", pdfname + ".pdf"])
    else:
        sh.move(f"{pdfname}_fig.pdf", f"{pdfname}.pdf")
        sp.run(["touch", pdfname + ".pdf"]) # force viewer to update; with mv it doesn't always
        # todo: Path('path/to/file.txt').touch()
    for f in [f"{pdfname}_{x}.pdf" for x in ("fig", "copy")]:
        if os.path.isfile(f): os.remove(f)
    # maybe spool temp files in memory: https://docs.python.org/3.6/library/tempfile.html

def __DEPRECATED_do_tex(tex,name,pdfprepend,silent,testfile="__NFA_standalone__.tex"):
    if not sh.which("pdflatex"):
        print("\ndo_tex: pdflatex is not installed: aborting")
        return
    with tempfile.TemporaryDirectory(prefix="NFA_do_tex") as td:
        with open(td+"/x.tex",'w') as f:
            f.write("\documentclass{minimal}\n" +
                "\\usepackage{tikz}\n\\usetikzlibrary{backgrounds,arrows,automata,shadows,matrix,decorations,shapes,calc,positioning}" +
                "\n\\tikzset{every state/.append style={minimum size=1.5em,\n  circular glow={fill=gray!30},fill=blue!2!white\n}}" +
                "\n\\tikzset{accepting/.append style={fill=green!2,circular glow={fill=gray!30}}}\n\\tikzset{fsa/.style={baseline=-.5ex,semithick,>=stealth',"+
                "\n  shorten >=1pt,auto,node distance=3.5em,initial text=}}\n\\tikzset{fst/.style={fsa,node distance=5em}}"+
                "\n\\tikzset{mathnodes/.style={execute at begin node=\\(,execute at end node=\\)}}" +
                "\n\\begin{document}\n"+tex+"\n\end{document}")
        testfile and sh.copy(td+"/x.tex",testfile)
        r = sp.run(["pdflatex", "-halt-on-error", "x.tex"],cwd=td,capture_output=silent)
        if r.returncode: print(r)
        if sh.which("pdfcrop"):
            sp.run(["pdfcrop", "x.pdf", "xc.pdf"], cwd=td,capture_output=silent)
            sh.move(td + "/xc.pdf", name + "_fig.pdf")
        else:
            print("\ndo_tex: pdfcrop is not installed: no cropping shall be done")
            sh.move(td + "/x.pdf", name + "_fig.pdf")

        assert not r.returncode
        if os.path.isfile(name + ".pdf"):
            sh.copy(name+".pdf", name + "_copy.pdf")
            if pdfprepend:
                sp.run(["pdftk", name + "_fig.pdf", name + "_copy.pdf", "cat", "output", name + ".pdf"])
            else:
                sp.run(["pdftk", name + "_copy.pdf", name + "_fig.pdf", "cat", "output", name + ".pdf"])
        else:
            sh.move(name + "_fig.pdf", name + ".pdf")
            sp.run(["touch", name + ".pdf"])



class pdf_renderer:
    """
    Parallel processing pipeline for pdf rendering.
    Use do_dot and do_tex to submit render jobs.
    """
    def __init__(s):
        assert sh.which("pdftk")
        s.pool = ThreadPoolExecutor()
        s.temp_dir = tempfile.mkdtemp(prefix="NFA__Framework__")
        s.jobs = {} ; s.jobsLock = Lock()
        s.jgen = fresh_gen()
        s.concatenator = None               # concatenator process
        s.concatenator_parameters = None    # concat last woken with...
        s.accumulator = f"{s.temp_dir}/accumulator.pdf"

    def dot_name(s, jn): return f"{s.temp_dir}/{jn}.dot"
    def pdf_name(s, jn): return f"{s.temp_dir}/{jn}.pdf"

    def do_dot(s, dot_contents, pdfname, **kw):
        pdfname = pdfname+".pdf"
        assert sh.which(ren := kw["renderer"]), f"{ren} is not installed!"
        jn = next(s.jgen)
        with open(s.dot_name(jn),"w", encoding="utf-8") as f: f.write(dot_contents)
        s.check_concatenator_change(pdfname, **kw)
        with s.jobsLock: s.jobs[jn] = s.pool.submit(s.dot_compiler, jn, pdfname, **kw)
        s.wake_concatenator(pdfname, **kw)

    def do_tex(s, tex, pdfname, **kw):
        if not sh.which("pdflatex"):
            print("pdflatex is not installed: aborting LaTeX content (normal for students)")
            return
        pdfname = pdfname + ".pdf"
        jn = next(s.jgen)
        td = Path(s.temp_dir) / f"do_tex__{jn}"
        td.mkdir(exist_ok=1)
        with open(texfile := td/"x.tex", 'w') as f:
            f.write("\documentclass{minimal}\n" +
                    "\\usepackage{tikz}\n\\usetikzlibrary{backgrounds,arrows,automata,shadows,matrix,decorations,shapes,calc,positioning}" +
                    "\n\\tikzset{every state/.append style={minimum size=1.5em,\n  circular glow={fill=gray!30},fill=blue!2!white\n}}" +
                    "\n\\tikzset{accepting/.append style={fill=green!2,circular glow={fill=gray!30}}}\n\\tikzset{fsa/.style={baseline=-.5ex,semithick,>=stealth'," +
                    "\n  shorten >=1pt,auto,node distance=3.5em,initial text=}}\n\\tikzset{fst/.style={fsa,node distance=5em}}" +
                    "\n\\tikzset{mathnodes/.style={execute at begin node=\\(,execute at end node=\\)}}" +
                    "\n\\begin{document}\n" + tex + "\n\end{document}")
        s.check_concatenator_change(pdfname, **kw)
        with s.jobsLock: s.jobs[jn] = s.pool.submit(s.tex_compiler, jn, texfile, pdfname, **kw)
        s.wake_concatenator(pdfname, **kw)

    def tex_compiler(s,jn,texfile, pdfname, silent, **kw):
        r = sp.run(["pdflatex", "-halt-on-error", texfile], cwd=Path(texfile).parent, capture_output=silent)
        assert not r.returncode, r
        if sh.which("pdfcrop"):
            r = sp.run(["pdfcrop", f := Path(texfile).with_suffix(".pdf"), s.pdf_name(jn)], capture_output=True)
            f.unlink()
            assert not r.returncode, r
        else: sh.move(Path(texfile).with_suffix(".pdf"), s.pdf_name(jn))

    def check_concatenator_change(s, pdfname, **kw):
        """If there are parameter changes that alter the behaviour of the concatenator, we can't just rely on
        the existing concatenator process; we must wait for it to finish so that a new one is awoken
        with the new parameters"""
        if not s.concatenator_parameters: return
        new_params = kw | {"pdfname": pdfname}
        if any(s.concatenator_parameters[p] != new_params[p] for p in
            ["pdfname", "pdfprepend"]):
            s.flush_concatenator()

    def wake_concatenator(s, pdfname, **kw):
        if s.concatenator is None or s.concatenator.done():
            s.concatenator = s.pool.submit(s.pdf_concatenator, pdfname, **kw)
            s.concatenator_parameters = kw | {"pdfname": pdfname}

    def flush_concatenator(s):
        while not s.concatenator.done(): sleep(.1) # why do I need that? Doesn't result() wait upon process?
        return s.concatenator.result()

    def dot_compiler(s,jn, pdfname, renderer="dot", renderer_options = [], pdfcrop=False, **kw):
        cmd = [renderer] + renderer_options + ["-Tpdf", s.dot_name(jn), "-o", s.pdf_name(jn)]
        r = sp.run(cmd, capture_output=True)
        if renderer == "dot" and r.returncode == -6 and r.stderr==b'corrupted size vs. prev_size\n':
            print("corrupted size vs. prev_size random bug in dot, run again, https://gitlab.com/graphviz/graphviz/-/issues/2395")
            r = sp.run(cmd, capture_output=True)
        assert not r.returncode if renderer == "dot" else True, r
        if pdfcrop and sh.which("pdfcrop"):
            r = sp.run(["pdfcrop", s.pdf_name(jn), s.pdf_name(jn)+"_"], capture_output=True)
            Path(s.pdf_name(jn)+"_").rename(s.pdf_name(jn))
            assert not r.returncode, r

    def pdf_concatenator(s, pdfname, pdfprepend, **kw):
        target = Path(pdfname)
        while s.jobs:
            done = []
            for jn, f in s.jobs.items():
                if f.done(): done.append(jn)
                else:        break
            if done:
                for jn in done:
                    if (ex := s.jobs[jn].exception()) is not None:
                        print("Exception on job", jn, "\n", repr(ex))
                        s.pool.shutdown()
                        raise ex
                targets = [s.pdf_name(j) for j in done]
                if target.is_file():
                    sh.move(target, s.accumulator)
                    targets = [s.accumulator] + targets
                if pdfprepend: targets.reverse()
                sp.run(["pdftk", *targets , "cat", "output", pdfname])
                for t in targets: Path(t).unlink(missing_ok=1)
                with s.jobsLock:
                    for jn in done: del s.jobs[jn]
            else: sleep(0.3)

    def print_status(s):
        """
        Dispay indicator of how many pdf jobs remain.
        At the end, if there have been problems, vomit relevant info.
        Blocking call until all is rendered.
        """
        if s.concatenator is None: return
        rot = rotating_timer_gen()
        while not s.concatenator.done():
            print(erase_line+f"PDF> {next(rot)} jobs: {len(s.jobs)}", end="")
            sleep(.3)
        print(erase_line+"PDF> All done.")
        indicators = (s.jobs, s.concatenator.exception())
        assert indicators == ({}, None), indicators

def rotating_timer_gen(): yield from cycle("-\|/")

def flattupleL(t):
    """Flatten left-assoc single depth tuple"""
    t,x = t
    assert t != ()
    return t + (x,) if type (t) is tuple else (t,x)

# assert flattupleL(((0,), 1)) == (0, 1)
# assert flattupleL(((0, 1), 2)) == (0, 1, 2)
# assert flattupleL(((0, 1, 2), 3)) == (0, 1, 2, 3)
# assert flattupleL(((0, 1, 2, 3), 4)) == (0, 1, 2, 3, 4)
# assert flattupleL(((0, 1, 2, 3, 4), 5)) == (0, 1, 2, 3, 4, 5)

def Ltuple(t):
    """make left-assoc tuple"""
    *r,x = t
    return (Ltuple(r),x) if r else x

# assert Ltuple((0,1,2)) == ((0,1),2), Ltuple((0,1,2))

def tuplepart(t,i):
    assert i >= 2
    i -= 2
    return t[:i+1] if i > 0 else t[i] , t[i + 1]
# assert tuplepart((0, 1, 2, 3, 4),2) == (0, 1)
# assert tuplepart((0, 1, 2, 3, 4),3) == ((0, 1), 2)
# assert tuplepart((0, 1, 2, 3, 4),4) == ((0, 1, 2), 3)
# assert tuplepart((0, 1, 2, 3, 4),5) == ((0, 1, 2, 3), 4)


def PP(x,name=""):
    """print and return a value; for debugging purposes"""
    print(f"PP {name}: ",x)
    return x

def defcst(*l,namespace=globals()):
    """define global constants X containing "X" (capitalised)"""
    d = {s:s.capitalize() for s in l}
    namespace.update(d)
    return list(d.values())


class VecSet:
    """
    dual set / vector view, given ordered elements A B C
    {A,C} <-> 1 0 1
    """
    def __init__(s,vec):
        s.vec = tuple(vec)
        s.n = len(vec)
        s.set = set(s.vec)

    def setofvec(s,v,zero = 0):
        S =  fset( s.vec[i] for i in range(min(len(v),s.n)) if v[i] != zero )
        return S if len(v) <= s.n else (S,v[s.n:])

    def setsofvec(s,v,*p,**k):
        return (S := s.setofvec(v[:s.n],*p,**k) , fset(s.set - S))

    def vecofset(s,S,one=1,zero=0):
        return tuple( one if e in S else zero for e in s.vec )


# V = defcst("a","b","c")
# VS = VecSet(V)
# print(VS.setofvec([0,1,0,89]))
# print(VS.setofvec([1,1,1]))
# print(VS.setsofvec([1,0,1]))
# print(VS.vecofset({a,c,67}))


def powerset(iterable, minlen=0, maxlen=2**64):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(minlen,min(len(s),maxlen)+1) )

def powerfset(s, minlen=0, maxlen=2**64):
    """returns set of fset subsets of s of cardinal in [[minlen, maxlen]]"""
    return set(
        chain.from_iterable( map(fset,combinations(s, r)) for r in range(minlen,min(len(s),maxlen)+1) )
        )

def partitions(s,n=2):
    yield from ( map(fset,part) for part in set_partitions(s,n) )

def covers(s, n=2):
    """overlapping partitions: gen of tuples of sets"""
    if (d := n - len(s)) > 0:
        yield from ( c+(fset(),)*d for c in covers(s, len(s)))
        return
    # S = powerfset(s, 1, len(s) - 1)
    S = powerfset(s, 1)
    yield from ( l for l in combinations(S,n) if fset.union(*l) == s )

def pairwise(iterable):
    """s -> (s0,s1), (s1,s2), (s2, s3), ..."""
    a, b = tee(iterable)
    next(b, None)
    return zip(a, b)

def r(it,maxi=None):
    return range( len(it) if maxi is None else min(maxi,len(it)) )

def invd(d):
    """invert dictionary or assoc list, losslessly;
    targets set, so looses key order
    key: value  ->  value : {key1, key2}"""
    if not isinstance(d,dict): d = dict(d)
    invd = defaultdict(set)
    for k, v in d.items(): invd[v].add(k)
    return invd

def invdl(d):
    """invert dictionary or assoc list, losslessly;
    keeps order or appearence of keys:
    key: value  ->  value : [key1, key2]"""
    if not isinstance(d,dict): d = dict(d)
    invd = defaultdict(list)
    for k, v in d.items(): invd[v].append(k)
    return invd

def is_prefix(t, tt): return len(t) <= len(tt) and tt[:len(t)] == t

def rev_graph(g):
    gr = defaultdict(list)
    for p in g:
        for q in g[p]:
            gr[q].append(p)
    return gr

def grouper(iterable, n, fillvalue=None):
    "Collect data into fixed-length chunks or blocks"
    # grouper('ABCDEFG', 3, 'x') --> ABC DEF Gxx"
    args = [iter(iterable)] * n
    return zip_longest(*args, fillvalue=fillvalue)

def num_to_str(n):
    if n <= 25: return chr(97+n)
    if n <= 51: return chr(65+n-26)
    assert False

# assert "".join(map(num_to_str,range(52))) == "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"

@contextmanager
def cd(dir):
    currdir = os.getcwd()
    os.chdir(os.path.expanduser(dir))
    try: yield
    finally: os.chdir(currdir)

@contextmanager
def elapsed(msg="ELAPSED:", v=True):
    from timeit import default_timer
    start = default_timer()
    elapser = lambda: default_timer() - start
    yield lambda: elapser()
    end = default_timer()
    elapser = lambda: end-start
    if v: print(msg, end-start)

def texesc(s):
    """tex string escape"""
    return "".join('\\'+a if a in ('{','}') else a for a in str(s))

def classes_of_equiv(elems, eq):
    classes = []
    for e in elems:
        for c in classes:
            if eq(e,c[0]):
                c.append(e)
                break
        else: classes.append([e])
        ## TODO: opti for nmini: do not create new classes for non root elems
    return classes

def peek(s):
    """get an element out of a set; like pop() but non-destructive"""
    return next(iter(s))

def peeks(*ss):
    """get an element out of every set; like pop() but non-destructive"""
    return [ next(iter(s)) for s in ss ]

if __debug__:
    l = [1,2,3,10,11,12,30]
    assert classes_of_equiv(l, lambda a,b: a//10 == b//10) == [[1, 2, 3], [10, 11, 12], [30]]
    assert classes_of_equiv(l, lambda a,b: a%10  == b%10 ) == [[1, 11], [2, 12], [3], [10, 30]]


class disjoint_sets:

    def __init__(s):
        s.parent = {}

    def find(s,e):
        p = s.parent.setdefault(e,e)
        return e if p == e else s.find(p)

    def union(s,e,f):
        pe, pf = map(s.find, (e,f))
        s.parent[pe] = pf

    def classes(s):
        d = {}
        for e in s.parent:
            fe = s.find(e)
            d[fe] = d.get(fe,fset()) | {e}
        return tuple(sorted(d.values(), key=len, reverse=1))


# DS = disjoint_sets()
# print(DS.parent, DS.classes())
# DS.union("a", "b")
# DS.union("b", "c")
# DS.union("d", "e")
# # DS.union("a", "d")
# print(DS.parent, DS.classes())