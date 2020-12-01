# Copyright 2019,  Vincent Hugot <vincent.hugot@insa-cvl.fr>
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

from itertools import *
# from functools import reduce
import subprocess as sp
from math import sqrt
import os
import tempfile, shutil as sh
from shutil import copy
from collections import defaultdict

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
    try:
        s = str(sorted(aset,key=lambda x:(len(x), str(x))))
    except TypeError:
        s = str(sorted(aset,key=lambda x:( (0 if isinstance(x,int) else 1), str(x)  )))
    return f"{l}{s[1:-1]}{r}"

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


def fresh_gen(s=()):
    """return generator of states not in s (at next() time)."""
    # s = set(s) # local copy in case s modified during lifespan of gen
    # that would not work as expected, as this is executed at time of first next(),
    # not actually at time of fresh_gen() call...
    k=0
    while True:
        if k not in s: yield k
        k+=1

if __debug__:
    g = fresh_gen((1, 3, 5))
    assert [next(g) for _ in range(5)] == [0, 2, 4, 6, 7]
    Q = set()
    g = fresh_gen(Q)
    next(g)
    Q.add(1)
    assert  next(g) == 2

def try_eval(s):
    try: return eval(s)
    except: return s

class fset(frozenset): # less ugly writing in subset constructions
    def __init__(s,*args): super().__init__()
    def __repr__(s): return super().__repr__()[5:-1] if s else '{}'
    def __or__(s,o): return fset(frozenset.__or__(s,o))
    def __and__(s, o): return fset(frozenset.__and__(s, o))
    def __sub__(s, o): return fset(frozenset.__sub__(s, o))


assert str(fset({1,2,3})) == '{1, 2, 3}'

def do_dot(pdfname,pdfprepend, store=None):
    assert sh.which("pdftk")
    assert sh.which("dot")
    r = sp.run(["dot", "-Tpdf", pdfname + ".dot", f"-o{pdfname}_fig.pdf"],capture_output=True)  # 3.7 capture output
    if r.returncode: print(r)
    assert not r.returncode
    if store: copy(f"{pdfname}_fig.pdf", f"{store}.pdf")
    if os.path.isfile(pdfname + ".pdf"):
        sp.run(["cp", pdfname + ".pdf", pdfname + "_copy.pdf"])
        if pdfprepend:
            sp.run(["pdftk", pdfname + "_fig.pdf", pdfname + "_copy.pdf", "cat", "output", pdfname + ".pdf"])
        else:
            sp.run(["pdftk", pdfname + "_copy.pdf", pdfname + "_fig.pdf", "cat", "output", pdfname + ".pdf"])
    else:
        sp.run(["mv", pdfname + "_fig.pdf", pdfname + ".pdf"])
        sp.run(["touch", pdfname + ".pdf"]) # force viewer to update; with mv it doesn't always
    sp.run(["rm", "-f"] + [f"{pdfname}_{x}.pdf" for x in ("fig", "copy")])
    # maybe spool temp files in memory: https://docs.python.org/3.6/library/tempfile.html

def do_tex(tex,name,pdfprepend,silent,testfile="__NFA_standalone__.tex"):
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


def powerset(iterable):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))

def powerfset(s):
    """returns set of fset subsets of s"""
    return set(
        chain.from_iterable( map(fset,combinations(s, r)) for r in range(len(s)+1) )
        )

def pairwise(iterable):
    """s -> (s0,s1), (s1,s2), (s2, s3), ..."""
    a, b = tee(iterable)
    next(b, None)
    return zip(a, b)

def r(it,maxi=None):
    return range( len(it) if maxi is None else min(maxi,len(it)) )

def invd(d):
    """invert dictionary or assoc list, losslessly"""
    if not isinstance(d,dict): d = dict(d)
    invd = defaultdict(set)
    for k, v in d.items(): invd[v].add(k)
    return invd

def is_prefix(t, tt): return len(t) <= len(tt) and tt[:len(t)] == t

def rev_graph(g):
    gr = defaultdict(list)
    for p in g:
        for q in g[p]:
            gr[q].append(p)
    return gr
