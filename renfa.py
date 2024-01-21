# Copyright 2021,  Vincent Hugot <vincent.hugot@insa-cvl.fr>
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

# McNaughton–Yamada–Thompson's algorithm.

# Students: pattern-matching techniques in this file are documented in my lecture notes, sections
# "Advanced structural pattern matching" and "A smidgen of Computer Algebra".

from dataclasses import dataclass
from nfa import *
from functools import cached_property

class _RE: pass

class VOID(_RE): pass

@dataclass
class WRD(_RE): w: str

@dataclass
class BinOp(_RE):
    l: object
    r: object

class OR (BinOp):
    symb = " | "

class CONCAT (BinOp):
    symb = ""

@dataclass
class STAR(_RE): e : object

def needsparent(s): return len(s) > 1 and s[0]+s[-1] != "()"

def restr(e):
    match e:
        case VOID() :       return "∅"
        case WRD(""):       return "ɛ"
        case WRD(w) :       return w
        case BinOp(l,r):    return f"({restr(l)}{e.symb}{restr(r)})"
        case STAR(e):
            s = restr(e)
            return f"({s})*" if needsparent(s) else f"{s}*"
        case _: raise ValueError(e)

def reaut(e):
    match e: # invariant: all states numerical
        case VOID() :       return NFA({0}, [1], [])
        case WRD(""):       return NFA({0}, {1}, { (0, "", 1) })
        case WRD(w):        return NFA.of_word(w)
        case OR(l,r):
            A,B = NFA.disjoint([reaut(x) for x in (l,r)])
            return NFA(["i"], ["f"], {
                ("i", "", peek(A.I)),
                ("i", "", peek(B.I)),
                (peek(A.F), "", "f"),
                (peek(B.F), "", "f") } | A.Δ | B.Δ ).renum()
        case CONCAT(l, r):
            A, B = NFA.disjoint([reaut(x) for x in (l, r)])
            return NFA(["i"], ["f"], {
                ("i", "", peek(A.I)),
                (peek(A.F), "", peek(B.I)),
                (peek(B.F), "", "f")} | A.Δ | B.Δ).renum()
        case STAR(e):
            A = reaut(e)
            return NFA(["i"], ["f"], {
                ("i", "", peek(A.I)), ("i", "", "f"),
                (peek(A.F), "", peek(A.I)),
                # ("f", "", "i"), # simpler, provided concat is eps, not unify states
                (peek(A.F), "", "f")} | A.Δ ).renum()
        case _:  raise ValueError(e)

class E:
    def __init__(s,*args):
        match args:
            case []: s.e = VOID()
            case [str() as x] : s.e = WRD(x)
            case [_RE as x]: s.e = x
            case _: assert 0

    def __repr__(s):
        x = restr(s.e)
        return x if len(x) <= 1 or x[0]+x[-1] != "()" else x[1:-1]

    def __or__(s, o):   return E(OR(s.e,o.e))
    def __add__(s,o):   return E(CONCAT(s.e,o.e))
    def star(s):        return E(STAR(s.e))

    def MYT(s): return reaut(s.e).named(f"{s}") # McNaughton–Yamada–Thompson

    @cached_property
    def nfa(s): return s.MYT()

    @cached_property
    def mini(s): return s.nfa.rm_eps().trim().mini().renum().named(f"{s} /M")

    def __contains__(s, w): return w in s.nfa
    def __iter__(s): return s.mini.lang()
    def __getitem__(s,i): return s.mini.__getitem__(i)

    def show(s):
        s.nfa.visu() ; s.mini.visu()
        return s

    def show_all(s):
        s.nfa.visu().rm_eps().visu().trim().visu().dfa().visu().mini().visu().renum().visu()
        return s
