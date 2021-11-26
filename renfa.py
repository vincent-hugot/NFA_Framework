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


from dataclasses import dataclass
from nfa import *

class VOID: pass

@dataclass
class WRD: w: str

@dataclass
class BinOp:
    l: object
    r: object

class OR (BinOp):
    symb = "|"

class CONCAT (BinOp):
    symb = "."

@dataclass
class STAR: e : object

e = CONCAT(STAR(OR(VOID(), WRD("ab"))), WRD(""))

print(e)

def restr(e):
    match e:
        case VOID() :       return "∅"
        case WRD(""):       return "ɛ"
        case WRD(w) :       return w
        case BinOp(l,r):    return f"({restr(l)} {e.symb} {restr(r)})"
        case STAR(e):       return f"({restr(e)})*"
        case _:             raise ValueError(e)

print(restr(e))

def reaut(e):
    match e: # invariant: all states numerical
        case VOID() :       return NFA({0}, [1], [])
        case WRD(""):       return NFA({0}, {1}, { (0, "", 1) })
        case WRD(w):        return NFA.of_word(w)
        case OR(l,r):
            A,B = NFA.disjoint([reaut(x) for x in (l,r)])
            return NFA(["i"], ["f"], {
                ("i", "", next(iter(A.I))),
                ("i", "", next(iter(B.I))),
                (next(iter(A.F)), "", "f"),
                (next(iter(B.F)), "", "f") } | A.Δ | B.Δ ).renum()
        case CONCAT(l, r):
            A, B = NFA.disjoint([reaut(x) for x in (l, r)])
            return NFA(["i"], ["f"], {
                ("i", "", next(iter(A.I))),
                (next(iter(A.F)), "", next(iter(B.I))),
                (next(iter(B.F)), "", "f")} | A.Δ | B.Δ).renum()
        case STAR(e):
            A = reaut(e)
            return NFA(["i"], ["f"], {
                ("i", "", next(iter(A.I))), ("i", "", "f"),
                (next(iter(A.F)), "", next(iter(A.I))),
                (next(iter(A.F)), "", "f")} | A.Δ ).renum()
        case _:  raise ValueError(e)

NFA.clear()
# reaut(VOID()).visu()
# reaut(WRD("")).visu()
# reaut(WRD("ab")).visu()
# reaut(A := OR(WRD("ab"), WRD(""))).visu()
# reaut(CONCAT(A, WRD("cd"))).visu()
# reaut(STAR(A)).visu()
e = STAR(OR(WRD("ab"), WRD("")))

def handle(e):
    reaut(e).visu().rm_eps().visu().trim().visu().dfa().visu().mini().visu().renum().visu()

f = STAR(
    OR(
        OR(WRD("aa"), WRD("bb")),
        CONCAT(
            CONCAT(
                OR(WRD("ab"), WRD("ba")),
                STAR(OR(WRD("aa"), WRD("bb"))),
            ),
            OR(WRD("ab"), WRD("ba"))
        )
    )
)

handle(e)
handle(f)