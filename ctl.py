# Copyright 2019-2024,  Vincent Hugot <vincent.hugot@insa-cvl.fr>
# This file is part of VH's NFA Framework.
#
# VH's NFA Framework is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License
# as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.
#
# VH's NFA Framework is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty
# of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License along with VH's NFA Framework.
# If not, see <https://www.gnu.org/licenses/>.

"""CTL model-checking;

A terrible implementation for pedagogical purposes.

WILL BE REDONE SOON WITH PROPER STRUCTURAL PATTERN MATCHING (c.f. renfa.py for an example)

Use:
from ctl import AND, OR, NOT, TT, FF, IMPLIES, XOR, EX, EU, AU, AX, AG, EG, AF, EF, check, checkvisu
"""

# φ ::= p  | ¬ φ | φ ∨ φ | EX φ | E [φ U φ] | A [φ U φ].

# from pampy import match, REST, _
from enum import Enum
from nfa import *
import copy

LogOps = Enum('LogOps','AND OR NOT TT FF IMPLIES XOR EX EU AU AX AG EG AF EF')
globals().update(LogOps.__members__)

symb = {
        AND:        '∧',
        OR:         '∨',
        NOT:        '¬',
        FF:         '⊥',
        TT:         '⊤',
        IMPLIES:    '→',
        XOR:        '⊕',
        EX: "∃○", EU: "∃𝖴", AU:"∀𝖴",
        AX:"∀○", AG:"∀□", EG:"∃□", AF:"∀◊", EF:"∃◊"
    }

def isatom(x):
    return type(x) is not tuple

def f_str(f):
    if isatom(f): return symb[f] if type(f) is LogOps else  str(f)
    o,*r = f
    assert len(r) > 0
    if len(r) == 1: return f"({symb[o]} {f_str(r[0])})"
    if len(so := symb[o]) == 2:
        g,h = r ; Q,O = so
        return f"{Q}({f_str(g)} {O} {f_str(h)})"
    return "(" + f" {symb[o]} ".join(map(f_str,r)) + ")"

symbtex = {
        AND:        '\\land',
        OR:         '\\lor',
        NOT:        '\\neg',
        FF:         '\\bot',
        TT:         '\\top',
        IMPLIES:    '\\simplies',
        XOR:        '\\oplus',
        EX: "\\exists\\NEXT", EU: "\\exists\\UNTI", AU:"\\forall\\UNTI",
        AX:"\\forall\\NEXT", AG:"\\forall\\GENE", EG:"\\exists\\GENE", AF:"\\forall\\FINA", EF:"\\exists\\FINA"
    }

# def f_tex(f):
#     if isatom(f): return symb[f] if type(f) is LogOps else  str(f)
#     o,*r = f
#     assert len(r) > 0
#     if len(r) == 1: return f"{{{symbtex[o]} {f_tex(r[0])}}}"
#     if len(so := symbtex[o]) == 2:
#         g,h = r ; Q,O = so
#         return f"{Q}{{{f_tex(g)} {O} {f_tex(h)}}}"
#     return "{" + f" {symbtex[o]} ".join(map(f_tex,r)) + "}"

def f_tex(f):
    z = f_tex
    match f:
        case str(): return f
        case LogOps(): return symbtex[f]
        case LogOps() as o, g:
            return f"{{{symbtex[o]} {z(g)}}}"
        case LogOps() as o, g, h:
            match [x for x in  symbtex[o].split("\\") if x]:
                case o,: return f"\p{{{z(g)} \\{o} {z(h)}}}"
                case q,o: return f"\\{q}\p{{{z(g)} \\{o} {z(h)}}}"
                case _: assert False, _
        case _:  assert False, _


def subs(f):
    if isatom(f): return {f}
    return {f} | set.union(*(subs(φ) for φ in f[1:] ))

def f_len(f):
    if isatom(f): return 1
    return 1+max(f_len(φ) for φ in f[1:])

def sortsubs(f):
    return sorted(subs(f), key=f_len)


def check(A,l,f):
    """
    Model-check CTL formula; side effects on l
    :param A: transition system
    :param l: dict state -> set of atomic labels; will be updated
    :param f: CTL formula on same atomic labels
    :return:  l, dict subformula -> states that satisfy it
    """
    for q in A.Q - l.keys(): l[q]=set()
    R = { (p,q) for p,_,q in A.Δ }
    def pred(phi):
        return { p for (p,q) in R if phi in l[q] }

    subs_f = sortsubs(f)
    sf = set(subs_f)
    for f in subs_f:
        if f == TT:
           for q in A.Q: l[q] |= {TT}
           continue
        elif f == FF or isatom(f):
            continue

        o,*r = f
        if o == EX:
            assert len(r) == 1
            for p in pred(r[0]): l[p] |= {f}
        elif o == AX:
            assert len(r) == 1
            for p in pred(r[0]):
                if all( r[0] in l[q] for (s,q) in R if s==p ) :
                    l[p] |= {f}
        elif o == NOT:
            assert len(r) == 1
            for q in A.Q:
                if r[0] not in l[q]: l[q] |= {f}
        elif o == AND:
            for q in A.Q:
                if all( φ in l[q] for φ in r ): l[q] |= {f}
        elif o == OR:
            for q in A.Q:
                if any( φ in l[q] for φ in r ): l[q] |= {f}
        elif o == XOR:
            for q in A.Q:
                if sum( φ in l[q] for φ in r ) == 1: l[q] |= {f}
        elif o == IMPLIES:
            g,h = r
            for q in A.Q:
                if not g in l[q] or h in l[q]: l[q] |= {f}
        elif o == EU:
            g,h = r
            Q = { q for q in A.Q if h in l[q] }
            while True:
                for q in Q:  l[q] |= {f}
                P = Q.copy()
                Q = {q for q in A.Q if g in l[q]} & pred(f)
                if P == Q: break
        elif o == EF:
            (h,) = r
            Q = { q for q in A.Q if h in l[q] }
            while True:
                for q in Q:  l[q] |= {f}
                P = Q.copy()
                Q = pred(f)
                if P == Q: break
        elif o == AU:
            g, h = r
            Q = {q for q in A.Q if h in l[q]}
            while True:
                for q in Q:  l[q] |= {f}
                P = Q.copy()
                Q = { p for p in pred(f) if g in l[p] and all( f in l[q] for (s,q) in R if s==p ) }
                if P == Q: break
        elif o == AF:
            (h,) = r
            Q = {q for q in A.Q if h in l[q]}
            while True:
                for q in Q:  l[q] |= {f}
                P = Q.copy()
                Q = { p for p in pred(f) if all( f in l[q] for (s,q) in R if s==p ) }
                if P == Q: break
        elif o == AG:
            (h,) = r
            equi = (NOT, (EF,  (NOT, h)))
            check(A,l,equi)
            rm = subs(equi) - sf
            for q in A.Q:
                if equi in l[q]:  l[q] |= {f}
                l[q] -= rm
        elif o == EG:
            (h,) = r
            equi = (NOT, (AF,  (NOT, h)))
            check(A,l,equi)
            rm = subs(equi) - sf
            for q in A.Q:
                if equi in l[q]:  l[q] |= {f}
                l[q] -= rm
        else: assert False, f
    return  l, { f : {q for q in l if f in l[q]} for f in subs_f }


ATOMS = "atoms"
SIMPLE = "simple"
DETAILED = "detailed"

CHECKVISU = (ATOMS, SIMPLE, DETAILED)

def checkvisu(A,labels,f,visu=None):
    """
    Check transition system with atomic labels wrt. CTL formula.
    Visualise the system's annotations.
    :param A: TS
    :param labels: dict state -> set of atomic labels. No side-effect
    :param f: CTL formula on same atomic labels
    :param visu: which visualisations should be made: subcollection of (ATOMS, SIMPLE, DETAILED)
    :return: as check: updated labels, dict subformula -> states that satisfy it
    """
    l = copy.deepcopy(labels)
    N = A.name

    visu = visu if visu is not None else CHECKVISU

    if ATOMS in visu:
        n = f"{N} : {f_str(f)}: atoms"
        A.label(l,f_str).named(n).visu(
            node_shape="box",epsilon_style="",size=False,break_strings=False)

    res = check(A,l,f)

    if SIMPLE in visu:
        dmod = { q:
                 'color="#00BB00" fillcolor="#007700" penwidth=2 fontcolor=white'
                 if f in l[q] else
                 'color="#770000" fillcolor="#BB0000" penwidth=2 fontcolor=white'
                 for q in l }
        n = f"{N} : {f_str(f)}: simple"
        A.named(n).visu(dmod=dmod,epsilon_style="",size=False)

    if DETAILED in visu:
        n = f"{N} : {f_str(f)}: detailed"
        l = { q: sorted(l[q], key=lambda x:(f_len(x),f_str(x))) for q in l }
        A.label(l,f_str).named(n).visu(
            break_strings=False,node_shape="box",epsilon_style="",size=False)

    A.name = N
    return res
