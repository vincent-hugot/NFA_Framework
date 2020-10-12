#!/usr/bin/env python3

# Exercice 1 (Le loup, la chèvre et le chou) Un fermier accompagné d’une chèvre, d’un
# loup et d’un choux doit traverser une rivière pour rentrer chez lui. Malheureusement, il ne
# possède qu’une minuscule barque ne lui permettant de transporter qu’un seul de ses "compa-
# gnon" à la fois. Ainsi, à chaque aller-retour, il doit en laisser deux sans surveillance le temps
# de faire le voyage. Comment va-t-il s’y prendre pour tous les faire traverser, sans qu’aucun
# ne se fasse manger par un de ses "collègue" durant la période où ils ne sont pas surveillés ?
# (Le loup mange la chèvre et la chèvre mange le chou.)


from nfa import *
from itertools import *

sp.run(["rm", "-f", f"{NFA.VISUPDF}.pdf"])

# NFA.NOVISU = True
NFA.VISULANG = 2
NFA.VISU_INITIAL_ARROW = False
NFA.VISUDOUBLEARROWS = True
_ = NFA.Stay

actorsv = defcst("wolf", "goat", "cabb", "farmer", namespace=globals())
actors = fset(actorsv)

NFA.visutext("Direct method")

Farmer = NFA(
    {actors},
    set(),
    set(),
    name="Farmer",
    worder=tuple
).visu()

def _licit(q):
    return farmer in q if {wolf, goat} <= q or {goat,cabb} <= q else True

def licit(q):
   return _licit(q) and _licit(actors - q)


def growfarmer(A):
    has=False
    def extend(q):
        nonlocal has
        if farmer in q:
            for a in q:
                Q = q - {a, farmer}
                if licit(Q): has = A.try_rule(q, a, Q) or has

        if farmer not in q:
            for a in actors - q:
                Q = q | {a,farmer}
                if licit(Q): has = A.try_rule(q, a, Q) or has

    for q in A.Q.copy(): extend(q)
    return has


Farmer.growtofixpoint(growfarmer, record_steps=True)
Farmer.F = { fset(()) }

Farmer.visusteps()#(rankdir="TB")
Farmer.map(f=lambda q: (
    ", ".join(q) + " \\n~~~~~~~\\n " + ", ".join(actors-q)
)).visu(break_strings=False)

##########################################################################
NFA.visutext("Product, old vector version")
# This version is deprecated; see new version below.

Char = NFA.spec("""
0
1
0 1 1
1 0 0
""","Char").visu()

VS = VecSet(actorsv)
sysv = [Char.copy().named(x) for x in actorsv]

def prodfilter(A, P, v, Q):
    return Q not in A.Q and licit(VS.setofvec(Q))  # not in Q optional: cycles or not.

moves = [ {farmer,a} for a in actors ]

svec = {VS.vecofset(S, one=z, zero=_) for z in (0, 1) for S in moves}

P = NFA.sprod(*sysv,
              svec=svec,
              filter=prodfilter
              )

print(repr(P))

P=P.visu().map(f=lambda v:VS.setsofvec(v,zero=1),
             g=lambda v: ", ".join(VS.setofvec(v,zero=_) - {farmer})
             ).visu()


print(f"Total solutions: {len(sols := list(P))}")

for sol in sols: print(sol)

##########################################################################
NFA.visutext("Product, named version (NEW)")
NFA.NOVISU = False
sds = [{farmer:x, a:x} for a in actors for x in (0, 1)]

def prodfilter(A, P, v, Q):
    return Q not in A.Q and licit({c for c,x in Q if x==0})


P = NFA.nsprod(*(reversed(sysv)),
               sds=sds,
               filter=prodfilter,
               # nice=True, # breaks visusteps if true
               record_steps=True
               )

print(repr(P))
# P.visusteps()
P.dnice().visu()

# P=P.visu()