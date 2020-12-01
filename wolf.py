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

NFA.NOVISU = False
NFA.VISULANG = 2
NFA.VISU_INITIAL_ARROW = False
NFA.VISUDOUBLEARROWS = True

actorsv = defcst("wolf", "goat", "cabb", "farmer", namespace=globals())
actors = fset(actorsv)

NFA.visutext("Naïve method")

Farmer = NFA(
    {actors},
    name="Farmer",
    worder=tuple
).visu()

def _licit(s):
    return farmer in s if {wolf, goat} <= s or {goat, cabb} <= s else True

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
Farmer.F = { fset() }

Farmer.visusteps()#(rankdir="TB")
Farmer.map(f=lambda q: (
    ", ".join(q) + " \\n~~~~~~~\\n " + ", ".join(actors-q)
)).visu(break_strings=False)

##########################################################################
##########################################################################

NFA.visutext("Named Product")
NFA.NOVISU = False

Char = NFA.spec("""
0
1
0 1 1
1 0 0""","Char").visu()

sysv = [Char.copy().named(x) for x in actorsv]
sds = [{farmer:x, a:x} for a in actors for x in (0, 1)]

def prodfilter(A, P, v, Q):
    return Q not in A.Q and licit(invd(Q)[0]) # not in Q optional: cycles or not.

P = NFA.nsprod(*(reversed(sysv)),
               sds=sds,
               filter=prodfilter,
               # nice=True, # breaks visusteps if true
               record_steps=True
               ).visu()

print(repr(P))
# P.visusteps()
P.dnice().visu()
