#!/usr/bin/env python3
from nfa import *
from itertools import *

NFA.clear()
NFA.VISUDOUBLEARROWS = False

A = NFA.spec("""
0
2
0 a 1 a 2
1 a 0 b 2 
""",name="A").visu()

A.run("aaab")

B = NFA.spec("""
0
0
0 c 1 a 0
1 c 0""", name="B").visu()

NFA.visutext("DETERMINISATION")

A.visu().dfa().visu(doublearrows=True)

NFA.visutext("PRODUCTS")

(A & B).visu().dfa().visu().mini().visu()

(A | B).visu().dfa().visu().mini().visu().renum().visu()

# U = (A & B).named("U").visu()
# U.F = set(product(A.F,B.Q)) | set(product(A.Q,B.F))
# U.Q |= U.F
# U.visu().mini().visu()

NFA.visutext("COMPLETE")

Σ="abc"
OA, OB = A, B
A = A.complete(Σ).visu()
B = B.complete(Σ).visu()

NFA.visutext("UNION THROUGH PRODUCT OF COMPLETE")

U = ( A & B ).named("A ∪(prod) B")
U.F = set(product(A.F,B.Q)) | set(product(A.Q,B.F))
U = U.visu().trim().visu().dfa().visu().mini().visu().renum().visu()
# U.run("cc")
AUB = (A | B).mini().renum().visu()
NFA.visutext(U.iso(AUB))

NFA.visutext("SHUFFLE: UNSYNCHRONISED PRODUCT")
A, B = OA, OB
Shu = A.visu() @ B.visu()
Shu.visu().mini().visu()

S = NFA.of_word("abc").visu() @ NFA.of_word("ABC").visu()
S.visu()
(-S).visu()

S = NFA.of_word("a") @ NFA.of_word("ABC")
S.visu()

S = NFA.of_word("abc") @ NFA.of_word("abc")
S.visu().mini().visu()

S = NFA.of_word("abc") @ NFA.of_word("abc") @ NFA.of_word("abc")
S.renum().visu().mini().visu()
