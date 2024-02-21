#!/usr/bin/env python3

from buta import *

# A= BUTA({"qf"}, {
#     "aq", "bq"
# })
#
# print(A, repr(A))

print(
    A := BUTA.spec("""
ql
a q
a q'
g q' q
g q q
b q
⊥ ql
f q ql ql
""", "A"))

# term.COLOUR_STR =False

print("run", A.run( ('a',) ) )
print("run", A.run( "a" ) )
print("run", A.run(
    t := ('f',
          "b",
          ('f', 'a', '⊥'),
          )
))
print(t in A, "b" in A, "⊥" in A, ("⊥",) in A)
assert term(("⊥",)) == term("⊥")
print(t, term(t), tuple(term(t)))

for t in (terms := term.sh(A[:20])):
    print(f"{t.height():2d} {str(term.order(t)):<30} -- {t}")
    assert t in A

print(t)
for pos ,u in t.positions_subterms().items():
    print(f"{''.join(map(str ,pos)):<5} -- {u}")
    assert t@ pos == u and t(pos) is not None
print(t)

print(t.replace(pos,("Z","X", "Y")))
print(t.substitute({"a": ("Z","X","Y"), "b":11 }))

print("TS", t := term.spec("f( a , b (), g(hi!(i(x))))"))

l = ("f", ("g", "x"), ("g", "y"))
R = TRS([])
# print(R.match(l, u))

# to have correct display of couple states

print( couples := BUTA({}, {
    ("f", tuplestate((1,2)), (3,4))
}, "couples"))

print(TRS({(("a", "x"),"b")}))
R = TRS.spec("g(x) -> g(g(x))")
print(R.rules, list(R), str(R))

print("_"*80)

print(A)

print(
    B := BUTA.spec("""
qf
a qf
g qf qf
# f qf qf qf
""", "B"))

print("A", list(A[:5]))
print("B", list(B[:5]))

P= A&B
print( P)

print( P.accessibles() )

# print(X := P.trim())

print(t, t.leaves(), T("f()").leaves() )

print([e for e in " x y z X x1 x_1 a b c A1 x__1".split() if e not in R.vars])

print(T("f(a,g(b))").to_tuple())

print(R)

for l, t in [
    ('a', 'a'),
    ('f(x)', 'f(x)'),
    ('a', 'x'),
    ('x', 'a'),
    ('f(x)', 'f(f(a))'),
    ('f(x,g(y))', 'f(f(a),g(g(b)))'),
    ('f(x,g(y),a)', 'f(f(a),g(g(b)),b)'),
    ]:
    l, t = T(l), T(t)
    print(l, t, σ := R.match(l,t) )
    if σ is not None: assert l.substitute(σ) == t

# print(A, A.map(f=lambda q:f"f{q}", g=lambda f:f"g{f}"))
# print(A)
# print(A.collapse([{"q","q'"}]))

print("REWRITE", R, I := Ts("f(a)", "g(b)", "g(g(c))", "f(g(x))") )
RI = R(I)
print(set(RI))

print(X := set(R.closure(Ts("g(b)"), tlim=0.01)), len(X))

Af0 = BUTA.spec("""
qf
⊥ q⊥
f q⊥ qf
""","Af0")
Rfdouble = TRS.spec("f(x) -> g(f(x),a,f'(x)); g(x,a,y) -> h(y,b,x)")
print(Rfdouble)

# print("="*80)
clos = term.sh(Rfdouble.closure(set(Af0), tlim=0.01))
print(len(clos))
# print("="*80)
# print(Af0.completed_rules(Rfdouble))
Ac = Af0.copy(); n = 0
while not set(clos) <= set(Ac):
    Ac.complete_inplace(Rfdouble)#.print()
    n+=1
print("closure covered in", n, "steps")

Rfaax = TRS.spec("f(x) -> f(a(a(x)))")

Af0.complete(Rfaax, 2).print()

Ac = Af0.complete(Rfaax, 1).collapse([["0", "q⊥"]]).print() # assumes numbering scheme of .complete
assert Ac.is_complete(Rfaax)

OS = BUTA.of_set([T("a"), "f(a,b(b(b(a))))"])
OS.print()

Aabsbs = BUTA.spec("""
qf
⊥ qab
a qab qab
b qab qab

⊥ qb
b qb qb

f qab qb qf
""","f(ab*,b*)").print()

Aasabs = BUTA.spec("""
qf
⊥ qab
a qab qab
b qab qab

⊥ qa
a qa qa

f qa qab qf
""","f(a*,ab*)").print()

I = Aabsbs & Aasabs
I.print().trim().print()

I = Aabsbs | Aasabs
I.print().trim().print()

Rfx     = TRS.spec("f(x) -> x")

A = Af0.complete(Rfx).print()


A = BUTA.spec("""
q
a qa
f qa qfa
: qfa q q
⊥ q
""","comb(f(a),...⊥)").print()

R = TRS.spec("a -> b; f(x) -> f(g(x))")
print(f"{R=}")

B = A.image(R).print().image(R).print(20)
assert T(":(f(g(a)), :(f(g(a)), ⊥))") in B


A = BUTA.spec("""
q
⊥ q
f q q
""", name="ERROR eps-transition").print()

R = TRS.spec("f(x) -> x")

B = A.complete(R).print()