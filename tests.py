#!/usr/bin/env python3
import toolkit
from nfa import NFA
from toolkit import powerfset, pdf_renderer

#####################################
NFA.clear()

# NFA.NOVISU = True

def ann(f):
    """Test procedures announce themselves"""
    def g(*p,**kw):
        print( f.__name__ , "-"*30)
        NFA.visutext(f.__name__)
        f(*p,**kw)
    return g

@ann
def interro201819():
    A = NFA.spec("""
    0
    5
    
    0 a 1 c 2
    1 b 1 a 3
    2 b 2 a 4
    3 c 3 a 5 a 2
    4 c 3 a 5 a 1
    """, name="interro2018-2019").visu()
    # A.table()
    A.texvisu("0 / 1 > 3\n 0 \ 2 > 4 / 5","3 ns,c 2 4 ne,c 1 2 lb 2")
    A = A.dfa().visu().texvisu(renum=True)

    A.mini().visu().texvisu(renum=True)



    B=NFA.spec("""
    eps
    fi
    eps a a c c
    a b ab a aa
    c b cb a ca
    ab a aba b ab
    cb a cba b cb
    aba c ac
    aa c ac a fi
    ca a fi c ac
    cba a fi c ac
    ac c ac a fi
    """, name="StudentMini").visu().mini().visu()

    C = NFA.spec("""
    I
    IV
    I a II c II
    II b II a III
    III c III a IV
    """, name="RealMini").visu()

    (C - B).visu().mini().visu()
    (C | B).visu()

# interro201819()



# from minimisation exercise
@ann
def minimisation_exo():
    NFA.spec("""
    a
    c f g
    
    a 0 b 1 e
    b 0 b 1 c
    e 0 e 1 f
    f 1 c 0 b
    c 1 f 0 e
    d 0 c 1 g
    g 0 d 1 f
    """,name="Minimisation exo", Qtype=str
    ).visu().trim().visu().dfa().visu().mini(table=False).visu()

# minimisation_exo()

###from révisions exercise
@ann
def revision_interro():
    NFA.spec("""
    1
    2
    1 a 1 a 2 b 2 eps 3
    2 b 2
    3 a 3
    """,name="Révision ε-removal"
    ).visu().rm_eps().visu().dfa().visu().mini().visu()

    NFA({1},{3},{
        (1,"a",2),
        (2,"b",3),
        (3,"c",2),
        (3,'',1)
        }, name="ε2").visu().rm_eps().visu().dfa().visu().mini().visu()


# revision_interro()
@ann
def shuffles():
    Big = NFA.of_set({"aAbBcC","aaaBBB"},"two").visu()
    A = Big.proj("abc").visu().renum().visu()
    B = Big.proj("ABC").renum().visu()
    C = (A@B).setnop(name="Shuffle")
    C.visu().dfa().visu().mini().visu()

    Bad = (C - Big).mini().visu()

    C.run("aABbcC")

    A = NFA.universal('abc').visu()
    B = NFA.of_word("abc").visu()
    C = (A -  B).visu().mini().visu()

    # fun case where determinising is removing redundant loops.
    S = (A@B).setnop(name="Shuffle").visu().dfa().visu()
    ##print(A[0], A[1], list(A[:10]))

    (A|B).visu().mini().visu()
    NFA.union(A,A,B,A).visu().dfa().visu().mini().visu()


# shuffles()


# a in third position before end
@ann
def exo_explosive_det():
    A = NFA( {0}, {3},
        { (0,'a',0), (0,'b',0), (0,'a',1),
          (1,'a',2), (1,'b',2),(2,'a',3),(2,'b',3)},
        name="a__"
    ).visu()
    # B = NFA.spec("""
    # 0
    # 3
    # 0 a 0 b 0 a 1
    # 1 a 2 b 2
    # 2 a 3 b 3
    # """,name='B').visu()
    # print(A)
    # A.table()
    A.texvisu("0 > 1 > 2 > 3")
    A.run("abaabbaaababb")
    # Ad = A.dfa().visu(pdfname="export.pdf")#.texvisu("0 / 1 \n 0 \ 2",renum=True)
    A.dfa(pdf=NFA.VISUPDF).visu()#.table()
    # print(A.dfa())

# exo_explosive_det()

# a b a factor
@ann
def exo_aba_factor():
    A = NFA( {0}, {3},
        { (0,'a',0), (0,'b',0), (0,'a',1),
          (1,'b',2), (2,'a',3), (3,'a',3), (3,'b',3) },
        name="_aba_").visu()
    A.dfa().visu().mini().visu()
    A.homo({'b': "cde", 'a':'A'}).visu()\
        .homo({'d': ""}).visu().rm_eps().trim().visu()\
        .dfa().visu().mini().visu()

# exo_aba_factor()

def arun():
    NFA.of_word("aaa").add_rule(0, 'b', 1).run("baa")

# arun()
@ann
def isomorphisms():
    IH = NFA.spec("""
    0
    0
    0 B 0 A 1
    1 A 0 
    """,name="(AA|B)*")

    IH.visu().complete().visu().ihomo({'a': 'AB', 'b':'BA'}).visu()

    IH.ihomo_visu({'a': 'AB', 'b':'BA'})
    IH.complete().ihomo_visu({'a': 'AB', 'b':'BA'})

# isomorphisms()
@ann
def ofset():
    A = NFA.of_set({"a","acb","acccb","bb"}).renum().visu().mini().visu()

# ofset()
@ann
def testproducts():
    NFA.VISULANG = 5
    NFA.VISU_INITIAL_ARROW = False
    Char = NFA.spec("""
    0
    1
    0 1 1
    1 0 0
    """).map(g=int).named("Char").visu()
    _ = NFA.Stay
    C1=Char.copy().map(g=lambda x:"b" if x else "a").named("C1")
    C2=Char.copy().map(g=lambda x:"B" if x else "A").named("C2")
    from itertools import product
    NFA._sprod2_brutal(Char, Char, {(0, 0), (1, 1)}).visu()
    NFA._sprod2_brutal(Char, Char, set(product([0, 1], repeat=2))).visu()
    NFA._sprod2_brutal(Char, Char, {(_, 0), (_, 1) , (1, _)}).visu()
    NFA._sprod2_brutal(Char, Char, {(_, 0), (_, 1) , (1, 1)}).visu()
    NFA._sprod2_brutal(Char, Char, {x for y in [0, 1] for x in {(_, y), (y, _)}}).visu()
    (Char @ Char).visu()
    C1.visu()
    NFA._sprod2_brutal(Char, C1, set(product([0, 1, _], ["a", 'b', _]))).visu()
    (NFA.of_word([1,2,3]) @ NFA.of_word([_,_])).visu()

    NFA.sprod_brutal (Char, C1, svec=set(product([0, 1, _], ["a", 'b', _]))).visu()
    X=NFA.sprod_brutal(Char, C1, C2, svec=set(product([0, 1, _], ["a", 'b', _], ["A", "B", _]))).visu()
    Y=NFA.sprod_brutal(Char, Char, Char, svec=set(product([0, 1, _], repeat=3))).visu()

    # on the fly version tests
    svec = NFA.shuffle([1,1],[_]) | NFA.shuffle([0],[_,_])
    P = NFA.sprod_brutal(Char, Char, Char, svec=svec).visu()

    svec = NFA.shuffle([1,1],[_]) | NFA.shuffle([0],[_,_])
    P = NFA.sprod(Char, Char, Char, svec=svec, record_steps=True).visu()

    P.visusteps(P._grow_step)

    svec = {(1,1)}
    P = NFA.sprod_brutal(Char, Char, svec=svec, silent=[0]).visu()
    Q = NFA.sprod(Char, Char, svec=svec, silent=[0]).visu()
    NFA.VISULANG = 10
    NFA.VISU_INITIAL_ARROW = True

# testproducts()

#########################################
# Digicode

@ann
def digicode():
    NFA.VISULANG = 15
    Digi = NFA.of_word("123").visu()

    # for c in "01234567890":
    for c in "x123":
        Digi.add_rule(0,c,0)
    Digi.name="Digicode"
    Digi.texvisu("0 > 1 > 2 > 3")#.table()
    Digi.visu().dfa().visu().texvisu("0 > 1 > 2 > 3",
    "0 lb 0 3 <40,ns 0 3 < 1 2 >70,ns,~ 0",renum=True)

# digicode()
########################################

@ann
def exoEqualRegexp():
    A = NFA.spec("""
    1 3
    4
    1 a 2 a 3
    2 b 3
    3 a 4 eps 1""").named("A").visu()

    B = NFA.spec("""
    1 
    4 2
    1 a 2
    2 b 3 a 4
    3 a 4
    4 eps 2""").named("B").visu()
    A = A.rm_eps().visu()
    B = B.rm_eps().visu()

    A = A.dfa().visu()
    B = B.dfa().visu().complete().visu().mini().visu()

@ann
def even_odd():
    P = NFA.spec("""
    P I
    P I Ia Paa
    P a Pa b P 
    Pa a Paa
    Paa a Pa b I
    I b I a Ia
    Ia a Iaa b P
    Iaa a Ia 
    """,name="a_blocks_alternate_even_odd").visu().dfa().visu().mini().visu()

@ann
def simplifyArdenSystem():
    ard = NFA.spec("""
    A
    C A
    A 0 B 1 C
    B 0 C
    C 0 C 1 C eps A
    """,name="Arden").visu().mini().visu()

    (-ard).mini().visu()

@ann
def rm_esp_clos_test():
    A = NFA.spec("""
    0
    2
    0 eps 1
    1 eps 2
    2 a 0
    """).visu().rm_eps().visu()

@ann
def ctl_tests():
    from ctl import AND, OR, NOT, TT, FF, IMPLIES, XOR, EX, EU, AU, AX, AG, EG, AF, EF, checkvisu
    n = NFA.VISULANG
    NFA.VISULANG = 0

    p,q="pq"
    exo = NFA.spec("""
    0
    __
    0  1  2
    1  0
    2  3  5  9
    3 2 4 6
    4 5
    5 1 6 7
    6 9
    7 1 2
    8  8 
    9 1 6 9
    10 8
    11 10 2
    """,name="Exo1-exam17",style="ts")

    labels = {
        1 : {p}, 4: {p},
        6 : {p}, 7 : {p}, 8 : {q,p}, 9 : {p,q},
        10:{p},11:{p}
    }

    # exo.label(labels,f_str).visu()

    # fo =  (OR, (AND, (EX, p), (NOT,p)), p)
    # fo = (OR, p, (NOT, p))
    # fo = (OR, (NOT, (EX, (NOT, p))), (AX, p))
    # fo = (IMPLIES, p, q)
    # fo = (IMPLIES, (NOT, p), (AX, p))
    # fo = (XOR, p, (AX, p))
    # fo = (AND, (AU, TT, q), (AF,q))
    # fo = (EF, q)
    # fo = (AND, (NOT, (EU, TT, (NOT, p))), (AG, p))
    # fo = (AG, p)
    fo = (AND, (EG, q), (EG, p), (EG, (OR, p, q)), (AG, (OR, p, q)))

    checkvisu(exo,labels,fo)

    kat = NFA.spec("""
    0
    __
    0 1 2
    1 0 3
    2 1
    3 3
    """, name="Katoen examples",style="ts").visu()

    labels = { 0: {p}, 1:{p,q}, 2:{q}, 3:{p} }
    kat.texvisu("0 \ 2 / 1 > 3", "3 lb 3")

    for f in [
        q,
        (EX, p), (AX, p),
        (EG, p), (AG, p),
        (EF, (EG, p)),
        (EF, (AG, p)),
        (AF, (EG, p)),
        (AF, (AG, p)),
        (AU, p, q),
        (EU, p, q),
        (EU, p, (AND, (NOT, p), (AU, (NOT, p), q))),
        (AX, (AX, q)),
        (EX, (AX, q)),
        (AX, (EX, q)),
        (EX, (EX, q)),
        (AX, (AF, (AND, p, q))),
        (AF, (AX, (AND, p, q))),
    ]:
        checkvisu(kat,labels,f,visu=("simple","detailed"))

    NFA.VISULANG = n


@ann
def exam2020():
    A = NFA.spec("""
    1 2
    1
    1 a 1 b 2
    2 a 3 b 2
    3 a 3 b 1""").visu()
    A.texvisu()
    A.texvisu("1 _ 2 > 3","1 la 1 2 lb 2 3 la 3 3 ~ 1")
    A.dfa().visu().mini().visu()


@ann
def decExam2020Verif():

    def decrement(n,X):
        return NFA({n}, set(range(n + 1)), {
            (p, g, p - g)
            for p in range(n + 1)
            for g in X
            if p - g >= 0
        }).named(f"Decrement({n}, {X})")

    P = decrement(4,{1,2,4}).visu()
    P.texvisu(defbend="bend left")
    P.texvisu(qloc="4 / 3 \\ 2 / 1 \\ 0",bends="4 >40,~ 0")
    P.texvisu(qloc="4 \ 3 / 2 \ 1 / 0", bends="4 < 0")
    decrement(5, set(range(1,5+1))).visu()
    decrement(5, (1,2,3)).visu()

    def increment(n,m,i,X):
        return NFA({i}, Q := set(range(n, m + 1)), {
            (p, k if k < 0 else f"+{k}", p + k )
            for p in Q
            for k in X
            if n <= p + k  <= m
        }).named(f"Increment({n}, {m}, {i}, {X})")

    P = increment(-2,3,0,{-1, 1, 2}).visu()
    P.texvisu(qloc="0 / 1 / 2 > 3 \n 0 \\ -1 \\ -2",
              bends="-2 <55 0  -1 >20,~ 1  0 <55 2  1 >,~ 3",
              defbend="bend left")

    # IndyT = increment(0,15,15,{-1,-2,-4,-8}).visu().texvisu()




@ann
def concatenation():
    A = NFA.of_set({"abc", "ABC"}).renum().visu()
    B = NFA.of_set({"012", "789"}).renum().visu()

    C = A + B
    C = C.visu()  # .renum().visu()

    D = NFA.concatenate(A, B, C).visu().renum().named("D").visu() \
        .rm_eps().visu().dfa().visu().mini().visu()

    # words of fixed length
    L = NFA.of_length(0, "abc").visu()
    L = NFA.of_length(2, "abc").visu()
    L = NFA.of_length(4, "01").visu()
    L = NFA.of_length(4, "01").setworder(tuple).visu()

def interfaceAutomataProduct():
    NFA.VISULANG = 0
    client = NFA.spec("""
        1 
        1
        1 msg! 2
        2 ok? 1""").named("client").visu()

    comp = NFA.spec("""
        1 
        1
        1 msg? 2
        2 envoyer! 3
        3 nack? 4 ack? 6
        4 envoyer! 5
        5 ack? 6 nack? 7
        6 ok! 1
        7 echec! 1
        """).named("comp").visu()

    comp_client = NFA.interface_sprod(comp, client,visu_dnice=True).visu()

    canal = NFA.spec("""
            1 
            1
            1 envoyer? 2
            2 token! 3
            3 ack! 4
            4 liberer_token! 1
            D nack! D
            """).named("canal").visu()
    # print(canal)

    canal_comp_client = NFA.interface_sprod(comp_client, canal,visu_dnice=True).visu().trim().visu()
    NFA.VISULANG = 10

    Vendor = NFA.spec("""
    0
    7
    0 pay? 1
    ## 1 deliver! 2 
    1 verif! 3
    ## 2 verif! 4
    3 deliver! 4 transfer? 5
    4 transfer? 7
    5 deliver! 7
    """, name="Vendor", worder=tuple)
    Vendor.visu()

    Client = NFA.spec("""
    0
    0
    0 pay! 0 deliver? 0 cancel! 0
    """, name="Client", worder=tuple)
    Client.visu()

    Bank = NFA.spec("""
    0
    1 3
    0 cancel? 1
    0 verif? 2
    2 transfer! 3
    """, name="Bank", worder=tuple)
    Bank.visu()

    CB = NFA.interface_sprod(Client, Bank).visu()
    Sys = NFA.interface_sprod(CB, Vendor).visu()

@ann
def verif_mini_prog():
    prog = NFA.spec("""
    1
    __
    1 b=1 1 b=0 2
    2 b:=1 3
    3 proc() 4
    4 b:=0 1""").visu().texvisu("1 > 2 > 3 > 4", "4 < 1")

@ann
def synchro_prod_poly_example():
    A = NFA.spec("""
        0
        1
        0 a 1 c 1
        1 a 0""").named("A").visu()

    B = NFA.spec("""
        0
        1
        0 b 1 c 1
        1 b 0""").renum(2).named("B").visu()

    _ = NFA.Stay
    C = NFA.sprod(A, B, svec={("a", _), (_, "b"), ("c", "c")}).visu()  # .texvisu(renum=True)

    D = A | B | C
    D.visu().texvisu(renum=True, at={
        '0': (0, .5), '1': (1, .5), '2': (-.5, 0), '3': (-.5, -1),
        '(0, 2)': (0, 0), '(1, 2)': (1, 0),
        '(0, 3)': (0, -1), '(1, 3)': (1, -1),
    }.get, params=",x=3cm,y=3cm")

@ann
def hard_minimisation():
    tab = False
    def fib(n):
        if n == 0: return "0"
        if n == 1: return "1"
        return fib(n - 1) + fib(n - 2)

    def FIB(n):
        return {fib(k) for k in range(n)}

    S = FIB(6)

    A = NFA.of_set(S).dfa().renum().visu().mini(table=tab).visu()

    # starts with final, need to ensure I, II and not II, I, prev bug.
    B = NFA.spec("""
    0
    0
    0 a 1 b 1
    1 b 0 a 1
    """).visu().mini(table=tab).visu()

    C = NFA.of_word("aaaa").complete().visu().mini(table=tab).visu()

@ann
def nondet_vulgarise():
    NFA.VISULANG = 0
    # NFA.VISUSIZE = False
    A = NFA( {0}, {3},
        { (0,'a',0), (0,'b',0), (0,'a',1),
          (1,'a',2), (1,'b',2),(2,'a',3),(2,'b',3)},
        name="a__"
    ).visu()

    A.run("bababa",used_states=False,labeljust="c")
    A.dfa(pdf=NFA.VISUPDF).visu()

def _AMC():
    A = NFA.spec("""
    0
    1
    0 a 0 a 1 b 1 a 2
    1 a 1 b 0
    2 a 0""", "test")

    A.visu().dfa().visu()
    A.AMC()
    A.dfa().AMC(Qadd=powerfset(A.Q) - {fset()})

@ann
def process_language_v1():
    NFA.VISULANG = 0
    As, sync = NFA.processes("""
    bool        W0   := False   # process 0 wants critical access
    bool        W1   := False   # process 1 wants critical access
    int[0,1]    Turn := 0       # Whose turn is this ?

    process P0:
      while True {
        # noncritical section
        W0    := True;
        Turn  := 1;
        wait W1 = False or Turn = 0;
        # critical section
        W0    := False;
      }

    process P1:
      while True {
        # noncritical section
        W1    := True;
        Turn  := 0;
        wait  W0 = False or Turn = 1;
        # critical section
        W1    := False;
        }
    """)

    # print(sync)
    for A in As: A.visu()
    res = NFA.nsprod(*As, sds=sync)
    res.visu()
    NFA.VISULANG = 10

@ann
def fonts(solve=1):
    A = NFA.of_word("ab") @ NFA.of_word("_")
    base = A.name
    for font in [ # fc-match <name>
        NFA.VISUFONT,
        "Linux Biolinum",
        "Libertinus Sans",
        "Libertinus Math",
        "Libertinus",
        "Libertinus, Linux libertine",
        "Times", # -> Nimbus Roman
        "DejaVu Math TeX Gyre",
        "Times New Roman, Liberation serif",
        "Palatino",
        "Bitstream Vera Serif",
        "URW Bookman",
        "Noto Serif",
        "Helvetica", # -> Nimbus Sans
        "Liberation Sans, Arial",
        "Noto Sans",
        ]:
        if solve and toolkit.sh.which("fc-match"): print(font, "->",
          toolkit.sp.run(["fc-match", font], capture_output=1).stdout.decode().strip())
        A.named(base+" "+font).visu(fontname=font)

@ann
def concat_changes_test():
    "edge cases for multiprocess renderer"
    NFA.clear()
    other = "test_other"; toolkit.os.unlink(other+".pdf")
    for target in NFA.VISUPDF, other:
        for prepend in 0,1:
            for i in range(3):
                NFA.visutext(f"{target} {prepend=} n°{i}", pdfname=target, pdfprepend=prepend)





def main():
    exoEqualRegexp()
    even_odd()
    interro201819()
    minimisation_exo()
    revision_interro()
    rm_esp_clos_test()
    exo_aba_factor()
    exo_explosive_det()
    arun()
    concatenation()
    shuffles()
    ofset()
    isomorphisms()
    testproducts()
    digicode()
    simplifyArdenSystem()
    ctl_tests()
    exam2020()
    decExam2020Verif()
    interfaceAutomataProduct()
    verif_mini_prog()
    synchro_prod_poly_example()
    hard_minimisation()
    process_language_v1()
    fonts()
    # concat_changes_test()

# NFA.sanity_check()
# fonts()
# from transition_deterministic_minimisation import *
# main()
fonts()
# ctl_tests()
# process_language_v1()


pdf_renderer.print_status()