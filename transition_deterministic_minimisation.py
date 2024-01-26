from nfa import *

NFA.VISULANG=15
NFA.VISULANGFILTER = ("power", 2)
# NFA.NOVISU = True

def a_in_nth_pos(n,a="a",al="ab"):
    return NFA({0}, {n},
               { (p,a,p+1) for p in range(n-1) for a in al } | { (n-1,a,n) },
               name=f"[{al}]*{n-1} {a}"
               )


def uniquelast(al, n):
    """the last n letters are unique in word"""
    return NFA({f"{a}0" for a in al},
               {n},
               { (f"{a}0", b ,  f"{a}0")
                    for a in al
                    for b in set(al) - {a} } |
               { (f"{a}{k}", a , (f"{a}{k+1}" if k<n-1 else n) )
                    for a in al
                    for k in range(n) },
               name=f"unique_last({al=},tail={n})"
               )

def do_unique_last():
    A = uniquelast("abc",1).visu()
    A.dfa().visu()
    # UniqueLast.dfa(multi_init=True).visu()
    A.mini().visu()

    A.trans_det_Moore().visu()
    A.tdBrzozowski().visu()

    A.mini().trans_det_Moore().visu()
    A.mini().tdBrzozowski().visu()


def modulo(N, a="a", acc=lambda n,N: n%N, desc=" != 0"):
    def q(n): return f"{n}%{N}"
    return NFA({q(0)}, { q(i) for i in range(N) if acc(i,N) },
               { (q(i), a, q((i+1)%N)) for i in range(N) },
               name=f"modulo {N}{desc}")


def do_modulo():
    B = modulo(K := 2) | modulo(L := 3)
    # NFA.NOVISU = True
    B.visu().mini().visu().tdBrzozowski().visu().tdBrzozowski().visu()
    B.tdBrzozowski().visu()
    C : NFA = B.reverse().dfa().reverse().visu()
    NFA.NOVISU = False
    NN = 6#K*L # works somewhat for 6 but not 15 !!!
    C = NFA.of_word("a"*(NN-1)).named(f"Not multiple of {NN}")
    C.I = C.Q - {0} ; C.F = {0}
    C.add_rule(NN-1, "a", 0)
    C.visu()
    PS = powerfset(C.I, 1,NN//2)
    print(len(PS))
    # .trans_det_Moore()
    NFA.visutext("search tdmini")
    A = min( ( C.dfa(force_init={P, fset(C.I)-P}) for P in PS ),
                key=lambda A:len(A.Q))
    A.visu().trans_det_Moore().visu()
    # 6 -> not plultiples of 2 | multiple of two but not of three (2, 4, 8)*


nTwo = NFA.spec("""
_0
_1
_0 a _1
_1 a _0""", "-2")
nThree = NFA.spec("""
0
1 2
0 a 1
1 a 2
2 a 0""", "-3")

TwoNThree = NFA.spec("""
0
2 4
0 a 1
1 a 2
2 a 3
3 a 4 
4 a 5
5 a 0
""","2 -3")

def do_modulo_break():
    U = nTwo | TwoNThree
    U.visu().dfa().visu()

    for mut in powerset(U.Q, 2):
        Um = U.copy().named(str(mut))
        Um.F = U.F ^ set(mut)
        if U == Um:
            Ummin = Um.trans_det_Moore()
            if len(Ummin.Q) <= 5:
                Ummin.visu()

def do_nth_pos():
    NFA.visutext("Brz works")
    C = NFA.union(*(a_in_nth_pos(i) for i in [1, 2, 3])).visu()

    C.mini().visu().tdBrzozowski().visu()
    C.trans_det_Moore().visu()
    C.tdBrzozowski().visu()

    NFA.visutext("Brz doesn't work")
    D = a_in_nth_pos(2,"c", "abc") | a_in_nth_pos(2,"b", "abc") | a_in_nth_pos(3,"a", "abc")
    D.visu().tdBrzozowski().visu().tdBrzozowski().visu()
    D.mini().visu()
    D.trans_det_Moore().visu().reverse().trans_det_Moore().reverse().visu() # not always applicable



def permut(N):
    "basic automaton with circular permuation for a"
    return NFA({n for n in range(N) if not n%2}, {0}, {
        (n, "a", n+1) for n in range(N-1)
    } | { (N-1, "a", 0) }, name=f"permut {N}")

def cycle(a,*l):
    "cycle to rules"
    l = l + (l[0],)
    return { (p,a,q) for p,q in zip(l,l[1:]) }

def cycles(N):
    "theoretical cycles"
    even = [k for k in range(0, N-2, 2)]
    odd = [N-2] + [ k for k in range(1, N-2, 2) ]
    solo= [N-1]
    r = even, odd, solo
    assert sum(map(len,r)) == N
    return r

def do_permut(N=8):
    # NFA.VISULAYOUT="circo"
    P = permut(N)
    # P.add_rules(
    #     cycle("b", 0,2,4) | cycle("b", 6,1,3,5) | cycle("b", 7)
    # )
    print(N, cycles(N))
    for c in cycles(N): P.add_rules(cycle("b", *c))
    assert P.is_det(True, ignore_inits=True)

    P.visu(layout="circo")

    PD = P.dfa().visu()
    targets = powerfset(P.Q, N//2, N//2)
    print(len(targets), "targets")
    print("missing:", m := (targets - PD.Q), len(m) )
    assert not m

    PD.mini().visu()
    return len(m)

def bonfante_permut(N=4):
    P = permut(N).named(f"Bonfante {N}")
    P.I = P.Q
    P.add_rules(
        cycle("b", 0) | cycle("b", *range(1, N))
        | {(0, "c", 0)}
        | {(q, "c", (q + 1) % N) for q in range(1, N)}
    )
    assert P.is_det(True, ignore_inits=True)
    return P

def do_bonfante_permut(N=4):
    P = bonfante_permut(N)

    P.visu(layout="circo")

    PD : NFA = P.dfa().visu()
    assert len(PD.Q) == 2**len(P.Q) - 1
    # PD.trans_det_Moore().visu().tdBrzozowski().visu() # nothing works

def adrien_periods(N):
    # l'ensemble des préfixes non n périodiques, c'est à dire les mots u tels qu'il existe k pour lequel la k et n+k ieme lettres sont différentes.
    # C'est facile de faire un DFA qui teste ça pour tout k congru à i modulo n et ça ne nécessite que 3n états.
    # C'est facile de combiner ces gadgets en un seul MEDA de taille 3n qui reconnaît notre langage.
    # Le DFA minimal pour ce langage doit garder en mémoire les n dernières lettres lues. C'est nécessairement exponentiel.
    A = NFA(range(N), (), {
        r for p in range(N - 1) for r in [(p, x, (p + 1) % N) for x in "ab"]
    }, name=f"Adrien Periods {N=}")

    def no(a):
        def q(n): return f"{a}{n}"

        return (
                [(N - 1, a, q(1))]
                + [(q(i), symb, q((i + 1) % N)) for symb in A.Σ for i in range(1, N)]
                + [(q(0), symb, q(1) + "!") for symb in A.Σ - {a}]
                + [(q(1) + "!", symb, q(2)) for symb in A.Σ]
        )

    for s in A.Σ: A.add_rules(no(s))
    A.F = {s + "1!" for s in A.Σ}
    return A

def do_adrien(N):
    A = adrien_periods(N)
    A.visu()
    A.dfa().visu().mini().visu().tdBrzozowski().visu()


def enum_nfa(N, Σ):
    Q = range(N); S = len(Σ)
    num = (2**N - 1)**2 * 2**(S*N**2)
    print(N, S, num)
    return num, (
        NFA(I, F, Δ)
        for I in powerset(Q, 1)
        for F in powerset(Q, 1)
        for Δ in powerset(product(Q,Σ,Q))
    )


def enum_mida(N, Σ):
    Q = range(N); S = len(Σ)
    num = (2**N - 1)**2 * (N+1)**(S*N)
    print(f"mida {N=} {S=} {num=}")
    return num, (
        NFA(I, F, Δ)
        for Δl in powerset(product(Q,Σ))
        for images in product(Q,repeat=len(Δl))
        for Δ in [ [ (p,a,q) for ((p,a),q) in zip(Δl, images) ] ]
        for I in powerset(Q, 1)
        for F in powerset(Q, 1)
    )

Adrien_non_unique_minimal = NFA.spec("""
    0 1 
    1 2
    0 # 0 a 1 b 2
    1 b 2
    2 a 1
    """, "Adrien non unique minimal")

def Adrien_normal_counterexample():
    # NFA.NOVISU = 1
    NFA.VISULANG = 10
    A = Adrien_non_unique_minimal.visu()
    A.mini().visu()

    B = A.copy().named("Adrien normal counterexample"); B.I = {0,2}
    B.visu().mini().visu()

    assert A==B

    # A= (NFA.of_word("a")| NFA.of_word("b")).visu()
    # A = NFA.spec("0 1\n0\n0 a 1\n1 b 0").visu()
    # A = NFA.universal("a").visu()
    # A = NFA.spec("0\n1\n0 a 0 b 1\n1 b 1 b 0").visu() # NFA
    num, Cs = enum_mida(2, A.Σ)

    # NFA.NOVISU = 1
    pos = 0
    for k,C in enumerate(Cs, 1):
        # if k < 0: continue # start at specific number
        if not k % 10**3: print(f"{k:.2E}   {100*k/num:.1f}%    {k}\r", end="")
        if C == A:
            pos += 1
            print(C.named(k).visu())
            # break
    print(k, "tested of", num, ", of which positives:", pos)


def time_prof(A:NFA):
    """temporal (past/future) profile:
    dicts q -> past , q -> future"""
    return { q : A.past(q).mini() for q in A.Q }, { q : A.future(q).mini() for q in A.Q }

def past_breaking(A,n=2):
    """minDFA -> min MIDA if separable"""
    A.visu()
    init = peek(A.I)
    past = A.past(init).mini().renum().named("past").visu()
    def open(A, Fs) -> NFA: # set additional states to final
        A = A.copy(); A.F |= Fs
        return A.mini().named(Fs)
    for basis in powerfset(past.Q-past.F, 1):
        for part in map(list,partitions(basis, n)):
            group = [ open(past,F) for F in part ]
            if sum( B.size for B in group ) < past.size:
                print(part)
                NFA.Union(group).named(f"{A.name} : {part}").visu()



def do_past_future_analysis():
    A = (modulo(K := 2) | modulo(L := 3)).dfa().renum().named("A")#.visu()
    # time_prof(A)
    # NFA.NOVISU = 1
    U = nTwo | nThree
    UM = U.visu().dfa().visu() # is mini
    p,f = time_prof(UM)
    pp,ff = time_prof(U)
    p.update(pp); f.update(ff)
    for Q in UM.Q:
        assert p[Q] == NFA.Inter(p[q] for q in Q)
        assert f[Q] == NFA.Union(f[q] for q in Q)
    # NFA.NOVISU = 0

    past_breaking(A)

def adrien_big_counter():
    def cycle(a,n):
        return [ (f"{a}{i}", "#", f"{a}{(i+1)%n}") for i in range(n) ]
    A = NFA.spec("""
    0 c0
    a0 b0 b2
    c0 c a2
    0 a a0 c a0
    0 b b0
    """, "Big counter")
    k=4
    A.add_rules(cycle("a", 2*k) + cycle("b", 3*k))
    return A


def search_covers(A0, n, ok=1, sz=1000):
    NFA.visutext(title := f"{A0.name}, {n}"+("" if ok else "<br/>COUNTEREX"))
    A0.visu()
    assert A0.is_det(ignore_inits=1)  # input is known MIDA
    A = A0.mini().renum().visu()

    NFB = A.reverse().dfa().renum().reverse().named("BRNF I")
    NFR = A.reverse().named("REVERSE F")

    def cutI(Is) -> NFA:
        A = NFB.copy(); A.I = Is
        return A.mini().named(f"I{Is}")

    def cutF(Is) -> NFA:
        A = NFR.copy(); A.I = Is
        return A.reverse().mini().named(f"F{Is}")

    NFR.cut = cutF ; NFB.cut = cutI

    NFs = [NF.visu() for NF in [NFR, NFB] if len(NF.I) <= 6]


    def MIDA(NF,cover): return NFA.Union(map(NF.cut, cover)).trans_det_Moore()
    minA = min( (MIDA(NF,c) for NF in NFs for c in covers(NF.I, n)),
                key=lambda A:len(A.Q)).visu()

    assert minA == A and minA.is_det(show=1, ignore_inits=1)
    if ok: assert len(minA.Q) == min(len(A0.Q), sz), title
    return minA


def Adrien_go_wok(N):
    def wok(k):
        def p(n): return f"{k}p{n}" if n<N else q(0)
        def q(n): return f"{k}q{n}"
        return NFA(
            [p(0)],
            [ q(i) for i in range(2**k, 2**(k+1)) ],#+[q(0)],
            { (p(j), 1, p(j+1)) for j in range(N) }
            |
            {(p(j), 0, p(j + 1)) for j in range(N) if j != k }
            |
            {(q(j), "#", q((j + 1) % 2**(k+1))) for j in range(2**(k+1))}
        )
    return NFA.Union( wok(k) for k in range(N) ).named(f"woks {N}")





def do_search_covers():
    # NFA.NOVISU = 1
    search_covers((modulo(K := 2) | modulo(L := 3)).renum().named("A"), 2)
    search_covers( ("#"+modulo(K := 2) | "#"+modulo(L := 3) ).rm_eps().trim().renum().named("A broken"),2)
    # return
    search_covers(uniquelast("abc", 1).named("B"), 3)
    search_covers(C := NFA.union(*(a_in_nth_pos(i) for i in [1, 2, 3])).named("C"), 6, sz=4) # overkill on 3
    search_covers(C, 2, sz=5)
    search_covers(Adrien_non_unique_minimal, 3)
    search_covers(Adrien_non_unique_minimal, 2)
    search_covers(bonfante_permut(2), 2)
    search_covers(adrien_periods(3), 3)
    search_covers(adrien_big_counter(), 2, ok=0)
    search_covers(Adrien_go_wok(3), 3, ok=0)


############################
# NFA.NOVISU = True

# do_permut(8)
# do_bonfante_permut(3)
# do_unique_last()
# do_nth_pos()
# do_adrien(3)
# do_modulo()
# do_modulo_break()
# Adrien_normal_counterexample()
# do_past_future_analysis()
do_search_covers()

# search_covers(Adrien_go_wok(3), 3)

# TODO: extend covers to step 0, 1, 2... residuals? FINALS L1.L2
# VH: besides, use minimisation more sparsely
# AB: exemple small NFA big MIDA (2hand VH)
# AB: ajouter exemple wok vide
# justif union finie de politiques deterministes
