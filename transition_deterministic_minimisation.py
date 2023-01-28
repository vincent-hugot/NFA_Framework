from nfa import *

NFA.VISULANG=0

def a_in_nth_pos(n,a="a",al="ab"):
    return NFA({0}, {n},
               { (p,a,p+1) for p in range(n-1) for a in al } | { (n-1,a,n) },
               name=f"[{al}]*{n-1} {a}"
               )


def uniquelast(al, n):
    """the last n letters are unique in word"""
    return NFA({f"{a}0" for a in al},
               {f"{a}{n}" for a in al },
               { (f"{a}0", b ,  f"{a}0")
                    for a in al
                    for b in set(al) - {a} } |
               { (f"{a}{k}", a ,  f"{a}{k+1}")
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
    B = modulo(3) | modulo(5)

    B.visu().mini().visu().tdBrzozowski().visu()
    B.tdBrzozowski().visu()
    B.reverse().dfa().reverse().visu()

def do_nth_pos():
    NFA.visutext("Brz works")
    C = NFA.union(*(a_in_nth_pos(i) for i in [1, 2, 3])).visu()

    C.mini().visu().tdBrzozowski().visu()
    C.trans_det_Moore().visu()
    C.tdBrzozowski().visu()

    NFA.visutext("Brz doesn't work")
    D = a_in_nth_pos(2,"c", "abc") | a_in_nth_pos(2,"b", "abc") | a_in_nth_pos(3,"a", "abc")
    D.visu().mini().visu()
    D.trans_det_Moore().visu()



def permut(N):
    return NFA({n for n in range(N) if not n%2}, {0}, {
        (n, "a", n+1) for n in range(N-1)
    } | { (N-1, "a", 0) }, name=f"permut {N}")

def cycle(a,*l):
    l = l + (l[0],)
    return { (p,a,q) for p,q in zip(l,l[1:]) }


def do_permut():
    # NFA.VISULAYOUT="circo"
    P = permut(8)
    P.add_rules(
        cycle("b", 0,2,4) | cycle("b", 6,1,3,5) | cycle("b", 7)
    )

    P.visu(layout="circo")
    PD = P.dfa().visu()

    targets = powerfset(P.Q, 4, 4)
    print(len(targets), "targets")
    print("missing:", targets - PD.Q)
    PD.mini().visu()




do_unique_last()
do_modulo()
do_nth_pos()
do_permut()