from nfa import *

NFA.VISULANG=0
# NFA.NOVISU = True

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

    PD.mini().visu()
    return len(m)




############################
NFA.NOVISU = True

# do_unique_last()
# do_modulo()
# do_nth_pos()
for N in range(4, 200, 2):
    assert not do_permut(N)



# Adrien example explosion:
# Salut. Je sais que tu es en pleine prépa de slides donc considère ce message comme un changement d'idée OPTIONNEL ET NON URGENT orienté automates.
#Pour un exemple le plus simple possible de l'explosion exponentielle des automates à entrées multiples, je trouve ceci:
#l'ensemble des préfixes non n périodiques, c'est à dire les mots u tels qu'il existe k pour lequel la k et n+k ieme lettres sont différentes.
#C'est facile de faire un DFA qui teste ça pour tout k congru à i modulo n et ça ne nécessite que 3n états.
#C'est facile de combiner ces gadgets en un seul MEDA de taille 3n qui reconnaît notre langage.
#Le DFA minimal pour ce langage doit garder en mémoire les n dernières lettres lues. C'est nécessairement exponentiel. 
