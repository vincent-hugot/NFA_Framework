
# Copyright 2019,  Vincent Hugot <vincent.hugot@insa-cvl.fr>
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


from toolkit import *
from collections import defaultdict
import html


# TODO: meta decorator to choose what to preserve, using setattr
def preserve(m):
    """
    Decorator: preverse annex properties:
    worder
    :param m:
    :return:
    """
    def f(s,*p,**k):
        worder = s.worder
        _grow_step = s._grow_step
        res = m(s,*p,**k)
        res.worder = worder
        res._grow_step = _grow_step
        return res
    return f

class NFA:

    VISUPDF = "visu"    # name of default visualisation file
    VISULANG = 10       # default visualisation: how many language elements; zero to deactivate
    VISUSIZE = True     # default visualisation of automaton's size
    VISU_INITIAL_ARROW = True   # True for initial arrow, else special style
    VISURANKDIR="LR"    # dot parameter rankdir for graph direction / TB
    VISUFACTORISE = True     # factorise multiple transitions
    VISUDOUBLEARROWS = False # use <-a-> for -a-> <-a- ?
    NOVISU = False      # globally deactivate visualisation; for profiling etc
    LARGE_RENDERER = "sfdp" # alternative graph renderer for large graphs
    LARGE_RENDERER_OPTIONS = ["-Goverlap=false"]  # additional graph renderer options
    LARGE = 800        # a NFA is considered large when it reaches this size

    def __init__(s,I=(),F=(),Δ=(),name="",Q=set(),trimmed=False,worder=str):
        """
        :return: New NFA
        :param I: initial states
        :param F: final states
        :param Δ: rules (p,a,q)
        :param Q: additional states (if not in rules)
        :param name: what's its name?
        :param trimmed: is it already trimmed? (avoid redoing it)
        :param worder: type of the words of the language. str / tuple
        """
        s.Δ = set()
        s.Σ = set()
        s._I, s._F = set(I), set(F)
        s.Q = s._I | s._F | Q # if you need useless states, with no associated rules
        s.add_rules(Δ)
        s._trimmed = trimmed
        s.name=name
        s.worder=worder
        s._grow_step = None # for step by step constuctions

    @property
    def F(s): return s._F

    @F.setter
    def F(s, F): s.Q |= F; s._F = F

    @property
    def I(s): return s._I

    @I.setter
    def I(s, I): s.Q |= I; s._I = I

    def add_rule(s,p,a,q,final=False):
        s.Δ.add((p,a,q))
        s.Σ.add(a)
        s.Q |= {p,q}
        if final: s.F.add(q)
        return s

    def try_rule(s,p,a,q,final=False):
        """add if this is new and report if you did something"""
        if (p,a,q) in s.Δ: return False
        s.add_rule(p,a,q,final)
        return True

    def add_rules(s,Δ,final=False):
        for r in Δ: s.add_rule(*r,final=final)
        return s



    def trans_2(s):
        """get dict (p,a) -> set of q : delta total function"""
        look = { (p,a) : set() for p in s.Q for a in s.Σ }
        # look = defaultdict(lambda : set()) # breaks complete !
        for (p,a,q) in s.Δ:
            look[p,a] = look[p,a] | {q}
        return look

    def trans_2d(s):
        """deterministic case; partial"""
        return { (p,a) : q for (p,a,q) in s.Δ }

    def trans_1(s):
        """get dict p -> set of (a,q)"""
        look = {}
        for (p,a,q) in s.Δ:
            look[p] = look.get(p,set()) | {(a,q)}
        return look

    def trans_pq(s):
        """get dict p,q -> set of symbs linking them"""
        d = defaultdict(lambda : set())
        for p,a,q in s.Δ: d[(p,q)].add(a)
        return d

    def lang(s):
        """generator of all words in language; small length first;
        unspecified order otherwise
        Will always terminate if finite language !
        supports epsilon and general word transitions; will break length ordering
        :param worder: constructor for output type
        """
        s = s.renum(smart=False).trim() # always a good idea for performance
        runs = { (s.worder(), q) for q in s.I }
        look = s.trans_1()
        safety = 0 # count unproductive loops to avoid infinites if empty lang
        while True:
            acc = { w for (w,p) in runs
                    if p in s.F }
            for w in acc: yield w; safety = 0 # loop has been productive
            runs = { (w+str(a) if s.worder is str else w+(a,) , q)
                     for (w,p) in runs
                     for (a,q) in look.get(p,()) }
            safety += 1
            if safety > len(s.Q): break

    # iterable: over the language
    def __iter__(s):
        return s.lang()

    def lang_up_to_len(s,n):
        for w in s.lang():
            if len(w) > n: break
            yield w

    # test whether langage is finite; pumping lemma
    def is_finite(s):
        for w in s.lang():
            if len(w) >= len(s.Q): return False
        return True

    @preserve
    def __matmul__(s,o):
        """ shuffle product;
        should support epsilons"""
        return NFA(
            { (i,j) for i in s.I for j in o.I },
            { (i,j) for i in s.F for j in o.F },
            { ((p,r), a, (q,r)) for (p,a,q) in s.Δ for r in o.Q }
            |
            { ((r,p), a, (r,q)) for (p,a,q) in o.Δ for r in s.Q },
            name=f"({s.name} ∥ {o.name})"
        )

    @staticmethod
    def disjoint(os):
        """Make automata states disjoint if need be
        :param os: list of automata"""
        if len(os) <= 1: return os
        couples = ( (os[i],os[j]) for i in range(len(os)-1) for j in range(i+1,len(os)) )
        if any( A.Q & B.Q for A,B in couples ):
            return [s.map(lambda q: (k, q)) for k, s in enumerate(os)]
        return os


    def concatenate(*os):
        """Concatenate automata / languages"""
        os = NFA.disjoint(os)
        res = NFA(
            os[0].I,
            os[-1].F,
            set.union(*(s.Δ for s in os)),
            name="("+" + ".join(s.name or "None" for s in os) +")",
            trimmed=all(A._trimmed for A in os)
        )
        for A,B in pairwise(os):
            res.add_rules( { (p,'',q) for p in A.F for q in B.I } )
        return res


    @preserve
    def __add__(s,o):
        """
        Concatenate
        :param o: other automaton
        """
        return s.concatenate(o)

    def __mul__(s, n:int):
        """
        Repeat
        :param n:
        :return: automaton concatenated to itself
        """
        if n < 0: raise ValueError
        if n == 0: return NFA((), (), (), name=f"{s.name} * 0")
        if n == 1: return s
        return (s + (s * (n - 1))).named(f"{s.name} * {n}")



    @staticmethod
    def shuffle(u,v,aut=False):
        """word shuffle"""
        u,v = ( NFA.of_word(w) for w in (u,v) )
        return u @ v if aut else set( u @ v )

    def __and__(s,o):
        """fully synchronised product: language intersection"""
        if not all( s.Σ ): s = s.rm_eps()
        if not all( o.Σ ): o = o.rm_eps()
        return NFA(
            { (i,j) for i in s.I for j in o.I },
            { (i,j) for i in s.F for j in o.F },
            { ((p,P), a, (q,Q))
              for (p,a,q) in s.Δ for (P,b,Q) in o.Δ if a == b },
            name=f"({s.name} ∩ {o.name})")

    class StayC:
        def __repr__(s): return "_"
        def __lt__(s,o): return True
        def __gt__(s, o): return False
    Stay = StayC() # special static  stay operation symbol

    def _sprod2_brutal(s, o, svec, _=Stay, silent=()):
        assert all(len(v) == 2 for v in svec), len(svec.pop())
        return NFA(
            {(i, j) for i in s.I for j in o.I},
            {(i, j) for i in s.F for j in o.F},
            {((p, P), (a,b), (q, Q)) for (p, a, q) in s.Δ for (P, b, Q) in o.Δ if (a,b) in svec}
            |
            {((p, r), (a, _), (q, r)) for (p, a, q) in s.Δ for r in o.Q if a in silent or (a, _) in svec}
            |
            {((r, p), (_, a), (r, q)) for (p, a, q) in o.Δ for r in s.Q if a in silent or (_, a) in svec}
            |
            ( {((R, r), (_, _), (R, r)) for R in s.Q for r in o.Q} if (_,_) in svec else set() )
            ,
            name=f"({s.name} ⨉b {o.name})",
            worder=tuple
        )

    @staticmethod
    def sprod_brutal(*As, svec, _=Stay, silent=()):
        """as sprod, but performs product brutally"""
        assert all( len(v) == len(As) for v in svec ), (len(svec.pop()),len(As))
        l = As
        R,*As = As
        i=1
        while As:
            A,*As = As
            i += 1
            R = R._sprod2_brutal(A, svec and {tuplepart(t, i) for t in svec}, _, silent).map(flattupleL, flattupleL)
        return R.named("(" + " ⨉b ".join(s.name or "None" for s in l) + ")")

    @staticmethod
    def sprod(*As, svec,
              _=Stay,
              silent=(),
              record_steps=False,
              stopper=None,
              filter=lambda A,P,v,Q:True,
              hook = lambda A: None
              ):
        """ DEPRECATED
        :param hook: called on current version of automaton at each step
        :param filter: rulefilter(A,P,v,Q) predicate on automaton and rule, filtering
            what rules / states are added (in batch)
        :param stopper: predicate on automaton: stop when some condition is reached
        :param record_steps: for growtofixpoint/visusteps
        :param _: stay operation symbol
        :param svec: synchronisation vectors set
        :param silent: silent transitions can occur in one system regardless of synchro.
            Equivalent to adding ____a__ vectors
        :return: synchonised product along vectors; on-the-fly, starting from initial
            states
        """
        assert all( len(err := v) == len(As) for v in svec ), (err,len(As))
        assert all ( a == _ or a in A.Σ or (err := (a,A.name)) and False
                     for v in svec for a,A in zip(v,As) ), err


        I = set(product(*(A.I for A in As)))
        tr = [A.trans_2() for A in As]

        for a in silent:
            svec |= NFA.shuffle([_]*(len(As)-1),[a])

        def grow(A : NFA):
            newrules= set()
            for v in svec:
                for P in A.Q: # P
                    # print(f"{v=} {P=}")
                    Qs = set(product( *( [p] if a == _ else t.get((p,a),[])
                                         for p,a,t in zip(P,v,tr) ) ) )
                    # print(Qs)
                    newrules |= {(P,v,Q) for Q in Qs if filter(A, P, v, Q)} - A.Δ
            if not newrules:
                A.F = { Q for Q in A.Q if all( q in B.F for q,B in zip(Q,As) ) }
            else: A.add_rules(newrules)
            # print(repr(A.visu()))
            hook(A)
            if stopper and stopper(A): return False
            return newrules
        R = NFA(I, (), (),worder=tuple).growtofixpoint(grow,record_steps)
        return R.named("(" + " ⨉ ".join(A.name or "None" for A in As) + ")")

    @staticmethod
    def nsprod_interf(*As, svec, _=Stay, pretty_trans=False, pretty_states=False, pretty=None, filter=lambda P, v, Q:True, **kw):
        """DEPRECATED. Named synchronised product. INTERFACE VERSION
        Same as sprod, but with a more convenient interface:
        svec of the form [{component_name: transition, ...},...]"""
        vd = { tuple( d[n] if (n:=A.name) in d else _  for A in As ) : tuple(d.items())
               for d in svec }

        def toass(v): return tuple((c.name, x) for c, x in zip(As, v))

        def filterv(A,P,v,Q):
            return filter(dict(toass(P)), dict(toass(v)), dict(toass(Q)))

        R = NFA.sprod(*As,svec=set(vd),_=_,**kw)

        if pretty: pretty_trans = pretty_states = pretty

        if pretty_states is False: R = R.map(f=toass)
        if pretty_trans is False: R = R.map(g=toass)

        if pretty_states is True:
            def ps(x):return f"{', '.join([f'{cn}:{a}' for cn,a in toass(x)])}"
            R = R.map(f=ps)

        if pretty_trans is True :
            def pt(x): return f"{', '.join([f'{cn}:{a}' for cn,a in vd[x]])}"
            R = R.map(g=pt)


        return R.named("(" + " ⨉ ".join(A.name or "None" for A in As) + ")")

    @staticmethod
    def nsprod(*C, sds,
              silent=set(),
              record_steps=False,
              stopper=None,
              filter=lambda A, P, v, Q: True,
              hook=lambda A: None,
              nice=False,
              # disable
              ):
        """ Named synchronised product of systems, along synchronisation dictionaries set
          [{component_name: transition, ...},...]
        :param sds: synchronisation dictionaries list
        :param filter: rulefilter(A,P,v,Q) predicate on automaton and rule, filtering
            what rules / states are added (in batch).
            States are tuple of couples, since dict is not hashable.
        :param record_steps: for growtofixpoint/visusteps
        :param stopper: predicate on automaton: stop when some condition is reached
        :param hook: called on current version of automaton at each step
        :param silent: silent transitions can occur in any one system regardless of synchro.
            equivalent to adding all {c:a} to sds
        :param nice: call dnice at the end for nicer visualisation.
        :return: synchonised product along vectors; on-the-fly, starting from initial
            states"""
        C = { c.name : c for c in C }
        for d in sds:
            for c in d: assert d[c] in C[c].Σ, (c,d)

        I = { tuple( (c,q) for c in C for q in C[c].I ) }

        assert all( silent <= c.Σ for c in C.values() )
        sds += [ {c:a} for c in C for a in silent ]

        T = { c : C[c].trans_2() for c in C }
        def grow(A : NFA):
            newrules= set()
            for d in sds:
                # print(f"for {d=} in sds")
                dt = tuple( (c,d[c]) for c in C if c in d)
                for P in A.Q:
                    Pd = dict(P)
                    # print(f"for {Pd=} in A.Q:")
                    # print(f"{T[c]=} {P[c]=} {d[c]=}")
                    Qsd = { c:T[c][(Pd[c],d[c])] if c in d else {Pd[c]} for c in C }
                    # print(f"{Qsd=}")
                    Qs = set() if set() in Qsd.values() else { tuple( (c,a) for c in C for a in Qsd[c] ) }
                    # print(f"{Qs=}")

                    newrules |= {(P,dt,Q) for Q in Qs if filter(A, P, dt, Q)} - A.Δ
            if not newrules:
                A.F = { Q for Q in A.Q if all( q in C[c].F for c,q in Q ) }
            else:
                A.add_rules(newrules)
            # print(repr(A.visu()))
            hook(A)
            if stopper and stopper(A): return False
            return newrules
        R = NFA(I, (), (),worder=tuple).growtofixpoint(grow,record_steps)
        if nice:
            assert not record_steps, "Steps visualisation incompatible with dnice mapping"
            R = R.dnice()
        return R.named("(" + " ⨉ ".join(c or "None" for c in C) + ")")

    def dnice(s):
        """nicer states and transitions for dictionary-based product automata"""
        def nice(x): return f"{', '.join([f'{cn}:{a}' for cn, a in x])}"
        return  s.map(f=nice, g=nice)

    def label(s, l, f_str):
        bs = '\\'
        def disp(q):
            return f"{q}:{bs}n{f'{bs}n'.join(f_str(phi) for phi in l.get(q, ()))}"
        return s.map(f=lambda q:disp(q)).named(s.nop("λ"))


    @preserve
    def proj(s,al):
        """projected NFA on smaller alphabet"""
        return NFA(s.I,s.F,
                   { (p,a,q) if a in al else (p,'',q)
                     for (p,a,q) in s.Δ } ).rm_eps().trim().setnop('π',s.name)

    @preserve # depends on functions
    def map(s, f=lambda x:x, g=lambda x:x):
        """renames all states and symbols according to a function
        if f is not injective, might change language !
        :param f states fun
        :param g symbols fun
        """
        f = { x: f(x) for x in s.Q }.get
        g = { x: g(x) for (_,x,_) in s.Δ }.get

        return NFA(
            {f(q) for q in s.I},
            {f(q) for q in s.F},
            {(f(p), g(a), f(q)) for (p,a,q) in s.Δ },
            Q={f(q) for q in s.Q},
            name=s.nop('↦'))

    def stringify(s,f=str,g=str):
        """when states contain sets, string rep may vary from moment to moment
        fix a single string representation"""
        f = {p : f(p) for p in s.Q}
        g = {a : g(a) for a in s.Σ}
        return s.map(lambda x:f[x],lambda x:g[x])

    def setworder(s,w):
        s.worder = w
        return s

    # preserve not usable due to variant return type
    def renum(s,n=0,smart=True,getiso=False,getboth=False):
        assert not (getiso and getboth)
        """change complicated states to n, n+1,,..
        smart renumber: in order of accessibility
        if getiso get the dict isomorphism instead
        if ghetboth get AUT, iso"""
        if not smart:
            f = dict(zip(s.Q,range(n,n+len(s.Q))))
        else:
            d = s.trans_1() ; f = {}
            acc = { p : { q for _,q in d.get(p,()) } for p in s.Q }
            g = iter(range(n,n+len(s.Q)))
            def up(new):
                newf = { e : next(g) for e in new - set(f) }
                if not newf: return False
                f.update(newf); return True
            up(s.I)
            while up( set().union(*(acc[p] for p in f)) ):
                pass
            up(s.Q - set(f))
        if getiso: return f
        S = s.map(lambda x: f[x]).setnop('ℕ', name=s.name).setworder(s.worder)
        if getboth: return S, f
        return S


    # language union
    def __or__(s,o): return NFA.union(s,o)

    def union(*os):
        """Union of arguments"""
        if not os: return NFA(set(), set(), set())
        os = NFA.disjoint(os)
        return NFA(
            set.union(*(s.I for s in os)),
            set.union(*(s.F for s in os)),
            set.union(*(s.Δ for s in os)),
            name="("+" ∪ ".join(s.name or "None" for s in os) +")",
            trimmed=all(A._trimmed for A in os)
        )

    @staticmethod
    def Union(it):
        """Union of iterators"""
        return NFA.union(*it)

    def __contains__(s,w):
        """language membership test"""
        return s(w) & s.F

    def run(s,w,*p,**k):
        """visualise a run on w; params as visu"""
        dmod={} ; e = s.I ; u = s.worder()
        for a in w+'Δ' if s.worder is str else w+('Δ',) : # final end-of-word unlikely symbol
            dmod.update({ q: 'color="#BB0000" fillcolor="#BB0000" penwidth=2 fontcolor=white' for q in e })
            s.visu(dmod=dmod, comment="/R:"+str(u),*p,**k)
            u += a if s.worder is str else (a,)
            dmod = { k: # formerly used states and transitions
                         'color="#AA0000" fillcolor="#CC9999"'
                         if k in s.Q else
                         'color="#AA0000" fontcolor="#BB0000"'
                     for (k,v) in dmod.items()  }
            dmod.update({ (p,b,q):
                              'color="#BB0000" penwidth=1.2 fontcolor="#BB0000"'
                          for p,b,q in s.Δ if p in e and b == a  })
            e = { q for p,b,q in s.Δ if p in e and b == a }
        return s



    # returns epsilon-free version of automaton
    def rm_eps(s):
        look = s.trans_2()
        def clos(p):
            s = {p}
            while True:
                ss = s | set().union(*(look.get((q,''),set()) for q in s))
                if s == ss : return s
                s = ss
        def closs(s): return set().union(*( clos(p) for p in s ))
        return NFA(closs(s.I), s.F,
                   { (p,a,q)
                     for p,a in look if a != ''
                     for q in closs(look[p,a]) },name=s.nop('ε') )


    def __call__(s,w,Q=None):
        """
        returns exact states accessed by reading word from starting states
        :param w: the word
        :param Q:stating states: default: from initials
        """
        assert all(a for a in s.Σ)
        e = s.I if Q is None else Q
        for a in w:
            e = {q for p, b, q in s.Δ if p in e and b == a}
        return e

    def accessibles(s):
        """return set of accessible states"""
        d = s.trans_1()
        acc = { p : { q for _,q in d.get(p,()) } for p in s.Q }
        x = s.I # accessibles
        while True:
            xx = x | set().union(*(acc[p] for p in x))
            if xx == x: break
            x = xx
        return x

    def reverse(s):
        return NFA(s.F, s.I, { (q,a,p) for p,a,q in s.Δ } )

    def coaccessibles(s):
        return s.reverse().accessibles()

    # brutally remove all states not in S
    def only(s,S,trimmed=False):
        return NFA(s.I & S, s.F & S,
                   { (p,a,q) for p,a,q in s.Δ if {p,q} <= S},
                   Q=s.Q & S, trimmed=trimmed, name=s.nop('t' if trimmed else 'only') )

    def nop(s,o):
        """
        name after operation
        :param o: letter or string for operation type
        :return: new name with suffix indication operation history

        for internal use
        """
        return s.name + f" /{o}"

    @preserve
    def setnop(s,o=None,name=None):
        """
        Set name with additional operation.
        Used to bypass large chains of op chars
        :param o: op char
        :param name: if defined, overrides real name
        :return: self
        """
        name = name if name else s.name
        if name:
            s.name = name
            if o: s.name = s.nop(o)
        return s

    @preserve
    def named(s, name):
        s.name = name
        return s

    @preserve
    def trim(s):
        if s._trimmed: return s.copy()
        use = s.accessibles() & s.coaccessibles()
        return s.only(use,trimmed=True)

    @staticmethod
    def of_word(w):
        """return a NFA (DFA) accepting a single word"""
        n = len(w)
        return NFA({0}, {n}, { (k,w[k],k+1)
                               for k in range(n) },
                   name = "/W:" + str(w)[:10],
                   trimmed=True,
                   worder=str if type(w) is str else tuple)

    @staticmethod
    def of_length(n,Σ):
        return NFA({0}, {n}, {(k, a, k + 1)
                        for k in range(n) for a in Σ},
                   name=f"/{Σ}^{n}:",
                   trimmed=True)

    @staticmethod
    def of_length_range(n,m,Σ):
        A = NFA.of_length(m,Σ)
        A.F = set(range(n,m+1))
        return A.named(f"/{Σ}^[{n},{m}]:")

    def extend(s,Σ):
        """concatenate language with Σ^*"""
        S = s.copy()
        S.add_rules({(p, a, p) for p in S.F for a in Σ})
        return S.setnop('e')

    @staticmethod
    def of_set(L,name=None):
        """return a NFA accepting exact finite langage"""
        return NFA.Union(NFA.of_word(w) for w in L).setnop(name=name or "/OfSet")

    @preserve
    def copy(s): return NFA(s.I, s.F, s.Δ, Q=s.Q, trimmed=s._trimmed, name=s.name)

    @preserve
    def dfa(s,pdf=None):
        """return equivalent DFA; no epsilons need apply
        if pdf is specified, generate step by step slides"""
        if pdf: return s.dfa_pdf(pdf) # delegate visualisation
        if not all( a != "" for a in s.Σ ): s = s.rm_eps().setnop('d')
        if s.is_det(): return s.copy()
        l = s.trans_2()
        do, done, rlz  = { fset(s.I) }, set(), set()
        while do:
            P = do.pop(); done.add(P)
            for a in s.Σ:
                Q = fset(set().union(*(l[p,a] for p in P)))
                if not Q: continue # useless: not coaccessible
                rlz.add( (P,a,Q) )
                if Q not in done: do.add(Q)
        return NFA({ fset(s.I) },
                   { P for P in done if s.F & P },
                   rlz, name=s.nop('d'))

    @preserve
    def dfa_pdf(s,pdf=None):
        s.visu(pdfname=pdf, test=False,print_extra="dfa_pdf: INIT: ")
        res = s.dfa()
        d= {k:"style=invis" for k in res.Q | res.Δ }
        l = s.trans_2()
        do, done, rlz = {fset(s.I)}, set(), set()
        while do:
            P = do.pop(); done.add(P)
            for q in done: d.pop(q,None)
            d[P] = 'color="#BB0000" fillcolor="#BB0000" penwidth=2 fontcolor=white'
            d.update({q: 'color="#AA0000" fillcolor="#CC9999"' for q in do})
            res.visu(pdfname=pdf, test=False, dmod=d,print_extra=f"dfa_pdf: {P}")
            for a in s.Σ:
                Q = fset(set().union(*(l[p, a] for p in P)))
                if not Q: continue  # useless: not coaccessible
                rlz.add((P, a, Q))
                del d[(P,a,Q)]
                if Q not in done: do.add(Q)
        res.visu(pdfname=pdf, test=False,print_extra="dfa_pdf: END: ")
        return res

    def visusteps(s, dsteps=None,print_current=True,*p,**kw):
        """Visualise several steps through progressive reveal.
        Same API as visu()
        :param dsteps: dict state/trans -> step index;
            by default uses that produced by .growtofixpoint()
        """
        if print_current: print(f"{erase_line}{term_visu_style}Visusteps: {repr(s)}{term_reset}", end="")

        if dsteps is None: dsteps = s._grow_step
        d = {k: "style=invis" for k in s.Q | s.Δ}
        n = min(dsteps.values()) ; N = max(dsteps.values())
        for k in range(n,N+1):
            if print_current: print(f"{erase_line}{term_visu_style}Visusteps {k}/{N}: {repr(s)}{term_reset}\r", end="")
            d.update({ x : 'color="#BB0000" fillcolor="#BB0000" penwidth=2 fontcolor=white'
                       for x in dsteps if dsteps[x]==k and x in s.Q } )
            d.update({x: 'color="#BB0000" fillcolor="#BB0000" penwidth=2 fontcolor="#BB0000"'
                      for x in dsteps if dsteps[x] == k and x in s.Δ})
            d.update({x: 'color="#BB4455" fillcolor="#FFF5FF" penwidth=2'
                      for x in dsteps if dsteps[x] == k-1 and x in s.Q })

            # print(d.keys() - dsteps.keys())
            for x in tuple(d):
                if x in dsteps:
                    if dsteps[x] < k - 1 or dsteps[x] == k - 1 and x in s.Δ : del d[x]

            # bugs with double arrows, and is not meaningful because
            # back arrow not reached at same time as direct arrow.
            s.visu(dmod=d,*p,doublearrows=False,print_current=False,**kw)
        if print_current: print(erase_line, end="")
        return s.visu(*p,**kw)



    def is_det(s,show=False):
        """ is it deterministic ?
        :param show: display nondeterministic aspects of automaton"""
        def p(*x):
            if show: print(*x)
        if len(s.I) > 1: p("Init",s.I); return False
        for k,v in s.trans_2().items():
            if len(v) > 1: p(*k, "->",v); return False
        return True

    @preserve
    def complete(s,Σ=set()):
        """return complete version (sink state)
        :param Σ: complete over symbols not appearing in automaton
        """
        Σ = (Σ if type(Σ) is set else set(Σ)) | s.Σ

        sink = 0
        l = s.trans_2()
        if all( l.values() ) and Σ <= s.Σ : return s.copy()
        while sink in s.Q: sink += 1
        return NFA(s.I, s.F,
                   s.Δ
                   | {(sink,a,sink) for a in Σ}
                   | { (p,a,sink)
                        for p in s.Q for a in Σ
                        if not l.get((p,a), None)
                       },
                   name=s.nop('c') )

    @preserve
    def __neg__(s):
        """language complementation"""
        on = s.name
        s = s.dfa().complete()
        return NFA(s.I, s.Q - s.F, s.Δ, name=f"{on} /-")

    def repr(s,N=20):
        L = list(s[:N + 1]); L.sort()
        n = len(L) if len(L) < N else f"{N}+"
        return f"{s}L {n:<3} {sortstr(L)}"

    def __repr__(s):
        return f"<NFA {s.name} #{s.size} Σ{len(s.Σ)} Q{len(s.Q)} I{len(s.I)} F{len(s.F)} Δ{len(s.Δ)}>"\
               f"{':Trim' if s._trimmed else ''}"


    def test(s, N=50):
        print(s.repr(N)); return s

    def __str__(s):
        return (f"NFA {s.name}:" if s.name else "")+ \
               f"  ## = {s.size}\n"\
               f"Σ {len(s.Σ):<3} {sortstr(s.Σ)}\n"\
               f"Q {len(s.Q):<3} {sortstr(s.Q)}\n"\
               f"I {len(s.I):<3} {sortstr(s.I)}\n"\
               f"F {len(s.F):<3} {sortstr(s.F)}\n"\
               f"Δ {len(s.Δ):<3} {sortstr(s.Δ)}"

    def universal(al):
        """universal automaton on alphabet"""
        assert al
        return NFA({0},{0}, { (0,a,0) for a in al },
                   name="/U:" + (r:=repr(al))[:20] + ("..." if len(r)>20 else ""),
                   trimmed=True )

    @preserve
    def __sub__(s,o):
        """language difference"""
        sc,oc = s.complete(s.Σ|o.Σ), o.complete(s.Σ|o.Σ)
        return (sc & (-oc)).setnop(name=f"({s.name} ∖ {o.name})")

    def __getitem__( s, i ) :
        """language pseudo-indexing and slicing ; terms may be repeated"""
        if isinstance( i, int ) :
            g = iter(s)
            for _ in range(i): next(g)
            return next(g)
        elif isinstance( i, slice ) :
            return islice(s.lang(),i.start,i.stop,i.step)
        else:
            raise (TypeError, "Invalid argument type.")

    def is_empty(s):
        """test whether language is empty"""
        return not s.rm_eps().trim().Q

    def is_universal(s):
        """is universal on its *implicit* alphabet?"""
        return s.Σ and (-s).is_empty()

    # language inclusion
    def __le__(s,o): return (s - o).is_empty()

    def __eq__(s,o):
        """language equivalence: s <= o <= s"""
        return bool(s.mini().renum(smart=False).iso(o.mini().renum(smart=False)))

    def texvisu(s,*texargs,pdfname=None,pdfprepend=False,texout="__NFA__.tex",
                silent=True,print_current=True,renum=False,**texkwargs):
        """TeXperiment: visualise pdf of tex output; same arguments as tex
        :param renum: renum states and use mapping -- use if complicated states
        :param print_current: as visu()
        :param texout: write tex figure to...
        :param silent: silence the output of LaTeX and pdfcrop processes
        :param pdfname: name of target visualisation pdf; as visu()
        :param pdfprepend: as visu()
        :return:
        """
        if NFA.NOVISU: return s
        if print_current:
            print(f"{erase_line}{term_visu_style}TeX Visu: {repr(s)}{term_reset}", end="")
        if renum:
            S, f = s.stringify().map(f=lambda q: q.replace("{", "\\{").replace("}", "\\}")).renum(getboth=True)
            f = {str(v): k for k, v in f.items()}
            S.texvisu(*texargs,qmap=f.get,**texkwargs)
            return s
        texc = s.tex(*texargs,**texkwargs)
        with open(texout,'w') as f: f.write(texc)
        pdfname = NFA.VISUPDF if not pdfname else pdfname
        do_tex(texc,pdfname,pdfprepend,silent)
        if print_current: print(erase_line, end="")
        return s

    def tex(self, qloc="",bends="",defbend='',defavoidbend="bend left=10",
            defloop='loop above',qmap=lambda x:x, params="",at=lambda x:None):
        """
        :param defloop: default loop stype
        :param defavoidbend: default p <-> q avoidance bending
        :param qloc: spacial relations between states; chains p REL q REL r
        :param bends: any number of p BEND q ; e.g. <, >, ~, >20; multiple BENDs can
            be separated w/ commas
        :param defbend: default bend / transition command
        :param params: global parameters of the picture
        :param at: node -> position. force absolute position through "at" keyword
        :param qmap: mapping for pretty-printing complex states; comes from renum in texvisu
        :return: TikZ code
        """
        i = "    "
        s = self.stringify()
        r = f"\\begin{{tikzpicture}}[fsa,mathnodes,{params}]\n"


        loc = {}
        order = []
        if qloc:
            cmds = {
                "/": "above right",
                "\\": "below right",
                "bl": "below left",
                ">": "right",
                "<": "left",
                "^": "above",
                "_": "below",
            }
            for li in qloc.splitlines():
                chain = li.split()
                while len(chain) > 1:
                    p, c, q, *rest = chain
                    loc[q] = f"{cmds[c]}=of {p}"
                    order += [p,q]
                    chain = chain[2:]
        elif len(s.Q) > 1: # default node locations: square
            order = list(s.I) + list(s.Q - s.F - s.I) + list(s.F - s.I)
            import math
            N = math.ceil(math.sqrt(len(order)))
            k = 0 ; o = iter(order)
            p = P = next(o)
            while True:
                k = (k + 1) % N
                q = next(o,None)
                if not q: break
                if k: loc[q] = f"right=of {p}"
                else:
                    loc[q] = f"below=of {P}"
                    P = q
                p = q


        order = [e for k, e in enumerate(order) if e not in order[:k]]

        for q in order + list(s.Q - set(order)):
            absl = f"at {p} " if (p := at(qmap(q))) else ""
            rell = loc.get(q,'')  if not p else "" # some tests depend on renum; should update to use qmap q if option
            r += f"{i}\\node[state,{'initial,' if q in s.I else ''}{'accepting,' if q in s.F else ''}]" \
                 f" ({q}) [{rell}] {absl}{{{qmap(q)}}};\n"

        cmds = {
            "<" : "bend left",
            ">" : "bend right",
            "~" : "swap",
            "-" : "",
            "ns": "near start",
            "NS": "very near start",
            "ne": "near end",
            "NE": "very near end",
            "c" : "inner sep = 0", # close
            "la": "loop above",
            "lb": "loop below",
        }
        b = defaultdict(lambda : "")
        for li in bends.splitlines():
            l = li.split()
            while l:
                p, B, q, *l = l
                for bend in B.split(","):
                    if bend[0] in ('<', '>'):
                        x, degrees = bend[0], bend[1:]
                        b[(p,q)] += f"{cmds[x]}{'='+degrees if degrees else ''},"
                    else:
                        b[(p, q)] += f"{cmds.get(bend,bend)},"


        r += f"  \\path [->]\n"
        tr = s.trans_pq()
        for (p,q),A in tr.items():
            r += f"{i}({p})  edge  [{defloop+',' if p==q else ''}" \
                 f"{b.get((p,q), defavoidbend if p!=q and (q,p) in tr else defbend)}]  " \
                 f"node {{{', '.join(sorted(map(str,A)))}}} ({q})\n"

        r += ";\n\\end{tikzpicture}"
        return r

    def visu(s,
             test=False,
             factor=None,
             lbltrans=lambda x:x,
             dmod={},
             pdfname=None,
             pdfprepend=False,
             comment="",
             nocomment=False,
             name=True,
             lang=None,
             rankdir=None,
             initarrow=True,
             size=None,
             doublearrows=None,
             break_strings=True,
             print_current=True,
             print_extra="",
             node_shape="circle",
             epsilon_style='label=ε color="#666666"',
             escape_name=True,
             ):
        """Thanks to dot, visualise the saggital diagram of the automaton.
        A pdf is generated and updated for each call, as well as a dot for the last call only
        factor : should multiple transitions p a q, p b q be represented
        as a single p a,b q arrow ?
        depends on external software: graphviz/dot and pdftk

        :param nocomment: do not print name / comment
        :param size: should size be displayed in default comment ?
        :param test: should test() be called as well ?
        :param factor: factorise multiple transitions
        :param doublearrows: factorise -> and <- on same label as <->
        :param lbltrans: apply transformation before writing state labels
            typical use: just remove everything for unlabelled nodes
        :param dmod: dict of special effects on states and transitions
        :param pdfname: name of target pdf, NFA.VISUPDF by default
        :param pdfprepend: prepend to pdf, or postpend
        :param comment: top left label for graph
        :param name: name as default comment?
        :param lang: how many elements of language to display?
        :param rankdir: LR or TB: direction of graphs; VISURANKDIR by default
        :param initarrow: use an arrow for initial state. Alternative: special style.
            Default is NFA.VISU_INITIAL_ARROW
        :param break_strings: should long strings be broken ?
        :param print_current: print current visualisation task on current output; is erased after completion.
            Potential problems on some displays.
        :param print_extra: extra info to add to visualisation task
        :param node_shape: basic node shape; "circle" by default
        :param epsilon_style: special style of epsilon transitions
        :param escape_name: HTML escape for automaton name
        :return: self"""

        if NFA.NOVISU: return s

        if print_current:
            print(f"{erase_line}{term_visu_style}Visu:{print_extra} {repr(s)}{term_reset}", end="")

        def breaker(e): # intelligent string breaker
            s = str(e)
            if len(s) < 15:  return s
            n = 5 + sqrt(len(s)) * 1.3
            ss, i, reps = "", 0, 0
            for j,a in enumerate(s):
                nn = n-3 if not reps and n >11 else n
                if j-i <= nn-3: continue
                if j-i > nn+3 or a== ' ' :
                    ss += s[i:j+(0 if a == ' ' else 1)] + "\\n"
                    reps += 1
                    i=j+1
            ss += s[i:]
            # assert len(ss) == len(s) + 2*reps , (s, "   ", ss)
            return ss

        if not break_strings: breaker = str

        if test: s.test()

        dmod2 = {}
        for k in dmod:
            if k in s.Q: dmod2[breaker(k)] = dmod[k]
            if k in s.Δ:
                dmod2[ tuple(map(breaker,k))] = dmod[k]
        dmod = dmod2
        original, s = s , s.stringify(f=breaker)

        factor = NFA.VISUFACTORISE if factor is None else factor
        if factor: # factorise multiple transitions
            symbs = {}
            for p,a,q in s.Δ:
                symbs[p,q] = symbs.get((p,q),[]) + [a]

            dmod2={}
            for k in set(dmod):
                if k in s.Δ:
                    p,a,q = k
                    if k in dmod: dmod2[(p,  breaker(", ".join(sorted(symbs[p,q])))  ,q)] = dmod[k]
                    for a in symbs[p,q]:
                        if (p,a,q) in dmod: del dmod[p,a,q]
            dmod.update(dmod2)

            s = NFA(s.I,s.F,
                    { (p,  breaker(", ".join(sorted(symbs[p,q])))  ,q)
                      for p,q in symbs})

        doublearrows = NFA.VISUDOUBLEARROWS if doublearrows is None else doublearrows
        if doublearrows:
            remove = set()
            for (p,a,q) in s.Δ:
                if p != q and (q,a,p) in s.Δ and (p,a,q) not in remove:
                    remove.add((q,a,p))
                    dmod[(q,a,p)] = " style=invis " + dmod.get((p, a, q), "")
                    dmod[(p,a,q)] = " dir=both " + dmod.get((p,a,q),"")
            # s.Δ = s.Δ - remove
            # invisibility instead of removing addresses dot's behaviour
            # wrt <->: it only counts as -> wrt rendering constraints;
            # thus dot's rendering ends up random and often very poor
            # invis drawback: <-> end up curved to avoid invisible edges

        dotc = """
            digraph AST {
            bgcolor="transparent";
            //ranksep=0;
            //nodesep=1;
            rankdir=%s;
            //ratio=compress
            size="8,5"
            edge [arrowhead=vee fontname = "palatino" arrowsize=.7];
            """ \
               % (rankdir or NFA.VISURANKDIR)
        comment = comment or ""
        if name and original.name:
            comment = f"<i><b>{(html.escape if escape_name else lambda x:x)(original.name)}</b></i>" + comment

        size = NFA.VISUSIZE if size is None else size
        if size:
            comment += ("<br/><br/>" + f"<b>#Q = {len(s.Q)}</b>" 
                         f"   #I = {len(s.I)}   #F = {len(s.F)}   #Δ = {len(original.Δ)}"
                         f"   #Σ = {len(original.Σ)}"
                         f"   <b>## = {original.size}</b>")

        lang = NFA.VISULANG if lang is None else lang
        if lang:
            L = list(original[:lang+1])
            comment += "<br/><br/>" + html.escape(sortstr(L[:lang])) + ("+" if len(L)>lang else "")

        if comment and not nocomment: dotc += """
            label=<%s>;
            labelloc=top;
            labeljust=left;\n""" % comment
        num = s.renum(smart=True,getiso=True)

        def accsrt(qs):
            """sort states by accessibility"""
            return sorted(qs,key=num.get)

        def rlsrt(r):
            p,a,q=r
            return num[p],num[q],a
        sΔ = sorted(s.Δ,key=rlsrt)

        pdfname = NFA.VISUPDF if not pdfname else pdfname
        initarrow = initarrow and NFA.VISU_INITIAL_ARROW

        with open(pdfname+".dot", "w") as f:
            f.write(dotc)
            if not initarrow:
                f.write('node [style=filled shape="cds",fillcolor="#FFF2F2",margin=.2];\n')
                f.writelines([f'{num[q]} [ label="{lbltrans(q)}" {dmod.get(q, "")}]\n' for q in accsrt(s.I - s.F)])
                f.write('node [style=filled shape="cds",fillcolor="#F2FFF2",margin=.2 ];\n')
                f.writelines([f'{num[q]}[penwidth=3] [ label="{lbltrans(q)}" {dmod.get(q, "")}]\n' for q in accsrt(s.I & s.F)])
            else:
                f.write('node [fillcolor="#FF8888" shape="point" width=.05 height=.05];\n')
                f.writelines([f'"XINIT_{num[q]}"\n' for q in accsrt(s.I)]+['\n'])

            f.write(f"""node [shape="{node_shape}" fontname = "palatino"
                  style=filled fillcolor="#F5F5FF" margin=0 width=.3 height=.3];\n""")
            f.writelines([f'{num[q]} [ label="{lbltrans(q)}" {dmod.get(q,"")}]\n'
                          for q in accsrt(s.Q - s.F - (set() if initarrow else s.I))])

            f.write('node [shape="doublecircle",fillcolor="#F2FFF2"];\n')
            f.writelines([f'{num[q]} [ label="{lbltrans(q)}" {dmod.get(q,"")}]\n' for q in accsrt(s.F)])

            if initarrow: f.writelines([f'"XINIT_{num[p]}" -> "{num[p]}"\n' for p in accsrt(s.I)])
            f.writelines([f'"{num[p]}" -> "{num[q]}" [ label = "{a}" {dmod.get((p,a,q),"")}]\n'
                          for p,a,q in sΔ if a])
            f.writelines([f'"{num[p]}" -> "{num[q]}" [ {epsilon_style} {dmod.get((p,a,q),"")} ]\n'
                          for p,a,q in sΔ if not a])
            f.write('}')

        is_small = original.size < NFA.LARGE
        do_dot(pdfname,pdfprepend,
               renderer="dot" if is_small else NFA.LARGE_RENDERER,
               renderer_options= [] if is_small else NFA.LARGE_RENDERER_OPTIONS )
        if print_current: print(erase_line, end="")

        return original

    @staticmethod
    def visutext(txt,**kw):
        """create a pdf page with the given text"""
        NFA((),(),(),name=f'<FONT POINT-SIZE="50">{txt}</FONT>').visu(lang=0,size=False,escape_name=False,**kw)

    # automaton minimisation, Brzozowski method
    def Brzozowski(s,table=False):
        return s.trim().reverse().dfa().reverse().dfa()

    # automaton minimisation
    def mini(s,*a,**k):
        # r1 = s.Moore(*a, **k)
        # r2 = s.Moore2(*a, **k)
        # r3 = s.Brzozowski(*a, **k)
        # assert r1.iso(r2) and r2.iso(r3), (r1.visu(),r2.visu(),r3.visu())
        return s.Moore2(*a, **k)

    def Moore(s,table=False):
        """Automaton minimisation, Moore method
        SUPERCEDED by Moore2.
        I really hate the way I wrote this; I tried to emulate
        the manual way to do it, so that I can later extend the code to
        generate the manual table of classes, for pedagogical purposes
        A much more elegant implementation is possible (even within that constraint)"""
        def namer():
            seen = {}
            k=0
            def f(x):
                nonlocal seen, k
                if x in seen: return seen[x]
                seen[x] = k ; k+=1
                return k-1
            return f
        oname = s.name
        s = s.trim().dfa().complete()
        if not s.Q: return s.copy()
        try: Q = sorted(s.Q)
        except TypeError : Q = list(s.Q)
        sy = sorted(s.Σ)
        n,m = len(Q),len(sy)+1
        index = { p:i for i,p in enumerate(Q) }
        score = [ [None for _ in range(n)] for _ in range(m) ]
        score[0] = [1 if p in s.F else 0 for p in Q]
        l = s.trans_2d()
        while True:
            for i,a in enumerate(sy):
                for j,p in enumerate(Q):
                    score[i+1][j] = score[0][ index[ l[p,a] ] ]
            na = namer(); res = score[0].copy()
            for j,p in enumerate(Q):
                score[0][j] = na( tuple( score[k][j] for k in range(m) ) )
            if res == score[0]: break
        groups = [ set() for _ in range(max(res)+1) ] # representative of each group
        for i,q in enumerate(Q):
            groups[res[i]] = i
        itog = {} # group index to sets/groups of real states
        for i,q in enumerate(Q):
            itog[groups[res[i]]] = itog.get(groups[res[i]],set()) | {q}
        return NFA({ g for g in groups if itog[g] >= s.I } ,
                   { g for g in groups if itog[g] & s.F },
                   { (g,a, groups[score[i+1][groups[res[g]]]] )
                     for g in groups for i,a in enumerate(sy) }
                   ).trim().map(lambda x:fset(itog[x])).setnop("M", oname)


    def Moore2(s,table=False):
        """ Automaton minimisation, Moore method.
            :param table: print Moore table as side effect """
        oname = s.name
        s = s.trim().dfa().complete()
        if not s.Q: return s.copy()
        try: Q = sorted(s.Q)
        except TypeError : Q = list(s.Q)
        symbs = sorted(s.Σ)
        cl = {} ## classes : { n : { symbol : { state: class }  } } symbol can be eps
        cl[0] = {}
        cl[0][""] = { q : int(q in s.F) for q in Q }
        l = s.trans_2d()
        def feed(n): # feed syms n and initialise n+1
            for a in symbs:
                cl[n][a] = { q: cl[n][""][ l[q,a] ] for q in Q }
            cl[n+1] = {}
            bilan = { q : tuple(t[q] for t in [cl[n][a] for a in [""]+symbs]) for q in Q }
            ntup = {} # number bilan tuples
            current = 0 # current class number
            for q in Q:
                tup = bilan[q]
                if tup not in ntup:
                    ntup[tup] = current
                    current += 1
            fbilan = { q : ntup[bilan[q]] for q in Q } # final bilan
            cl[n+1][""] = fbilan
        n = 0
        feed(n)
        while cl[n][""] != cl[n+1][""]:
            n += 1
            feed(n)
        classes = invd(cl[n][""]) # c -> set of states of class c
        rep = { c: list(classes[c])[0] for c in classes} # representative of class
        if table: s._Moore_table(Q, symbs, cl,n)
        return NFA(
            { c for c in classes if classes[c] >= s.I },
            { c for c in classes if classes[c] & s.F },
            { (p,a,cl[n][a][rep[p]]) for p in classes for a in symbs }
        ).trim().map(f=lambda c:fset(classes[c])).setnop("M", oname)

    def _Moore_table(s,Q,symbs,cl,n): # used from Moore2 only
        cid='c<{{\ \ }}'
        bs = "\\"
        def esc(s):
            return "".join('\\'+a if a in ('{','}') else a for a in str(s))
        macro = "\\newcommand{\RNum}[1]{\\uppercase\expandafter{\\romannumeral #1\\relax}}\n"
        begin = ( f"% {s.name}, Moore\n"
            f"\\begingroup{macro}\\begin{{tabular}}{{r<{{\ \ \ }}>{{\\boldmath}}{cid*len(Q)}}}\n"
            f"""& { ' & '.join(f"${esc(q)}$" for q in Q) }  \\\\"""
            f"\hline\n" )
        def pp(c): return f"\\RNum{{{c+1}}}"
        for k in range(n+2):
            begin+= "$\eps$ & " + " & ".join( pp(c) for c in cl[k][""].values() ) + "\\\\\n"
            if k == n+1: break
            for a in symbs:
                begin += f"${esc(a)}$ & " + " & ".join(pp(c) for c in cl[k][a].values()) + "\\\\\n"
            begin += "\hline"

        end = f"\end{{tabular}}\endgroup\n"
        print(begin+end)


    def iso(s,o):
        """get state isomorphism between dfas
        Returns False if no isomorphism
        """
        # s = s.trim() ; o = o.trim()
        assert s.is_det() & o.is_det()
        if s.I == o.I == set(): return True
        if list(map(len, (s.I, s.Q, s.F, s.Δ))) != list(map(len, (o.I, o.Q, o.F, o.Δ))) \
                or s.Σ != o.Σ :
            return False
        p,P = next(iter(s.I)) , next(iter(o.I))
        f = {}
        l, m = s.trans_2d(), o.trans_2d()
        res = True
        def trav(p,P):
            nonlocal res,f
            if not res: return
            if p in f:
                if f[p] != P or (p in s.F) != (P in o.F) : res = False
            else:
                f[p] = P
                for a in s.Σ:
                    if ((p,a) in l) != ((P,a) in m): res = False; return
                    if (p,a) not in l: continue
                    trav(l[p,a], m[P,a])
        trav(p,P)
        return f if res else False

    @staticmethod
    def spec(x,name="/Spec", Qtype=try_eval, Ttype=try_eval, style="classic",**kwargs):
        """
        :param x: the spec
        :param Qtype: constructor for states, eg int; defaults, evaluates python if possible
        :param Ttype: constructor for transitions
        :param style:
            Spec format: intials "p q r" on 1st line, finals on second,
                use __ for empty set
            rules on other lines, depends on style.

            style classic: rules "p  a q_a  b q_b .... z q_z, one per line.
                use eps for epsilon

            style ts: rules "p  q_a q_b .... q_z, one per line.
                as classic, epsilon for all labels: transition sytem

            style polar: rules "p a b c ... z q", one per line.
                Not well supported
        :type kwargs: remaming arguments passed to NFA constructor
        :return: new NFA from compact spec
        """
        i,f,*r = (ll for l in x.splitlines() if (ll := l.strip()))
        i,f = ( '' if l.strip() == '__' else l for l in (i,f) )

        Δ = set()
        for rs in r:
            if style == "classic":
                # if not rs: continue
                p, *A = rs.split()
                if p == "##": continue
                while len(A) >= 2:
                    a, q, *A = A
                    Δ.add((p,'' if a == 'eps' else a ,q))
            elif style == "ts":
                p, *A = rs.split()
                while A:
                    q, *A = A
                    Δ.add((p,'',q))
            elif style=="polar":
                p,*A,q = rs.split()
                Δ |= { (p,a,q) for a in A}
            else: assert False
        res = NFA(set(i.split()), set(f.split()), set(Δ), **kwargs )
        if Qtype: res = res.map(f=Qtype).named(name)
        if Ttype: res = res.map(g=Ttype).named(name)
        return res

    # apply h, given as letter-to-string function or dict
    # if dict incomplete, assume identity
    def homo(s,hd):
        if isinstance(hd,dict):
            h = lambda x: hd[x] if x in hd else x
        else: h = hd
        new = fresh_gen(s.Q)
        Δ = s.Δ.copy()
        for p,a,q in s.Δ:
            Δ.remove((p,a,q))
            w = h(a)
            states = [p] + [next(new) for _ in range(len(w)-1)] + [q]
            for k in range(len(states)-1) :
                Δ.add( (states[k], w[k:k+1], states[k+1]) )
        return NFA(s.I,s.F,Δ,name=s.nop('h'))

    def ihomo(s,h):
        """inverse homomorphism; given by dictionary"""
        return NFA(s.I,s.F,{ (p,a,q) for p in s.Q for a in h for q in s(h[a],Q={p}) }, name=s.nop('i'))

    def ihomo_visu(s,h,pdf=VISUPDF):
        ih = s.ihomo(h)
        A = NFA(s.I,s.F, s.Δ | ih.Δ, name=ih.name)
        A.visu(test=False,factor=False,pdfname=pdf,
               dmod={ r:'color="#ddAAAA" fontcolor="#ddAAAA"' for r in s.Δ},
               comment="/"+str(h))

    def table(s):
        """latex transition table, printed as side effect"""
        # assert not s.I & s.F # not handled
        sy = sorted(s.Σ)
        Q = sorted(s.Q, key=str)
        t = s.trans_2()
        cid='c<{{\ \ }}'
        bs = "\\"
        def esc(s):
            return "".join('\\'+a if a in ('{','}') else a for a in s)
        begin = ( f"% Name = {s.name}\n"
            f"\\begin{{tabular}}{{r>{{\\boldmath}}c<{{\ \ \ }}{cid*len(sy)}}}\n"
            f"""&& { ' & '.join(f"${a}$" if a else f"${bs}eps$" for a in sy) }  \\\\"""
            f"\hline\n" )

        for q in Q:
            # begin+= "Initial" if q in s.I else "Final" if q in s.F else ""
            spec = []
            if q in s.I: spec.append("Initial")
            if q in s.F: spec.append("Final")
            begin += ", ".join(spec)
            begin+= f" & ${esc(str(q))}$ & "
            begin+= ' & '.join(f"${ ', '.join( map(esc,map(str,t[q,a])) ) }$" if t[q,a] else "" for a in sy)
            begin+= "\\\\ \n"

        end = f"\hline\n\end{{tabular}}\n"
        print(begin+end)
        return s

    @property
    def size(s):
        return len(s.Q) + 3*len(s.Δ) + len(s.I) + len(s.F) + len(s.Σ)

    def growtofixpoint(s,grow,record_steps=False):
        """In place: grow the automaton according to grow(A)
        monotone growth procedure, until fixpoint is reached.
        grow acts as predicate "I have grown".

        record_steps: state/trans -> step index dict created in s._grow_step
        """
        n = 0
        if record_steps: s._grow_step = {x:0 for x in s.Q | s.Δ }
        while True:
            if not grow(s): break
            n += 1
            if record_steps:
                s._grow_step.update({x:n for x in (s.Q | s.Δ) - s._grow_step.keys()})
        return s

    # interface automata; cf Sebti Mouelhi PhD 2011
    # assume strings on transitions

    def Σins(s):  return { a[:-1] for a in s.Σ if a and a[-1] == "?" }
    def Σouts(s): return { a[:-1] for a in s.Σ if a and a[-1] == "!" }
    def Σh(s):    return { a[:-1] for a in s.Σ if a and a[-1] == ";" }

    @staticmethod
    def interface_sprod(A,B,visu_dnice=False):
        An = A.name ; Bn = B.name
        Ai, Bi = A.Σins(), B.Σins()
        Ao, Bo = A.Σouts(), B.Σouts()
        Ah, Bh = A.Σh(), B.Σh()
        def bare(Σ): return {a[:-1] for a in Σ}
        assert bare(A.Σ) == Ai|Ao|Ah, f" {A.Σ=} {Ai=} {Ao=} {Ah=}"
        assert bare(B.Σ) == Bi | Bo | Bh, f" {B.Σ=} {Bi=} {Bo=} {Bh=}"
        assert not (Ai & Bi) and not (Ao & Bo)
        assert all(not I&O and not O&H and not H&I for (I,O,H) in ((Ai,Ao,Ah), (Bi,Bo,Bh)))
        # print(f" {A.Σ=} {Ai=} {Ao=} {Ah=}")
        sds = (
           [ { An: io+"?", Bn: io+"!"}  for io in Ai & Bo ]
         + [ { An: oi+"!", Bn: oi+"?"}  for oi in Ao & Bi ]
        )
        shared = { a+suff for suff in "!?" for a in Ai & Bo | Ao & Bi }
        sds += [ { Aut.name: i } for Aut in (A,B) for i in Aut.Σ - shared ]
        # print(sds)
        P =  NFA.nsprod(A,B,sds=sds)
        if visu_dnice: P.dnice().visu()

        def collapse_tr(t):
            if len(t) == 1: return t[0][1]
            elif len(t) == 2: return t[0][1][:-1]+";"
            else: assert False
        def collapse_state(Q):
            (_,p),(__,q) = Q
            return x if len (x:=f"{p}{q}") <= 2 else f"{p},{q}"

        R = NFA(P.I, P.F, (
            (p,collapse_tr(a),q) for p,a,q in P.Δ
        ) ).map(collapse_state).named(f"{An} ⨉i {Bn}")
        R.worder = A.worder

        return R

    def prefixes(s):
        """returns languages of prefixes"""
        r = s.trim()
        r.F = r.Q
        return r.named(s.nop("pref"))

    def suffixes(s):
        """returns languages of suffixes"""
        r = s.trim()
        r.I = r.Q
        return r.named(s.nop("suff"))

    def factors(s):
        """returns languages of factors"""
        r = s.trim()
        r.I = r.Q; r.F = r.Q
        return r.named(s.nop("factors"))

    def prefix_free_min(s):
        """return language of words in s with no proper prefixes in s"""
        r = s.dfa()
        r.Δ = { (p,a,q) for p,a,q in r.Δ if p not in r.F }
        return r.trim().renum().named(s.nop("pfmin"))




