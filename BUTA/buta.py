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


from toolkit import *
from colorama import Fore, Back, Style
import re

class tuplestate(tuple): pass # when stuff must not be str() as a term

class term (tuple):
    """Terms, or trees.
    Initialised from tuple (f, t1,...,tn) and behaves as such.
    Also behaves like a function : position -> symbol
    """

    COLOUR_STR=True
    # should all str be coloured for terminal output?

    def __new__(cls, it):
        """
        Create a term from a nested tuple. Anything else shall be considered a leaf.
        All nested tuples shall be converted to terms.

        Internally, a term is always a tuple (f, t1,...,tn) which means leaves are
        of the form (a,) for matching / recursion purposes.

        :param it: tuple form of the term to create
        """
        if type(it) is term: return it
        if type(it) is not tuple: return super().__new__(cls, (it,))
        f, *st = it
        t = (f, *map(term, st))
        return super().__new__(cls, t)

    def __str__(self):
        if term.COLOUR_STR: return self.colour_str()
        f, *s = self
        return f"{f}({', '.join( map(str,s) )})" if s else str(f)


    COLOURS = [Fore.WHITE, Fore.BLUE, Fore.GREEN, Fore.YELLOW, Fore.MAGENTA, Fore.RED]
    @staticmethod
    def _col_par(col):
        c = term.COLOURS[col]
        return f"{c}{Style.BRIGHT}({Style.RESET_ALL}", f"{c}{Style.BRIGHT}){Style.RESET_ALL}"

    def colour_str(s,col=0):
        f, *st = s
        lp, rp = term._col_par(col)
        return f"{f}{lp}{', '.join(t.colour_str((col+1) % len(term.COLOURS)) for t in st)}{rp}" \
            if st else str(f)

    def __repr__(s): return str(s)

    def height(self):
        """height of term; leaves -> 0"""
        f, *s = self
        if not s: return 0
        return 1 + max( t.height() for t in s )

    @staticmethod
    def order(t):
        "height ordering key, for sorting purposes"
        f, *st = t
        sh = [s.height() for s in st]
        return t.height(), max(sh, default=-1), sum(sh), sh, f

    @staticmethod
    def sh(terms):
        "sort terms by height"
        return sorted(terms, key=term.order)

    def positions_subterms(s):
        """A position is a word (tuple), following standard definition
        :param left: number of leftmost child
            The default is 1 so that t[1] being the leftmost subterm
            matches the underlying tuple structure.
        :return: dict positions -> subterms
        """
        f, *st = s
        d = { ():s }
        for n,t in enumerate(st,1):
            d |= { (n,*pos) : u for pos,u in t.positions_subterms().items() }
        return d

    @staticmethod
    def normalise_position(pos):
        """Normalise a position given
           as string, eg "", "12",... or "1 21 1", or as int eg 12, if maximum
            arity <= 9. Uses same default for leftmost as positions_subterms
        :param pos:
        :return: normalise int tuple position
        """
        if type(pos) is int: pos = str(pos)
        if type(pos) is str:
            if " " in pos: pos = tuple(int(n) for n in pos.split())
            else: pos = tuple(int(n) for n in pos)
        return pos

    def __matmul__(s, pos):
        """
        Subterm at position
        :param pos: position
        :return: the subterm at that position
        """
        pos = term.normalise_position(pos)
        return s.positions_subterms().get(pos, None)

    def __call__(s, pos):
        """
        symbol at position
        :param pos: position, as in __matmul__
        :return: the symbol at that position
        """
        return None if (sub := s@pos) is None else sub[0]

    def replace(s,pos,u):
        """Replace subterm t@pos by u"""
        pos = term.normalise_position(pos)
        if not pos: return term(u)
        k, *pos = pos
        assert k < len(s), ((k,*pos), s)
        return term(s[:k] + ((s@(k,)).replace(pos,u),) + s[k+1:])

    def substitute(s, sub):
        """
        apply a leaf symbol -> term substitution
        :param sub: a dict substitution
        :return: the new term
        """
        f, *st = s
        if f in sub and not st: return term(sub[f])
        return term((f, *(t.substitute(sub) for t in st)))

    def leaves(s):
        """
        :return: set of leaves of term
        """
        f, *st = s
        if not st: return {f}
        return set.union(*( t.leaves() for t in st ))

    @staticmethod
    def spec(s):
        """get term from string specification, for instance 'f(a, b(), g(hi!(i(x))))'"""
        if isinstance(s, term): return s
        from lark import Lark, Transformer
        class trans(Transformer):
            def leaf(s,x): return str(x[0]).strip()
            def node(s,x): return (str(x[0]).strip(),*x[1:])
        p = Lark("""S: /([^(),])+/ 
          t : S -> leaf | S "()" -> leaf | S "(" t ("," t)* ")" -> node""",
          start="t", parser="lalr", transformer=trans())
        return term(p.parse(s))

    def to_tuple(s):
        """deep conversion to tuple"""
        f, *st = s
        return (f, *map(term.to_tuple, st))

T = term.spec
def Ts(*ts): return set(map(T,ts))

class predset:
    """set characterised by either explicit sets or predicates; union only"""

    def __init__(s, S={}, P=None, Ps=[]):
        """
        :param S: set
        :param P: predicate
        :param Ps: list of predicates (or)
        """
        s.S =  set(S)
        s.Ps = list(Ps) + ([] if P is None else [P])

    def __contains__(s, e): return e in s.S or any(p(e) for p in s.Ps)

    __call__ = __contains__

    def __or__(s,o): return predset(S=s.S | o.S, Ps=s.Ps + o.Ps)


class trs_rule(tuple):
    """Rewrite rule for TRS. Initialised from tuple (l,r) and
    behaves as such. Converts l and r to terms"""

    def __new__(cls, rule):
        assert len(rule) == 2
        return super().__new__(cls, map(term, rule))

    def __repr__(s):
        l,r = s
        return f"{l} ⟶ {r}"

class TRS:
    """term rewriting system (TRS)"""

    def __init__(s, rules, vars=predset(P=lambda e: re.fullmatch(r"_?[x-zX-Z][0-9_]*", e))):
        """
        Create a term rewriting system (TRS)
        :param rules: collection of couples of terms (l,r)
        :param vars: collection of symbols treated as variables, or predicate
            identifying variables
        """
        s.rules = set(map(trs_rule,rules)) ; s.vars = vars

    def __or__(s,o): return TRS(s.rules | o.rules, s.vars | o.vars)

    def match(s,t,u):
        """
        :return: a var -> tree dict substitution transforming t in u, or None if no match
        """
        class NoMatch(Exception): pass
        d = {}
        def z(t,u):
            # print("z", t.to_tuple(), u.to_tuple())
            match t,u:
                case (x,), (y,*sty):
                    # print("simple", (x,), (y,*sty))
                    if x in s.vars: d[x] = u
                    elif x==y: assert not sty
                    else: raise NoMatch
                case (x,*stx), (y,*sty) if x==y:
                    assert len(stx) == len(sty)
                    for tx, ty in zip(stx, sty): z(tx, ty)
                case _: raise NoMatch
                    # print(tuple(t),tuple(u))
        try: z(t,u); return d
        except NoMatch: return None

    def rewrite(s, terms):
        for t in terms:
            for l,r in s.rules:
                for a, ta in t.positions_subterms().items():
                    # print(t, l, r, a, ta)
                    if (σ := s.match(l,ta)) is not None:
                        # print(σ, t.replace(a, r.substitute(σ)))
                        yield t.replace(a, r.substitute(σ))

    def closure(s, I, lim=0, tlim=0, prnt_steps=0):
        with elapsed(v=0) as time:
            yield from I
            seen = I
            current = I
            n = len(I)
            while True:
                new = set()
                for t in s.rewrite(current):
                    if 0 < tlim < time(): return
                    if t not in new and t not in current and t not in seen:
                        yield t
                        new.add(t)
                        n += 1
                        if n >= lim > 0: return
                if not new: return
                if prnt_steps: print(new)
                seen |= current
                current = new


    def __call__(s, terms): return s.rewrite(terms)

    @staticmethod
    def spec(s):
        """Get TRS from string description:
            a list of rules separated by ;. each rule of the form
            f(..) -> g(..)"""
        lines = ( l for l in s.split(";") if l )
        return TRS( tuple(map(lambda x: term.spec(x.strip()),li.split("->")))  for li in lines)

    def __iter__(s): yield from s.rules

    def __repr__(s): return repr(s.rules)

    def vars_of(s, t):
        """set of variables of rule term"""
        return set(filter(s.vars, t.leaves()))
            





class buta_rule(tuple):
    """Transition rule for BUTA. Initialised from tuple (f, p1,..,pn, q) and
    behaves as such."""

    def __repr__(s):
        f, *p, q = s
        return f"{term((f, *p))} ⟶ {q}"



# TODO: meta decorator to choose what to preserve, using setattr
def preserve(m):
    """
    Decorator: preverse annex properties:
    :param m:
    :return:
    """
    def f(s,*p,**k):
        res = m(s,*p,**k)
        # for now no properties to preserve
        return res
    return f

class BUTA:
    """Bottom-Up Nondeterministic Tree Automaton.
    Manipulates classes terms and rules internally, but accepts their
    tuple representation in most methods. Do not manipulate Δ directly.
    """

    def __init__(s, F=(), Δ=(), name="", Q=(), Σ=(),trimmed=False):
        s.Δ = set()
        s.Σ = dict(Σ)
        s._F = set(F)
        s.Q = s._F | set(Q)  # if you need useless states, with no associated rules
        s.add_rules(Δ)
        s.name = name
        s._trimmed = trimmed

    def copy(s):
        return BUTA(s.F, s.Δ, s.name, s.Q, s.Σ, s._trimmed)

    @property
    def F(s): return s._F

    @F.setter
    def F(s, F): s.Q |= (F := set(F)); s._F = F

    def add_rules(s,Δ,final=False):
        """add a set of rules, following add_rule"""
        for r in Δ: s.add_rule(*r,final=final)
        return s

    def add_rule(s,f,*ps, final=False):
        """
        add a rule f(p1,...,pn) -> q to Δ
        Makes sure to update other attributes acordingly.
        :param f: symbol
        :param ps: states p1,..,pn, q
        :param final: should q be final ?
        :return: self, updated in place
        """
        *p, q = ps
        s.Δ.add(buta_rule((f, *p, q)))
        if f in s.Σ: assert (ar := s.Σ[f])  == len(p), (ar, len(p))
        else:        s.Σ[f] = len(p)
        s.Q |= {*p,q}
        if final: s.F.add(q)
        return s

    @property
    def size(s):
        return len(s.Q) + sum( len(r) for r in s.Δ ) + len(s.F) + len(s.Σ)

    def sorted_rules(s):
        return sorted(s.Δ, key=lambda r:(len(r), *map(str,r)))

    def pretty_rules(s):
        return "{" + ', '.join( str(r) for r in s.sorted_rules() ) + "}"

    def __str__(s):
        return (f"BUTA {s.name}:" if s.name else "") + \
               f"  ## = {s.size}\n" \
               f"Σ {len(s.Σ):<3} {s.Σ}\n" \
               f"Q {len(s.Q):<3} {sortstr(s.Q)}\n" \
               f"F {len(s.F):<3} {sortstr(s.F)}\n" \
               f"Δ {len(s.Δ):<3} {s.pretty_rules()}"

    def __repr__(s):
        return f"<BUTA {s.name} #{s.size} Σ{len(s.Σ)} Q{len(s.Q)} " \
               f"F{len(s.F)} Δ{sum( len(r) for r in s.Δ )}>"\
               f"{':Trim' if s._trimmed else ''}"

    @staticmethod
    def spec(x, name="/Spec", Qtype=try_eval, Ttype=try_eval, **kwargs):
        """Get automaton from compact textual description
        :param x: the spec:
         one line for final states, then one line per rule; all space separated:
            ------------------
            qf1 qf2 ...
            f p1 p2 ... pn  q
            ...
            ------------------
        # as first character comments out a whole line
        :param Qtype: constructor for states, eg int; defaults, evaluates python if possible
        :param Ttype: constructor for transition symbols
        :type kwargs: remaining arguments passed to BUTA constructor
        :return: new BUTA from compact spec
        """
        f, *rs = (ll for l in x.splitlines() if (ll := l.strip()) and ll[0] != '#')
        f = '' if f.strip() == '__' else f

        return BUTA(map(Qtype, f.split()), (
            (Ttype(f), *map(Qtype, pq))
            for r in rs
            for f, *pq in [r.split()]
        ), name=name)

    def named(s, name):
        """change name in place and return s"""
        s.name = str(name)
        return s

    def trans_lhs(s):
        """transitions as dict lhs -> set of rhs(=states)"""
        look = defaultdict(lambda : set())
        for f,*p,q in s.Δ: look[(f,*p)].add(q)
        return look

    def run(s, t):
        """
        :param t: a ground term
        :return: set of states in which t is recognised
        """
        l = s.trans_lhs()
        def z(t):
            f, *s = t
            if not s: return l[t]
            ps = list(product(*map(z,s)))
            return set.union(*(l[(f,*p)] for p in ps) ) if ps else set()
        return z(term(t))

    def __call__(s, t):
        """as .run"""
        return s.run(t)

    def __contains__(s, t):
        """language membership test"""
        return s.run(t) & s.F

    def __iter__(s):
        """enumerate terms in language, without repetition; undefined order"""
        acc = defaultdict(lambda : set())
        s = s.trim()
        rules = s.sorted_rules()
        safety = 0
        while True:
            for f, *ps, q in rules:
                for line in product(*(acc[p] for p in ps)):
                    t = term((f,*line))
                    if t not in acc[q]:
                        if q in s.F:
                            yield t
                            safety = 0
                        acc[q] |= {t}
            safety += 1
            if safety > len(s.Q): break


    def __getitem__( s, i ) :
        """language pseudo-indexing and slicing"""
        if isinstance( i, int ) :
            g = iter(s)
            for _ in range(i): next(g)
            return next(g)
        elif isinstance( i, slice ) :
            return islice(iter(s),i.start,i.stop,i.step)
        else:
            raise (TypeError, "Invalid argument type.")

    def __and__(s, o):
        """Intersection"""
        return BUTA( set(product(s.F, o.F)),
                     {
                         (f, *map(tuplestate,zip(p,q)))
                         for (f,*p) in s.Δ
                         for (g,*q) in o.Δ
                         if f==g
                     },
                     name=f"{s.name} ∩ {o.name}")
        # r.F = ( (p,q) for (p,q) in r.Q if p in s.F and q in o.F )

    @staticmethod
    def disjoint(os):
        """Make automata states disjoint if need be
        :param os: list of automata"""
        if len(os) <= 1: return os
        couples = ( (os[i],os[j]) for i in range(len(os)-1) for j in range(i+1,len(os)) )
        if any( A.Q & B.Q for A,B in couples ):
            return [s.map(lambda q: tuplestate((k, q))) for k, s in enumerate(os)]
        return os
    
    # language union
    def __or__(s,o): return s.union(o)

    def union(*os):
        """Union of argument NFAs"""
        if not os: return BUTA(set(), set())
        os = BUTA.disjoint(os)
        return BUTA(
            set.union(*(s.F for s in os)),
            set.union(*(s.Δ for s in os)),
            name="("+" ∪ ".join(s.name or "None" for s in os) +")")


    def accessibles(s):
        """return the sets (acc, coa) of accessible and co-accessible states
        Not as simple a coaccessible concept as for NFA"""
        acc = { q for (f,*p,q) in s.Δ if not p }
        coa = s.F.copy()
        while True:
            na = { q for (f,*p,q)  in s.Δ if set(p) <= acc }
            nc = { p for (f,*ps,q) in s.Δ if q in coa for p in ps }
            if na <= acc and nc <= coa: break
            acc |= na ; coa |= nc
        return acc, coa

    def only(s,S):
        """keep only what uses states in S"""
        return BUTA( s.F & S, { (f,*p) for (f,*p) in s.Δ if set(p) <= S }, name=s.name+"/o")

    def trim(s):
        """keep only useful states"""
        A,C = s.accessibles()
        if len(Q := (A&C)) == len(s.Q): return s
        else:                           return s.only(Q).trim()

    def is_empty(s):
        """test whether language is empty"""
        return not s.trim().Q

    def map(s, f=lambda x:x, g=lambda x:x):
        """renames all states and symbols according to a function
        if f is not injective, might change language !
        :param f states fun
        :param g symbols fun
        """
        f = { x: f(x) for x in s.Q }.get
        g = { x: g(x) for (x,*_) in s.Δ }.get

        return BUTA(
            {f(q) for q in s.F},
            {(g(a), *map(f,qs)) for (a,*qs) in s.Δ },
            Q={f(q) for q in s.Q},
            name=s.name + '↦')

    def collapse(s, clusters):
        """
        :param clusters: collection of sets of states
        :return: new automaton collapsing states in same sets
        """
        f = {}
        if not clusters: return s
        for c in clusters:
            rep = peek(c)
            f |= { q:rep for q in c }
        for q in s.Q - set.union(*map(set,clusters)): f[q] = q
        return s.map(f=f.get)


    def completed_rules(s, R : TRS):
        """
        One step of Genet completion
        :param R: A TRS
        :return: Delta transition rules joining critical pairs wrt R
        """
        rules = set()
        fresh = fresh_gen(s.Q, str)
        def normalise(t, qt):
            # print("norm", t, qt)
            f, *st = t
            if not st and f in s.Q: return f
            if not st:  rules.add( (f, qt) )
            else:       rules.add( (f, *(normalise(u, next(fresh)) for u in st), qt ))
            return qt

        for l,r in R.rules:
            vars = set(filter(R.vars, l.leaves())) # set salt constant in one Python process, so no need for list(..) for the zip
            assert not vars & set(s.Σ)
            for σ in ( dict(zip(vars,val)) for val in product( s.Q, repeat=len(vars) ) ):
                A = s.copy().add_rules(σ.items())
                Ql, Qr = A(l), A(r)
                for ql in Ql:
                    if ql not in Qr:
                        # print(r,σ,ql)
                        normalise( r.substitute(σ), ql )
        return set(map(buta_rule, rules))

    def complete_inplace(s, R:TRS, n=1):
        """
        Complete automaton in place wrt TRS R
        :param n: number of completion steps to do
        :param R: TRS
        :return: self, altered
        """
        assert n >= 0
        if not n: return s
        for _ in range(n): s.add_rules(s.completed_rules(R))
        return s.named(s.name+f"*{n if n > 1 else ''}")
    
    def complete(s, R:TRS, n=1):
        """
        Return completed automaton wrt TRS R
        :param n: number of completion steps to do
        :param R: TRS
        :return: completed automata
        """
        return s.copy().complete_inplace(R, n=n)

    def is_complete(s, R:TRS):
        """
        :param R: TRS
        :return: Are we complete wrt rewriting by R?
        """
        return not s.completed_rules(R)

    def image(s, R : TRS):
        """
        :param R: A TRS
        :return: NFA for R([[A]]), direct image
        """
        A = s.map(lambda q: tuplestate( (q,0) ))
        def prime(q): return tuplestate( (q[0], 1) ) if q in A.Q else q
        A.F = { prime(qf) for qf in A.F }
        complete = {(*p, prime(q)) for (*p, q) in A.completed_rules(R)}
        def prime_one(p): return [ p[:i] + [prime(p[i])] + p[i+1:] for i in range(len(p)) ]
        transmit = { (f, *primed, prime(q)) for f,*p,q in A.Δ if p for primed in prime_one(p) }
        A.add_rules( complete | transmit )
        return A.named(f"R({s.name})")

    def stringify(s, f=str, g=str):
        """when states contain sets, string rep may vary from moment to moment
        fix a single string representation.
        Ensure no collision"""
        f = {p: f(p) for p in s.Q}
        g = {a: g(a) for a in s.Σ}
        res = s.map(f.get, g.get)
        assert len(res.Q) == len(s.Q)
        return res

    def print(s, n=10):
        """
        print the description of the automaton
        :param n: max number of language terms to display
        :return: self
        """
        print(s)
        l = term.sh(s[:n+1])
        print("Lang ", str(l) if len(l) <= n else str(l)[:-1] + ",...]")
        return s
    
    @staticmethod
    def of_set(L):
        rules = set(); F = set()
        fresh = fresh_gen()
        def rec(t, qt):
            f, *st = t
            if not st:  rules.add( (f, qt) )
            else:       rules.add( (f, *(rec(u, next(fresh)) for u in st), qt ))
            return qt
        for t in map(term.spec, L):
            F.add(qf := next(fresh))
            rec(t, qf)
        return BUTA(F, rules, name=f"OfSet {L}")
        





# TODO: support epsilon and generalised rules.
# epsilon not trivial to handle in implem because no way to know in p -> q whether p symbol or state:
# can test p in Q but then dependent upon order of introduction of the rules
# if you do epsilon, might as well do configurations and base everything on rewriting?