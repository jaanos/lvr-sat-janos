#!/usr/bin/python
# -*- coding: utf-8 -*-

import prop

def dpllStep(l, trace=False):
    """Korak metode DPLL.
    
    Argumenta:
    l     -- seznam disjunktov
    trace -- ali naj se izpisuje sled dokazovanja, privzeto False
    """
    num = 1
    out = []
    while num > 0:
        while num > 0:
            literals = {}
            next = []
            for x in l:
                if isinstance(x, prop.Literal):
                    if x.p in literals and not literals[x.p]:
                        if trace:
                            print("Contradiction for literal %s" % x.p)
                        return False
                    else:
                        literals[x.p] = True
                elif isinstance(x, prop.Not):
                    if x.t.p in literals and literals[x.t.p]:
                        if trace:
                            print("Contradiction for literal %s" % x.p)
                        return False
                    else:
                        literals[x.t.p] = False
                elif len(x.l) == 0:
                    if trace:
                        print("Empty disjunction found")
                    return False
                elif not any([prop.Not(y) in x.l for y in x.l if isinstance(y, prop.Literal)]):
                    next.append(x)
            num = len(literals)
            out += list(literals.items())
            l = [y for y in [x.apply(literals) for x in next] if not isinstance(y, prop.And)]
            if trace > 1:
                print("Found %d literals: %s, simplified to %s" % (num, literals, l))
        pure = {}
        for d in l:
            for x in d.l:
                if isinstance(x, prop.Literal):
                    pure[x.p] = None if (x.p in pure and pure[x.p] != True) else True
                else:
                    pure[x.t.p] = None if (x.t.p in pure and pure[x.t.p] != False) else False
        purs = [(k, v) for (k, v) in pure.items() if v != None]
        num = len(purs)
        out += purs
        l = [y for y in [x.apply(dict(purs)) for x in l] if not isinstance(y, prop.And)]
        if trace > 1:
            print("Found %d pures: %s, simplified to %s" % (num, purs, l))
    if len(l) == 0:
        return dict(out)
    p, v = pure.popitem()
    if trace:
        print("Trying %s:T" % p)
    true = dpllStep([y for y in [x.apply({p: True}) for x in l] if not isinstance(y, prop.And)], trace)
    if type(true) == dict:
        return dict(out + [(p, True)] + list(true.items()))
    if trace:
        print("Failed %s:T" % p)
        print("Trying %s:F" % p)
    false = dpllStep([y for y in [x.apply({p: False}) for x in l] if not isinstance(y, prop.And)], trace)
    if type(false) == dict:
        return dict(out + [(p, False)] + list(false.items()))
    if trace:
        print("Failed %s:F" % p)
    return False
        
def dpll(f, trace=False):
    """Glavni program metode DPLL.
    
    Argumenta:
    f     -- logični izraz
    trace -- ali naj se izpisuje sled dokazovanja, privzeto False
    """
    f = prop.cnf(f)
    if isinstance(f, prop.And):
        l = f.l
    else:
        l = [f]
    return dpllStep(l, trace)
