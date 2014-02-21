#!/usr/bin/python
# -*- coding: utf-8 -*-

import re

def paren(s, level, expl):
    return s if level <= expl else '('+s+')'

def isLiteral(s):
    return isinstance(s, basestring) and re.match(r'^[a-z]+$', s)

def nnf(f):
    return f.simplify()
    
def cnf(f):
    return f.simplify().cnf()

def dnf(f):
    return f.simplify().dnf()

class LogicalFormula:
    def __init__(self):
        raise Exception('Instantiating an abstract class.')
        
    def __hash__(self):
        return self.__repr__().__hash__()
        
    def simplify(self):
        return self
        
    def cnf(self):
        return self
    
    def dnf(self):
        return self
        
    def apply(self, d):
        return self

class Literal(LogicalFormula):
    def __init__(self, p):
        if not isLiteral(p):
            raise Exception('Literals must be strings of lowercase letters!')
        self.p = p
        
    def __repr__(self, level=0):
        return paren(self.p, level, 6)
        
    def __cmp__(self, other):
        if not isinstance(other, LogicalFormula):
            return 1
        elif isinstance(other, Literal):
            return cmp(self.p, other.p)
        else:
            return -1
            
    def apply(self, d):
        if d.has_key(self.p):
            if isLiteral(d[self.p]):
                return Literal(d[self.p])
            elif isinstance(d[self.p], LogicalFormula):
                return d[self.p].simplify()
        return self

class Not(LogicalFormula):
    def __init__(self, t):
        if isLiteral(t):
            t = Literal(t)
        elif not isinstance(t, LogicalFormula):
            raise Exception('Only logical formulas can be negated!')
        self.t = t
        
    def __repr__(self, level=0):
        return paren('~'+self.t.__repr__(6), level, 6)
        
    def __cmp__(self, other):
        if not isinstance(other, LogicalFormula) or isinstance(other, Literal):
            return 1
        elif isinstance(other, Not):
            return cmp(self.t, other.t)
        else:
            return -1
        
    def simplify(self):
        if isinstance(self.t, Not):
            return self.t.t.simplify()
        elif isinstance(self.t, And):
            return Or([Not(x) for x in self.t.l]).simplify()
        elif isinstance(self.t, Or):
            return And([Not(x) for x in self.t.l]).simplify()
        else:
            return self
            
    def apply(self, d):
        return Not(self.t.apply(d)).simplify()
    
class And(LogicalFormula):
    def __init__(self, *l):
        self.l = None
        if len(l) == 1:
            if isinstance(l[0], Or):
                self.l = l[0].l
            elif isLiteral(l[0]):
                self.l = [Literal(l[0])]
            elif isinstance(l[0], list) or isinstance(l[0], tuple):
                l = list(l[0])
        if self.l == None:
            l = [Literal(x) if isLiteral(x) else x for x in l]
            if any([not isinstance(x, LogicalFormula) for x in l]):
                 raise Exception('Only logical formulas can be conjoined!')
            self.l = l
        
    def __repr__(self, level=0):
        if len(self.l) == 0:
            return paren('T', level, 6)
        elif len(self.l) == 1:
            return self.l[0].__repr__(level)
        else:
            return paren(' /\\ '.join([x.__repr__(6) for x in self.l]), level, 5)
    
    def __cmp__(self, other):
        if not isinstance(other, LogicalFormula) or isinstance(other, Literal) or isinstance(other, Not):
            return 1
        elif isinstance(other, And):
            return cmp(self.l, other.l)
        else:
            return -1
        
    def simplify(self):
        l = sum([y.l if isinstance(y, And) else [y] for y in [x.simplify() for x in self.l]], [])
        if any([isinstance(x, Or) and len(x.l) == 0 for x in l]):
            return False()
        elif len(l) == 1:
            return l[0]
        else:
            l = sorted(set(l))
            if any([x.t in l for x in l if isinstance(x, Not)]):
                return False()
            else:
                return And(l)
        
    def cnf(self):
        return And([x.cnf() for x in self.l])
        
    def dnf(self):
        if len(self.l) == 0:
            return self
        elif len(self.l) == 1:
            return self.l[0].cnf()
        l = [x.dnf() for x in self.l]
        if isinstance(l[0], Or):
            return Or([And([x] + l[1:]).dnf() for x in l[0].l]).simplify()
        else:
            return Or([And([l[0], x]) for x in Or(And(l[1:]).cnf()).l]).simplify()
            
    def apply(self, d):
        return And([x.apply(d) for x in self.l]).simplify()
        
        
class Or(LogicalFormula):
    def __init__(self, *l):
        self.l = None
        if len(l) == 1:
            if isinstance(l[0], Or):
                self.l = l[0].l
            elif isLiteral(l[0]):
                self.l = [Literal(l[0])]
            elif isinstance(l[0], list) or isinstance(l[0], tuple):
                l = list(l[0])
        if self.l == None:
            l = [Literal(x) if isLiteral(x) else x for x in l]
            if any([not isinstance(x, LogicalFormula) for x in l]):
                 raise Exception('Only logical formulas can be disjoined!')
            self.l = l
        
    def __repr__(self, level=0):
        if len(self.l) == 0:
            return paren('F', level, 6)
        elif len(self.l) == 1:
            return self.l[0].__repr__(level)
        else:
            return paren(' \\/ '.join([x.__repr__(5) for x in self.l]), level, 4)
        
    def __cmp__(self, other):
        if not isinstance(other, Or):
            return 1
        else:
            return cmp(self.l, other.l)
        
    def simplify(self):
        l = sum([y.l if isinstance(y, Or) else [y] for y in [x.simplify() for x in self.l]], [])
        if any([isinstance(x, And) and len(x.l) == 0 for x in l]):
            return True()
        elif len(l) == 1:
            return l[0]
        else:
            l = sorted(set(l))
            if any([x.t in l for x in l if isinstance(x, Not)]):
                return True()
            else:
                return Or(l)
        
    def cnf(self):
        if len(self.l) == 0:
            return self
        elif len(self.l) == 1:
            return self.l[0].cnf()
        l = [x.cnf() for x in self.l]
        if isinstance(l[0], And):
            return And([Or([x] + l[1:]).cnf() for x in l[0].l]).simplify()
        else:
            return And([Or([l[0], x]) for x in And(Or(l[1:]).cnf()).l]).simplify()
            
    def dnf(self):
        return Or([x.dnf() for x in self.l])
        
    def apply(self, d):
        return Or([x.apply(d) for x in self.l]).simplify()

class Implies(Or):
    def __init__(self, prec, cons):
        if isLiteral(prec):
            prec = Literal(prec)
        if isLiteral(cons):
            cons = Literal(cons)
        if not isinstance(prec, LogicalFormula) or not isinstance(cons, LogicalFormula):
            raise Exception('Only logical formulas can be imply or be implied!')
        self.l = [Not(prec), cons]
        
    def __repr__(self, level=0):
        if len(self.l) == 2 and isinstance(self.l[0], Not):
            return paren(self.l[0].t.__repr__(2) + ' => ' + self.l[1].__repr__(1), level, 1)
        else:
            return Or.__repr__(self, level)
        
        
class True(And):
    def __init__(self):
        self.l = []

class False(Or):
    def __init__(self):
        self.l = []
