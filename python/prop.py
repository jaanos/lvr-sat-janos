#!/usr/bin/python
# -*- coding: utf-8 -*-

import re

try:
    basestring
except NameError:
    basestring = str

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
    
def sat(f):
    d = {}
    if not f.simplify().ncf().node(d).valuate(True):
        return False
    val = {k.p: v.v for (k, v) in d.items() if isinstance(k, Literal)}
    if None in val.values():
        return None
    else:
        return val
    
class DAGNode:
    def __init__(self):
        raise Exception('Instantiating an abstract class.')
        
    def valuate(self, b):
        if self.v != None:
            return self.v == b
        self.v = b
        return None
        
    def parents(self, b):
        for x in self.a:
            if not x.update(b):
                return False
        return True
        
    def update(self, b):
        return True
        
class DAGLiteral(DAGNode):
    def __init__(self, d, p):
        self.p = p
        self.a = []
        self.v = None
        
    def valuate(self, b):
        return DAGNode.valuate(self, b) != False

class DAGNot(DAGNode):
    def __init__(self, d, t):
        self.t = t.node(d)
        self.t.a.append(self)
        self.a = []
        self.v = None
        
    def valuate(self, b):
        val = DAGNode.valuate(self, b)
        if val == None:
            return self.t.valuate(not b) and self.parents(b)
        else:
            return val
        
    def update(self, b):
        return self.valuate(not b)

class DAGAnd(DAGNode):
    def __init__(self, d, l):
        self.l = [x.node(d) for x in l]
        for x in self.l:
            x.a.append(self)
        self.a = []
        if len(l) == 0:
            self.v = True
        else:
            self.v = None
            
    def valuate(self, b):
        val = DAGNode.valuate(self, b)
        if val == None:
            if b:
                for x in self.l:
                    if not x.valuate(True):
                        return False
            elif not any([x.v == False for x in self.l]):
                n = [x for x in self.l if x.v == None]
                if len(n) == 0 or (len(n) == 1 and not n[0].valuate(False)):
                    return False
            return self.parents(b)
        else:
            return val
            
    def update(self, b):
        if not b:
            return self.valuate(False)
        elif not self.v and not any([x.v == False for x in self.l]):
            if all([x.v for x in self.l]):
                return False
            n = [x for x in self.l if x.v == None]
            if len(n) == 0 or (len(n) == 1 and not n[0].valuate(False)):
                return False
        return True
            
class LogicalFormula:
    def __init__(self):
        raise Exception('Instantiating an abstract class.')
        
    def __hash__(self):
        return self.__repr__().__hash__()
        
    def __eq__(self, other):
        return not (self != other)
    
    def __le__(self, other):
        return not (self > other)
    
    def __gt__(self, other):
        return not (self < other or self == other)
    
    def __ge__(self, other):
        return not (self < other)
    
    def simplify(self):
        return self
        
    def cnf(self):
        return self
    
    def dnf(self):
        return self
        
    def ncf(self):
        return self
        
    def apply(self, d):
        return self
    
    def node(self):
        raise Exception('Not applicable in DAG.')

class Literal(LogicalFormula):
    def __init__(self, p):
        if not isLiteral(p):
            raise Exception('Literals must be strings of lowercase letters!')
        self.p = p
        
    def __repr__(self, level=0):
        return paren(self.p, level, 6)
        
    def __ne__(self, other):
        return not isinstance(other, Literal) or self.p != other.p
        
    def __lt__(self, other):
        if isinstance(other, Literal):
            return self.p < other.p
        else:
            return isinstance(other, LogicalFormula)
                        
    def apply(self, d):
        if d.has_key(self.p):
            if isLiteral(d[self.p]):
                return Literal(d[self.p])
            elif isinstance(d[self.p], bool):
                return Tru() if d[self.p] else Fls()
            elif isinstance(d[self.p], LogicalFormula):
                return d[self.p].simplify()
        return self
        
    def node(self, d):
        if not d.has_key(self):
            n = DAGLiteral(d, self.p)
            d[self] = n
        return d[self]

class Not(LogicalFormula):
    def __init__(self, t):
        if isLiteral(t):
            t = Literal(t)
        elif not isinstance(t, LogicalFormula):
            raise Exception('Only logical formulas can be negated!')
        self.t = t
        
    def __repr__(self, level=0):
        return paren('~'+self.t.__repr__(6), level, 6)
    
    def __ne__(self, other):
        return not isinstance(other, Not) or self.t != other.t
        
    def __lt__(self, other):
        if isinstance(other, Not):
            return self.t < other.t
        else:
            return isinstance(other, LogicalFormula) and not isinstance(other, Literal)

    def simplify(self):
        if isinstance(self.t, Not):
            return self.t.t.simplify()
        elif isinstance(self.t, And):
            return Or([Not(x) for x in self.t.l]).simplify()
        elif isinstance(self.t, Or):
            return And([Not(x) for x in self.t.l]).simplify()
        else:
            return self
            
    def ncf(self):
        if isinstance(self.t, Not):
            return self.t.t.ncf()
        elif isinstance(self.t, Or):
            return And([Not(x).ncf() for x in self.t.l])
        else:
            return Not(self.t.ncf())
            
    def apply(self, d):
        return Not(self.t.apply(d)).simplify()
        
    def node(self, d):
        if not d.has_key(self):
            n = DAGNot(d, self.t)
            d[self] = n
        return d[self]
    
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
    
    def __ne__(self, other):
        return not isinstance(other, And) or self.l != other.l
        
    def __lt__(self, other):
        if isinstance(other, And):
            return self.l < other.l
        else:
            return isinstance(other, LogicalFormula) and not isinstance(other, Literal) and not isinstance(other, Not)
        
    def simplify(self):
        l = sum([y.l if isinstance(y, And) else [y] for y in [x.simplify() for x in self.l]], [])
        if any([isinstance(x, Or) and len(x.l) == 0 for x in l]):
            return Fls()
        elif len(l) == 1:
            return l[0]
        else:
            l = set(l)
            l.difference_update([x for x in l if isinstance(x, Or) and any([y in x.l for y in l])])
            assorb = [(x, [y.t for y in l if isinstance(y, Not) and y.t in x.l] + [Not(y) for y in l if Not(y) in x.l]) for x in l if isinstance(x, Or)]
            remove = [x[0] for x in assorb if len(x[1]) > 0]
            add = [Or([y for y in x[0].l if y not in x[1]]).simplify() for x in assorb if len(x[1]) > 0]
            l.difference_update(remove)
            l.update(add)
            if any([x.t in l for x in l if isinstance(x, Not)]):
                return Fls()
            return And(sorted(l))
        
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
        elif len(l) == 2 and isinstance(l[1], Or):
            return Or([And([l[0], x]).dnf() for x in l[1].l]).simplify()
        else:
            return Or([And([l[0], x]) for x in Or(And(l[1:]).dnf()).l]).simplify()
            
    def ncf(self):
        return And([x.ncf() for x in self.l])
            
    def apply(self, d):
        return And([x.apply(d) for x in self.l]).simplify()
        
    def node(self, d):
        if not d.has_key(self):
            n = DAGAnd(d, self.l)
            d[self] = n
        return d[self]
        
        
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
        
    def __ne__(self, other):
        return not isinstance(other, Or) or self.l != other.l
        
    def __lt__(self, other):
        return isinstance(other, Or) and self.l < other.l
        
    def simplify(self):
        l = sum([y.l if isinstance(y, Or) else [y] for y in [x.simplify() for x in self.l]], [])
        if any([isinstance(x, And) and len(x.l) == 0 for x in l]):
            return Tru()
        elif len(l) == 1:
            return l[0]
        else:
            l = set(l)
            l.difference_update([x for x in l if isinstance(x, And) and any([y in x.l for y in l])])
            assorb = [(x, [y.t for y in l if isinstance(y, Not) and y.t in x.l] + [Not(y) for y in l if Not(y) in x.l]) for x in l if isinstance(x, And)]
            remove = [x[0] for x in assorb if len(x[1]) > 0]
            add = [And([y for y in x[0].l if y not in x[1]]).simplify() for x in assorb if len(x[1]) > 0]
            l.difference_update(remove)
            l.update(add)
            if any([x.t in l for x in l if isinstance(x, Not)]):
                return Tru()
            else:
                return Or(sorted(l))
        
    def cnf(self):
        if len(self.l) == 0:
            return self
        elif len(self.l) == 1:
            return self.l[0].cnf()
        l = [x.cnf() for x in self.l]
        if isinstance(l[0], And):
            return And([Or([x] + l[1:]).cnf() for x in l[0].l]).simplify()
        elif len(l) == 2 and isinstance(l[1], And):
            return And([Or([l[0], x]).cnf() for x in l[1].l]).simplify()
        else:
            return And([Or([l[0], x]) for x in And(Or(l[1:]).cnf()).l]).simplify()
            
    def dnf(self):
        return Or([x.dnf() for x in self.l])
        
    def ncf(self):
        return Not(And([Not(x).ncf() for x in self.l]))
        
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
        
        
class Tru(And):
    def __init__(self):
        self.l = []

class Fls(Or):
    def __init__(self):
        self.l = []
