#!/usr/bin/python
# -*- coding: utf-8 -*-

import prop
import math
import re

# Združljivost za Python 2 in Python 3
try:
    basestring
except NameError:
    basestring = str
    
def iff(p, q):
    """Vrne logično ekvivalenco izrazov p in q kot konjunkcijo dveh implikacij."""
    return prop.And(prop.Implies(p, q), prop.Implies(q, p))

def sudoku(s, abc):
    """Vrne logični izraz, ki opisuje sudoku s z abecedo abc"""
    n = len(abc)
    r = int(math.sqrt(n))
    
    if isinstance(abc, basestring):
        s = [[None if s[i][j] in [None, ""] else str(s[i][j]) for j in range(n)] for i in range(n)]
        assert all([all([x == None or (len(x) == 1 and x in abc) for x in l]) for l in s]), "Sudoku vsebuje neveljavne simbole!"
    else:
        assert None not in abc, "Abeceda ne sme vsebovati None!"
        assert all([all([x == None or x in abc for x in l]) for l in s]), "Sudoku vsebuje neveljavne simbole!"
    
    assert n == r*r, "Velikost abecede ni popoln kvadrat!"
    assert len(s) == n, "Število vrstic se ne ujema s številom znakov!"
    assert all([len(l) == n for l in s]), "Število stolpcev se ne ujema s številom znakov!"
    
    l = []
    
    for i in range(n):
        for j in range(n):
            if s[i][j] != None:
                # Obstoječa števila
                t = abc.index(s[i][j])
                for k in range(n):
                    if k == t:
                        l.append("r%dc%dv%d" % (i, j, k))
                    else:
                        l.append(prop.Not("r%dc%dv%d" % (i, j, k)))
            else:
                # Vsako polje ima natanko eno vrednost
                l.append(prop.Or([prop.And([("r%dc%dv%d" % (i, j, x) if x == y else prop.Not("r%dc%dv%d" % (i, j, x))) for x in range(n)]) for y in range(n)]))
            # V vsaki vrstici se pojavi vsaka vrednost
            l.append(prop.Or(["r%dc%dv%d" % (j, x, i) for x in range(n)]))
            # V vsakem stolpcu se pojavi vsaka vrednost
            l.append(prop.Or(["r%dc%dv%d" % (x, j, i) for x in range(n)]))
    
        # V vsakem kvadratu se pojavi vsaka vrednost
        for j in range(r):
            for k in range(r):
                l.append(prop.Or(sum([["r%dc%dv%d" % (r*j+x, r*k+y, i) for x in range(r)] for y in range(r)], [])))
            
    return prop.And(l)

def solveSudoku(abc, d):
    """Reši sudoku z abecedo abc pri prireditvi logičnih spremenljivk,
    podani s slovarjem d."""
    n = len(abc)
    s = [[None]*n for i in range(n)]
    for k, v in d.items():
        if not v:
            continue
        i, j, c = [int(x) for x in re.match('^r([0-9]+)c([0-9]+)v([0-9]+)', k).groups()]
        s[i][j] = abc[c]
    return s
        
# Primer sudokuja - težavnost easy :)
sudoku = \
[[None, '8', None, '1', '6', None, None, None, '7'],
 ['1', None, '7', '4', None, '3', '6', None, None],
 ['3', None, None, '5', None, None, '4', '2', None],
 [None, '9', None, None, '3', '2', '7', None, '4'],
 [None, None, None, None, None, None, None, None, None],
 ['2', None, '4', '8', '1', None, None, '6', None],
 [None, '4', '1', None, None, '8', None, None, '6'],
 [None, None, '6', '7', None, '1', '9', None, '3'],
 ['7', None, None, None, '9', '6', None, '4', None]]
 
def hadamard(n):
    """Vrne logični izraz, ki je izpolnljiv, ko obstaja Hadamardova matrika
    reda n."""
    if n == 1:
        return prop.Literal("r0c0")
    if n % 2 == 1:
        return prop.Fls()
        
    # Prva vrstica in stolpec
    l = ["r0c0"]
    for i in range(1, n):
        l.append("r0c%d" % i)
        l.append("r%dc0" % i)
        
    # Štejemo resnične vrednosti XORa i-te in j-te vrstice
    for i in range(n):
        for j in range(i+1, n):
            # Resničnih je n/2
            l.append("r%dr%df%dn%d" % (i, j, n, n//2))
            # Pravili za prvega
            l.append("r%dr%df1n0" % (i, j))
            l.append(prop.Not("r%dr%df1n1" % (i, j)))
            for k in range(1, n):
                # Ali do indeksa k ni nobenega resničnega?
                l.append(iff("r%dr%df%dn0" % (i, j, k+1), prop.And("r%dr%df%dn0" % (i, j, k), iff("r%dc%d" % (i, k), "r%dc%d" % (j, k)))))
                if k < n//2:
                    # Ali so do indeksa k vsi resnični?
                    l.append(iff("r%dr%df%dn%d" % (i, j, k+1, k+1), prop.And("r%dr%df%dn%d" % (i, j, k, k), prop.Not(iff("r%dc%d" % (i, k), "r%dc%d" % (j, k))))))
                for m in range(min(k, n//2)):
                    # Ali je do indeksa k m+1 resničnih?
                    l.append(iff("r%dr%df%dn%d" % (i, j, k+1, m+1), prop.Or(prop.And("r%dr%df%dn%d" % (i, j, k, m), prop.Not(iff("r%dc%d" % (i, k), "r%dc%d" % (j, k)))), prop.And("r%dr%df%dn%d" % (i, j, k, m+1), iff("r%dc%d" % (i, k), "r%dc%d" % (j, k))))))
    return prop.And(l)

def makeHadamard(n, d):
    """Iz spremenljivk naredi Hadamardovo matriko."""
    return [[1 if d["r%dc%d" % (i, j)] else 0 for j in range(n)] for i in range(n)]
