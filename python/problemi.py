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
                        l.append(prop.Literal("r%sc%sv%s" % (i, j, k)))
                    else:
                        l.append(prop.Not("r%sc%sv%s" % (i, j, k)))
            else:
                # Vsako polje ima natanko eno vrednost
                l.append(prop.Or([prop.And([("r%sc%sv%s" % (i, j, x) if x == y else prop.Not("r%sc%sv%s" % (i, j, x))) for x in range(n)]) for y in range(n)]))
            # V vsaki vrstici se pojavi vsaka vrednost
            l.append(prop.Or(["r%sc%sv%s" % (j, x, i) for x in range(n)]))
            # V vsakem stolpcu se pojavi vsaka vrednost
            l.append(prop.Or(["r%sc%sv%s" % (x, j, i) for x in range(n)]))
    
        # V vsakem kvadratu se pojavi vsaka vrednost
        for j in range(r):
            for k in range(r):
                l.append(prop.Or(sum([["r%sc%sv%s" % (r*j+x, r*k+y, i) for x in range(r)] for y in range(r)], [])))
            
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