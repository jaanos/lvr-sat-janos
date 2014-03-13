#!/usr/bin/python
# -*- coding: utf-8 -*-

import re

# Združljivost za Python 2 in Python 3
try:
    basestring
except NameError:
    basestring = str

# Ali naj se seznami konjunktov in disjunktov sortirajo?
# Nastavi na list za nesortiranje
# Nastavi na sorted za sortiranje
sortSet = list

def paren(s, level, expl):
    """Postavi oklepaje okoli izraza.
    
    Vrne niz s, ko je level <= expl, niz s, obdan z oklepaji, sicer.
    
    Argumenti:
    s     -- niz za izpis
    level -- nivo postavljanja oklepajev
    exp   -- najmanjša vrednost argumenta level, da se izpišejo oklepaji
    
    """
    return s if level <= expl else '('+s+')'

def isLiteral(s):
    """Ugotovi, ali je s niz, ki predstavlja logično spremenljivko.
    
    Argument:
    s -- ime spremenljivke
    """
    return isinstance(s, basestring) and re.match(r'^[a-z][a-z0-9]*$', s)

def nnf(f):
    """Vrne izraz f v negacijski normalni obliki, torej brez implikacij
    in z negacijami samo neposredno na spremenljivkah.
    
    Argument:
    f -- logični izraz
    """
    return f.simplify()
    
def cnf(f):
    """Vrne izraz f v konjunktivni normalni obliki, torej kot konjunkcijo
    enega ali več disjunkcij spremenljivk in njihovih negacij.
    
    Argument:
    f -- logični izraz
    """
    return f.flatten().cnf()

def dnf(f):
    """Vrne izraz f v disjunktivni normalni obliki, torej kot disjunkcijo
    enega ali več konjunkcij spremenljivk in njihovih negacij.
    
    Argument:
    f -- logični izraz
    """
    return f.flatten().dnf()
    
def getValues(d, root=None, p=None):
    """Vrne prireditve vrednosti spremenljivkam.
    
    Če katera od spremenljivk nima vrednosti, vrne None. V nasprotnem primeru
    prireditve vrne v obliki slovarja.
    
    Argumenta:
    d    -- slovar podizrazov
    root -- koren grafa
    p    -- začetna predpostavka, privzeto None (trajna vrednost)
    """
    if root != None:
        if not root.getSure(p):
            return root
    val = {k.p: v.getValue(p) for (k, v) in d.items() if isinstance(k, Literal)}
    if root == None and None in val.values():
        return None
    else:
        return {k: v for (k, v) in val.items() if v != None}
    
def sat(f, d=None, root=False, trace=False):
    """Poskusi določiti izpolnljivost logične formule f s pomočjo linearnega
    algoritma.
    
    Če ugotovi, da formula ni izpolnljiva, vrne False.
    Če najde prireditev vrednosti spremenljivkam, da je formula izpolnljiva,
    jo vrne v obliki slovarja.
    Če ne ugotovi, ali je formula izpolnljiva, vrne None.
    
    Argumenti:
    f     -- logični izraz
    d     -- slovar podizrazov, privzeto None (naredi nov slovar)
    root  -- ali naj se vrne koren grafa v primeru neodločenosti
    trace -- ali naj se izpisuje sled dokazovanja, privzeto False
    """
    if not type(d) == dict:
        d = {}
    n = f.simplify().ncf().node(d)
    if not n.valuate(True, (None, 0), None, trace):
        return False
    out = getValues(d, n)
    if not root and type(out) != dict:
        return None
    else:
        return out
        
def sat3(f, d=None, root=False, trace=False):
    """Poskusi določiti izpolnljivost logične formule f s pomočjo kubičnega
    algoritma.
    
    Če ugotovi, da formula ni izpolnljiva, vrne False.
    Če najde prireditev vrednosti spremenljivkam, da je formula izpolnljiva,
    jo vrne v obliki slovarja.
    Če ne ugotovi, ali je formula izpolnljiva, vrne None.
    
    Argumenti:
    f     -- logični izraz
    d     -- slovar podizrazov, privzeto None (naredi nov slovar)
    root  -- ali naj se vrne koren grafa v primeru neodločenosti
    trace -- ali naj se izpisuje sled dokazovanja, privzeto False
    """
    if not type(d) == dict:
        d = {}
    rt = sat(f, d, True, trace)
    if rt == False or type(rt) == dict:
        return rt
    
    next = sum([[(n, k) for k in range(n.numVariants()) if n.v[k] == None] for n in d.values()], [])
    lt = len(next)
    ln = lt+1
    while lt < ln:
        todo = next
        next = []
        for n, k in todo:
            if n.v[k] != None:
                continue
            if trace > 1:
                print("Trying to assign temporary values to %d:%s" % (k, n))
            if n.valuate(True, (None, k), (True, k), trace):
                s = getValues(d, rt, True)
                if type(s) == dict:
                    return s
                if n.valuate(False, (None, k), (False, k), trace):
                    s = getValues(d, rt, False)
                    if type(s) == dict:
                        return s
                    for nn in d.values():
                        nn.clearTemp()
                else:
                    for nn in d.values():
                        for i in range(nn.numVariants()):
                            if nn.vt[i] != None:
                                nn.setValue(nn.vt[i], nn.ct[i], (None, i))
                        nn.clearTemp()
            else:
                for nn in d.values():
                    nn.clearTemp()
                if n.valuate(False, (None, k), (None, k), trace):
                    s = getValues(d, rt)
                    if type(s) == dict:
                        return s
                else:
                    return False
            if n.v[k] != None:
                next.append((n, k))
        ln = lt
        lt = len(next)
    if root:
        return rt
    else:
        False
    
def abbrev(p, s=None):
    """Vrne okrajšano obliko opisa stanja valuacije."""
    if type(p) == tuple:
        return '(%s,%d)' % (abbrev(p[0]), p[1])
    elif type(p) == list:
        return '[%s]' % ''.join([abbrev(x, s[i]) for i, x in enumerate(p)])
    elif p == True:
        return 'T' if s else 't'
    elif p == False:
        return 'F' if s else 'f'
    else:
        return 'N' if s else 'n'
    
class DAGNode:
    
    """Abstraktni razred vozlišča v usmerjenem acikličnem grafu (DAG).
    
    Metode:
    __init__    -- konstruktor
    __repr__    -- znakovna predstavitev
    init        -- inicializacija
    getValue    -- vrne ustrezno trenutno vrednost
    setValue    -- nastavi ustrezno trenutno vrednost
    getSure     -- ali vrednosti otrok zagotavljajo trenutno vrednost
    setSure     -- nastavi zagotovilo o trenutni vrednosti
    clearTemp   -- pobriše začasne oznake
    numVariants -- število variant podizrazov, ki jih je treba preveriti
    valuate     -- valuacija v dano logično vrednost
    parents     -- posodobitev stanja staršev
    update      -- posodobitev po spremembi stanja enega od otrok
    
    Spremenljivke:
    a  -- seznam prednikov
    v  -- trenutno znane vrednosti izraza
    vt -- začasne vrednosti ob predpostavki o veljavnosti začetnega vozlišča
    vf -- začasne vrednosti ob predpostavki o neveljavnosti začetnega vozlišča
    c  -- vozlišča, od katerega so prišle vrednosti izraza
    ct -- vozlišča, od katerega so prišle vrednosti izraza ob predpostavki o
          veljavnosti začetnega vozlišča
    cf -- vozlišča, od katerega so prišle vrednosti izraza ob predpostavki o
          neveljavnosti začetnega vozlišča
    s  -- ali vrednosti otrok zagotavljajo trenutno znane vrednosti
    st -- ali vrednosti otrok zagotavljajo trenutno znane začasne vrednosti
          ob predpostavki o veljavnosti začetnega vozlišča
    sf -- ali vrednosti otrok zagotavljajo trenutno znane začasne vrednosti
          ob predpostavki o neveljavnosti začetnega vozlišča
    """
    
    def __init__(self):
        """Konstruktor. Na abstraktnem razredu ga ne smemo klicati."""
        raise Exception('Instantiating an abstract class.')
        
    def __repr__(self):
        """Znakovna predstavitev."""
        return '%s(%s,%s)' % tuple([abbrev(x, y) for (x, y) in [(self.v, self.s), (self.vt, self.st), (self.vf, self.sf)]])
        
    def init(self):
        """Inicializacija vozlišča."""
        self.a = []
        self.v = [None]*self.numVariants()
        self.vt = [None]*self.numVariants()
        self.vf = [None]*self.numVariants()
        self.c = [None]*self.numVariants()
        self.ct = [None]*self.numVariants()
        self.cf = [None]*self.numVariants()
        self.s = [False]*self.numVariants()
        self.st = [False]*self.numVariants()
        self.sf = [False]*self.numVariants()
        
    def getValue(self, p=None):
        """Vrne trajno ali začasno vrednost izraza.
        
        Argument:
        p -- začetna predpostavka, privzeto None (trajna vrednost)
        """
        if type(p) == tuple:
            p, k = p
        else:
            k = 0
        if p == None:
            return self.v[k]
        elif p:
            return self.vt[k]
        else:
            return self.vf[k]
            
    def setValue(self, b, c=None, p=None):
        """Nastavi trajno ali začasno vrednost izraza. Če sta začasni
        vrednosti enaki, nastavi tudi trajno vrednost.
        
        Argumenti:
        b -- nastavljena vrednost
        c -- vozlišče, od katerega je prišla vrednost izraza, privzeto None
        p -- začetna predpostavka, privzeto None (trajna vrednost)
        """
        if type(p) == tuple:
            p, k = p
        else:
            k = 0
        if p == None:
            self.v[k] = b
            self.vt[k] = b
            self.vf[k] = b
            self.c[k] = c
        elif p:
            self.vt[k] = b
            self.ct[k] = c
            if self.vf[k] == b:
                self.v[k] = b
                self.c[k] = (c, self.cf[k])
        else:
            self.vf[k] = b
            self.cf[k] = c
            if self.vt[k] == b:
                self.v[k] = b
                self.c[k] = (self.ct[k], c)
                
    def getSure(self, p=None):
        """Pove, ali vrednosti otrok zagotavljajo trenutno vrednost.
        
        Argument:
        p -- začetna predpostavka, privzeto None (trajna vrednost)
        """
        if type(p) == tuple:
            p, k = p
        else:
            k = 0
        if p == None:
            return self.s[k]
        elif p:
            return self.st[k]
        else:
            return self.sf[k]
            
    def setSure(self, p=None, trace=False):
        """Nastavi zagotovilo o trenutni vrednosti. Če obstajata zagotovili
        o začasni vrednosti, nastavi zagotovilo o trajni vrednosti.
        
        Vrne True, če je zagotovilo novo, in False, če je že obstajalo.
        
        Argumenta:
        p     -- začetna predpostavka, privzeto None (trajna vrednost)
        trace -- ali naj se izpisuje sled dokazovanja, privzeto False
        """
        if type(p) == tuple:
            p, k = p
        else:
            k = 0
        if p == None:
            if self.s[k]:
                return False
            self.s[k] = True
            self.st[k] = True
            self.sf[k] = True
        elif p:
            if self.st[k]:
                return False
            self.st[k] = True
            if self.sf[k]:
                self.s[k] = True
        else:
            if self.sf[k]:
                return False
            self.sf[k] = True
            if self.st[k]:
                self.s[k] = True
        if trace > 3:
            print("Ensured at %s the value of the node %s" % (abbrev((p, k)), self))
        return True
                
    def clearTemp(self):
        """Pobriše začasne oznake."""
        for i in range(self.numVariants()):
            if self.v[i] == None:
                self.vt[i] = None
                self.vf[i] = None
                self.ct[i] = None
                self.cf[i] = None
                self.st[i] = False
                self.sf[i] = False
            
    def numVariants(self):
        """Vrne število variant podizrazov, ki jih je treba preveriti.
        
        Generična metoda, vrne 1."""
        return 1
        
    def valuate(self, b, c=None, p=None, trace=False):
        """Valuacija v logično vrednost b.
        
        Metodo kličejo nadomestne metode v dedujočih razredih. Če je vrednost
        že določena, pove, ali podana vrednost ustreza določeni. V nasprotnem
        primeru nastavi podano vrednost in vrne None. Tedaj sledi nadaljnja
        obdelava v klicoči metodi.
        
        Argumenti:
        b     -- nastavljena vrednost
        c     -- vozlišče, od katerega je prišla vrednost izraza, privzeto
                 None
        p     -- začetna predpostavka, privzeto None (trajna vrednost)
        trace -- ali naj se izpisuje sled dokazovanja, privzeto False
        """
        v = self.getValue(p)
        if v != None:
            if trace:
                if v != b:
                    print("Error valuating to %s:%s the node %s from %s" % (abbrev(p), abbrev(b), self, c))
                elif trace > 4:
                    print("Skipping valuation to %s:%s of the node %s" % (abbrev(p), abbrev(b), self))
            return v == b
        if trace > 2:
            print("Valuating to %s:%s the node %s" % (abbrev(p), abbrev(b), self))
        self.setValue(b, c, p)
        return None
        
    def parents(self, b, p=None, trace=False):
        """Posodobi starše po uspešni valuaciji v logično vrednost b.
        
        Vrne True, če so vse posodobitve uspele, in False sicer.
        
        Argumenti:
        b     -- nastavljena vrednost
        p     -- začetna predpostavka, privzeto None (trajna vrednost)
        trace -- ali naj se izpisuje sled dokazovanja, privzeto False
        """
        if type(p) == tuple:
            p, k = p
        else:
            k = 0
        for x in self.a:
            if type(x) == tuple:
                x, t = x
            else:
                t = 0
            if not x.update(b, (self, k), (p, t), trace):
                return False
        return True
        
    def update(self, b, c=None, p=None, trace=False):
        """Posodobi stanje po valuaciji enega od otrok v logično vrednost b.
        
        Generična metoda, ne spreminja stanja in vrne True.
        
        Argumenti:
        b     -- nastavljena vrednost otroka
        c     -- vozlišče, od katerega je prišla vrednost izraza, privzeto
                 None
        p     -- začetna predpostavka, privzeto None (trajna vrednost)
        trace -- ali naj se izpisuje sled dokazovanja, privzeto False
        """
        return True
        
class DAGLiteral(DAGNode):
    
    """Razred vozlišča v DAG, ki predstavlja logično spremenljivko.
    
    Deduje od razreda DAGNode.
    
    Nepodedovana spremenljivka:
    p -- ime spremenljivke
    """
    
    def __init__(self, d, p):
        """Konstruktor. Nastavi ime spremenljivke.
        
        Argumenta:
        d -- slovar podizrazov
        p -- ime spremenljivke
        """
        self.p = p
        self.init()
        
    def __repr__(self):
        """Znakovna predstavitev."""
        return '%s: %s' % (DAGNode.__repr__(self), self.p)
        
    def valuate(self, b, c=None, p=None, trace=False):
        """Valuacija v logično vrednost b.
        
        Valuacija uspe, če vrednost b ne nasprotuje že znani vrednosti.
        
        Argumenti:
        b     -- nastavljena vrednost
        c     -- vozlišče, od katerega je prišla vrednost izraza, privzeto
                 None
        p     -- začetna predpostavka, privzeto None (trajna vrednost)
        trace -- ali naj se izpisuje sled dokazovanja, privzeto False
        """
        if type(p) == tuple:
            p = p[0]
        self.setSure(p, trace)
        return DAGNode.valuate(self, b, c, p, trace) != False and self.parents(b, p, trace)

class DAGNot(DAGNode):
    
    """Razred vozlišča v DAG, ki predstavlja logično negacijo.
    
    Deduje od razreda DAGNode.
    
    Nepodedovana spremenljivka:
    t -- vozlišče, ki ustreza negiranemu izrazu
    """
    
    def __init__(self, d, t):
        """Konstruktor. Za negirani izraz poišče ali ustvari vozlišče
        ter se vanj doda kot starš.
        
        Argumenta:
        d -- slovar podizrazov
        t -- negirani izraz
        """
        self.t = t.node(d)
        self.t.a.append(self)
        self.init()
        
    def __repr__(self):
        """Znakovna predstavitev."""
        r = str(self.t)
        if len(r) > 100:
            r = '...'
        return "%s: ~(%s)" % (DAGNode.__repr__(self), r)
        
    def valuate(self, b, c=None, p=None, trace=False):
        """Valuacija v logično vrednost b.
        
        Valuacija uspe, če vrednost b ne nasprotuje že znani vrednosti in se
        negirani izraz uspešno valuira v nasprotno vrednost.
        
        Argumenti:
        b     -- nastavljena vrednost
        c     -- vozlišče, od katerega je prišla vrednost izraza, privzeto
                 None
        p     -- začetna predpostavka, privzeto None (trajna vrednost)
        trace -- ali naj se izpisuje sled dokazovanja, privzeto False
        """
        val = DAGNode.valuate(self, b, c, p, trace)
        if val == None:
            if type(p) == tuple:
                p = p[0]
            return self.t.valuate(not b, (self, 0), p, trace) and self.parents(b, p, trace)
        else:
            return val
        
    def update(self, b, c=None, p=None, trace=False):
        """Posodobi stanje po valuaciji otroka v logično vrednost b.
        
        Uspe, če uspe valuacija v nasprotno vrednost od b.
        
        Argumenti:
        b     -- nastavljena vrednost otroka
        c     -- vozlišče, od katerega je prišla vrednost izraza, privzeto
                 None
        p     -- začetna predpostavka, privzeto None (trajna vrednost)
        trace -- ali naj se izpisuje sled dokazovanja, privzeto False
        """
        if type(p) == tuple:
            p = p[0]
        sure = self.t.getSure(p) and self.setSure(p, trace)
        if b != None:
            b = not b
            val = DAGNode.valuate(self, b, c, p, trace)
            if val == False:
                return False
            elif val:
                b = None
        return (b == None and not sure) or self.parents(b, p, trace)

class DAGAnd(DAGNode):
    
    """Razred vozlišča v DAG, ki predstavlja logično konjunkcijo.
    
    Deduje od razreda DAGNode.
    
    Nepodedovana spremenljivka:
    l -- seznam vozlišč, ki ustrezajo konjunktom
    """
    
    def __init__(self, d, l):
        """Konstruktor. Za vsak konjunkt poišče ali ustvari vozlišče
        ter se doda kot starš dobljenemu vozlišču.
        
        Argumenta:
        d -- slovar podizrazov
        l -- seznam konjuktov
        """
        self.l = [x.node(d) for x in l]
        for i, x in enumerate(self.l):
            x.a.append((self, i))
        self.init()
        
    def __repr__(self):
        """Znakovna predstavitev."""
        r = ') /\\ ('.join([str(x) for x in self.l])
        if len(r) > 100:
            r = '%d conjuncts' % len(self.l)
        return '%s: (%s)' % (DAGNode.__repr__(self), r)
        
    def getValue(self, p=None):
        """Vrne trajno ali začasno vrednost izraza.
        
        Če hočemo vrednost zadnjega podizraza (dolžine 1), vrnemo vrednost zadnjega konjunkta.
        
        Argument:
        p -- začetna predpostavka, privzeto None (trajna vrednost)
        """
        if type(p) == tuple and p[1] == self.numVariants():
            return self.l[-1].getValue(p[0])
        else:
            return DAGNode.getValue(self, p)
            
    def numVariants(self):
        """Vrne število variant podizrazov, ki jih je treba preveriti.
        
        Vrne 1 ali število konjunktov minus 1."""
        return max(1, len(self.l)-1)
                            
    def valuate(self, b, c=None, p=None, trace=False):
        """Valuacija v logično vrednost b.
        
        Valuacija uspe, če vrednost b ne nasprotuje že znani vrednosti. Če je
        b resničen, se morajo še vsi konjunkti valuirati v True. V nasprotnem
        primeru preveri, ali je trenutna vrednost vsaj enega konjunkta različna
        od True. Če edini tak konjunkt še nima vrednosti, ga valuira v False.
        
        Argumenti:
        b     -- nastavljena vrednost
        c     -- vozlišče, od katerega je prišla vrednost izraza, privzeto
                 None
        p     -- začetna predpostavka, privzeto None (trajna vrednost)
        trace -- ali naj se izpisuje sled dokazovanja, privzeto False
        """
        val = DAGNode.valuate(self, b, c, p, trace)
        if val == None:
            if type(p) == tuple:
                p, k = p
            else:
                k = 0
                
            if len(self.l) == 0:
                if not b:
                    return False
                self.setSure(p, trace)
            elif len(self.l) == 1:
                if not self.l[0].valuate(b, (self, k), p, trace):
                    return False
            else:
                i = k
                if b:
                    while i < len(self.l)-1:
                        val = DAGNode.valuate(self, True, (self, k), (p, i+1), trace) if i < len(self.l)-2 else self.l[-1].valuate(True, (self, k), p, trace)
                        if val == False or not self.l[i].valuate(True, (self, k), p, trace):
                            return False
                        elif val:
                            break
                        i += 1
                else:
                    while i < len(self.l)-1:
                        if self.l[i].getValue(p):
                            val = DAGNode.valuate(self, False, (self, k), (p, i+1), trace) if i < len(self.l)-2 else self.l[-1].valuate(False, (self, k), p, trace)
                            if val == False:
                                return False
                            if val:
                                break
                        else:
                            if (self.getValue((p, i+1)) if i < len(self.l)-2 else self.l[-1].getValue(p)) and not self.l[i].valuate(False, (self, k), p, trace):
                                return False
                            break
                        i += 1
            if k > 0:
                return self.update(b, (self, k), (p, k-1), trace)
            else:
                return self.parents(b, p, trace)
        else:
            return val
            
    def update(self, b, c=None, p=None, trace=False):
        """Posodobi stanje po valuaciji enega od otrok v logično vrednost b.
        
        Če je b neresničen, se poskusi valuirati v False. Če je v nasprotnem
        primeru trenutna vrednost True, preveri, ali je trenutna vrednost vsaj
        enega konjunkta različna od True. Če edini tak konjunkt še nima
        vrednosti, ga valuira v False.
        
        Argumenti:
        b     -- nastavljena vrednost otroka
        c     -- vozlišče, od katerega je prišla vrednost izraza, privzeto
                 None
        p     -- začetna predpostavka, privzeto None (trajna vrednost)
        trace -- ali naj se izpisuje sled dokazovanja, privzeto False
        """
        if type(p) == tuple:
            p, k = p
        else:
            k = 0
        if len(self.l) <= 1:
            sure = True
        else:
            if b:
                if k == len(self.l)-1:
                    k -= 1
                    if self.getValue((p, k)) == False:
                        if not self.l[k].valuate(False, c, p, trace):
                            return False
                        else:
                            b = None
                    elif not self.l[k].getValue(p):
                        b = None
                elif (c[0] if type(c) == tuple else c) != self:
                    if self.getValue((p, k)) == False:
                        if not (self.valuate(False, c, (p, k+1), trace) if k < len(self.l)-2 else self.l[-1].valuate(False, c, p, trace)):
                            return False
                        else:
                            b = None
                    elif not (self.l[-1].getValue(p) if k == len(self.l)-2 else self.getValue((p, k+1))):
                        b = None
                else:
                    if self.getValue((p, k)) == False:
                        if not self.l[k].valuate(False, c, p, trace):
                            return False
                        else:
                            b = None
                    elif not self.l[k].getValue(p):
                        b = None
                sure = (self.l[-1].getSure(p) if k == len(self.l)-2 else self.getSure((p, k+1))) and self.l[k].getSure(p) and self.setSure((p, k), trace)
                while b != None:
                    val = DAGNode.valuate(self, True, c, (p, k), trace)
                    if val == False:
                        return False
                    elif val:
                        b = None
                    k -= 1
                    if k < 0:
                        break
                    if self.getValue((p, k)) == False:
                        if not self.l[k].valuate(False, c, p, trace):
                            return False
                        else:
                            b = None
                    elif not self.l[k].getValue(p):
                        b = None
                    sure = sure and self.l[k].getSure(p) and self.setSure((p, k), trace)
            else:
                if k == len(self.l)-1:
                    k -= 1
                sure = (self.l[-1].getValue(p) == False and self.l[-1].getSure(p)) if k == len(self.l)-2 else (self.getValue((p, k+1)) == False and self.getSure((p, k+1)))
                sure = (sure or (self.l[k].getValue(p) == False and self.l[k].getSure(p))) and self.setSure((p, k), trace)
                while b != None:
                    val = DAGNode.valuate(self, False, c, (p, k), trace)
                    if val == False:
                        return False
                    elif val:
                        b = None
                    k -= 1
                    if k < 0:
                        break
                    sure = (sure or (self.l[k].getValue(p) == False and self.l[k].getSure(p))) and self.setSure((p, k), trace)
        while sure and k >= 0:
            sure = self.l[k].getSure(p)
            if self.getValue((p, k)) == False:
                sure = sure or (self.l[-1].getValue(p) if k == len(self.l)-2 else self.getValue((p, k+1))) == False
            sure = sure and self.setSure((p, k), trace)
            k -= 1
        return (b == None and not sure) or self.parents(b, p, trace)
            
class LogicalFormula:
    
    """Abstraktni razred logičnih formul.
    
    Metode:
    __init__ -- konstruktor
    __hash__ -- zgostitev
    __repr__ -- znakovna predstavitev
    __eq__   -- relacija "je enak"
    __ne__   -- relacija "ni enak"
    __lt__   -- relacija "je manjši"
    __le__   -- relacija "je manjši ali enak"
    __gt__   -- relacija "je večji"
    __ge__   -- relacija "je večji ali enak"
    flatten  -- splošči izraz
    simplify -- poenostavi izraz
    cnf      -- pretvori v konjunktivno normalno obliko
    dnf      -- pretvori v disjunktivno normalno obliko
    ncf      -- pretvori v obliko z negacijami in konjunkcijami
    apply    -- vrne izraz glede na podane vrednosti spremenljivk
    node     -- vrne vozlišče v DAG, ki ustreza izrazu
    """
    
    def __init__(self):
        """Konstruktor. Na abstraktnem razredu ga ne smemo klicati."""
        raise Exception('Instantiating an abstract class.')
        
    def __hash__(self):
        """Zgostitev. Vrne zgostitev znakovne predstavitve."""
        return self.__repr__().__hash__()
        
    def __repr__(self, level=0):
        """Znakovna predstavitev.
        
        Argument:
        level -- nivo za postavljanje oklepajev, privzeto 0 (brez oklepajev)
        """
        return ""
        
    def __eq__(self, other):
        """Relacija "je enak".
        
        Zaradi dedovanja metode __hash__ je definirana kot negacija relacije
        "ni enak".
        """
        return not (self != other)
    
    def __ne__(self, other):
        """Relacija "ni enak".
        
        Podrazredi morajo povoziti to metodo.
        """
        return True
    
    def __lt__(self, other):
        """Relacija "je manjši".
        
        Podrazredi morajo povoziti to metodo.
        """
        return True
    
    def __le__(self, other):
        """Relacija "je manjši ali enak".
        
        Definirana je kot negacija relacije "je večji".
        """
        return not (self > other)
    
    def __gt__(self, other):
        """Relacija "je večji".
        
        Definirana je kot presek relacij "je večji ali enak" in "ni enak".
        """
        return self >= other and self != other
    
    def __ge__(self, other):
        """Relacija "je večji ali enak".
        
        Definirana je kot negacija relacije "je manjši".
        """
        return not (self < other)
        
    def flatten(self):
        """Splošči izraz.
        
        Generična metoda, vrne sebe.
        """
        return self
    
    def simplify(self):
        """Poenostavi izraz.
        
        Generična metoda, vrne sebe.
        """
        return self
        
    def cnf(self):
        """Pretvori v konjunktivno normalno obliko.
        
        Generična metoda, vrne sebe.
        """
        return self
    
    def dnf(self):
        """Pretvori v disjunktivno normalno obliko.
        
        Generična metoda, vrne sebe.
        """
        return self
        
    def ncf(self):
        """Pretvori v obliko z negacijami in konjunkcijami.
        
        Generična metoda, vrne sebe.
        """
        return self
        
    def apply(self, d):
        """Vrne izraz glede na podane vrednosti spremenljivk.
        
        Generična metoda, vrne sebe.
        
        Argument:
        d -- slovar vrednosti spremenljivk
        """
        return self
    
    def node(self, d):
        """Vrne vozlišče v DAG, ki ustreza izrazu.
        
        Generična metoda, javi napako.
        
        Argument:
        d -- slovar vozlišč za izraze
        """
        raise Exception('Not applicable in DAG.')

class Literal(LogicalFormula):
    
    """Logična spremenljivka.
    
    Deduje od razreda LogicalFormula.
    
    Spremenljivka:
    p -- ime spremenljivke
    """
    
    def __init__(self, p):
        """Konstruktor. Nastavi se ime spremenljivke, ki mora biti niz malih
        črk.
        
        Argument:
        p -- ime spremenljivke
        """
        if not isLiteral(p):
            raise Exception('Literals must be strings of lowercase letters!')
        self.p = p
        
    def __repr__(self, level=0):
        """Znakovna predstavitev. Ta je enaka imenu spremenljivke."""
        return paren(self.p, level, 6)
        
    def __ne__(self, other):
        """Relacija "ni enak".
        
        Spremenljivke se razlikujejo po svojem imenu.
        """
        return not isinstance(other, Literal) or self.p != other.p
        
    def __lt__(self, other):
        """Relacija "je manjši".
        
        Spremenljivke se razvrščajo po svojem imenu in so manjše od ostalih
        logičnih izrazov.
        """
        if isinstance(other, Literal):
            return self.p < other.p
        else:
            return isinstance(other, LogicalFormula)
                        
    def apply(self, d):
        """Vrne izraz glede na podane vrednosti spremenljivk.

        Nadomesti spremenljivko z vrednostjo iz slovarja, če ta obstaja.
        
        Argument:
        d -- slovar vrednosti spremenljivk
        """
        if self.p in d:
            if isLiteral(d[self.p]):
                return Literal(d[self.p])
            elif isinstance(d[self.p], bool):
                return Tru() if d[self.p] else Fls()
            elif isinstance(d[self.p], LogicalFormula):
                return d[self.p].flatten()
        return self
        
    def node(self, d):
        """Vrne vozlišče v DAG, ki ustreza izrazu.
        
        Če izraza še ni v slovarju d, naredi novo vozlišče in ga doda v slovar.
        
        Argument:
        d -- slovar vozlišč za izraze
        """
        if self not in d:
            n = DAGLiteral(d, self.p)
            d[self] = n
        return d[self]

class Not(LogicalFormula):
    
    """Logična negacija.
    
    Deduje od razreda LogicalFormula.
    
    Spremenljivka:
    t -- negirani izraz
    """
    
    def __init__(self, t):
        """Konstruktor. Nastavi se negirani izraz.
        
        Če je t veljaven niz, se negira spremenljivka s tem imenom.
        
        Argument:
        t -- negirani izraz
        """
        if isLiteral(t):
            t = Literal(t)
        elif not isinstance(t, LogicalFormula):
            raise Exception('Only logical formulas can be negated!')
        self.t = t
        
    def __repr__(self, level=0):
        """Znakovna predstavitev. Negacija se označi z znakom ~."""
        return paren('~'+self.t.__repr__(6), level, 6)
    
    def __ne__(self, other):
        """Relacija "ni enak".
        
        Negacije se ločijo po negiranem izrazu.
        """
        return not isinstance(other, Not) or self.t != other.t
        
    def __lt__(self, other):
        """Relacija "je manjši".
        
        Negacije se razvrščajo po negiranem izrazu in so manjše od ostalih
        logičnih izrazov, razen spremenljivk.
        """
        if isinstance(other, Not):
            return self.t < other.t
        else:
            return isinstance(other, LogicalFormula) and not isinstance(other, Literal)
            
    def flatten(self):
        """Splošči izraz.
        
        Izniči dvojne negacije in splošči podizraze."""
        if isinstance(self.t, Not):
            return self.t.t.flatten()
        elif isinstance(self.t, And):
            return Or([Not(x) for x in self.t.l]).flatten()
        elif isinstance(self.t, Or):
            return And([Not(x) for x in self.t.l]).flatten()
        else:
            return self

    def simplify(self):
        """Poenostavi izraz.
        
        Izniči dvojno negacijo ter porine negacijo v konjunkcijo ali
        disjunkcijo po de Morganovih zakonih.
        """
        if isinstance(self.t, Not):
            return self.t.t.simplify()
        elif isinstance(self.t, And):
            return Or([Not(x) for x in self.t.l]).simplify()
        elif isinstance(self.t, Or):
            return And([Not(x) for x in self.t.l]).simplify()
        else:
            return self
            
    def ncf(self):
        """Pretvori v obliko z negacijami in konjunkcijami.
        
        Izniči dvojno negacijo ter porine negacijo v  disjunkcijo po
        de Morganovih zakonih.
        """
        if isinstance(self.t, Not):
            return self.t.t.ncf()
        elif isinstance(self.t, Or):
            return And([Not(x).ncf() for x in self.t.l])
        else:
            return Not(self.t.ncf())
            
    def apply(self, d):
        """Vrne izraz glede na podane vrednosti spremenljivk.

        Aplikacijo naredi na negiranem izrazu, nato pa izvede poenostavitev.
        
        Argument:
        d -- slovar vrednosti spremenljivk
        """
        return Not(self.t.apply(d)).flatten()
        
    def node(self, d):
        """Vrne vozlišče v DAG, ki ustreza izrazu.
        
        Če izraza še ni v slovarju d, naredi novo vozlišče in ga doda v slovar.
        
        Argument:
        d -- slovar vozlišč za izraze
        """
        if self not in d:
            n = DAGNot(d, self.t)
            d[self] = n
        return d[self]
    
class And(LogicalFormula):
    
    """Logična konjunkcija.
    
    Deduje od razreda LogicalFormula.
    
    Spremenljivka:
    l -- seznam konjunktov
    """
    
    def __init__(self, *l):
        """Konstruktor. Nastavijo se konjunkti.
        
        Konjunkti so lahko podani kot argumenti, kot seznam ali kot
        logična konjunkcija. Če je kateri od konjunktov veljaven niz, se
        uporabi spremenljivka s tem imenom.
        
        Argumenti:
        *l -- konjunkti
        """
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
            self.l = l[:]
        
    def __repr__(self, level=0):
        """Znakovna predstavitev. Konjunkti so ločeni z znakoma /\. Prazna
        konjunkcija je logična resnica in se označi z znakom T."""
        if len(self.l) == 0:
            return paren('T', level, 6)
        elif len(self.l) == 1:
            return self.l[0].__repr__(level)
        else:
            return paren(' /\\ '.join([x.__repr__(6) for x in self.l]), level, 5)
    
    def __ne__(self, other):
        """Relacija "ni enak".
        
        Konjukcije se ločijo po seznamu konjunktov.
        """
        return not isinstance(other, And) or self.l != other.l
        
    def __lt__(self, other):
        """Relacija "je manjši".
        
        Konjukcije se razvrščajo po seznamu konjunktov in so manjše od
        disjunkcij.
        """
        if isinstance(other, And):
            return self.l < other.l
        else:
            return isinstance(other, LogicalFormula) and not isinstance(other, Literal) and not isinstance(other, Not)
            
    def flatten(self):
        """Splošči izraz."""
        if len(self.l) == 1:
            return self.l[0].flatten()
        else:
            l = sum([y.l if isinstance(y, And) else [y] for y in [x.flatten() for x in self.l]], [])
            if any([isinstance(x, Or) and len(x.l) == 0 for x in l]):
                return Fls()
            else:
                return And(l)
        
    def simplify(self):
        """Poenostavi izraz.
        
        Najprej splošči gnezdene konjunkcije med poenostavljenimi konjunkti.
        Če je konjunkt natanko eden, ga vrne, sicer pa poenostavi disjunkcije
        med konjunkti po pravilih absorpcije. Če je po teh poenostavitvah
        kateri od konjunktov prazna disjunkcija (tj. logična neresnica) ali se
        kateri od konjunktov pojavi še v negirani obliki, potem vrne logično
        neresnico. V nasprotnem primeru se konjunkti uredijo po določenem
        vrstnem redu.
        """
        l = sum([y.l if isinstance(y, And) else [y] for y in [x.simplify() for x in self.l]], [])
        if len(l) == 1:
            return l[0]
        else:
            l = set(l)
            l.difference_update([x for x in l if isinstance(x, Or) and any([y in x.l for y in l])])
            assorb = [(x, [y.t for y in l if isinstance(y, Not) and y.t in x.l] + [Not(y) for y in l if Not(y) in x.l]) for x in l if isinstance(x, Or)]
            remove = [x[0] for x in assorb if len(x[1]) > 0]
            add = [Or([y for y in x[0].l if y not in x[1]]).simplify() for x in assorb if len(x[1]) > 0]
            l.difference_update(remove)
            l.update(add)
            if len(l) == 1:
                return l.pop()
            if any([isinstance(x, Or) and len(x.l) == 0 for x in l]) or any([x.t in l for x in l if isinstance(x, Not)]):
                return Fls()
            return And(sortSet(l))
        
    def cnf(self):
        """Pretvori v konjunktivno normalno obliko.
        
        Vse konjunkte pretvori v konjunktivno normalno obliko.
        """
        return And([x.cnf() for x in self.l]).flatten()
        
    def dnf(self):
        """Pretvori v disjunktivno normalno obliko.
        
        Če je število konjunktov 0 ali 1, vrne sebe oziroma edinega konjunkta v
        disjunktivni normalni obliki. Sicer pretvori vse konjunkte v
        disjunktivno normalno obliko, nato pa po pravilih za distributivnost
        naredi disjunkcijo več konjunktov.
        """
        if len(self.l) == 0:
            return self
        elif len(self.l) == 1:
            return self.l[0].dnf()
        l = [x.dnf() for x in self.flatten().l]
        a = [x for x in l if not isinstance(x, Or)]
        d = [x for x in l if isinstance(x, Or)]
        if len(d) == 0:
            return And(a)
        else:
            return Or([And(a + [x] + d[1:]).dnf() for x in d[0].l]).flatten()
            
    def ncf(self):
        """Pretvori v obliko z negacijami in konjunkcijami.
        
        Vse konjunkte pretvori v obliko z negacijami in konjunkcijami.
        """
        return And([x.ncf() for x in self.l])
            
    def apply(self, d):
        """Vrne izraz glede na podane vrednosti spremenljivk.

        Aplikacijo naredi na vsakem konjunktu, nato pa izvede poenostavitev.
        
        Argument:
        d -- slovar vrednosti spremenljivk
        """
        return And([x.apply(d) for x in self.l]).flatten()
        
    def node(self, d):
        """Vrne vozlišče v DAG, ki ustreza izrazu.
        
        Če izraza še ni v slovarju d, naredi novo vozlišče in ga doda v slovar.
        
        Argument:
        d -- slovar vozlišč za izraze
        """
        if self not in d:
            n = DAGAnd(d, self.l)
            d[self] = n
        return d[self]
        
        
class Or(LogicalFormula):
    
    """Logična disjunkcija.
    
    Deduje od razreda LogicalFormula.
    
    Spremenljivka:
    l -- seznam disjunktov
    """
    
    def __init__(self, *l):
        """Konstruktor. Nastavijo se disjunkti.
        
        Disjunkti so lahko podani kot argumenti, kot seznam ali kot
        logična disjunkcija. Če je kateri od disjunktov veljaven niz, se
        uporabi spremenljivka s tem imenom.
        
        Argumenti:
        *l -- disjunkti
        """
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
            self.l = l[:]
        
    def __repr__(self, level=0):
        """Znakovna predstavitev. Disjunkti so ločeni z znakoma \/. Prazna
        disjunkcija je logična neresnica in se označi z znakom F."""
        if len(self.l) == 0:
            return paren('F', level, 6)
        elif len(self.l) == 1:
            return self.l[0].__repr__(level)
        else:
            return paren(' \\/ '.join([x.__repr__(5) for x in self.l]), level, 4)
        
    def __ne__(self, other):
        """Relacija "ni enak".
        
        Disjukcije se ločijo po seznamu disjunktov.
        """
        return not isinstance(other, Or) or self.l != other.l
        
    def __lt__(self, other):
        """Relacija "je manjši".
        
        Disjukcije se razvrščajo po seznamu konjunktov in so večje od ostalih
        logičnih izrazov.
        """
        return isinstance(other, Or) and self.l < other.l
        
    def flatten(self):
        """Splošči izraz."""
        if len(self.l) == 1:
            return self.l[0].flatten()
        else:
            l = sum([y.l if isinstance(y, Or) else [y] for y in [x.flatten() for x in self.l]], [])
            if any([isinstance(x, And) and len(x.l) == 0 for x in l]):
                return Tru()
            else:
                return Or(l)
        
    def simplify(self):
        """Poenostavi izraz.
        
        Najprej splošči gnezdene disjunkcije med poenostavljenimi disjunkti.
        Če je disjunkt natanko eden, ga vrne, sicer pa poenostavi konjunkcije
        med disjunkti po pravilih absorpcije. Če je po teh poenostavitvah
        kateri od disjunktov prazna konjunkcija (tj. logična resnica) ali se
        kateri od disjunktov pojavi še v negirani obliki, potem vrne logično
        resnico. V nasprotnem primeru se disjunkti uredijo po določenem
        vrstnem redu.
        """
        l = sum([y.l if isinstance(y, Or) else [y] for y in [x.simplify() for x in self.l]], [])
        if len(l) == 1:
            return l[0]
        else:
            l = set(l)
            l.difference_update([x for x in l if isinstance(x, And) and any([y in x.l for y in l])])
            assorb = [(x, [y.t for y in l if isinstance(y, Not) and y.t in x.l] + [Not(y) for y in l if Not(y) in x.l]) for x in l if isinstance(x, And)]
            remove = [x[0] for x in assorb if len(x[1]) > 0]
            add = [And([y for y in x[0].l if y not in x[1]]).simplify() for x in assorb if len(x[1]) > 0]
            l.difference_update(remove)
            l.update(add)
            if len(l) == 1:
                return l.pop()
            if any([isinstance(x, And) and len(x.l) == 0 for x in l]) or any([x.t in l for x in l if isinstance(x, Not)]):
                    return Tru()
            else:
                return Or(sortSet(l))
        
    def cnf(self):
        """Pretvori v konjunktivno normalno obliko.
        
        Če je število disjunktov 0 ali 1, vrne sebe oziroma edinega disjunkta v
        konjunktivni normalni obliki. Sicer pretvori vse disjunkte v
        konjunktivno normalno obliko, nato pa po pravilih za distributivnost
        naredi konjunkcijo več disjunktov.
        """
        if len(self.l) == 0:
            return self
        elif len(self.l) == 1:
            return self.l[0].cnf()
        l = [x.cnf() for x in self.flatten().l]
        a = [x for x in l if not isinstance(x, And)]
        d = [x for x in l if isinstance(x, And)]
        if len(d) == 0:
            return Or(a)
        else:
            return And([Or(a + [x] + d[1:]).cnf() for x in d[0].l]).flatten()
            
    def dnf(self):
        """Pretvori v disjunktivno normalno obliko.
        
        Vse disjunkte pretvori v disjunktivno normalno obliko.
        """
        return Or([x.dnf() for x in self.l]).flatten()
        
    def ncf(self):
        """Pretvori v obliko z negacijami in konjunkcijami.
        
        Negacije vseh disjunktov pretvori v obliko z negacijami in
        konjunkcijami ter vrne njihovo negirano konjunkcijo.
        """
        return Not(And([Not(x).ncf() for x in self.l]))
        
    def apply(self, d):
        """Vrne izraz glede na podane vrednosti spremenljivk.

        Aplikacijo naredi na vsakem disjunktu, nato pa izvede poenostavitev.
        
        Argument:
        d -- slovar vrednosti spremenljivk
        """
        return Or([x.apply(d) for x in self.l]).flatten()

class Implies(Or):
    
    """Logična implikacija, predstavljena kot disjunkcija konsekvensa z
    negacijo precedensa.
    
    Deduje od razreda Or.
    """
    
    def __init__(self, prec, cons):
        """Konstruktor. Nastavita se disjunkta.
                
        Argumenta:
        prec -- precedens
        cons -- konsekvens
        """
        if isLiteral(prec):
            prec = Literal(prec)
        if isLiteral(cons):
            cons = Literal(cons)
        if not isinstance(prec, LogicalFormula) or not isinstance(cons, LogicalFormula):
            raise Exception('Only logical formulas can be imply or be implied!')
        self.l = [Not(prec), cons]
        
    def __repr__(self, level=0):
        """Znakovna predstavitev. Precedens in konsekvens sta ločena z znakoma
        =>."""
        if len(self.l) == 2 and isinstance(self.l[0], Not):
            return paren(self.l[0].t.__repr__(2) + ' => ' + self.l[1].__repr__(1), level, 1)
        else:
            return Or.__repr__(self, level)
        
class Tru(And):
    
    """Logična resnica, predstavljena kot prazna konjunkcija.
    
    Deduje od razreda And.
    """
    
    def __init__(self):
        """Konstruktor. Nastavi se prazen seznam konjunktov."""
        self.l = []

class Fls(Or):
    
    """Logična neresnica, predstavljena kot prazna disjunkcija.
    
    Deduje od razreda Or.
    """
    
    def __init__(self):
        """Konstruktor. Nastavi se prazen seznam disjunktov."""
        self.l = []
