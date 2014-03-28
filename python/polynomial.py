#!/usr/bin/python
# -*- coding: utf-8 -*-

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
    """Vrne okrajšano obliko opisa stanja valuacije.
    
    Argumenta:
    p -- objekt za krajšanje
    s -- zagotovilo, privzeto None
    """
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
        while sure and k > 0:
            k -= 1
            sure = self.l[k].getSure(p)
            if self.getValue((p, k)) == False:
                sure = sure or (self.l[-1].getValue(p) if k == len(self.l)-2 else self.getValue((p, k+1))) == False
            sure = sure and self.setSure((p, k), trace)
        return (b == None and not sure) or self.parents(b, p, trace)