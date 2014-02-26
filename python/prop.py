#!/usr/bin/python
# -*- coding: utf-8 -*-

import re

# Združljivost za Python 2 in Python 3
try:
    basestring
except NameError:
    basestring = str

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
    """Ugotovi, ali je s niz, ki predstavlja logično spremenljivko."""
    return isinstance(s, basestring) and re.match(r'^[a-z]+$', s)

def nnf(f):
    """Vrne izraz f v negacijski normalni obliki, torej brez implikacij
    in z negacijami samo neposredno na spremenljivkah.
    """
    return f.simplify()
    
def cnf(f):
    """Vrne izraz f v konjunktivni normalni obliki, torej kot konjunkcijo
    enega ali več disjunkcij spremenljivk in njihovih negacij.
    """
    return f.simplify().cnf()

def dnf(f):
    """Vrne izraz f v disjunktivni normalni obliki, torej kot disjunkcijo
    enega ali več konjunkcij spremenljivk in njihovih negacij.
    """
    return f.simplify().dnf()
    
def sat(f):
    """Poskusi določiti izpolnljivost logične formule f s pomočjo linearnega
    algoritma.
    
    Če ugotovi, da formula ni izpolnljiva, vrne False.
    Če najde prireditev vrednosti spremenljivkam, da je formula izpolnljiva,
    jo vrne v obliki slovarja.
    Če ne ugotovi, ali je formula izpolnljiva, vrne None.
    """
    d = {}
    if not f.simplify().ncf().node(d).valuate(True):
        return False
    val = {k.p: v.v for (k, v) in d.items() if isinstance(k, Literal)}
    if None in val.values():
        return None
    else:
        return val
    
class DAGNode:
    
    """Abstraktni razred vozlišča v usmerjenem acikličnem grafu (DAG).
    
    Metode:
    __init__ -- konstruktor
    valuate  -- valuacija v dano logično vrednost
    parents  -- posodobitev stanja staršev
    update   -- posodobitev po spremembi stanja enega od otrok
    
    Spremenljivke:
    a -- seznam prednikov
    v -- trenutno znana vrednost izraza
    """
    
    def __init__(self):
        """Konstruktor. Na abstraktnem razredu ga ne smemo klicati."""
        raise Exception('Instantiating an abstract class.')
        
    def valuate(self, b):
        """Valuacija v logično vrednost b.
        
        Metodo kličejo nadomestne metode v dedujočih razredih. Če je vrednost
        že določena, pove, ali podana vrednost ustreza določeni. V nasprotnem
        primeru nastavi podano vrednost in vrne None. Tedaj sledi nadaljnja
        obdelava v klicoči metodi.
        """
        if self.v != None:
            return self.v == b
        self.v = b
        return None
        
    def parents(self, b):
        """Posodobi starše po uspešni valuaciji v logično vrednost b.
        
        Vrne True, če so vse posodobitve uspele, in False sicer.
        """
        for x in self.a:
            if not x.update(b):
                return False
        return True
        
    def update(self, b):
        """Posodobi stanje po valuaciji enega od otrok v logično vrednost b.
        
        Generična metoda, ne spreminja stanja in vrne True."""
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
        self.a = []
        self.v = None
        
    def valuate(self, b):
        """Valuacija v logično vrednost b.
        
        Valuacija uspe, če vrednost b ne nasprotuje že znani vrednosti.
        """
        return DAGNode.valuate(self, b) != False

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
        self.a = []
        self.v = None
        
    def valuate(self, b):
        """Valuacija v logično vrednost b.
        
        Valuacija uspe, če vrednost b ne nasprotuje že znani vrednosti in se
        negirani izraz uspešno valuira v nasprotno vrednost.
        """
        val = DAGNode.valuate(self, b)
        if val == None:
            return self.t.valuate(not b) and self.parents(b)
        else:
            return val
        
    def update(self, b):
        """Posodobi stanje po valuaciji enega od otrok v logično vrednost b.
        
        Uspe, če uspe valuacija v nasprotno vrednost od b."""
        return self.valuate(not b)

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
        for x in self.l:
            x.a.append(self)
        self.a = []
        if len(l) == 0:
            self.v = True
        else:
            self.v = None
            
    def valuate(self, b):
        """Valuacija v logično vrednost b.
        
        Valuacija uspe, če vrednost b ne nasprotuje že znani vrednosti. Če je
        b resničen, se morajo še vsi konjuknti valuirati v True. V nasprotnem
        primeru preveri, ali je trenutna vrednost vsaj enega konjunkta različna
        od True. Če edini tak konjunkt še nima vrednosti, ga valuira v False.
        """
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
        """Posodobi stanje po valuaciji enega od otrok v logično vrednost b.
        
        Če je b neresničen, se poskusi valuirati v False. Če je v nasprotnem
        primeru trenutna vrednost True, preveri, ali je trenutna vrednost vsaj
        enega konjunkta različna od True. Če edini tak konjunkt še nima
        vrednosti, ga valuira v False.
        """
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
        if d.has_key(self.p):
            if isLiteral(d[self.p]):
                return Literal(d[self.p])
            elif isinstance(d[self.p], bool):
                return Tru() if d[self.p] else Fls()
            elif isinstance(d[self.p], LogicalFormula):
                return d[self.p].simplify()
        return self
        
    def node(self, d):
        """Vrne vozlišče v DAG, ki ustreza izrazu.
        
        Če izraza še ni v slovarju d, naredi novo vozlišče in ga doda v slovar.
        
        Argument:
        d -- slovar vozlišč za izraze
        """
        if not d.has_key(self):
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
        return Not(self.t.apply(d)).simplify()
        
    def node(self, d):
        """Vrne vozlišče v DAG, ki ustreza izrazu.
        
        Če izraza še ni v slovarju d, naredi novo vozlišče in ga doda v slovar.
        
        Argument:
        d -- slovar vozlišč za izraze
        """
        if not d.has_key(self):
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
            self.l = l
        
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
            if any([isinstance(x, Or) and len(x.l) == 0 for x in l]) or any([x.t in l for x in l if isinstance(x, Not)]):
                    return Fls()
            return And(sorted(l))
        
    def cnf(self):
        """Pretvori v konjunktivno normalno obliko.
        
        Vse konjunkte pretvori v konjunktivno normalno obliko.
        """
        return And([x.cnf() for x in self.l])
        
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
        l = [x.dnf() for x in self.l]
        if isinstance(l[0], Or):
            return Or([And([x] + l[1:]).dnf() for x in l[0].l]).simplify()
        elif len(l) == 2 and isinstance(l[1], Or):
            return Or([And([l[0], x]).dnf() for x in l[1].l]).simplify()
        else:
            return Or([And([l[0], x]) for x in Or(And(l[1:]).dnf()).l]).simplify()
            
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
        return And([x.apply(d) for x in self.l]).simplify()
        
    def node(self, d):
        """Vrne vozlišče v DAG, ki ustreza izrazu.
        
        Če izraza še ni v slovarju d, naredi novo vozlišče in ga doda v slovar.
        
        Argument:
        d -- slovar vozlišč za izraze
        """
        if not d.has_key(self):
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
            self.l = l
        
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
            if any([isinstance(x, And) and len(x.l) == 0 for x in l]) or any([x.t in l for x in l if isinstance(x, Not)]):
                    return Tru()
            else:
                return Or(sorted(l))
        
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
        l = [x.cnf() for x in self.l]
        if isinstance(l[0], And):
            return And([Or([x] + l[1:]).cnf() for x in l[0].l]).simplify()
        elif len(l) == 2 and isinstance(l[1], And):
            return And([Or([l[0], x]).cnf() for x in l[1].l]).simplify()
        else:
            return And([Or([l[0], x]) for x in And(Or(l[1:]).cnf()).l]).simplify()
            
    def dnf(self):
        """Pretvori v disjunktivno normalno obliko.
        
        Vse disjunkte pretvori v disjunktivno normalno obliko.
        """
        return Or([x.dnf() for x in self.l])
        
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
        return Or([x.apply(d) for x in self.l]).simplify()

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
