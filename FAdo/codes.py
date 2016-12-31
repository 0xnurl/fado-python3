# -*- coding: utf-8 -*-
"""Code theory module

.. versionadded:: 1.0

.. *Authors:* Rogério Reis, Nelma Moreira & Stavros Konstantinidis

.. *This is part of FAdo project*   http://fado.dcc.fc.up.pt.

.. *Copyright:* 1999-2014 Rogério Reis & Nelma Moreira {rvr,nam}@dcc.fc.up.pt

.. This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as published
   by the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
   or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
   for more details.

   You should have received a copy of the GNU General Public License along
   with this program; if not, write to the Free Software Foundation, Inc.,
   675 Mass Ave, Cambridge, MA 02139, USA."""
from __future__ import absolute_import
from __future__ import unicode_literals
from __future__ import print_function
from __future__ import division
from future import standard_library
standard_library.install_aliases()
from builtins import range
from builtins import *
from builtins import object
import copy

from . import reex
from .common import *
from . import fio
from .transducers import SFT, infixTransducer, prefixTransducer, suffixTransducer, outfixTransducer, hypercodeTransducer
from . import fa
from . import fl


def fixedHierSubset(x, y):
    """ Returns whether x==y, or the fixed property with name x is a subset of y
    Currently (Jan 2015) the fixed properties names are   'UD_codes',
    'Prefix_codes', 'Suffix_codes', 'Infix_codes', 'Outfix_codes', 'Hypercodes'
    :param tuple x
    :param tuple y
    :rtype: bool
    """
    if x == y:
        return True
    if x[0] != 'Fixed' or y[0] != 'Fixed':
        return False
    if x[1] == 'Hypercodes' or y[1] == 'UD_codes':
        return True
    if x[1] == 'UD_codes' or y[1] == 'Hypercodes':
        return False
    if x[1] == 'Infix_codes':
        if y[1] == 'Outfix_codes':
            return False
        else:
            return True
    if x[1] == 'Outfix_codes':
        if y[1] == 'Infix_codes':
            return False
        else:
            return True
    if y[1] == 'Infix_codes' or y[1] == 'Outfix_codes':
        return False
    if x[1] == y[1]:
        return True
    else:
        return False


def isSubclass(p1, p2):
    """Which property (language class) is a subclass of the other (if any).
       It returns 1 if p1 is a subclass of p2; 2 if p2 is a subclass of p1;
       3 if they are equal; 0 otherwise
    :param IPTProp p1: an input preserving transducer property
    :param IPTProp p2: an input preserving transducer property
    :rtype: int    """

    def _lessEqualID(X, Y):
        """ Returns whether the property with ID X is a subset of that with ID Y.
        This is the case when X has a subset X1, say, such that each property named
        in X1 is  a subset of some property named in Y
        :param set X
        :param set Y
        :rtype: bool
        """
        YL = [y for y in Y]
        YDel = []
        for x in X:
            for y in YL:
                if fixedHierSubset(x, y):
                    YDel.append(y)
            YL = [y for y in YL if y not in YDel]
            if len(YL) == 0:
                return True
        return False

    if p1.Sigma != p2.Sigma:
        return 0
    if p1.ID <= p2.ID:
        if p2.ID <= p1.ID:
            return 3
        else:
            return 2
    if p2.ID <= p1.ID:
        return 1
    if _lessEqualID(p1.ID, p2.ID):
        return 1
    if _lessEqualID(p2.ID, p1.ID):
        return 2
    return 0


def unionOfIDs(X, Y):
    """ Returns the "union" of the two sets: property ID X and propoerty ID Y.
    The result is the set union minus any element in one set that names
    a property containing a property named in the other set
    :param set X
    :param set Y
    :rtype: set
    """
    Z = set() | X
    XL = [x for x in X]
    YL = [y for y in Y]
    while len(XL) > 0 and len(YL) > 0:
        x = XL.pop()
        YDel = []
        for j in range(0, len(YL)):
            y = YL[j]
            if fixedHierSubset(x, y):
                YDel.append(y)
            elif fixedHierSubset(y, x):
                Z.add(y)
                YDel.append(y)
                Z.remove(x)
                break
            else:
                pass
        YL = [y for y in YL if y not in YDel]
    return Z | set(YL)


class CodeProperty(object):
    """
    .. seealso:: K. Dudzinski and S. Konstantinidis: Formal descriptions of code properties: decidability, complexity,
       implementation. International Journal of Foundations of Computer Science 23:1 (2012), 67--85.

    :var Sigma: the alphabet"""
    def __init__(self, name, alph):
        if name is None:
            raise CodingTheoryError('new property must have a name')
        self.Sigma = alph
        self.ID = set()
        if type(name) is set:
            self.ID.update(name)
        else:
            self.ID.add(name)

    @abstractmethod
    def satisfiesP(self, aut):
        """Satisfaction of the property by the automaton language

        :param NFA|DFA aut: the automaton
        :rtype: bool"""
        pass

    @abstractmethod
    def notSatisfiesW(self, aut):
        """Return a witness of non-satisfaction of the property by the automaton language

        :param DFA|NFA aut: the automaton
        :return: word witness tuple
        :rtype: tuple"""
        pass

    @abstractmethod
    def maximalP(self, aut, U=None):
        """Tests if the language is maximal w.r.t. the property

        :param DFA|NFA U: Universe of permitted words (Sigma^* as default)
        :param DFA|NFA aut: the automaton
        :rtype: bool"""
        pass

    @abstractmethod
    def notMaximalW(self, aut, U=None):
        """Witness of non maximality

        :param DFA|NFA aut: the automaton
        :param DFA|NFA U: Universe of permitted words (Sigma^* as default)
        :return: a witness
        :rtype: str"""
        pass


class IPTProp(CodeProperty):
    """Input Preserving Transducer Property

    .. inheritance-diagram:: IPTProp

    :var SFT Aut: the transducer defining the property
    :var set Sigma: alphabet"""
    def __init__(self, aut, name=None):
        """ Constructor
        :param SFT aut: Input preserving transducer"""
        if name is None:
            name = aut.codeOfTransducer()
        super(IPTProp, self).__init__(name, aut.Sigma)
        self.Aut = aut

    def __and__(self, other):
        """ Conjunction of two properties

        :param IPTProp other: right hand operand
        :rtype: IPTProp """
        sub = isSubclass(self, other)
        if sub == 1 or sub == 3:
            return self
        if isinstance(other, IATProp):
            if sub == 2:
                return other
            nt = other.Aut.dup()
            n = nt.addState()
            nt.addInitial(n)
            nt.addFinal(n)
            for s in nt.Sigma:
                nt.addTransition(n, s, s, n)
            name = unionOfIDs(self.ID, other.ID)
            pty = IPTProp(self.Aut | nt, name)
            return pty
        else:
            if sub == 2:
                return other
            name = unionOfIDs(self.ID, other.ID)
            pty = IPTProp(self.Aut | other.Aut, name)
            return pty

    def notSatisfiesW(self, aut):
        """Return a witness of non-satisfaction of the property by the automaton language

        :param DFA|NFA aut: the automaton
        :return: word witness pair
        :rtype: tuple"""
        u, v, w = self.Aut.inIntersection(aut).outIntersection(aut).nonFunctionalW()
        if u == v:
            return u, w
        else:
            return u, v

    def satisfiesP(self, aut):
        """Satisfaction of the property by the automaton language

        :param DFA|NFA aut: the automaton
        :rtype: bool"""
        return self.notSatisfiesW(aut) == (None, None)

    def notMaximalW(self, aut, U=None):
        """Tests if the language is maximal w.r.t. the property

        :param DFA|NFA aut: the automaton
        :param DFA|NFA U: Universe of permitted words (Sigma^* as default)
        :rtype: bool
        :raises PropertyNotSatisfied: if not satisfied"""
        if not self.satisfiesP(aut):
            raise PropertyNotSatisfied("Property is not satisfied")
        l = (self.Aut.runOnNFA(aut) | self.Aut.inverse().runOnNFA(aut) | aut).__invert__()
        if U:
            l = l & U.toNFA()
        try:
            w = l.witness()
        except DFAEmptyDFA:
            w = None
        return w

    def maximalP(self, aut, U=None):
        """Tests if the language is maximal w.r.t. the property

        :param NFA aut: the automaton
        :param NFA U: Universe of permitted words (Sigma^* as default)
        :rtype: bool"""
        return self.notMaximalW(aut.toNFA(), U) is None


ErrDetectProp = IPTProp  # another name for IPTProp


class IATProp(IPTProp):
    """Input Altering Transducer Property

    .. inheritance-diagram:: IATProp"""

    def __and__(self, other):
        """ Conjunction of two properties

        :param IPTProp other: right hand operand
        :rtype: IPTProp """
        sub = isSubclass(self, other)
        if sub == 1 or sub == 3:
            return self
        if not isinstance(other, IATProp):
            if sub == 2:
                return other
            nt = self.Aut.dup()
            n = nt.addState()
            nt.addInitial(n)
            nt.addFinal(n)
            for s in nt.Sigma:
                nt.addTransition(n, s, s, n)
            name = unionOfIDs(self.ID, other.ID)
            pty = IPTProp(other.Aut | nt, name)
            return pty
        else:
            if sub == 2:
                return other
            name = unionOfIDs(self.ID, other.ID)
            pty = IATProp(self.Aut | other.Aut, name)
            return pty

    def notSatisfiesW(self, aut):
        """Return a witness of non-satisfaction of the property by the automaton language

        :param DFA|NFA aut: the automaton
        :return: word witness pair
        :rtype: tuple"""
        return self.Aut.inIntersection(aut).outIntersection(aut).nonEmptyW()


class TrajProp(IATProp):
    """Class of trajectoty properties

    .. inheritance-diagram:: TrajProp"""

    def __init__(self, aut, Sigma):
        """Constructor

        :param DFA|NFA aut: regular expression over {0,1}
        :param set Sigma: the alphabet"""
        super(TrajProp, self).__init__(self.trajToTransducer(aut, Sigma))

    @staticmethod
    def trajToTransducer(traj, Sigma):
        """ Input Altering Tranducer corresponding to a Trajectory

        :param NFA traj: trajectory language
        :param set Sigma: alphabet
        :rtype: SFT"""
        t = SFT()
        t.Sigma = Sigma
        for s, sn in enumerate(traj.States):
            no = t.stateIndex((sn, False), True)
            yes = t.stateIndex((sn, True), True)
            if s in traj.Final:
                t.addFinal(yes)
            if s in traj.Initial:
                t.addInitial(no)
            for b in traj.delta.get(s, {}):
                for c in Sigma:
                    for st in traj.delta[s][b]:
                        fNo = t.stateIndex((traj.States[st], False), True)
                        fYes = t.stateIndex((traj.States[st], True), True)
                        if b == "0":
                            t.addTransition(no, c, c, fNo)
                            t.addTransition(yes, c, c, fYes)
                        if b == "1":
                            t.addTransition(no, Epsilon, c, fYes)
                            t.addTransition(yes, Epsilon, c, fYes)
        return t


class FixedProp(CodeProperty):
    """ Abstract class for fixed properties """

    @abstractmethod
    def notSatisfiesW(self, aut):
        """Test whether the language is a code.

           :param DFA|NFA aut: the automaton
           :return: two different factorizations of the same word
           :rtype: tuple of list"""
        pass

    @abstractmethod
    def satisfiesP(self, aut):
        """Satisfaction of the property by the automaton language

        :param NFA|DFA aut: the automaton
        :rtype: bool"""
        pass

    @abstractmethod
    def maximalP(self, aut, U=None):
        """Tests if the language is maximal w.r.t. the property

        :param DFA|NFA U: Universe of permitted words (Sigma^* as default)
        :param DFA|NFA aut: the automaton
        :rtype: bool"""
        pass

    @abstractmethod
    def notMaximalW(self, aut, U=None):
        """Witness of non maximality

        :param DFA|NFA aut: the automaton
        :param DFA|NFA U: Universe of permitted words (Sigma^* as default)
        :return: a witness
        :rtype: str"""
        pass


class UDCodeProp(FixedProp):
    """ Uniquely decodable Code Property

    .. inheritance-diagram:: UDCodeProp"""

    def __init__(self, alphabet):
        super(UDCodeProp, self).__init__(('Fixed', 'UD_codes'), alphabet)

    def notSatisfiesW(self, aut):
        """Test whether the language is a code.

        :param DFA|NFA aut: the automaton
        :return: two different factorizations of the same word
        :rtype: tuple of list"""
        def _findFactors(w, m):
            l = []
            i1 = 0
            while True:
                j = m.find('1', i1)
                if j < 0:
                    break
                l.append(w[i1:j + 1])
                i1 = j + 1
            return l

        n = aut.toNFA()   # .eliminateEpsilonTransitions()
        for i in n.Initial:
            if i in n.Final:
                return [Epsilon], [Epsilon, Epsilon]
        t = SFT()
        t.States = copy.deepcopy(n.States)
        t.setInitial(n.Initial)
        t.setFinal(n.Initial)
        t.setSigma(n.Sigma)
        t.setOutput(['1', '0'])
        for si in n.delta:
            for sym in n.delta[si]:
                for so in n.delta[si][sym]:
                    if so not in n.Final:
                        t.addTransition(si, sym, '0', so)
                    else:
                        t.addTransition(si, sym, '0', so)
                        for ss in t.Initial:
                            t.addTransition(si, sym, '1', ss)
        t.trim()
        foo = t.nonFunctionalW()
        if foo == (None, None, None):
            return None, None
        else:
            return _findFactors(foo[0], foo[1]), _findFactors(foo[0], foo[2])

    def maximalP(self, aut, U=None):
        """Tests if the language is maximal w.r.t. the property
        :param DFA|NFA aut: the automaton
        :param DFA|NFA U: Universe of permitted words (Sigma^* as default)
        :rtype: bool"""
        t = infixTransducer(aut.Sigma, True)
        a = aut.dup().star()
        return (~(t.runOnNFA(a))).emptyP()

    def satisfiesP(self, aut):
        """Satisfaction of the code property by the automaton language

        :param DFA|NFA aut: the automaton
        :rtype: bool"""
        return self.notSatisfiesW(aut) == (None, None)


class PrefixProp(TrajProp, FixedProp):
    """ Prefix Property

    .. inheritance-diagram:: PrefixProp"""
    def __init__(self, t):
        name = ('Fixed','Prefix_codes')
        IATProp.__init__(self, t, name)

    def satisfiesPrefixP(self, aut):
        """Satisfaction of property by the automaton language: faster than satisfiesP

        :param DFA|NFA aut: the automaton
        :rtype: bool"""
        if isinstance(aut, fa.DFA):
            a = aut.dup()
            a.trim()
            for s in a.Final:
                if a.delta.get(s, {}):
                    return False
            return True
        else:
            return IATProp.satisfiesP(self, aut)


class SuffixProp(TrajProp, FixedProp):
    """ Suffix Property

    .. inheritance-diagram:: SuffixProp"""

    def __init__(self, t):
        name = ('Fixed','Suffix_codes')
        IATProp.__init__(self, t, name)


class InfixProp(PrefixProp, SuffixProp):
    """ Infix Property

    .. inheritance-diagram:: InfixProp"""

    def __init__(self, t):
        name = ('Fixed','Infix_codes')
        IATProp.__init__(self, t, name)


class OutfixProp(PrefixProp, SuffixProp):
    """ Outfix Property

    .. inheritance-diagram:: PrefixProp"""

    def __init__(self, t):
        name = ('Fixed','Outfix_codes')
        IATProp.__init__(self, t, name)


class HypercodeProp(InfixProp, OutfixProp):
    """ Hypercode Property

    .. inheritance-diagram:: PrefixProp"""

    def __init__(self, t):
        name = ('Fixed','Hypercodes')
        IATProp.__init__(self, t, name)


class ErrCorrectProp(ErrDetectProp):
    """ Error Correcting Property

    .. inheritance-diagram:: ErrCorrectProp"""
    def __init__(self, t):
        super(ErrCorrectProp, self).__init__(t)
        self.Name = "Error Correcting Codes"

    def notSatisfiesW(self, aut):
        """Satisfaction of the code property by the automaton language

        :param DFA|NFA aut: the automaton
        :rtype: tuple"""
        return self.Aut.inverse().outIntersection(aut).nonFunctionalW()

    def satisfiesP(self, aut):
        """Satisfaction of the property by the automaton language

        .. seealso:: S. Konstantinidis: Transducers and the Properties of Error-Detection, Error-Correction and
            Finite-Delay Decodability. Journal Of Universal Computer Science 8 (2002), 278-291.

        :param DFA|NFA aut: the automaton
        :rtype: bool"""
        return self.notSatisfiesW(aut) == (None, None, None)

    def notMaximalW(self, aut, U=None):
        """Tests if the language is maximal w.r.t. the property

        :param DFA|NFA aut: the automaton
        :param DFA|NFA U: Universe of permitted words (Sigma^* as default)
        :rtype: bool"""
        return ErrDetectProp(self.Aut.inverse().composition(self.Aut)).notMaximalW(aut, U)


def buildUDCodeProperty(alphabet):
    """Builds a UDCodeProp (from thin air ;-)

    :param set alphabet: alphabet
    :rtype: UDCodeProp"""
    return UDCodeProp(alphabet)


buildUDCodeProp = buildUDCodeProperty


def buildTrajPropS(regex, sigma):
    """Builds a TrajProp from a string regexp

    :param str regex: the regular expression
    :param set sigma: alphabet
    :rtype: TrajProp"""
    au = reex.str2regexp(regex).toNFA()
    return TrajProp(au, sigma)


def buildIATPropF(fname):
    """Builds a IATProp from a FAdo SFT file

    :param str fname: file name
    :rtype: IATProp"""
    t = fio.readOneFromFile(fname)
    return IATProp(t)


def buildIATPropS(s):
    """Builds a IATProp from a FAdo SFT string

    :param str s: string containing SFT
    :rtype: IATProp"""
    t = fio.readOneFromString(s)
    return IATProp(t)


def buildIPTPropF(fname):
    """Builds a IPTProp from a FAdo SFT file

    :param str fname: file name
    :rtype: IPTProp"""
    t = fio.readOneFromFile(fname)
    return IPTProp(t)


def buildIPTPropS(s):
    """Builds a IPTProp from a FAdo SFT string

    :param str s: file name
    :rtype: IPTProp"""
    t = fio.readOneFromString(s)
    return IPTProp(t)


def buildErrorDetectPropF(fname):
    """ Builds an Error Detecting Property

    :param str fname: file name
    :rtype: ErrDetectProp"""
    t = fio.readOneFromFile(fname)
    return IPTProp(t)


def buildErrorDetectPropS(s):
    """ Builds an Error Detecting Property from string

    :param str s: transducer string
    :rtype: ErrDetectProp"""
    t = fio.readOneFromString(s)
    return IPTProp(t)


def buildErrorCorrectPropF(fname):
    """ Builds an Error Correcting Property

    :param str fname: file name
    :rtype: ErrCorrectProp"""
    t = fio.readOneFromFile(fname)
    return ErrCorrectProp(t)


def buildErrorCorrectPropS(s):
    """ Builds an Error Correcting Property from string

    :param str s: transducer string
    :rtype: ErrCorrectProp"""
    t = fio.readOneFromString(s)
    return ErrCorrectProp(t)


def buildPrefixProperty(alphabet):
    """ Builds a Prefix Code Property

    :param set alphabet: alphabet
    :rtype: PrefixProp"""
    return PrefixProp(prefixTransducer(alphabet))


def buildSuffixProperty(alphabet):
    """ Builds a Suffix Code Property

    :param set alphabet: alphabet
    :rtype: PrefixProp"""
    return SuffixProp(suffixTransducer(alphabet))


def buildInfixProperty(alphabet):
    """ Builds a Suffix Code Property

    :param set alphabet: alphabet
    :rtype: PrefixProp"""
    return InfixProp(infixTransducer(alphabet))


def buildOutfixProperty(alphabet):
    """ Builds a Outfix Code Property

    :param set alphabet: alphabet
    :rtype: PrefixProp"""
    return OutfixProp(outfixTransducer(alphabet))


def buildHypercodeProperty(alphabet):
    """ Builds a Hypercode Property

    :param set alphabet: alphabet
    :rtype: PrefixProp"""
    return HypercodeProp(hypercodeTransducer(alphabet))


def createInputAlteringSIDTrans(n, sigmaSet):
    """Create an input-altering SID transducer based

    :param int n: max number of errors
    :param set sigmaSet: alphabet
    :return: a transducer representing the SID channel
    :rtype: SFT"""
    new = SFT()
    new.setSigma(sigmaSet)
    new.setOutput(sigmaSet)
    init = new.stateIndex((0, None), True)
    new.addInitial(init)
    for sy in new.Sigma:
        new.addTransition(init, sy, sy, init)
    i = 1
    while i <= n:
        d1 = new.stateIndex((i, None), True)
        new.addFinal(d1)
        for s in new.Sigma:
            new.addTransition(d1, s, s, d1)
            d = new.stateIndex((i, s), True)
            new.addFinal(d)
            if i == 1:
                new.addTransition(init, s, Epsilon, d)
                for s1 in new.Sigma - {s}:
                    new.addTransition(init, s, s1, d1)
            else:
                bar = new.stateIndex((i - 1, None))
                new.addTransition(bar, s, Epsilon, d1)
                new.addTransition(bar, Epsilon, s, d1)
                for s1 in new.Sigma:
                    foo = new.stateIndex((i - 1, s))
                    new.addTransition(foo, s1, Epsilon, d)
                    if s1 != s:
                        new.addTransition(bar, s, s1, d1)
                        new.addTransition(foo, Epsilon, s1, d1)
                        for s2 in new.Sigma:
                            new.addTransition(foo, s2, s1, d1)
            for s1 in new.Sigma - {s}:
                new.addTransition(d, s1, s1, d1)
        i += 1
    return new


def editDistanceW(auto):
    """Compute the edit distance of a given regular language accepted by the NFA via Input-altering transducer.

    .. attention::
       language should have at least two words

    .. seealso:: Lila Kari, Stavros Konstantinidis, Steffen Kopecki, Meng Yang. An efficient algorithm for computing
        the edit distance of a regular language via input-altering transducers. arXiv:1406.1041 [cs.FL]

    :param NFA auto: language recogniser
    :return: The edit distance of the given regular language plus a witness pair
    :rtype: tuple"""

    def _normalize(tr):
        tr.States = [(s1, s2, s3, s4) for (((s1, s2), s3), s4) in tr.States]

    def _addTNone(tr, au, n1, s1, si, so, symb1, symb2, l):
        for i1 in au.delta[si].get(symb1, []):
            for i2 in au.delta[so].get(symb2, []):
                new = tr.stateIndex((n1, None, i1, i2), True)
                l.add(new)
                if i1 in au.Final and i2 in au.Final:
                    tr.addFinal(new)
                tr.addTransition(s1, symb1, symb2, new)

    def _addT(tr, au, n1, s1, aa, si, so, symb1, symb2, l):
        for i1 in au.delta[si].get(symb1, []):
            for i2 in au.delta[so].get(symb2, []):
                new = tr.stateIndex((n1, aa, i1, i2), True)
                l.add(new)
                if i1 in au.Final and i2 in au.Final:
                    tr.addFinal(new)
                tr.addTransition(s1, symb1, symb2, new)

    def _noneLoops(tr, au, l):
        todo = copy.deepcopy(l)
        done = set()
        while todo:
            s = todo.pop()
            done.add(s)
            (a, _, s3, s4) = tr.States[s]
            for b in tr.Sigma:
                for i1 in au.delta[s3].get(b, []):
                    for i2 in au.delta[s4].get(b, []):
                        new = tr.stateIndex((a, None, i1, i2), True)
                        if i1 in au.Final and i2 in au.Final:
                            tr.addFinal(new)
                        if new not in done:
                            l.add(new)
                            todo.add(new)
                        tr.addTransition(s, b, b, new)

    def extendTrans(tr, au, lln, ll):
        """ Extend the transducer

        :param set ll: last level added states (not None)
        :param set lln: last level added states (None)
        :param SFT tr: the old transducer to be updated
        :param NFA au: the automaton recogize the regular language
        :return: last level added states lln, ll
        :rtype: tuple

        .. attention::
           NFA au must have its state names as indexes (renameStates())"""
        newll, newlln = set(), set()
        for s in lln:
            (m, _, s3, s4) = tr.States[s]
            for a in tr.Sigma:
                _addTNone(tr, au, m + 1, s, s3, s4, a, Epsilon, newlln)
                _addTNone(tr, au, m + 1, s, s3, s4, Epsilon, a, newlln)
                for b in tr.Sigma - {a}:
                    _addTNone(tr, au, m + 1, s, s3, s4, a, b, newlln)
        for s in ll:
            (m, a, s3, s4) = tr.States[s]
            for b in tr.Sigma:
                _addT(tr, au, m + 1, s, a, s3, s4, b, Epsilon, newll)
                if b != a:
                    _addTNone(tr, au, m + 1, s, s3, s4, Epsilon, b, newlln)
                    for c in tr.Sigma - {b}:
                        _addTNone(tr, au, m + 1, s, s3, s4, c, b, newlln)
        for s in newll:
            (m, a, s3, s4) = tr.States[s]
            for b in tr.Sigma - {a}:
                _addTNone(tr, au, m, s, s3, s4, b, b, newlln)
        _noneLoops(tr, au, newlln)
        return newlln, newll

    auto = auto.toNFA().renameStates().addEpsilonLoops()
    t = createInputAlteringSIDTrans(1, auto.Sigma).inIntersection(auto).outIntersection(auto)
    _normalize(t)
    lvn, lv = set(), set()
    for i in range(len(t.States)):
        n0, a0 = t.States[i][:2]
        if n0 != 0:
            if a0 is None:
                lvn.add(i)
            else:
                lv.add(i)
    errn = 1
    while True:
        w = t.nonEmptyW()
        if w != (None, None):
            return errn, w
        lvn, lv = extendTrans(t, auto, lvn, lv)
        errn += 1


def exponentialDensityP(aut):
    """ Checks if language density is exponential

    Using breadth first search (BFS)

    .. attention::
        aut should not have Epsilon transitions

    :param NFA aut: the representation of the language
    :rtype: bool"""
    import fractions
    from collections import deque

    def _listgcd(ll):
        if len(ll) == 1:
            return ll[0]
        return fractions.gcd(ll[0], _listgcd(ll[1:]))

    components = aut.trim().stronglyConnectedComponents()
    for c in components:
        if not len(c) == 1:
            g = aut.dup()
            g.deleteStates(list(set(g.indexList(g.States)) - set(c)))
            marked, levelNum, levelSym = [], [], []
            for _ in g.States:
                marked.append(False)
                levelNum.append([])
                levelSym.append([])
            v = g.States[0]
            queue = deque()
            queue.append(v)
            marked[g.stateIndex(v)] = True
            levelNum[g.stateIndex(v)].append(0)
            while len(queue):
                t = queue.popleft()
                symbols = [s for s in g.delta.get(g.stateIndex(t), {})]
                edges = [g.delta[g.stateIndex(t)][k] for k in symbols]
                for s in symbols:
                    if s not in levelSym[levelNum[g.stateIndex(t)][0]]:
                        levelSym[levelNum[g.stateIndex(t)][0]].append(s)
                for e in edges:
                    for o in e:
                        levelNum[o].append(levelNum[g.stateIndex(t)][0] + 1)
                        if not marked[o]:
                            marked[o] = True
                            queue.append(g.States[o])
            if [l for l in levelSym if len(l) > 1]:
                return True
            lengths = []
            for s in levelNum:
                first = s[0]
                for n in [m for m in s if m - first]:
                    lengths.append(n - first)
            d = _listgcd(lengths)
            if d == 1:
                return True
            pattern = ""
            for i in range(0, d):
                pattern = pattern + levelSym[i][0]
            for j in range(d, max(lengths)):
                if not levelSym[j][0] == pattern[j % d]:
                    return True
    return False


def long2base(n, q):
    """ Maps n to a list of digits corresponding to the base q representation of n in reverse order

    :param int n: a positive integer
    :param int q: base to represent n
    :return: list of q-ary 'digits', that is, elements of {0,1,..,q-1}
    :rtype: list"""
    lt = []
    while n > 0:
        lt.append(n % q)
        n /= q
    return lt


def list2string(lt, dy):
    """
    :param list lt: list of nonnegative integers from some set {0,1,...,q-1}
    :param dict dy: mapping from {0,1,...,q-1} to some alphabet symbols
    :return: string of symbols corresponding to the integers in lt
    :rtype: str"""
    return "".join([dy[i] for i in lt])


def notUniversalStatW(a, l, maxIter=20000):
    """ Tests statistically whether the NFA a is l-non-universal, by evaluating a on <= maxIter randomly chosen words of length l

    :type a: NFA
    :param int l: nonnegative integer
    :type maxIter: int
    :return: (w,i) where w is the word found at i-th try; or (None, i) after i tries
    :rtype: tuple"""
    if l == 0:  # first handle the case of the empty word
        if a.evalWordP(Epsilon):
            return None, 1
        else:
            return Epsilon, 1
    lt = [s for s in a.Sigma]
    # dictionary dy is used to refer to each alphabet symbol in lt using a numeric index
    dy = {i: lt[i] for i in range(0, len(lt))}
    q = len(lt)
    numWords = q ** l
    tmp = set()  # will remember in tmp the distinct words generated so far
    random.seed()
    for j in range(0, maxIter):
        # next pick one word out of the possible numWords of length l; specifically pick
        # the i-th one, where i is randomly chosen. For this, choose a random int n whose
        # base q representation is of the form '1d_1...d_l', where the l d's are digits
        # in {0,1,...,q-1}, so the desired number i is the one represented as 'd_1...d_l'
        n = random.randint(numWords, 2 * numWords - 1)
        w = list2string(long2base(n, q), dy)[:l]
        if not a.evalWordP(w):
            return w, j + 1
        tmp.add(w)  # Note: the current random word could be equal to a past one !!
        if len(tmp) == numWords:
            return None, numWords
    return None, maxIter


def symmAndRefl(t, ipt=False):
    """ Return the  transducer      t | t.inverse,  if ipt is True;
        return the transducer  t | t.inverse | id,  otherwise

    :type t: SFT
    :type ipt: bool
    :rtype: SFT"""
    t1 = t | t.inverse()
    if ipt is True:
        return t1
    t2 = SFT()
    s0 = t2.addState()
    t2.addInitial(s0)
    t2.addFinal(s0)
    for sym in t.Sigma:
        t2.addTransition(s0, sym, sym, s0)
    return t1 | t2


def constructCode(n, l, p, ipt=False, seed=None):
    """ Returns up to n words of length l satisfying the property p, the first one being seed.
        If ipt is True, the property is assumed to be input-preserving transducer type

    :type p: IATProp|IPTProp
    :type l: int
    :type n: int
    :type seed: str
    :type ipt: bool
    :rtype: list"""
    if n == 0:
        return []
    if l == 0:
        return [Epsilon]
    t = symmAndRefl(p.Aut, ipt)  # make a version of p.Aut that is symmetric and reflexive
    if seed is None or len(seed) != l:
        a0 = list(t.Sigma)[0]
        seed = "".join([a0 for _ in range(l)])
    lt = [seed]
    cnt, more = 1, True
    while more and cnt < n:
        a = fl.FL(lt).trieFA().toNFA()
        b = t.runOnNFA(a)
        (w, i) = notUniversalStatW(b, l)
        if w is None:
            more = False
        else:
            cnt += 1
            lt.append(w)
    return lt
