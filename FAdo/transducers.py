# -*- coding: utf-8 -*-
"""**Finite Tranducer Support**

Transducer manipulation.

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
from builtins import str
from builtins import zip
from builtins import range
from builtins import *
import copy
from exceptions import *

from . import fa
from . import common
from .common import *
from . import fl


class ZERO(Exception):
    """Simple exception for functionality testing algorithm"""
    pass


def _concat(xxx_todo_changeme2):
    (a, b) = xxx_todo_changeme2
    if a == Epsilon:
        return b
    elif b == Epsilon:
        return a
    else:
        return str(a) + str(b)


def concatN(x, y):
    """ Concatenation of tuples of words
    :param x: iterable
    :param y: iterable
    :return: iterable"""
    return tuple([_concat(a) for a in zip(x, y)])


def isLimitExceed(NFA0Delta, NFA1Delta):
    """Decide if the size of NFA0 and NFA1 exceed the limit.

    Size of NFA0 is denoted as N, and size of NFA1 is denoted as M. If N*N*M exceeds 1000000, return False,
    else return True. If bothNFA is False, then NFA0 should be NFA, and NFA1 should be Transducer. If both NFA is
    True, then NFA0 and NFA1 are both NFAs.

    :param dict NFA0Delta: NFA0's transition Delta
    :param dict NFA1Delta: NFA1's transition Delta
    :rtype: bool"""
    N = 0
    for s in list(NFA0Delta.keys()):
        for s1 in NFA0Delta[s]:
            N += len(NFA0Delta[s][s1])
    M = 0
    for s in list(NFA1Delta.keys()):
        for s1 in NFA1Delta[s]:
            M += len(NFA1Delta[s][s1])
    if N * N * M > 1000000:
        return True
    else:
        return False


class Transducer(fa.NFA):
    """Base class for Transducers

    .. inheritance-diagram:: Transducer"""
    def __init__(self):
        super(Transducer, self).__init__()
        self.Output = set()

    def succintTransitions(self):
        """ Collects the transition information in a concat way suitable for graphical representation.
        :rtype: list of tupples"""
        foo = dict()
        for s in self.delta:
            for c in self.delta[s]:
                for (oc, s1) in self.delta[s][c]:
                    k = (s, s1)
                    if k not in foo:
                        foo[k] = []
                    foo[k].append((c, oc))
        l = []
        for k in foo:
            cs = foo[k]
            s = "{0:s}/{1:s}".format(graphvizTranslate(str(cs[0][0])), graphvizTranslate(str(cs[0][1])))
            for c in cs[1:]:
                s += ", {0:s}/{1:s}".format(graphvizTranslate(str(c[0])), graphvizTranslate(str(c[1])))
            l.append((str(self.States[k[0]]), str(self.States[k[1]]), s))
        return l

    def setOutput(self, listOfSymbols):
        """ Set Output

        :param set|list listOfSymbols: output symbols"""
        self.Output = set(list(listOfSymbols))


class GFT(Transducer):
    """General Form Transducer

    .. inheritance-diagram:: GFT"""

    def __init__(self):
        super(GFT, self).__init__()
        self.Output = set()

    def __str__(self):
        """Return a string representing the details of the current transducer instance.

        :rtype: str"""
        return str((self.States, self.Sigma, self.Output, self.Initial, self.Final, self.delta))

    def __repr__(self):
        """Return a string adding type 'Transducer' in front of the representation

        :rtype: str"""
        return 'Transducer(%s)' % self.__str__()

    def addTransition(self, stsrc, wi, wo, sti2):
        """Adds a new transition

        :param int stsrc: state index of departure
        :param int sti2: state index of arrival
        :param str wi: word consumed
        :param str wo: word outputed"""
        if wi != Epsilon:
            for sym in wi:
                self.Sigma.add(sym)
        if wo != Epsilon:
            for sym in wo:
                self.Output.add(sym)
        if stsrc not in self.delta:
            self.delta[stsrc] = {wi: {(wo, sti2)}}
        elif wi not in self.delta[stsrc]:
            self.delta[stsrc][wi] = {(wo, sti2)}
        else:
            self.delta[stsrc][wi].add((wo, sti2))

    def toSFT(self):
        """Conversion to an equivalent SFT

        rtype: SFT """
        new = SFT()
        new.setSigma(self.Sigma)
        new.Output = set(self.Output)
        new.States = copy.deepcopy(self.States)
        new.setInitial(self.Initial)
        new.setFinal(self.Final)
        for st1 in self.delta:
            for wi in self.delta[st1]:
                cst = st1
                if wi == Epsilon:
                    for (wo, st2) in self.delta[st1][wi]:
                        lst = st2
                        if wo == Epsilon:
                            new.addTransition(cst, wi, wo, lst)
                        else:
                            for i in wo[:-1]:
                                mst = new.addState()
                                new.addTransition(cst, Epsilon, i, mst)
                                cst = mst
                            new.addTransition(cst, Epsilon, wo[-1:], lst)
                else:
                    for (wo, st2) in self.delta[st1][wi]:
                        lst = st2
                        if wo == Epsilon:
                            for i in wi[:-1]:
                                mst = new.addState()
                                new.addTransition(cst, i, Epsilon, mst)
                                cst = mst
                            new.addTransition(cst, wi[-1:], Epsilon, lst)
                        else:
                            z = list(zip(wi, wo))
                            n = len(wi)
                            m = len(wo)
                            if n > m:
                                z += list(zip(wi[m:], [Epsilon] * (n - m)))
                            elif m > n:
                                z += list(zip([Epsilon] * (m - n), wo[n:]))
                            n = len(z)
                            for (symi, symo) in z[:n - 1]:
                                mst = new.addState()
                                new.addTransition(cst, symi, symo, mst)
                                cst = mst
                            new.addTransition(cst, z[n - 1][0], z[n - 1][1], lst)
        return new

    def listOfTransitions(self):
        """ Collects into a sorted list the transitions of the transducer.
        :param GFT t
        :rtype: set of tuples"""
        def _comp(v1, v2):
            (v11, v12, v13, v14) = v1
            (v21, v22, v23, v24) = v2
            if v11 < v21:
                return -1
            if v11 > v21:
                return 1
            if v12 < v22:
                return -1
            if v12 > v22:
                return 1
            if v13 < v23:
                return -1
            if v13 > v23:
                return 1
            return 0

        trList = []
        for s in self.delta:
            for c in self.delta[s]:
                for (oc, s1) in self.delta[s][c]:
                    trList.append((s, c, oc, s1))
        trList.sort(_comp)
        return trList

    def codeOfTransducer(self):
        """ Appends into one string the codes of the alphabets and initial and final
        state sets and the set of transitions
        :param GFT t
        :rtype: tuple"""

        def _codeOfSet(S):
            """ Collects into a sorted list the elements of the set S and then
                returns the string representation of the list. The set S normally
                consists of integers or strings
            :param set S
            :rtype: str"""
            L = [x for x in S]
            L.sort()
            return str(L)

        return ('GFT', _codeOfSet(self.Sigma) + _codeOfSet(self.Output) + _codeOfSet(self.Initial) +\
               _codeOfSet(self.Final) + str(self.listOfTransitions()))


class SFT(GFT):
    """Standard Form Tranducer

    :var set Output: output alphabet

    .. inheritance-diagram:: SFT"""
    def __str__(self):
        """Return a string representing the details of the current transducer instance.

        :rtype: str"""
        return str((self.States, self.Sigma, self.Output, self.Initial, self.Final, self.delta))

    def __repr__(self):
        """Return a string adding type 'Transducer'in front of the representation

        :rtype: str"""
        return 'SFT(%s)' % self.__str__()

    def dup(self):
        """Duplicate of itself
        :rtype: SFT

        .. attention::
           only duplicates the initially connected component"""
        new = SFT()
        for si in self.delta:
            for syi in self.delta[si]:
                for (syo, so) in self.delta[si][syi]:
                    i1 = new.stateIndex(self.States[si], True)
                    i2 = new.stateIndex(self.States[so], True)
                    new.addTransition(i1, syi, syo, i2)
        for si in self.Initial:
            try:
                i1 = new.stateIndex(self.States[si])
            except common.DFAstateUnknown:
                continue
            new.addInitial(i1)
        for si in self.Final:
            try:
                i1 = new.stateIndex(self.States[si])
            except common.DFAstateUnknown:
                continue
            new.addFinal(i1)
        return new

    def deleteStates(self, lstates):
        """Delete given iterable collection of states from the automaton.

        :param set|list lstates: collection of int representing states"""
        for s in lstates:
            self.deleteState(self.stateIndex(s))

    def deleteState(self, sti):
        """Remove given state and transitions related with that state.

        :param int sti: index of the state to be removed
        :raises DFAstateUnknown: if state index does not exist"""
        if sti >= len(self.States):
            raise DFAstateUnknown(sti)
        if sti in self.delta:
            del self.delta[sti]
        for j in list(self.delta.keys()):
            for sym in list(self.delta[j].keys()):
                self._deleteRefInDelta(j, sym, sti)
        if sti in self.Final:
            self.Final.remove(sti)
        self._deleteRefInitial(sti)
        for s in self.Final:
            if sti < s:
                self.Final.remove(s)
                self.Final.add(s - 1)
        for j in range(sti + 1, len(self.States)):
            if j in self.delta:
                self.delta[j - 1] = self.delta[j]
                del self.delta[j]
        del self.States[sti]

    def toSFT(self):
        """Pacifying rule

        :rtype: SFT"""
        return self

    def toNFT(self):
        """ Transformation into Nomal Form Transducer

        :rtype: NFT"""
        new = NFT()
        new.setSigma(self.Sigma)
        new.setOutput(self.Output)
        new.States = copy.deepcopy(self.States)
        for s in list(self.delta.keys()):
            if s in self.Initial:
                new.addInitial(s)
            if self.finalP(s):
                new.addFinal(s)
            for sy in self.delta[s]:
                for syo, so in self.delta[s][sy]:
                    if sy == Epsilon or syo == Epsilon:
                        new.addTransition(s, sy, syo, so)
                    else:
                        ns = new.addState()
                        new.addTransition(s, sy, Epsilon, ns)
                        new.addTransition(ns, Epsilon, syo, so)
        return new

    def _deleteRefInDelta(self, src, sym, dest):
        """Deletion of a reference in Delta

        :param int src: source state
        :param int sym: symbol
        :param int dest: destination state"""
        foo = [(s1, s2) for (s1, s2) in self.delta[src][sym] if s2 < dest]
        bar = [(s1, s2 - 1) for (s1, s2) in self.delta[src][sym] if s2 > dest]
        ff = set(foo + bar)
        if not ff:
            del self.delta[src][sym]
            if not self.delta[src]:
                del self.delta[src]
        else:
            self.delta[src][sym] = ff

    def delTransition(self, sti1, sym, symo, sti2, _no_check=False):
        """Remove a transition if existing and perform cleanup on the transition function's internal data structure.

        :param symo: symbol output
        :param int sti1: state index of departure
        :param int sti2: state index of arrival
        :param sym: symbol consumed
        :param bool _no_check: dismiss secure code"""
        self.delta[sti1][sym].remove((symo, sti2))
        if not self.delta[sti1][sym]:
            del(self.delta[sti1][sym])
        if not self.delta[sti1]:
            del(self.delta[sti1])

    def trim(self):
        """Remove states that do not lead to a final state, or, inclusively,
        that can't be reached from the initial state. Only useful states
        remain.

        .. attention::
           in place transformation"""
        n = self.toInNFA()
        n.trim()
        diff = [x for x in self.States if x not in n.States]
        self.deleteStates(diff)
        return self

    def addTransitionQ(self, src, dest, sym, out, futQ, pastQ):
        """Add transition to the new transducer instance.

        :param src: source state
        :param dest: destination state
        :param sym: symbol
        :param out: output
        :param set futQ: queue for later
        :param set pastQ: past queue"""
        if dest not in pastQ:
            futQ.add(dest)
        i = self.stateIndex(dest, True)
        self.addTransition(src, sym, out, i)

    def outputS(self, s):
        """Output label coming out of the state i

        :param int s: index state
        :rtype: set"""
        return {x for z in [y for y in self.delta.get(s, [])] for (x, _) in self.delta[s][z]}

    def setInitial(self, sts):
        """Sets the initial state of a Transducer

        :param list sts: list of states"""
        self.Initial = set(sts)

    def addOutput(self, sym):
        """Add a new symbol to the output alphabet

        There is no problem with duplicate symbols because Output is a Set. No symbol Epsilon can be added

        :param str sym: symbol or regular expression to be added"""
        if sym == Epsilon:
            raise common.DFAepsilonRedefinition()
        self.Output.add(sym)

    def addTransition(self, stsrc, symi, symo, sti2):
        """Adds a new transition

        :param int stsrc: state index of departure
        :param int sti2: state index of arrival
        :param str symi: symbol consumed
        :param str symo: symbol output"""
        if symi != Epsilon:
            self.Sigma.add(symi)
        if symo != Epsilon:
            self.Output.add(symo)
        if stsrc not in self.delta:
            self.delta[stsrc] = {symi: {(symo, sti2)}}
        elif symi not in self.delta[stsrc]:
            self.delta[stsrc][symi] = {(symo, sti2)}
        else:
            self.delta[stsrc][symi].add((symo, sti2))

    def __or__(self, other):
        """ infix version of union

        :param other: other operand
        :rtype: SFT"""
        return self.union(other)

    def union(self, other):
        """Union of the two transducers

        :param SFT other: the other operand
        :rtype: SFT"""
        new = SFT()
        for sti in self.delta:
            for syi in self.delta[sti]:
                for (syo, sto) in self.delta[sti][syi]:
                    nsti = (0, self.States[sti])
                    isti = new.stateIndex(nsti, True)
                    nsto = (0, self.States[sto])
                    isto = new.stateIndex(nsto, True)
                    new.addTransition(isti, syi, syo, isto)
        for sti in self.Initial:
            new.addInitial(new.stateIndex((0, self.States[sti]), True))
        for sti in self.Final:
            new.addFinal(new.stateIndex((0, self.States[sti]), True))
        for sti in other.delta:
            for syi in other.delta[sti]:
                for (syo, sto) in other.delta[sti][syi]:
                    nsti = (1, other.States[sti])
                    isti = new.stateIndex(nsti, True)
                    nsto = (1, other.States[sto])
                    isto = new.stateIndex(nsto, True)
                    new.addTransition(isti, syi, syo, isto)
        for sti in other.Initial:
            new.addInitial(new.stateIndex((1, other.States[sti])))
        for sti in other.Final:
            new.addFinal(new.stateIndex((1, other.States[sti])))
        return new

    def concat(self, other):
        """Concatenation of transducers

        :param SFT other: the other operand
        :rtype: SFT"""
        new = SFT()
        for sti in self.delta:
            for syi in self.delta[sti]:
                for (syo, sto) in self.delta[sti][syi]:
                    nsti = (0, self.States[sti])
                    isti = new.stateIndex(nsti, True)
                    nsto = (0, self.States[sto])
                    isto = new.stateIndex(nsto, True)
                    new.addTransition(isti, syi, syo, isto)
        for sti in self.Initial:
            new.addInitial(new.stateIndex((0, self.States[sti]), True))
        for sti in other.delta:
            for syi in other.delta[sti]:
                for (syo, sto) in other.delta[sti][syi]:
                    nsti = (1, other.States[sti])
                    isti = new.stateIndex(nsti, True)
                    nsto = (1, other.States[sto])
                    isto = new.stateIndex(nsto, True)
                    new.addTransition(isti, syi, syo, isto)
        for sti in other.Final:
            new.addFinal(new.stateIndex((1, other.States[sti]), True))
        for sti in self.Final:
            for sto in other.Initial:
                new.addTransition(new.stateIndex((0, self.States[sti])),
                                  Epsilon, Epsilon,
                                  new.stateIndex((1, other.States[sto])))
        return new

    def star(self, flag=False):
        """Kleene star

        :param bool flag: plus instead of star
        :returns: the resulting Transducer
        :rtype: SFT"""
        new = SFT()
        for sti in self.delta:
            for syi in self.delta[sti]:
                for (syo, sto) in self.delta[sti][syi]:
                    nsti = (0, self.States[sti])
                    isti = new.stateIndex(nsti, True)
                    nsto = (0, self.States[sto])
                    isto = new.stateIndex(nsto, True)
                    new.addTransition(isti, syi, syo, isto)
        stin = new.addState('Initial')
        new.addInitial(stin)
        for so in self.Initial:
            iso = new.stateIndex((0, self.States[so]))
            new.addTransition(stin, Epsilon, Epsilon, iso)
        for so in self.Final:
            iso = new.stateIndex((0, self.States[so]))
            new.addTransition(iso, Epsilon, Epsilon, stin)
            new.addFinal(iso)
        if not flag:
            new.addFinal(stin)
        return new

    def toInNFA(self):
        """Delete the output labels in the transducer. Translate it into an NFA

        :rtype: NFA"""
        aut = fa.NFA()
        aut.setSigma(self.Sigma)
        aut.States = copy.copy(self.States)
        aut.setInitial(self.Initial)
        aut.setFinal(self.Final)
        for s in list(self.delta.keys()):
            aut.delta[s] = {}
            for c in self.delta[s]:
                aut.delta[s][c] = set([x for (_, x) in self.delta[s][c]])
        return aut

    def toOutNFA(self):
        """Returns the result of considering the output symbols of the transducer as input symbols of a NFA (ignoring
        the input symbol, thus)

        :return: the NFA
        :rtype: NFA"""
        return self.inverse().toInNFA()

    def runOnWord(self, word):
        """Returns the automaton accepting the outup of the transducer on the input word

        :param word: the word
        :rtype: NFA"""
        lang = fl.FL([word])
        return self.runOnNFA(lang.trieFA().toNFA())

    def __and__(self, other):
        return self.inIntersection(other)

    def inIntersection(self, other):
        """ Conjunction of transducer and automata: X & Y.

        :param DFA|NFA other: the automata needs to be operated.
        :rtype: SFT"""
        if isinstance(other, fa.DFA):
            nother = other.toNFA().renameStates()
        elif isinstance(other, fa.NFA):
            nother = other.renameStates()
        else:
            raise common.FAdoGeneralError("Incompatible objects")
        et, en = self.epsilonP(), nother.epsilonP()
        if en:
            par1 = self.dup()
            par1.addEpsilonLoops()
        else:
            par1 = self
        if et:
            par2 = nother.dup()
            par2.addEpsilonLoops()
        else:
            par2 = nother
        new = par1.productInput(par2)
        for x in [(par1.States[a], par2.States[b]) for a in par1.Final for b in par2.Final]:
            if x in new.States:
                new.addFinal(new.stateIndex(x))
        return new

    def productInput(self, other):
        """Returns a transducer (skeleton) resulting from the execution of the transducer with the automaton as
        filter on the input.

        :param NFA other: the automaton used as filter
        :rtype: SFT"""
        new = SFT()
        new.setSigma(self.Sigma.union(other.Sigma))
        notDone = set()
        done = set()
        for s1 in [self.States[x] for x in self.Initial]:
            for s2 in [other.States[x] for x in other.Initial]:
                sname = (s1, s2)
                sti = new.addState(sname)
                new.addInitial(sti)
                notDone.add(sname)
        while notDone:
            state = notDone.pop()
            done.add(state)
            (s1, s2) = state
            sti = new.stateIndex(state)
            (i1, i2) = (self.stateIndex(s1), other.stateIndex(s2))
            (k1, k2) = (self.inputS(i1), other.inputS(i2))
            for k in k1.intersection(k2):
                for (symo, o1) in self.delta[i1][k]:
                    for o2 in other.delta[i2][k]:
                        new.addTransitionQ(sti, (self.States[o1], other.States[o2]), k, symo, notDone, done)
        return new

    def composition(self, other):
        """Composition operation of a transducer with a transducer.

           :param SFT other: the second transducer
           :rtype: SFT"""
        if type(other) != SFT:
            raise common.FAdoGeneralError("Incompatible objects")
        new = SFT()
        notDone = set()
        done = set()
        e1, e2 = self.epsilonOutP(), other.epsilonP()
        if e1:
            par2 = copy.deepcopy(other)
            par2.addEpsilonLoops()
        else:
            par2 = other
        if e2:
            par1 = copy.deepcopy(self)
            par1.addEpsilonLoops()
        else:
            par1 = self
        for s1 in [par1.States[x] for x in par1.Initial]:
            for s2 in [par2.States[x] for x in par2.Initial]:
                sname = (s1, s2)
                sti = new.addState(sname)
                new.addInitial(sti)
                notDone.add(sname)
        while notDone:
            state = notDone.pop()
            done.add(state)
            (s1, s2) = state
            i = new.stateIndex(state)
            (i1, i2) = (par1.stateIndex(s1), par2.stateIndex(s2))
            (k1, k2) = (par1.outputS(i1), par2.inputS(i2))
            K = k1.intersection(k2)
            for s in par1.delta.get(i1, []):
                for (so1, o1) in par1.delta[i1][s]:
                    if so1 in K:
                        for (so2, o2) in par2.delta[i2][so1]:
                            new.addTransitionQ(i, (par1.States[o1], par1.States[o2]), s, so2, notDone, done)
        for x in [(par1.States[a], par2.States[b]) for a in par1.Final for b in par2.Final]:
            if x in new.States:
                new.addFinal(new.stateIndex(x))
        return new

    def functionalP(self):
        """Tests if a  transducer is functional using Allauzer & Mohri and Béal&Carton&Prieur&Sakarovitch algorithms.

        :rtype: bool

        .. seealso:: Cyril Allauzer and Mehryar Mohri, Journal of Automata Languages and Combinatorics,
            Efficient Algorithms for Testing the Twins Property, 8(2): 117-144, 2003.

        .. seealso:: M.P. Béal, O. Carton, C. Prieur and J. Sakarovitch. Squaring transducers: An efficient
            procedure for deciding functionality and sequentiality. Theoret. Computer Science 292:1 (2003), 45-63.

        .. note::
           This is implemented using nonFunctionalW()"""
        return self.nonFunctionalW() == (None, None, None)

    def _functionalP(self):
        """

        :rtype: bool"""
        notDone = []
        done = {}
        for s in self.Initial:
            notDone.append(s)
            done[s] = (Epsilon, Epsilon)
        while notDone:
            sti = notDone.pop()
            (preInput, preOutput) = done[sti]
            if sti in self.delta:
                for symi in self.delta[sti]:
                    for (symo, sto) in self.delta[sti][symi]:
                        if preInput == Epsilon:
                            newInput = symi
                        elif symi == Epsilon:
                            newInput = preInput
                        else:
                            newInput = preInput + symi
                        if preOutput == Epsilon:
                            newOutput = symo
                        elif symo == Epsilon:
                            newOutput = preOutput
                        else:
                            newOutput = preOutput + symo
                        if newOutput.startswith(newInput):
                            if newInput == newOutput:
                                newInput = newOutput = Epsilon
                            else:
                                newOutput = newOutput[len(newInput):]
                                newInput = Epsilon
                        elif newInput.startswith(newOutput):
                            if newInput == newOutput:
                                newInput = newOutput = Epsilon
                            else:
                                newInput = newInput[len(newOutput):]
                                newOutput = Epsilon
                        else:
                            if newInput != Epsilon and newOutput != Epsilon and newInput != newOutput:
                                return False
                        if sto in self.Final and (newInput != Epsilon or newOutput != Epsilon):
                            return False
                        if sto not in done:
                            notDone.append(sto)
                            done[sto] = (newInput, newOutput)
                        else:
                            if done[sto] == (newInput, newOutput):
                                continue
                            else:
                                return False
        return True

    def runOnNFA(self, nfa):
        """Result of applying a transducer to an automaton

        :param DFA|NFA nfa: input language to transducer
        :return: resulting language
        :rtype: NFA"""
        return self.inIntersection(nfa).toOutNFA()

    def outIntersectionDerived(self, other):
        """Naive version of outIntersection

        :param DFA|NFA other: the automaton used as a filter of the output
        :rtype: SFT"""
        return (self.inverse() & other).inverse()

    def outIntersection(self, other):
        """Conjunction of transducer and automaton: X & Y using output intersect operation.

        :param DFA|NFA other: the automaton used as a filter of the output
        :rtype: SFT"""
        foo = other.toNFA().renameStates()
        new = SFT()
        new.Output = set(self.Output.union(foo.Sigma))
        notDone = set()
        done = set()
        for s1 in [self.States[x] for x in self.Initial]:
            for s2 in [foo.States[x] for x in foo.Initial]:
                sname = (s1, s2)
                new.addState(sname)
                new.addInitial(new.stateIndex(sname))
                notDone.add((s1, s2))
        e1, e2 = self.epsilonOutP(), foo.epsilonP()
        if e1:
            par2 = foo.dup()
            par2.addEpsilonLoops()
        else:
            par2 = foo
        if e2:
            par1 = self.dup()
            par1.addEpsilonLoops()
        else:
            par1 = self
        while notDone:
            state = notDone.pop()
            done.add(state)
            (s1, s2) = state
            i = new.stateIndex(state)
            (i1, i2) = (par1.stateIndex(s1), par2.stateIndex(s2))
            (k1, k2) = (par1.outputS(i1), par2.inputS(i2))
            K = k1.intersection(k2)
            for s in par1.delta.get(i1, []):
                for (symo, sout1) in par1.delta[i1][s]:
                    if symo in K:
                        for sout2 in par2.delta[i2][symo]:
                            new.addTransitionQ(i, (par1.States[sout1], par2.States[sout2]), s, symo, notDone, done)
        for x in [(par1.States[a], par2.States[b]) for a in par1.Final for b in par2.Final]:
            if x in new.States:
                new.addFinal(new.stateIndex(x))
        return new

    def inverse(self):
        """Switch the input label with the output label.

        No initial or final state changed.

        :return: Transducer with transitions switched.
        :rtype: SFT"""
        new = SFT()
        new.States = self.States
        new.setFinal(self.Final)
        new.setInitial(list(self.Initial))
        new.setSigma(set(self.Output))
        new.Output = set(self.Sigma)
        for src in self.delta:
            for symi in self.delta[src]:
                for (symo, out) in self.delta[src][symi]:
                    new.addTransition(src, symo, symi, out)
        return new

    def reversal(self):
        """Returns a transducer that recognizes the reversal of the relation.

        :return: Transducer recognizing reversal language
        :rtype: SFT"""
        new = SFT()
        new.States = list(self.States)
        new.setFinal(set(self.Initial))
        new.setInitial(list(self.Final))
        new.setSigma(set(self.Output))
        new.Output = set(self.Sigma)
        for src in self.delta:
            for symi in self.delta[src]:
                for (symo, out) in self.delta[src][symi]:
                    new.addTransition(out, symo, symi, src)
        return new

    def epsilonP(self):
        """Test whether this transducer has input epsilon-transitions

        :rtype: bool"""
        for s in self.delta:
            if Epsilon in self.delta[s]:
                return True
        return False

    def addEpsilonLoops(self):
        """Add a loop transition with epsilon input and output to every state in the transducer."""
        for i in range(len(self.States)):
            self.addTransition(i, Epsilon, Epsilon, i)

    def evalWordP(self, wp):
        """Tests whether the transducer returns the second word using the first one as input

        :param tuple wp: pair of words
        :rtype: bool"""
        from . import fl
        (win, wout) = wp
        inT = self.inIntersection(fl.FL([win]).trieFA().toNFA())
        return not inT.outIntersection(fl.FL([wout]).trieFA().toNFA()).emptyP()

    def emptyP(self):
        """Tests if the relation realized  the empty transducer

        :rtype: bool"""
        return self.toInNFA().emptyP()

    def nonEmptyW(self):
        """Witness of non emptyness

        :return: pair (in-word, out-word)
        :rtype: tuple"""
        done = set()
        notDone = set()
        pref = dict()
        for si in self.Initial:
            pref[si] = (Epsilon, Epsilon)
            notDone.add(si)
        while notDone:
            si = notDone.pop()
            done.add(si)
            if si in self.Final:
                return pref[si]
            for syi in self.delta.get(si, []):
                for (syo, so) in self.delta[si][syi]:
                    if so in done or so in notDone:
                        continue
                    pref[so] = concatN(pref[si], (syi, syo))
                    notDone.add(so)
        return None, None

    def nonFunctionalW(self):
        """Returns a witness of non funcionality (if is that the case) or a None filled triple

        :return: witness
        :rtype: tuple"""
        def _len(a):
            if a == Epsilon:
                return 0
            else:
                return len(a)

        def _suffix(a, b):
            if a == b:
                return Epsilon
            elif _len(a) > _len(b):
                return ""
            else:
                if a == Epsilon:
                    return b
                elif a == b[:len(a)]:
                    return b[len(a):]
                else:
                    return ""

        def _newSValue(xxx_todo_changeme, xxx_todo_changeme1):
            (v1, v2) = xxx_todo_changeme
            (r1, r2) = xxx_todo_changeme1
            a, b = concatN((v1, v2), (r1, r2))
            s = _suffix(a, b)
            if s == Epsilon:
                return Epsilon, Epsilon
            if s:
                return Epsilon, s
            s = _suffix(b, a)
            if s:
                return s, Epsilon
            else:
                raise ZERO()

        def _completeCE(state, res, l):
            if state in sq.Final:
                return res
            for sy in sq.delta[state]:
                (i1, (o1, o2)) = sy
                for sto in sq.delta[state][sy]:
                    if sto not in l:
                        r = _completeCE(sto, concatN(res, (i1, o1, o2)), l + [sto])
                        if r:
                            return r
            return None

        if self.epsilonP() or self.epsilonOutP():
            wtrand = self.dup()
            wtrand.addEpsilonLoops()
        else:
            wtrand = self
        sq = wtrand.square_fv()
        sq.trim()
        valuei, svalue, done, notDone = dict(), dict(), set(), set()
        for sti in sq.Initial:
            notDone.add(sti)
            svalue[sti] = Epsilon, Epsilon
            valuei[sti] = Epsilon, Epsilon, Epsilon
        while notDone:
            sti = notDone.pop()
            done.add(sti)
            v = svalue[sti]
            for j in sq.delta.get(sti, []):
                (si, (s1, s2)) = j
                for o in sq.delta[sti][j]:
                    vi = concatN(valuei[sti], (si, s1, s2))
                    try:
                        vo = _newSValue(v, (s1, s2))
                        if o in sq.Final and vo != (Epsilon, Epsilon):
                            raise ZERO()
                        if o in svalue and svalue[o] != vo:
                            suf = _completeCE(o, (Epsilon, Epsilon, Epsilon), [o])
                            foo = concatN(vi, suf)
                            if foo[1] == foo[2]:
                                return concatN(valuei[o], suf)
                            else:
                                return foo
                    except ZERO:
                        suf = _completeCE(o, (Epsilon, Epsilon, Epsilon), [o])
                        if not suf:
                            raise common.TRError()
                        return concatN(vi, suf)
                    valuei[o] = vi
                    svalue[o] = vo
                    if o not in done:
                        notDone.add(o)
        return None, None, None

    def square(self):
        """Conjunction of transducer with itself

        :rtype: NFA"""
        new = fa.NFA()
        notDone = set()
        done = set()
        for s1 in [self.States[x] for x in self.Initial]:
            for s2 in [self.States[x] for x in self.Initial]:
                sname = (s1, s2)
                i = new.addState(sname)
                new.addInitial(i)
                notDone.add((s1, s2))
        while notDone:
            state = notDone.pop()
            done.add(state)
            (s1, s2) = state
            i = new.stateIndex(state)
            (i1, i2) = (self.stateIndex(s1), self.stateIndex(s2))
            (k1, k2) = (self.inputS(i1), self.inputS(i2))
            if i1 in self.Final and i2 in self.Final:
                new.addFinal(i)
            K = k1.intersection(k2)
            for syin in K:
                for (syout, sout) in self.delta[i1][syin]:
                    for (syout2, sout2) in self.delta[i2][syin]:
                        stoutr = (self.States[sout], self.States[sout2])
                        new.addTransitionQ(i, stoutr, (syin, (syout, syout2)), notDone, done)
        return new

    def square_fv(self):
        """Conjunction of transducer with itself (Fast Version)

        :rtype: NFA"""
        new = fa.NFA()
        notDone = set()
        done = set()
        for s1 in self.Initial:
            for s2 in self.Initial:
                sname = (s1, s2)
                i = new.addState(sname)
                new.addInitial(i)
                notDone.add(sname)
        while notDone:
            state = notDone.pop()
            done.add(state)
            (i1, i2) = state
            i = new.stateIndex(state)
            (k1, k2) = (self.inputS(i1), self.inputS(i2))
            if i1 in self.Final and i2 in self.Final:
                new.addFinal(i)
            K = k1.intersection(k2)
            for syin in K:
                for (syout, sout) in self.delta[i1][syin]:
                    for (syout2, sout2) in self.delta[i2][syin]:
                        stoutr = (sout, sout2)
                        new.addTransitionQ(i, stoutr, (syin, (syout, syout2)), notDone, done)
        return new

    def epsilonOutP(self):
        """Tests if epsilon occurs in transition outputs

        :rtype: bool"""
        for i in self.delta:
            for c in self.delta[i]:
                for (out, _) in self.delta[i][c]:
                    if out == Epsilon:
                        return True
        return False


class NFT(SFT):
    """Normal Form Transducer.

    Transsitions here have labels of the form (s,Epsilon) or (Epsilon,s)

    .. inheritance-diagram:: SFT"""
    pass


def infixTransducer(alphabet, preserving=False):
    """Creates an infix property transducer based on given alphabet

    :param bool preserving: input preserving transducer, else input altering
    :param list|set alphabet: alphabet
    :rtype: SFT """
    t = SFT()
    t.setSigma(alphabet)
    t.setOutput(alphabet)
    for _ in range(5):
        t.addState()
    t.addInitial(0)
    for a in t.Sigma:
        t.addTransition(0, a, Epsilon, 1)
        t.addTransition(1, a, Epsilon, 1)
        t.addTransition(1, a, a, 2)
        t.addTransition(2, a, a, 2)
        t.addTransition(2, a, Epsilon, 3)
        t.addTransition(3, a, Epsilon, 3)
        t.addTransition(0, a, a, 4)
        t.addTransition(4, a, a, 4)
        t.addTransition(4, a, Epsilon, 3)
    if preserving:
        t.setFinal({0, 1, 2, 3, 4})
    else:
        t.setFinal({1, 2, 3})
    return t


def prefixTransducer(alphabet, preserving=False):
    """Creates an prefix property transducer based on given alphabet

    :param bool preserving: input preserving transducer, else input altering
    :param list|set alphabet: alphabet
    :rtype: SFT """
    t = SFT()
    t.setSigma(alphabet)
    t.setOutput(alphabet)
    initial = t.stateIndex(0, True)
    final = t.stateIndex(1, True)
    t.addInitial(initial)
    t.addFinal(final)
    for i in alphabet:
        t.addTransition(initial, i, i, initial)
        t.addTransition(initial, i, Epsilon, final)
        t.addTransition(final, i, Epsilon, final)
    if preserving:
        t.addFinal(initial)
    return t


def suffixTransducer(alphabet, preserving=False):
    """Creates an suffix property transducer based on given alphabet

    :param bool preserving: input preserving transducer, else input altering
    :param list|set alphabet: alphabet
    :rtype: SFT """
    t = SFT()
    t.setSigma(alphabet)
    t.setOutput(alphabet)
    initial = t.stateIndex(0, True)
    final = t.stateIndex(1, True)
    t.addInitial(initial)
    t.addFinal(final)
    for i in alphabet:
        t.addTransition(initial, i, Epsilon, initial)
        t.addTransition(initial, i, Epsilon, final)
        t.addTransition(final, i, i, final)
    if preserving:
        t.addFinal(initial)
    return t


def outfixTransducer(alphabet, preserving=False):
    """Creates an outfix property transducer based on given alphabet

    :param bool preserving: input preserving transducer, else input altering
    :param list|set alphabet: alphabet
    :rtype: SFT """
    t = SFT()
    t.setSigma(alphabet)
    t.setOutput(alphabet)
    initial = t.stateIndex(0, True)
    middle = t.stateIndex(1, True)
    final = t.stateIndex(2, True)
    t.addInitial(initial)
    t.addFinal(middle)
    t.addFinal(final)
    for i in alphabet:
        t.addTransition(initial, i, i, initial)
        t.addTransition(initial, i, Epsilon, middle)
        t.addTransition(middle, i, Epsilon, middle)
        t.addTransition(middle, i, i, final)
        t.addTransition(final, i, i, final)
    if preserving:
        t.addFinal(initial)
    return t


def hypercodeTransducer(alphabet, preserving=False):
    """Creates an hypercode property transducer based on given alphabet

    :param bool preserving: input preserving transducer, else input altering
    :param list|set alphabet: alphabet
    :rtype: SFT """
    t = SFT()
    t.setSigma(alphabet)
    t.setOutput(alphabet)
    initial = t.stateIndex(0, True)
    final = t.stateIndex(1, True)
    t.addInitial(initial)
    t.addFinal(final)
    for i in alphabet:
        t.addTransition(initial, i, i, initial)
        t.addTransition(initial, i, Epsilon, final)
        t.addTransition(final, i, Epsilon, final)
        t.addTransition(final, i, i, final)
    if preserving:
        t.addFinal(initial)
    return t
