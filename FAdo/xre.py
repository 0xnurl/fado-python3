# -*- coding: utf-8 -*-
""" **Extended regular expressions manipulation**

Extended regular expression classes and its manipulation

.. versionadded:: 0.9.8

.. *Authors:* Rogério Reis & Nelma Moreira

.. Contributions by
    - Rafaela Bastos

.. *This is part of FAdo project*   http://fado.dcc.fc.up.pt

.. *Copyright:* 1999-2014 Rogério Reis & Nelma Moreira {rvr,nam}@dcc.fc.up.pt

.. This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
   See the GNU General Public License for more details.

   You should have received a copy of the GNU General Public Licensealong
   with this program; if not, write to the Free Software Foundation, Inc.,
   675 Mass Ave, Cambridge, MA 02139, USA."""
from __future__ import absolute_import
from __future__ import unicode_literals
from __future__ import print_function
from __future__ import division

from future import standard_library
standard_library.install_aliases()
from builtins import str
from builtins import range
from builtins import *
import copy

from .yappy_parser import *
from . import reex
from . import fa
from .common import *


class xre(reex.regexp):
    """Base class for extended regular expressions, used directly to represent a symbol.
  
    :var val: the actual symbol"""

    def __repr__(self):
        """Representation of the regular expression's syntactical tree."""
        return 'xre({0:>s})'.format(self.__str__())

    def unionSigma(self, reg):
        """Returns the union of two alphabets

        :param reg: xre
        :rtype: set
        """
        if self.Sigma is None:
            return reg.Sigma
        elif reg.Sigma is None:
            return self.Sigma
        else:
            return self.Sigma.union(reg.Sigma)

    def derivative(self, sigma):
        """Derivative of the regular expression in relation to the given symbol.

        :param sigma: an arbitrary symbol.
        :rtype: regular expression

        .. note:: whether the symbols belong to the expression's alphabet goes unchecked. The given symbol will be
           matched against the string representation of the regular expression's symbol.

        .. seealso::
            J. A. Brzozowski, Derivatives of Regular Expressions. J. ACM 11(4): 481-494 (1964)"""
        if str(self.val) == str(sigma):
            return xepsilon(self.Sigma)
        else:
            return xempty(self.Sigma)

    def partialDerivativeC(self, sigma):
        """

        :param sigma:
        :rtype: xre"""
        if self.val == sigma:
            return {xsigmaP(self.Sigma)}
        else:
            return {xsigmaS(self.Sigma)}

    def linearForm(self):
        """Linear form of the extended regular expression , as a mapping from heads to sets of tails,
            so that each pair (head,tail) is a monomial in the set of linear forms.

        :return: dictionary mapping heads to sets of tails
        :rtype: {symbol: set([regular expressions])}

        .. seealso:: Antimirov, 95"""
        if not self.Sigma:
            syms = self.setOfSymbols()
            self.setSigma(syms)
        return self._linearForm()

    def _linearForm(self):
        """ """
        return {self.val: {xepsilon(self.Sigma)}}

    def _linearFormC(self):
        """ """
        lf = {}
        for i in self.Sigma:
            if i == self.val:
                lf[i] = {xsigmaP(self.Sigma)}
            else:
                lf[i] = {xsigmaS(self.Sigma)}
        return lf

    def PD(self):
        """Closure of partial derivatives of the regular expression in relation to all words.
    
        .. Note: does not include the regular expression

        :return: set of regular expressions
        :rtype: set"""
        stack = [self]
        s = set()
        while stack:
            reg = stack.pop()
            lf = reg.linearForm()
            for head in lf:
                for st in lf[head]:
                    if not (st in s):
                        stack.append(st)
                        s.add(st)
        return s

    def concatenation(self, r):
        """Computes the concatenation of two regular expressions.

        :arg r: a regular expression
        :type r: xre
        :rtype: xre"""
        if type(r) is xepsilon:
            return self
        elif type(r) is xempty:
            return r
        sig = self.unionSigma(r)
        if type(r) is xconcat:
            return xconcat(copy.deepcopy([self] + r.val), sigma=sig)
        else:
            return xconcat(copy.deepcopy([self, r]), sigma=sig)

    def intersection(self, sx):
        """Computes the intersection of two regular expressions.

        :arg sx: a regular expression
        :type sx: xre
        :return type: xre"""
        if sx == self:
            return self
        elif type(sx) is xconj:
            return xconj(sx.val | {self}, sigma=self.unionSigma(sx))
        elif type(sx) is xstar:
            if type(sx.val) is xre:
                if sx.val == self:
                    return self
                else:
                    return xempty(self.Sigma)
            else:
                return xconj({self, sx}, sigma=self.unionSigma(sx))
        elif type(sx) is xempty or type(sx) is xepsilon:
            return xempty(self.Sigma)
        elif type(sx) is xre:
            if sx == self:
                return self
            else:
                return xempty(self.Sigma)
        else:
            return xconj({self, sx}, sigma=self.unionSigma(sx))

    def _not(self):
        """ """
        return xnot(copy.deepcopy(self))

    def compare(self, r, cmp_method="equivP", nfa_method=None):
        """Compare with another regular expression for equivalence.
        :param r:
        :param cmp_method:
        :param nfa_method: """
        if cmp_method == "compareMinimalDFA":
            return self.compareMinimalDFA(r, nfa_method)
        elif cmp_method == "equivP":
            return self.equivP(r)

    def support(self):
        """'Support of a regular expression.

        :return: set of regular expressions
        :rtype: set

        .. seealso::
            Champarnaud, J.M., Ziadi, D.: From Mirkin's prebases to Antimirov's word partial derivative.
            Fundam. Inform. 45(3), 195-205 (2001)"""
        return {xepsilon(self.Sigma)}

    def toDFA(self, dfa_method="dfaDerivatives"):
        """DFA that accepts the regular expression's language.
        :param dfa_method: """
        return self.__getattribute__(dfa_method)()

    def toNFA(self, nfa_method="nfaPD"):
        """NFA that accepts the regular expression's language.
        :param nfa_method: """
        return self.__getattribute__(nfa_method)()

    def equivP(self, reg):
        """Verifies if two regular expressions are equivalent.
    
        :param reg: regular expression
        :rtype: bool """
        s = {(self, reg)}
        # h = {(self, reg)}
        h = set([])
        sigma = self.setOfSymbols().union(reg.setOfSymbols())
        while s:
            s1, s2 = s.pop()
            if s1.ewp() != s2.ewp():
                return False
            h.add((s1, s2))
            for a in sigma:
                der1 = s1.derivative(a)
                der2 = s2.derivative(a)
                if (der1, der2) not in h:
                    #h.add((der1,der2))
                    s.add((der1, der2))
        return True

    def toDFA(self, dfa_method="dfaDerivatives"):
        """DFA that accepts the regular expression's language.
        :param dfa_method: """
        return self.__getattribute__(dfa_method)()

    def dfs(self):
        """ Minimal DFA of an extended regular expression 
        :return: minimal DFA
        :rtype: DFA
        """
        aut = fa.DFA()
        initial = aut.addState(self)
        aut.setInitial(initial)
        stack = [(self, initial)]
        sigma = copy.deepcopy(self.setOfSymbols())
        if self.Sigma is not None:
            sigma |= self.Sigma
        aut.setSigma(sigma)
        # equiv = {self:{self}}
        equiv = {}
        while stack:
            state, idx = stack.pop()
            state.setSigma(sigma)
            for symbol in sigma:
                d = state.derivative(symbol)
                f = True
                if d in aut.States:
                    i = aut.stateIndex(d)
                elif d in equiv:
                    i = aut.stateIndex(equiv[d])
                else:
                    for st in aut.States:
                        if d.equivP(st):
                            i = aut.stateIndex(st)
                            f = False
                            equiv[st] = d
                            equiv[d] = st
                    if f:
                        i = aut.addState(d)
                        stack.append((d, i))
                aut.addTransition(idx, symbol, i)
            if state.ewp():
                aut.addFinal(idx)
        return aut

    def dfaDerivatives(self):
        """Word derivatives automaton of the regular expression

        :return: word derivatives automaton
        :rtype: DFA

        .. seealso::
            J. A. Brzozowski, Derivatives of Regular Expressions. J. ACM 11(4): 481-494 (1964)"""
        aut = fa.DFA()
        i = aut.addState(self)
        aut.setInitial(i)
        stack = [(self, i)]
        sigma = copy.deepcopy(self.setOfSymbols())
        if self.Sigma is not None:
            sigma |= self.Sigma
        aut.setSigma(sigma)
        while stack:
            state, idx = stack.pop()
            state.setSigma(sigma)
            for symbol in sigma:
                st = state.derivative(symbol)
                if st in aut.States:
                    i = aut.stateIndex(st)
                else:
                    i = aut.addState(st)
                    stack.append((st, i))
                aut.addTransition(idx, symbol, i)
            if state.ewp():
                aut.addFinal(idx)
        return aut

    def nfaPD(self):
        """NFA that accepts the regular expression's language, and which is constructed from the expression's partial
         derivatives.

        :return: partial derivatives [or equation] automaton
        :rtype: NFA

        .. seealso::
            V. M. Antimirov, Partial Derivatives of Regular Expressions and Finite Automaton Constructions.
            Theor. Comput. Sci.155(2): 291-319 (1996)

        ..attention why different from reex.nfaPD    """
        aut = fa.NFA()
        i = aut.addState(self)
        aut.addInitial(i)
        stack = [(self, i)]
        sigma = copy.deepcopy(self.setOfSymbols())
        if self.Sigma is not None:
            sigma |= self.Sigma
        aut.setSigma(sigma)
        while stack:
            state, idx = stack.pop()
            state.setSigma(sigma)
            lf = state.linearForm()
            for head in list(lf.keys()):
                for st in lf[head]:
                    if st in aut.States:
                        i = aut.stateIndex(st)
                    else:
                        i = aut.addState(st)
                        stack.append((st, i))
                    aut.addTransition(idx, head, i)
            if state.ewp():
                aut.addFinal(idx)
        return aut

    def _cross(self, lists):
        """
        :param lists: """
        rex = list(copy.deepcopy(self.val))
        for i in range(len(rex)):
            re1 = rex[i]
            for j in range(i + 1, len(rex)):
                re2 = rex[j]
                for symbol in re1.last():
                    if not symbol in lists:
                        lists[symbol] = re2.first()
                    else:
                        lists[symbol] += re2.first()
                for symbol in re2.last():
                    if not symbol in lists:
                        lists[symbol] = re1.first()
                    else:
                        lists[symbol] += re1.first()
        return lists

    @staticmethod
    def _concat(der, r):
        """Computes a set that contains the concatenation of a regular expression with all the regular expression
        within a set.
    
        :param der:
        :param r:
        :arg der: set of regular expressions
        :arg re: regular expression
        :rtype: set of regular expression"""
        s = set()
        for i in der:
            ci = i.concatenation(r)
            if not (type(ci) is xempty):
                s.add(ci)
        return s

    @staticmethod
    def _intersection(a1, a2):
        """
        :param a1:
        :param a2:
        :return:"""
        s = set()
        for i in a1:
            for j in a2:
                res = i.intersection(j)
                if not (type(res) is xempty):
                    s.add(res)
        return s


class xspecialConst(xre):
    """Base class for xepsilon and xempty."""

    def __init__(self, sigma=None):
        """
        :param sigma: """
        self.Sigma = sigma

    def __copy__(self):
        """
        :return: """
        return self

    def __eq__(self, re):
        """
        :param re: the other re """
        if type(self) == type(re):
            return True

    def setOfSymbols(self):
        """
        :return:"""
        return set()

    def alphabeticLength(self):
        """
        :return:"""
        return 0

    def _marked(self, pos):
        """
        :param pos:
        :return:"""
        return self, pos

    def unmarked(self):
        """The unmarked form of the regular expression. Each leaf in its syntactical tree becomes a regexp(),
        the epsilon() or the emptyset().

        :rtype: (general) regular expression"""
        return self

    def first(self):
        """
        :return: """
        return []

    def last(self):
        """
        :return:"""
        return []

    def followLists(self, lists=None):
        """
        :param lists:
        :return:"""
        if lists is None:
            return {}
        return lists

    def followListsStar(self, lists=None):
        """
        :param lists:
        :return:"""
        if lists is None:
            return {}
        return lists


    def partialDerivatives(self, sigma):
        """
        :param sigma:
        :return:"""
        return set()

    def partialDerivativeC(self, sigma):
        """
        :param sigma:
        :return:"""
        return {xsigmaS(self.Sigma)}

    def linearForm(self):
        """
        :return: dictionary mapping heads to sets of tails
        :rtype: {symbol: set([regular expressions])}

        .. seealso:: Antimirov, 95"""
        if not self.Sigma:
            syms = self.setOfSymbols()
            self.setSigma(syms)
        return self._linearForm()

    def _linearForm(self):
        """
        :return:"""
        return {}

    def _linearFormC(self):
        """
        :return:"""
        lf = {}
        for sigma in self.Sigma:
            lf[sigma] = {xsigmaS(self.Sigma)}
        return lf

    def derivative(self, sigma):
        """
        :param sigma:
        :return:"""
        return xempty(self.Sigma)

    def support(self):
        """
        :return:"""
        return {}


class xempty(xspecialConst, reex.emptyset):
    """Class that represents the empty set."""

    def concatenation(self, r):
        """
        :param r:
        :return:"""
        return xempty(self.Sigma)

    def intersection(self, sx):
        """
        :param sx:
        :return:"""
        return xempty(self.Sigma)

    def _not(self):
        """
        :return:"""
        return xsigmaS(self.Sigma)


class xepsilon(xspecialConst, reex.epsilon):
    """Class that represents the empty word."""

    def concatenation(self, r):
        """
        :param r:
        :return:"""
        return r

    def intersection(self, sx):
        """
        :param sx:
        :return:"""
        if sx.ewp():
            return xepsilon(self.Sigma)
        else:
            return xempty(self.Sigma)

    def _not(self):
        return xsigmaP(self.Sigma)


class xsigmaS(xspecialConst):
    """Class that represents the complement of the empty set"""

    def __repr__(self):
        """
        :return:"""
        return "xsigmaS()"

    def __str__(self):
        """
        :return:"""
        return "xsigmaS"

    def ewp(self):
        """
        :return:"""
        return True

    def _linearForm(self):
        """
        :return:"""
        lf = {}
        for sigma in self.Sigma:
            lf[sigma] = {xsigmaS(self.Sigma)}
        return lf

    def _linearFormC(self):
        """
        :return:"""
        return {}

    def derivative(self, sigma):
        """
        :param sigma:
        :return:"""
        if self.Sigma is not None and sigma in self.Sigma:
            return xsigmaS(self.Sigma)
        else:
            return xempty(self.Sigma)

    def partialDerivatives(self, sigma):
        """
        :param sigma:
        :return:"""
        if  self.Sigma is not None and sigma in self.Sigma:
            return {xsigmaS(self.Sigma)}
        else:
            return set([])

    def partialDerivativeC(self, sigma):
        """
        :param sigma:
        :return:"""
        return set([])

    def support(self):
        """
        :return: """
        return {xsigmaS(self.Sigma)}

    def _not(self):
        """
        :return: """
        return xempty(self.Sigma)


class xsigmaP(xspecialConst):
    """Class that represents the complement of the empty word"""

    def __repr__(self):
        """
        :return:"""
        return "xsigmaP()"

    def __str__(self):
        """
        :return:"""
        return "xsigmaP"

    def ewp(self):
        """
        :return: """
        return False

    def derivative(self, sigma):
        """
        :param sigma:
        :return: """
        if self.Sigma is not None and sigma in self.Sigma:
            return xsigmaS(self.Sigma)
        else:
            return xempty(self.Sigma)

    def partialDerivatives(self, sigma):
        """
        :param sigma:
        :return: """
        if self.Sigma is not None and sigma in self.Sigma:
            return {xsigmaS(self.Sigma)}
        else:
            return set([])

    def partialDerivativeC(self, sigma):
        """
        :param sigma:
        :return: """
        return set([])

    def _linearForm(self):
        """
        :return:"""
        lf = {}
        for sigma in self.Sigma:
            lf[sigma] = {xsigmaS(self.Sigma)}
        return lf

    def _linearFormC(self):
        """
        :return: """
        return {}

    def support(self):
        """
        :return: """
        return {xsigmaS(self.Sigma)}

    def _not(self):
        """
        :return: """
        return xepsilon(self.Sigma)


class xconnective(xre):
    """Base class for xdisj, xconcat and xconj."""

    def __hash__(self):
        """
        :return: """
        return hash((frozenset(self.val), type(self)))

    def __len__(self):
        """
        :return: """
        return len(self.val)

    def alphabeticLength(self):
        """
        :return: """
        length = 0
        for i in self.val:
            length += i.alphabeticLength()
        return length

    def epsilonLength(self):
        """
        :return: """
        length = 0
        for i in self.val:
            length += i.epsilonLength()
        return length

    def treeLength(self):
        """
        :return: """
        length = 0
        for i in self.val:
            length += i.treeLength()
        return length + 1

    def syntacticLength(self):
        """
        :return: """
        length = len(self.val) - 1
        for i in self.val:
            length += i.syntacticLength()
        return length

    def setOfSymbols(self):
        """
        :return: """
        s = set()
        for i in self.val:
            s = s | i.setOfSymbols()
        return s

    def _setSigma(self, s):
        """
        :return: """
        for i in self.val:
            i.setSigma(self.Sigma, s)



class xdisj(xconnective):
    """Class that represents the disjunction operation."""

    def __repr__(self):
        """
        :return: """
        return "xdisj({0:s})".format(repr(self.val))

    def __str__(self):
        """
        :return: """
        return "({0:s})".format(self._strP())

    def _strP(self):
        """
        :return: """
        return " + ".join([str(i) for i in self.val])

    def ewp(self):
        """
        :return: """
        for i in self.val:
            if i.ewp():
                return True
        return False

    def _marked(self, pos):
        """
        :param pos:
        :return: """
        s = set()
        for i in self.val:
            mark, pos = i._marked(pos)
            s.add(mark)
        return xdisj(s), pos

    def first(self):
        """

        :return: """
        lfst = []
        for i in self.val:
            fst = i.first()
            lfst += fst
        return lfst

    def last(self):
        """
        :return: """
        llst = []
        for i in self.val:
            lst = i.last()
            llst += lst
        return llst

    def followLists(self, lists=None):
        """
        :param lists:
        :return: """
        if lists is None:
            lists = {}
        for i in self.val:
            i.followLists(lists)
        return lists

    def followListsStar(self, lists=None):
        """
        :param lists:
        :return: """
        if lists is None:
            lists = {}
        for i in self.val:
            i.followListsStar(lists)
        self._cross(lists)
        return lists

    def derivative(self, sigma):
        """
        :param sigma:
        :return: """
        s = set()
        for i in self.val:
            der = i.derivative(sigma)
            if not (type(der) is xempty):
                if type(der) is xdisj:
                    s.update(der.val)
                else:
                    s.add(der)
        if len(s) == 0:
            return xempty(self.Sigma)
        elif len(s) == 1:
            return s.pop()
        else:
            return xdisj(s,self.Sigma)

    def partialDerivatives(self, sigma):
        """
        :param sigma:
        :return: """
        s = set()
        for i in self.val:
            der = i.partialDerivatives(sigma)
            s.update(der)
        return s

    def partialDerivativeC(self, sigma):
        """
        :param sigma:
        :return: """
        pd = self.partialDerivatives(sigma)
        pdc = set()
        for di in pd:
            pdc.add(di._not())
        if pdc:
            if len(pdc) != 1:
                pdc = {xconj(pdc)}
        else:
            pdc = {xsigmaS(self.Sigma)}
        return pdc

    # noinspection PyUnusedLocal
    def _linearForm(self):
        """
        :return: """
        lf = {}
        sigma = copy.deepcopy(self.Sigma)
        for reg in self.val:
            reg.Sigma = sigma
            l = reg.linearForm()
            tails = set()
            for head in (list(lf.keys()) + list(l.keys())):
                tails = lf.get(head, set()) | l.get(head, set())
                if tails:
                    lf[head] = tails
        return lf

    def _linearFormC(self):
        """
        :return: """
        lf = self._linearForm()
        lfc = {}
        for head in (list(lf.keys())):
            pdc = set()
            for di in lf[head]:
                pdc.add(di._not())
            if pdc:
                if len(pdc) != 1:
                    pdc = {xconj(pdc)}
            else:
                pdc = {xsigmaS(self.Sigma)}
            lfc[head] = pdc
        for s in self.Sigma:
            if not s in lfc:
                lfc[s] = {xsigmaS(self.Sigma)}
        return lfc

    def intersection(self, sx):
        """
        :param sx:
        :return: """
        if type(sx) is xconj:
            return xconj(sx.val | {self}, sigma=self.unionSigma(sx))
        elif sx == self:
            return self
        elif type(sx) is xempty:
            return xempty(self.unionSigma(sx))
        elif type(sx) is xepsilon:
            if self.ewp():
                return xepsilon(self.Sigma)
            else:
                return xempty(self.Sigma)
        else:
            return xconj({self, sx}, sigma=self.unionSigma(sx))

    def support(self):
        """
        :return: """
        s = set()
        for i in self.val:
            p = i.support()
            s.update(p)
        return s


class xconcat(xconnective):
    """Class that represents the concatenation operation."""

    def __str__(self):
        """
        :return: """
        return "{0:s}".format(self._strP())

    def _strP(self):
        """
        :return: """
        rep = ""
        for i in self.val:
            rep += "{0:s}".format(str(i))
        return rep

    def __repr__(self):
        """
        :return: """
        return "xconcat({0:s})".format(repr(self.val))

    def head(self):
        """
        :return: """
        return copy.deepcopy(self.val[0])

    def tail(self):
        """
        :return: """
        if len(self) == 2:
            return copy.deepcopy(self.val[1])
        else:
            return xconcat(copy.deepcopy(self.val[1:]),self.Sigma)

    def headrev(self):
        """
        :return: """
        return copy.deepcopy(self.val[-1])

    def tailrev(self):
        """
        :return: """
        if len(self) == 2:
            return copy.deepcopy(self.val[0])
        else:
            return xconcat(copy.deepcopy(self.val[:-1]),self.Sigma)

    def ewp(self):
        """
        :return: """
        for i in self.val:
            if not (i.ewp()):
                return False
        return True

    def _marked(self, pos):
        """
        :param pos:
        :return: """
        l = []
        for i in self.val:
            mark, pos = i._marked(pos)
            l.append(mark)
        return xconcat(l,self.Sigma), pos

    def first(self):
        """
        :return: """
        lfst = self.head().first()
        if self.head().ewp():
            fst = self.tail().first()
            lfst += fst
        return lfst

    def last(self):
        """
        :return: """
        llst = self.headrev().last()
        if self.headrev().ewp():
            lst = self.tailrev().last()
            llst += lst
        return llst

    def followLists(self, lists=None):
        """
        :param lists:
        :return: """
        if lists is None:
            lists = {}
        self.head().followLists(lists)
        self.tail().followLists(lists)
        for i in self.head().last():
            if i not in lists:
                lists[i] = self.tail().first()
            else:
                lists[i] += self.tail().first()
        return lists

    def followListsStar(self, lists=None):
        """
        :param lists:
        :return: """
        if lists is None:
            lists = {}
        if self.head().ewp() and self.tail():
            self.head().followListsStar(lists)
            self.tail().followListsStar(lists)
        elif self.tail().ewp():
            self.head().followListsStar(lists)
            self.tail().followLists(lists)
        elif self.head().ewp():
            self.head().followLists(lists)
            self.tail().followListsStar(lists)
        else:
            self.head().followLists(lists)
            self.tail().followLists(lists)
        self._cross(lists)
        return lists

    def derivative(self, sigma):
        """
        :param sigma:
        :return: """
        ader = self.head().derivative(sigma)
        der = ader.concatenation(self.tail())
        if self.head().ewp():
            bder = self.tail().derivative(sigma)
            if type(bder) is xempty:
                return der
            else:
                if type(bder) is xdisj:
                    bder.val.add(der)
                    return bder
                else:
                    return xdisj({der, bder},self.Sigma)
        else:
            return der

    def partialDerivatives(self, sigma):
        """
        :param sigma:
        :return: """
        s = set()
        ader = self.head().partialDerivatives(sigma)
        s.update(self._concat(ader, self.tail()))
        if self.head().ewp():
            bder = self.tail().partialDerivatives(sigma)
            s.update(bder)
        return s

    def partialDerivativeC(self, sigma):
        """
        :param sigma:
        :return: """
        pd = self.partialDerivatives(sigma)
        pdc = set()
        for di in pd:
            pdc.add(di._not())
        if pdc:
            if len(pdc) != 1:
                pdc = {xconj(pdc)}
        else:
            pdc = {xsigmaS(self.Sigma)}
        return pdc

    def _linearForm(self):
        """
        :return: """
        sigma = copy.deepcopy(self.Sigma)
        arg1 = self.head()
        arg1.Sigma = sigma
        arg2n = self.tail()
        arg2n.Sigma = sigma
        if type(arg1) is xre:
            return {arg1.val: {arg2n}}
        else:
            lf = {}
            lf2 = {}
            lf1 = arg1.linearForm()
            if arg1.ewp():
                lf2 = self.tail().linearForm()
            for head in list(lf1.keys()):
                lf[head] = self._concat(lf1[head], self.tail())
            if lf2:
                for head in (list(lf.keys()) + list(lf2.keys())):
                    tails = lf.get(head, set()) | lf2.get(head, set())
                    if tails:
                        lf[head] = tails
            return lf

    def _linearFormC(self):
        """
        :return: """
        lf = self._linearForm()
        lfc = {}
        for head in (list(lf.keys())):
            pdc = set()
            for di in lf[head]:
                pdc.add(di._not())
            if pdc:
                if len(pdc) != 1:
                    pdc = {xconj(pdc)}
            else:
                pdc = {xsigmaS(self.Sigma)}
            lfc[head] = pdc
        for s in self.Sigma:
            if not s in lfc:
                lfc[s] = {xsigmaS(self.Sigma)}
        return lfc

    def support(self):
        """
        :return: """
        s = set()
        ap = self.head().support()
        s.update(self._concat(ap, self.tail()))
        bp = self.tail().support()
        s.update(bp)
        return s

    def concatenation(self, r):
        """
        :param r:
        :return: """
        if type(r) == xepsilon:
            return self
        elif type(r) == xempty:
            return xempty(self.Sigma)
        elif type(r) == xconcat:
            self.val.extend(copy.deepcopy(r.val))
            return self
        else:
            self.val.append(copy.deepcopy(r))
            return self

    def intersection(self, sx):
        """
        :param sx:
        :return: """
        if type(sx) is xconj:
            return xconj(sx.val | {self}, sigma=self.unionSigma(sx))
        else:
            if sx == self:
                return self
            elif type(sx) is xepsilon:
                if self.ewp():
                    return xepsilon(self.Sigma)
                else:
                    return xempty(self.Sigma)
            elif type(sx) is xempty:
                return xempty(self.Sigma)
            else:
                return xconj({self, sx}, sigma=self.unionSigma(sx))


class xconj(xconnective):
    """Class that represents the conjunction operation."""

    def __str__(self):
        """
        :return:"""
        return "({0:s})".format(self._strP())

    def _strP(self):
        """
        :return:"""
        return "&".join([str(i) for i in self.val])

    def __repr__(self):
        """
        :return: """
        return "xconj({0:s})".format(repr(self.val))

    def _marked(self, pos):
        """
        :param pos:
        :return: """
        s = set()
        for i in self.val:
            mark, pos = i._marked(pos)
            s.add(mark)
        return xconj(s), pos

    def ewp(self):
        """
        :return: """
        for i in self.val:
            if not i.ewp():
                return False
        return True

    def derivative(self, sigma):
        """
        :param sigma:
        :return:"""
        arg = copy.deepcopy(self.val)
        der = arg.pop().derivative(sigma)
        while arg:
            di = arg.pop().derivative(sigma)
            der = di.intersection(der)
        return der

    def partialDerivatives(self, sigma):
        """
        :param sigma:
        :return: """
        arg = copy.deepcopy(self.val)
        s = arg.pop().partialDerivatives(sigma)
        while arg:
            der = arg.pop().partialDerivatives(sigma)
            s = self._intersection(s, der)
        return s

    def partialDerivativeC(self, sigma):
        """
        :param sigma:
        :return:"""
        pdc = set()
        for i in self.val:
            pdi = i.partialDerivatives(sigma)
            if pdi:
                dic = set()
                for di in pdi:
                    dic.add(di._not())
                if len(dic) == 1:
                    pdc.add(dic.pop())
                else:
                    pdc.add(xconj(dic))
            else:
                pdc.add(xsigmaS(self.Sigma))
        return pdc

    # noinspection PyUnusedLocal
    def _linearForm(self):
        """
        :return:"""
        lf = {}
        sigma = copy.deepcopy(self.Sigma)
        arg = copy.deepcopy(self.val)
        r = arg.pop()
        r.Sigma = sigma
        lf = r.linearForm()
        while arg:
            ri = arg.pop()
            ri.Sigma = sigma
            l = ri.linearForm()
            heads = list(lf.keys())
            for head in heads:
                tails = self._intersection(l.get(head, set()), lf.get(head, set()))
                if tails == set():
                    del (lf[head])
                else:
                    lf[head] = tails
        return lf

    def _linearFormC(self):
        """
        :return: """
        lfc = {}
        for ri in self.val:
            ri.setSigma(self.Sigma)
            lfi = ri.linearForm()
            for head in (list(lfi.keys())):
                pdi = lfi[head]
                pdc = set()
                if pdi:
                    dic = set()
                    for di in pdi:
                        dic.add(di._not())
                    if len(dic) == 1:
                        pdc.add(dic.pop())
                    else:
                        pdc.add(xconj(dic))
                else:
                    pdc.add(xsigmaS(self.Sigma))
                if head in lfc:
                    lfc[head].update(pdc)
                else:
                    lfc[head] = pdc
        for s in self.Sigma:
            if not s in lfc:
                lfc[s] = {xsigmaS(self.Sigma)}
        return lfc

    def support(self):
        """
        :return: """
        arg = copy.deepcopy(self.val)
        x = arg.pop()
        s = x.support()
        while arg:
            x = arg.pop()
            p = x.support()
            s = self._intersection(s, p)
        return s

    def intersection(self, sx):
        """
        :param sx:
        :return: """
        if type(sx) is xconj:
            return xconj(sx.val | self.val)
        else:
            if type(sx) is xepsilon:
                if self.ewp():
                    return xepsilon(self.Sigma)
                else:
                    return xempty(self.Sigma)
            elif type(sx) is xempty:
                return xempty(self.Sigma)
            else:
                return xconj(self.val | {sx})


class xstar(xre):
    """Class that represents the Kleene closure."""

    def __str__(self):
        """
        :return: """
        if type(self.val) is xconcat or type(self.val) is xnot:
            return "({0:s})*".format(str(self.val))
        else:
            return "{0:s}*".format(str(self.val))

    def __repr__(self):
        """
        :return: """
        return "xstar({0:s})".format(repr(self.val))

    def ewp(self):
        """
        :return:"""
        return True

    def setOfSymbols(self):
        """
        :return: """
        return self.val.setOfSymbols()

    def alphabeticLength(self):
        """
        :return:"""
        return self.val.alphabeticLength()

    def epsilonLength(self):
        """
        :return: """
        return self.val.epsilonLength()

    def syntacticLength(self):
        """
        :return:"""
        return 1 + self.val.syntacticLength()

    def treeLength(self):
        """
        :return: """
        return 1 + self.val.treeLength()

    def _marked(self, pos):
        """
        :param pos:
        :return: """
        mark, pos = self.val._marked(pos)
        return xstar(mark), pos

    def first(self):
        """
        :return: """
        return self.val.first()

    def last(self):
        """
        :return: """
        return self.val.last()

    def followLists(self, lists=None):
        """
        :param lists:
        :return:"""
        return self.val.followListsStar(lists)

    def followListsStar(self, lists=None):
        """
        :param lists:
        :return:"""
        return self.val.followListsStar(lists)

    def derivative(self, sigma):
        """
        :param sigma:
        :return: """
        der = self.val.derivative(sigma)
        return der.concatenation(self)

    def partialDerivatives(self, sigma):
        """
        :param sigma:
        :return:"""
        der = self.val.partialDerivatives(sigma)
        return self._concat(der, self)

    def partialDerivativeC(self, sigma):
        """
        :param sigma:
        :return: """
        pd = self.partialDerivatives(sigma)
        pdc = set()
        for di in pd:
            pdc.add(di._not())
        if pdc:
            if len(pdc) != 1:
                pdc = {xconj(pdc)}
        else:
            pdc = {xsigmaS(self.Sigma)}
        return pdc

    def _linearForm(self):
        """
        :return:"""
        lf = {}
        reg = self.val
        reg.Sigma = copy.deepcopy(self.Sigma)
        lf1 = self.val.linearForm()
        for head in list(lf1.keys()):
            lf[head] = self._concat(lf1[head], self)
        return lf

    def _linearFormC(self):
        """
        :return:"""
        lf = self._linearForm()
        lfc = {}
        for head in (list(lf.keys())):
            pdc = set()
            for di in lf[head]:
                pdc.add(di._not())
            if pdc:
                if len(pdc) != 1:
                    pdc = {xconj(pdc)}
            else:
                pdc = {xsigmaS(self.Sigma)}
            lfc[head] = pdc
        for s in self.Sigma:
            if not s in lfc:
                lfc[s] = {xsigmaS(self.Sigma)}
        return lfc

    def support(self):
        """
        :return: """
        p = self.val.support()
        return self._concat(p, self)

    def intersection(self, sx):
        """
        :param sx:
        :return:"""
        if type(sx) is xconj:
            return xconj(sx.val | {self})
        else:
            if sx == self:
                return self
            elif type(sx) is xepsilon:
                return xepsilon()
            elif type(sx) is xempty:
                return xempty(self.Sigma)
            elif type(self.val) is xre and type(sx) is xre:
                if self.val == sx:
                    return sx
                else:
                    return xempty(self.Sigma)
            else:
                return xconj({self, sx})

    def _setSigma(self, s):
        self.val.setSigma(self.Sigma, s)

class xnot(xre):
    """ xnot class """

    def __init__(self, val, sigma=None):
        super(xnot, self).__init__(val, sigma)
        self.setSigma(self.val.Sigma)

    def __str__(self):
        """
        :return: """
        if type(self.val) is xconcat or type(self.val) is xstar:
            return "~(%s)" % (str(self.val))
        else:
            return "~%s" % (str(self.val))

    def __repr__(self):
        """
        :return:"""
        return "xnot(%s)" % repr(self.val)

    def ewp(self):
        """
        :return:"""
        if self.val.ewp():
            return False
        else:
            return True

    def alphabeticLength(self):
        """
        :return:"""
        return self.val.alphabeticLength()

    def epsilonLength(self):
        """
        :return:"""
        return self.val.epsilonLength()

    def syntacticLength(self):
        """
        :return:"""
        return 1 + self.val.syntacticLength()

    def treeLength(self):
        """
        :return:"""
        return 1 + self.val.treeLength()

    def setOfSymbols(self):
        """
        :return:"""
        return self.val.setOfSymbols()

    def derivative(self, sigma):
        """
        :param sigma:
        :return:"""
        der = self.val.derivative(sigma)
        if type(der) is xnot:
            return der.val
        else:
            return der._not()

    def partialDerivatives(self, sigma):
        """
        :param sigma:
        :return:"""
        return self.val.partialDerivativeC(sigma)

    def partialDerivativeC(self, sigma):
        """
        :param sigma:
        :return:"""
        return self.val.partialDerivatives(sigma)

    def _linearForm(self):
        """
        :return: """
        reg = self.val
        reg.Sigma = copy.deepcopy(self.Sigma)
        return reg._linearFormC()

    def _linearFormC(self):
        rex = self.val
        rex.Sigma = copy.deepcopy(self.Sigma)
        return rex._linearForm()

    def intersection(self, sx):
        """
        :param sx:
        :return: """
        if type(sx) is xconj:
            return xconj(sx.val | {self})
        elif sx == self:
            return self
        elif type(sx) is xepsilon:
            if self.ewp():
                return xepsilon(self.Sigma)
            else:
                return xempty(self.Sigma)
        elif type(sx) is xempty:
            return xempty(self.Sigma)
        else:
            return xconj({self, sx})

    def _not(self):
        return copy.deepcopy(self.val)

    def _setSigma(self, s):
        self.val.setSigma(self.Sigma, s)

rpn = ["x -> {0:s} | i | +  x  x  | & x x | . x x  | ~ x | * x".format(Epsilon)]


def rpn2xre(s):
    """Reads xre from RPN representation.
  
    :param s: the RPN representation of the regular expression
    :type s: string
    :rtype: xre"""
    (nf, reg) = _rpn2xre(re.sub("@epsilon", "@", s), 0)
    return reg


def _rpn2xre(s, i):
    """
    :param s:
    :param i:
    :return:"""
    if s[i] in "+.":
        (i1, arg1) = _rpn2xre(s, i + 1)
        (i2, arg2) = _rpn2xre(s, i1)
        if s[i] == ".":
            return i2, _concatrpn(arg1, arg2)
        else:
            return i2, _disjrpn(arg1, arg2)
    elif s[i] in "&.":
        (i1, arg1) = _rpn2xre(s, i + 1)
        (i2, arg2) = _rpn2xre(s, i1)
        if s[i] == ".":
            return i2, _concatrpn(arg1, arg2)
        else:
            return i2, _conjrpn(arg1, arg2)
    elif s[i] in "&+":
        (i1, arg1) = _rpn2xre(s, i + 1)
        (i2, arg2) = _rpn2xre(s, i1)
        if s[i] == "+":
            return i2, _disjrpn(arg1, arg2)
        else:
            return i2, _conjrpn(arg1, arg2)
    if s[i] == "~":
        (i1, arg1) = _rpn2xre(s, i + 1)
        if type(arg1) is xnot:
            return i1, xnot(arg1)
    if s[i] == "*":
        (i1, arg1) = _rpn2xre(s, i + 1)
        if type(arg1) is xstar:
            return i1, arg1
        else:
            return i1, xstar(arg1)
    if s[i] == "@":
        return i + 1, xepsilon()
    else:
        return i + 1, xre(s[i])


def _concatrpn(arg1, arg2):
    """
    :param arg1:
    :param arg2:
    :return:"""
    if type(arg1) is xepsilon:
        return arg2
    elif type(arg2) is xepsilon:
        return arg1
    if type(arg1) is xconcat:
        if type(arg2) is xconcat:
            return xconcat(arg1.val + arg2.val)
        else:
            return xconcat(arg1.val + [arg2])
    else:
        if type(arg2) is xconcat:
            return xconcat([arg1] + arg2.val)
        else:
            return xconcat([arg1, arg2])


def _disjrpn(arg1, arg2):
    """
    :param arg1:
    :param arg2:
    :return:"""
    if type(arg1) is xdisj:
        if type(arg2) is xdisj:
            s = arg1.val | arg2.val
        else:
            s = arg1.val | {arg2}
    else:
        if type(arg2) is xdisj:
            s = {arg1} | arg2.val
        else:
            s = {arg1, arg2}
    if len(s) == 0:
        return xempty()
    if len(s) == 1:
        return s.pop()
    else:
        return xdisj(s,self.Sigma)


def _conjrpn(arg1, arg2):
    """
    :param arg1:
    :param arg2:
    :return:"""
    if type(arg1) is xconj:
        if type(arg2) is xconj:
            s = arg1.val | arg2.val
        else:
            s = arg1.val | {arg2}
    else:
        if type(arg2) is xconj:
            s = {arg1} | arg2.val
        else:
            s = {arg1, arg2}
    if len(s) == 0:
        return xempty()
    if len(s) == 1:
        return s.pop()
    else:
        return xconj(s)


class ParseXRE(Yappy):
    """Parser for xre """
    # TODO: FALTA O SIGMAP E SIGMAS no common!"
    def __init__(self, no_table=0, table='.tablexreg'):
        """
        :param no_table:
        :param table:
        :return:"""
        grammar = [("r", ["r", "|", "c1"], self.DisjRule),
                   ("r", ["c1"], self.DefaultRule),
                   ("c1", ["c1", "&", "c"], self.ConjRule),
                   ("c1", ["c"], self.DefaultRule),
                   ("c", ["c", "s"], self.ConcatRule),
                   ("c", ["s"], self.DefaultRule),
                   ("s", ["s", "*"], self.StarRule),
                   ("s", ["f1"], self.DefaultRule),
                   ("f1", ["~", "f"], self.NotRule),
                   ("f1", ["f"], self.DefaultRule),
                   ("f", ["b"], self.DefaultRule),
                   ("f", ["(", "r", ")"], self.ParRule),
                   ("b", ["id"], self.BaseRule),
                   ("b", [EmptySet], self.BaseRule),
                   ("b", [Epsilon], self.BaseRule)]
        tokenize = [("\s+", ""),
                    (Epsilon, lambda x: (x, x)),
                    (EmptySet, lambda x: (x, x)),
                    #(common.SigmaS, lambda x: (x,x)),
                    #(common.SigmaP,lambda x: (x,x)),
                    ("[A-Za-z0-9]", lambda x: ("id", x)),
                    ("\|", lambda x: (x, x)),
                    ("\+", lambda x: ("|", x)),
                    ("\*", lambda x: (x, x)),
                    ("\&", lambda x: (x, x)),
                    ("\(|\)", lambda x: (x, x)),
                    ("~", lambda x: (x, x))]

        Yappy.__init__(self, tokenize, grammar, table, no_table)

    def DefaultRule(self, lst, context=None):
        """
        :param lst:
        :param context:
        :return:"""
        return lst[0]

    def BaseRule(self, lst, context=None):
        """
        :param lst:
        :param context:
        :return: """
        if lst[0] == Epsilon:
            return xepsilon()
        if lst[0] == EmptySet:
            return xempty()
            #if lst[0] == common.SigmaS:
        #  return xsigmaS()
        #if lst[0] == common.SigmaP:
        #  return xsigmaP()
        return xre(lst[0])

    def ParRule(self, lst, context=None):
        """
        :param lst:
        :param context:
        :return:"""
        return lst[1]

    def DisjRule(self, lst, context=None):
        """
        :param lst:
        :param context:
        :return: """
        return self._disj(lst)

    def _disj(self, lst):
        """
        :param lst:
        :return: """
        if type(lst[2]) is xempty:
            return lst[0]
        elif type(lst[0]) is xempty:
            return lst[2]
        else:
            if type(lst[2]) is xdisj and type(lst[0]) is xdisj:
                s = lst[2].val | lst[0].val
            elif type(lst[0]) is xdisj:
                s = lst[0].val | {lst[2]}
            elif type(lst[2]) is xdisj:
                s = lst[2].val | {lst[0]}
            else:
                s = {lst[0], lst[2]}
            if len(s) == 0:
                return xempty()
            if len(s) == 1:
                return s.pop()
            else:
                return xdisj(s)

    def ConcatRule(self, lst, context=None):
        """
        :param lst:
        :param context:
        :return:"""
        return self._concat(lst)

    def _concat(self, lst):
        """
        :param lst:
        :return: """
        if type(lst[1]) is xepsilon:
            return lst[0]
        elif type(lst[0]) is xepsilon:
            return lst[1]
        elif type(lst[1]) is xempty or type(lst[0]) is xempty:
            return xempty()
        elif type(lst[1]) is xconcat and type(lst[0]) is xconcat:
            return xconcat(lst[0].val + lst[1].val)
        elif type(lst[0]) is xconcat:
            return xconcat(lst[0].val + [lst[1]])
        elif type(lst[1]) is xconcat:
            return xconcat([lst[0]] + lst[1].val)
        else:
            return xconcat(lst)

    def ConjRule(self, lst, context=None):
        """
        :param lst:
        :param context:
        :return: """
        return self._conj(lst)

    def _conj(self, lst):
        """
        :param lst:
        :return: """
        if type(lst[0]) is xepsilon:
            if lst[2].ewp():
                return xepsilon()
            else:
                return xempty()
        elif type(lst[2]) is xepsilon:
            if lst[0].ewp():
                return xepsilon()
            else:
                return xempty()
        elif type(lst[0]) is xempty or type(lst[2]) is xempty:
            return xempty()
        else:
            if type(lst[2]) is xconj and type(lst[0]) is xconj:
                s = lst[2].val | lst[0].val
            elif type(lst[0]) is xconj:
                s = lst[0].val | {lst[2]}
            elif type(lst[2]) is xconj:
                s = lst[2].val | {lst[0]}
            else:
                s = {lst[0], lst[2]}
            if len(s) == 0:
                return xempty()
            if len(s) == 1:
                return s.pop()
            else:
                return xconj(s)

    def StarRule(self, lst, context=None):
        """
        :param lst:
        :param context:
        :return: """
        return xstar(lst[0])

    def NotRule(self, lst, context=None):
        """
        :param lst:
        :param context:
        :return: """
        return xnot(lst[1])


def str2xre(s, parser=ParseXRE, no_table=1, sigma=None, strict=False):
    """ Reads a xre from string.

    :param str s:  the string representation of the regular expression
    :param parser: a parser generator for regexps
    :type parser: Yappy
    :param int  no_table:
    :param sigma: alphabet of the regular expression
    :type sigma: list or set of symbols
    :param bool  strict: if True tests if the symbols of the regular expression are included in the sigma
    :rtype: xre"""
    s = re.sub("\s+", "", s)
    d = parser(no_table)
    try:
        reg = d.input(s)
    except LRParserError:
        raise regexpInvalid(s)
    if sigma is not None:
        reg.setSigma(sigma, strict)
    elif strict:
        reg.setSigma(reg.setOfSymbols())
    return reg


def to_x(reg):
    """Reads xre from FAdo regexp.
  
    :param reg:
    :arg re: the FAdo representation regexp for a regular expression.
    :type reg: regexp
    :rtype: xre"""
    if type(reg) is reex.regexp:
        return to_xregexp(reg)
    if type(reg) is reex.emptyset:
        return to_xempty(reg)
    if type(reg) is reex.epsilon:
        return to_xepsilon(reg)
    if type(reg) is reex.disj:
        return to_xdisj(reg)
    if type(reg) is reex.concat:
        return to_xconcat(reg)
    if type(reg) is reex.star:
        return to_xstar(reg)
    if type(reg) is conj:
        return to_xconj(reg)


def to_xregexp(reg):
    """
    :param reg:
    :return:"""
    return xre(reg.val)


def to_xempty(_):
    """
    :param _:
    :return: """
    return xempty()


def to_xepsilon(_):
    """
    :param _:
    :return: """
    return xepsilon()


def to_xdisj(reg):
    """
    :param reg:
    :return:"""
    return xdisj(_to_xdisj(reg))


def _to_xdisj(reg):
    """
    :param reg:
    :return: """
    if type(reg.arg1) is reex.disj:
        if type(reg.arg2) is reex.disj:
            return _to_xdisj(reg.arg1) | _to_xdisj(reg.arg2)
        else:
            return _to_xdisj(reg.arg1) | {to_x(reg.arg2)}
    else:
        if type(reg.arg2) is reex.disj:
            return {to_x(reg.arg1)} | _to_xdisj(reg.arg2)
        else:
            return {to_x(reg.arg1)} | {to_x(reg.arg2)}


def to_xconcat(reg):
    """
    :param reg:
    :return: """
    if type(reg.arg1) is reex.epsilon and type(reg.arg2) is reex.epsilon:
        return xepsilon()
    elif type(reg.arg1) is reex.epsilon:
        return to_x(reg.arg2)
    elif type(reg.arg2) is reex.epsilon:
        return to_x(reg.arg1)
    else:
        return xconcat(_to_xconcat(reg))


def _to_xconcat(reg):
    """

    :param reg:
    :return: """
    if type(reg.arg1) is reex.concat:
        if type(reg.arg2) is reex.concat:
            return _to_xconcat(reg.arg1) + _to_xconcat(reg.arg2)
        elif type(reg.arg2) is reex.epsilon:
            return _to_xconcat(reg.arg1)
        else:
            return _to_xconcat(reg.arg1) + [to_x(reg.arg2)]
    else:
        if type(reg.arg2) is reex.concat:
            return [to_x(reg.arg1)] + _to_xconcat(reg.arg2)
        elif type(reg.arg2) is reex.epsilon:
            return [to_x(reg.arg1)]
        else:
            return [to_x(reg.arg1)] + [to_x(reg.arg2)]


def to_xconj(reg):
    """

    :param reg:
    :return: """
    return xconj(_to_xconj(reg))


def _to_xconj(reg):
    """
    :param reg:
    :return:"""
    if type(reg.arg1) is conj:
        if type(reg.arg2) is conj:
            return _to_xconj(reg.arg1) | _to_xconj(reg.arg2)
        else:
            return _to_xconj(reg.arg1) | {to_x(reg.arg2)}
    else:
        if type(reg.arg2) is conj:
            return {to_x(reg.arg1)} | _to_xconj(reg.arg2)
        else:
            return {to_x(reg.arg1)} | {to_x(reg.arg2)}


def to_xstar(reg):
    """
    :param reg:
    :return:"""
    r = to_x(reg.arg)
    if type(r) == xepsilon:
        return r
    elif type(r) == xstar:
        return r
    else:
        return xstar(to_x(reg.arg))


class conj(reex.connective):
    """FAdo regexp class that represents the conjunction operation."""

    def __str__(self):
        """
        :return: """
        return "{0:s} & {1:s}".format(self.arg1._strP(), self.arg2._strP())

    def _strP(self):
        """
        :return: """
        return "({0:s} & {1:s})".format(self.arg1._strP(), self.arg2._strP())
