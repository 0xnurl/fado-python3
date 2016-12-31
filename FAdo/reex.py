# -*- coding: utf-8 -*-
"""**Regular expressions manipulation**

Regular expression classes and manipulation

.. *Authors:* Rogério Reis & Nelma Moreira

.. Contributions by
    - Marco Almeida
    - Hugo Gouveia
    - Eva Maia

.. *This is part of FAdo project*   http://fado.dcc.fc.up.pt

.. *Version:* 0.9.8

.. *Copyright:* 1999-2013 Rogério Reis & Nelma Moreira {rvr,nam}@dcc.fc.up.pt


.. This program is free software; you can redistribute it and/or modify it under the terms of the GNU General Public
   License as published by the Free Software Foundation; either version 2 of the License, or (at your option) any
   later version.

   This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied
   warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
   details.


   You should have received a copy of the GNU General Public Licensealong with this program; if not, write to the
   Free Software Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA."""
from __future__ import print_function
from __future__ import absolute_import
from __future__ import unicode_literals
from __future__ import division

from future import standard_library
standard_library.install_aliases()
from builtins import str
from builtins import *
from builtins import object
from collections import deque

from .yappy_parser import *

from .common import *
from . import fa
import copy


class regexp(object):
    """Base class for regular expressions.

    Used directly to represent a symbol. The type of the symbol is arbitrary.

    :var Sigma: alphabet set of strings
    :var val: the actual symbol

    .. inheritance-diagram:: regexp"""

    def __init__(self, val, sigma=None):
        """Constructor of a regular expression symbol.

        :arg val: the actual symbol"""
        self.val = val
        self.Sigma = sigma

    def __repr__(self):
        """Representation of the regular expression's syntactical tree."""
        return 'regexp({0:>s})'.format(self.__str__())

    def __str__(self):
        """String representation of the regular expression."""
        return str(self.val)

    _strP = __str__

    def __len__(self):
        """Size of the RE (the tree length)

        :rtype: int"""
        return self.treeLength()

    def rpn(self):
        """RPN representation
        :return: printable RPN representation"""
        return "%s" % repr(self.val)

    def __eq__(self, r):
        """Whether the string representations of two regular expressions are equal."""
        if type(r) == type(self) and ((self.Sigma is None) or (r.Sigma is None) or (self.Sigma == r.Sigma)):
            return repr(self) == repr(r)
        else:
            return False

    def __ne__(self, r):
        """Whether the string representations of two regular expressions are different."""
        return not self.__eq__(r)

    def __hash__(self):
        """Hash over regular expression's string representation"""
        return hash(repr(self))

    def __copy__(self):
        """Reconstruct the regular expression's syntactical tree, or, in other words,
           perform a shallow copy of the tree.
        :return: regular expression

        .. note::
           References to the expression's symbols in the leafs are preserved.

        .. attention:: Raw modifications on the regular expression's tree should be performed over
        a copy returned by this method, so that cached methods do not interfere."""

        return regexp(self.val)

    def setSigma(self, symbolSet, strict=False):
        """ Set the alphabet for a regular expression and all its nodes

        :arg symbolSet: accepted symbols. If None, alphabet is unset.
        :type symbolSet: list or set of str
        :arg strict: if True checks if setOfSymbols is included in symbolSet
        :type strict: bool

        ..attention: Normally this attribute is not defined in a regexp()"""
        if symbolSet is not None:
            if strict and not (self.setOfSymbols() <= symbolSet):
                raise regexpInvalidSymbols()
            self.Sigma = set(symbolSet)
        else:
            self.Sigma = None
        self._setSigma(strict)

    def _setSigma(self, strict=False):
        """

        :param strict:
        """
        pass

    def setOfSymbols(self):
        """Set of symbols that occur in a regular expression..

        :return: set of symbols
        :rtype: set of symbols"""
        return {self.val}

    def stringLength(self):
        """Length of the string representation of the regular expression.

        :rtype: integer"""
        return len(str(self))

    def measure(self, from_parent=None):
        """A list with four measures for regular expressions.

        :param from_parent:
        :rtype: [int,int,int,int]

        [alphabeticLength, treeLength, epsilonLength, starHeight]

        1. alphabeticLength: number of occurences of symbols of the alphabet;

        2. treeLength: number of functors in the regular expression, including constants.

        3. epsilonLength: number of occurrences of the empty word.

        4. starHeight: highest level of nested Kleene stars, starting at one for one star occurrence.

        .. attention::
           Methods for each of the measures are implemented independently. This is the most effective for obtaining
           more than one measure."""
        if not from_parent:
            from_parent = [0, 0, 0, 0]
        from_parent[0] += 1
        from_parent[1] += 1
        return from_parent

    def alphabeticLength(self):
        """Number of occurrences of alphabet symbols in the regular expression.

        :rtype: integer

        .. attention:: Doesn't include the empty word."""
        return 1

    def treeLength(self):
        """Number of nodes of the regular expression's syntactical tree.

        :rtype: integer"""
        return 1

    def epsilonLength(self):
        """Number of occurrences of the empty word in the regular expression.

        :rtype: integer"""
        return 0

    def starHeight(self):
        """Maximum level of nested regular expressions with a star operation applied.

        For instance, starHeight(((a*b)*+b*)*) is 3.

        :rtype: integer"""
        return 0

    def reduced(self, hasEpsilon=False):
        """Equivalent regular expression with the following cases simplified:

        1. Epsilon.RE = RE.Epsilon = RE

        2. EmptySet.RE = RE.EmptySet = EmptySet

        3. EmptySet + RE = RE + EmptySet = RE

        4. Epsilon + RE = RE + Epsilon = RE, where Epsilon is in L(RE)

        5. RE** = RE*

        6. EmptySet* = Epsilon* = Epsilon

        :param hasEpsilon: used internally to indicate that the language of which this term is a subterm has the empty
            word.
        :return: regular expression

        .. attention::
           Returned structure isn't strictly a duplicate. Use __copy__() for that purpose."""
        return self

    _reducedS = reduced

    def linearP(self):
        """Whether the regular expression is linear; i.e., the occurrence of a symbol in the expression is unique.

        :rtype: boolean"""
        return len(self.setOfSymbols()) is self.alphabeticLength()

    def first(self, parent_first=None):
        """List of possible symbols matching the first symbol of a string in the language of the regular expression.

        :param parent_first:
        :return: list of symbols"""
        if parent_first is None:
            return [self]
        parent_first.append(self)
        return parent_first

    def last(self, parent_last=None):
        """List of possible symbols matching the last symbol of a string in the language of the regular expression.

        :param parent_last:
        :return: list of symbols
        :rtype: list"""
        if parent_last is None:
            return [self]
        parent_last.append(self)
        return parent_last

    def followLists(self, lists=None):
        """Map of each symbol's follow list in the regular expression.

        :param lists:
        :return: map of symbols' follow lists
        :rtype: {symbol: list of symbols}

        .. attention::
           For first() and last() return lists, the follow list for certain symbols might have repetitions in the
           case  of follow maps calculated from star operators. The union of last(),
           first() and follow() sets are always disjoint when the regular expression is in star normal form (
           Brüggemann-Klein, 92), therefore FAdo implements them as lists. You should order exclusively,
           or take a set from a list in order to resolve repetitions."""
        if lists is None:
            return {self: []}
        if self not in lists:
            lists[self] = []
        return lists

    def followListsD(self, lists=None):
        """Map of each symbol's follow list in the regular expression.

        :param lists:
        :return: map of symbols' follow lists
        :rtype: {symbol: list of symbols}

        .. attention::
           For first() and last() return lists, the follow list for certain symbols might have repetitions in the case
           of follow maps calculated from star operators. The union of last(), first() and follow() sets are always
           disjoint

        .. seealso:: Sabine Broda, António Machiavelo, Nelma Moreira, and Rogério Reis. On the average size of
            glushkov and partial derivative automata. International Journal of Foundations of Computer Science,
            23(5):969-984, 2012.
            """
        if lists is None:
            return {self: []}
        if self not in lists:
            lists[self] = []
        return lists

    def followListsStar(self, lists=None):
        """Map of each symbol's follow list in the regular expression under a star.

        :param lists:
        :return: map of symbols' follow lists
        :rtype: {symbol: list of symbols}"""
        if lists is None:
            return {self: [self]}
        if self not in lists:
            lists[self] = [self]
        return lists

    def marked(self):
        """Regular expression in which every alphabetic symbol is marked with its position.

        The kind of regular expression returned is known, depending on the literary source, as marked,
        linear or restricted regular expression.

        :return: linear regular expression
        :rtype: regexp

        .. seealso:: R. McNaughton and H. Yamada, Regular Expressions and State Graphs for Automata,
            IEEE Transactions on Electronic Computers, V.9 pp:39-47, 1960

        ..attention: mark and unmark do not preserve the alphabet, neither set the new alphabet """
        return self._marked(0)[0]

    def _marked(self, pos):
        pos += 1
        return position((self.val, pos)), pos

    def unmarked(self):
        """The unmarked form of the regular expression. Each leaf in its syntactical tree becomes a regexp(),
        the epsilon() or the emptyset().

        :rtype: (general) regular expression"""
        return self.__copy__()

    def derivative(self, sigma):
        """Derivative of the regular expression in relation to the given symbol.

        :param sigma: an arbitrary symbol.
        :rtype: regular expression

        .. note:: whether the symbols belong to the expression's alphabet goes unchecked. The given symbol will be
           matched against the string representation of the regular expression's symbol.

        .. seealso:: J. A. Brzozowski, Derivatives of Regular Expressions. J. ACM 11(4): 481-494 (1964)"""
        if str(sigma) == str(self):
            return epsilon(self.Sigma)
        return emptyset(self.Sigma)

    def wordDerivative(self, word):
        """Derivative of the regular expression in relation to the given word,
           which is represented by a list of symbols.

        :param word: list of arbitrary symbols.
        :rtype: regular expression

        .. seealso:: J. A. Brzozowski, Derivatives of Regular Expressions. J. ACM 11(4): 481-494 (1964)

        .. note: semantically, the list represents a catenation of symbols (word), and its alphabet is not checked."""
        d = copy.deepcopy(self)
        for sigma in word:
            d = d.derivative(sigma)
        return d

    def partialDerivatives(self, sigma):
        """Set of partial derivatives of the regular expression in relation to given symbol.

        :param sigma: symbol in relation to which the derivative will be calculated.
        :return: set of regular expressions

        .. seealso:: Antimirov, 95"""
        if sigma == self.val:
            return {epsilon(self.Sigma)}
        return set()

    def linearForm(self):
        """Linear form of the regular expression , as a mapping from heads to sets of tails, so that each pair (head,
        tail) is a monomial in the set of linear forms.

        :return: dictionary mapping heads to sets of tails
        :rtype: {symbol: set([regular expressions])}

        .. seealso:: Antimirov, 95"""
        return {self.val: {epsilon(self.Sigma)}}

    def PD(self):
        """Closure of partial derivatives of the regular expression in relation to all words.

        :return: set of regular expressions
        :rtype: set

        .. seealso:: Antimirov, 95"""
        pd = set()
        stack = [self]
        while stack:
            r = stack.pop()
            pd.add(r)
            lf = r.linearForm()
            for head in lf:
                for tail in lf[head]:
                    if not tail in pd:
                        stack.append(tail)
        return pd

    def support(self):
        """'Support of a regular expression.

        :return: set of regular expressions
        :rtype: set

        .. seealso::
            Champarnaud, J.M., Ziadi, D.: From Mirkin's prebases to Antimirov's word partial derivative.
            Fundam. Inform. 45(3), 195-205 (2001)"""
        return {epsilon()}

    def _delAttr(self, attr):
        if hasattr(self, attr):
            delattr(self, attr)

    def _memoLF(self):
        if not hasattr(self, "_lf"):
            self._lf = {self.val: {epsilon(self.Sigma)}}

    def emptyP(self):
        """Whether the regular expression is the empty set.

        :rtype: Boolean"""
        return False

    def epsilonP(self):
        """Whether the regular expression is the empty word.

        :rtype: Boolean"""
        return False

    def ewp(self):
        """Whether the empty word property holds for this regular expression's language.

    :rtype: Boolean"""
        return False

    def snf(self, hollowdot=False):
        """Star Normal Form (SNF) of the regular expression.

        :param hollowdot:
        :return: regular expression in star normal form

        .. seealso: Brüggemann-Klein, 92"""
        return self

    def nfaThompson(self):
        """Epsilon-NFA constructed with Thompson's method that accepts the regular expression's language.

        :rtype: NFA

        .. seealso:: K. Thompson. Regular Expression Search Algorithm. CACM 11(6), 419-422 (1968)"""
        aut = fa.NFA()
        s0 = aut.addState()
        s1 = aut.addState()
        aut.setInitial([s0])
        if self.Sigma is None:
            aut.setSigma([self.val])
        else:
            aut.setSigma(self.Sigma)
        aut.setFinal([s1])  # val
        aut.addTransition(s0, self.val, s1)  # >(0)---->((1))
        return aut

    def nfaFollowEpsilon(self, trim=True):
        """Epsilon-NFA constructed with Ilie and Yu's method () that accepts the regular expression's language.

        :param trim:
        :return: NFA possibly with epsilon transitions
        :rtype: NFAe

        .. seealso:: Ilie & Yu, Follow automta, Inf. Comp. ,v. 186 (1),140-162,2003
        .. _a link: http://dx.doi.org/10.1016/S0890-5401(03)00090-7"""
        nfa = fa.NFAr()
        initial = nfa.addState("Initial")
        final = nfa.addState("Final")
        if self.Sigma is not None:
            nfa.setSigma(self.Sigma)
        self._nfaFollowEpsilonStep((nfa, initial, final))
        if len(nfa.delta.get(initial, [])) == 1 and \
                len(nfa.delta[initial].get(Epsilon, [])) == 1:
            new_initial = nfa.delta[initial][Epsilon].pop()
            del (nfa.delta[initial])
            nfa.deltaReverse[new_initial][Epsilon].remove(initial)
            initial = new_initial
        nfa.setInitial([initial])
        nfa.setFinal([final])
        if trim:
            nfa.trim()
        return nfa

    def _nfaFollowEpsilonStep(self, conditions):
        """Construction step of the Epsilon-NFA defined by Ilie & Yu for this class.

        :param conditions: A tuple consisting of an NFA, the initial state, and the final state in the context. A
        sub-automaton within the given automaton is thus constructed."""
        nfa, initial, final = conditions
        nfa.addSigma(self.val)
        nfa.addTransition(initial, self.val, final)

    def nfaGlushkov(self):
        """ Position or Glushkov automaton of the regular expression. Recursive method.


        :return: NFA
        """
        nfa = fa.NFA()
        initial = nfa.addState("Initial")
        nfa.addInitial(initial)
        if self.Sigma is not None:
            nfa.setSigma(self.Sigma)
        _, final = self._nfaGlushkovStep(nfa, nfa.Initial, set())
        nfa.Final = final
        return nfa

    def _nfaGlushkovStep(self, nfa, initial, final):
        """

        :param nfa:
        :param initial:
        :param final:
        :return:
        """
        try:
            target = nfa.addState(self.val)
        except DuplicateName:
            target = nfa.addState()
            # target = nfa.stateIndex(self.val)
        for source in initial:
            nfa.addTransition(source, self.val, target)
        final.add(target)
        return initial, final

    def nfaNaiveFollow(self):
        """NFA that accepts the regular expression's language, and is equal in structure to the follow automaton.

        :rtype: NFA

        .. note:: Included for testing purposes.

        .. seealso:: Ilie & Yu (Follow Automata, 2003)"""
        return self.snf().marked().nfaGlushkov().minimal().unmark()

    def nfaFollow(self):
        """NFA that accepts the regular expression's language, whose structure, and construction.

        :rtype: NFA

        .. seealso:: Ilie & Yu (Follow Automata, 03)"""
        nfa = self.nfaFollowEpsilon(False).toNFA()
        queue = deque(nfa.Initial)
        inverse_topo_order = deque()
        visited = set(nfa.Initial)
        while queue:
            state = queue.popleft()
            if nfa.hasTransitionP(state, Epsilon):
                inverse_topo_order.appendleft(state)
            if state in nfa.delta:
                for symbol in nfa.delta[state]:
                    for s in nfa.delta[state][symbol]:
                        if s not in visited:
                            queue.append(s)
                            visited.add(s)
        for i in inverse_topo_order:
            nfa.closeEpsilon(i)
        nfa.trim()
        return nfa

    def nfaPD(self):
        """NFA that accepts the regular expression's language,
           and which is constructed from the expression's partial derivatives.

        :return: partial derivatives [or equation] automaton
        :rtype: NFA

        .. seealso:: V. M. Antimirov, Partial Derivatives of Regular Expressions and Finite Automaton Constructions
           .Theor. Comput. Sci.155(2): 291-319 (1996)"""
        nfa = fa.NFA()
        i = nfa.addState(self)
        nfa.addInitial(i)
        if self.Sigma is not None:
            nfa.setSigma(self.Sigma)
        stack = [(self, i)]
        added_states = {self: i}
        while stack:
            state, state_idx = stack.pop()
            state_lf = state.linearForm()
            for head in state_lf:
                tails = state_lf[head]
                nfa.addSigma(head)
                for pd in tails:
                    if pd in added_states:
                        pd_idx = added_states[pd]
                    else:
                        try:
                            pd_idx = nfa.addState(pd)
                        except DuplicateName:
                            pd_idx = nfa.stateIndex(pd)
                        added_states[pd] = pd_idx
                        stack.append((pd, pd_idx))
                    nfa.addTransition(state_idx, head, pd_idx)
            if state.ewp():
                nfa.addFinal(state_idx)
        return nfa

    def nfaPDO(self):
        """NFA that accepts the regular expression's language, and which is constructed from the expression's partial
         derivatives.

        .. note:: optimized version

        :return: partial derivatives [or equation] automaton
        :rtype: NFA"""
        nfa = fa.NFA()
        i = nfa.addState(self)
        nfa.addInitial(i)
        if self.Sigma is not None:
            nfa.setSigma(self.Sigma)
        stack = [(self, i)]
        added_states = {self: i}
        while stack:
            state, state_idx = stack.pop()
            state._memoLF()
            for head in state._lf:
                nfa.addSigma(head)
                for pd in state._lf[head]:
                    if pd in added_states:
                        pd_idx = added_states[pd]
                    else:
                        pd_idx = nfa.addState(pd)
                        added_states[pd] = pd_idx
                        stack.append((pd, pd_idx))
                    nfa.addTransition(state_idx, head, pd_idx)
            if state.ewp():
                nfa.addFinal(state_idx)
        self._delAttr("_lf")
        return nfa

    def nfaPosition(self, lstar=True):
        """Position automaton of the regular expression.

        :arg lstar: if not None followlists are computed dijunct
        :type lstar: boolean
        :return: position NFA
        :rtype: NFA

        .. seealso:  Glushkov, 61"""
        nfa = fa.NFA()
        initial = nfa.addState("Initial")
        nfa.addInitial(initial)
        if self.Sigma is not None:
            nfa.setSigma(self.Sigma)
        return self.marked()._faPosition(nfa, initial, lstar)

    def dfaPosition(self):
        """Deterministic position automaton of a regular expression.

        :return: position DFA
        :rtype: DFA

        :raise common.DFAnotNFAFAdo: if not DFA

        .. note:: If this expression is not linear (cf. linearP()), exception may be raised
                  on non-deterministic transitions.

        .. seealso:  Glushkov, 61"""
        dfa = fa.DFA()
        initial = dfa.addState("Initial")
        dfa.setInitial(initial)
        if self.Sigma is not None:
            dfa.setSigma(self.Sigma)
        return self.marked()._faPosition(dfa, initial)

    def _faPosition(self, aut, initial, lstar=True):
        if self.ewp():
            aut.addFinal(initial)
        stack = []
        added_states = {}
        for sym in self.first():
            try:
                state_idx = aut.addState(str(sym))
            except DuplicateName:
                state_idx = aut.stateIndex(str(sym))
            added_states[sym] = state_idx
            stack.append((sym, state_idx))
            aut.addTransition(initial, sym.symbol(), state_idx)
        if lstar is False:
            follow_sets = self.followLists()
        else:
            follow_sets = self.followListsD()
        while stack:
            state, state_idx = stack.pop()
            for sym in follow_sets[state]:
                if sym in added_states:
                    next_state_idx = added_states[sym]
                else:
                    next_state_idx = aut.addState(str(sym))
                    added_states[sym] = next_state_idx
                    stack.append((sym, next_state_idx))
                aut.addTransition(state_idx, sym.symbol(), next_state_idx)
        for sym in self.last():
            if sym in added_states:
                aut.addFinal(added_states[sym])
        return aut

    def nfaPSNF(self):
        """Position or Glushkov automaton of the regular expression constructed from the expression's star normal form.

        :return: position automaton
        :rtype: NFA

        .. seeall: Brüggemann-Klein, 92"""
        return self.snf().nfaPosition(lstar=False)

    def _dfaD(self):
        """Word derivatives automaton of the regular expression

        :return: word derivatives automaton
        :rtype: DFA

        .. attention:
             This is a probably non terminating method. Must be removed. (nam)
        .. seealso:
            J. A. Brzozowski, Derivatives of Regular Expressions. J. ACM 11(4): 481-494 (1964)"""
        dfa = fa.DFA()
        initial = self
        initial_idx = dfa.addState(initial)
        dfa.setInitial(initial_idx)
        if self.Sigma is not None:
            dfa.setSigma(self.Sigma)
        dfa.setSigma(initial.setOfSymbols())
        stack = [(initial, initial_idx)]
        while stack:
            state, state_idx = stack.pop()
            for sigma in dfa.Sigma:
                d = state.derivative(sigma).reduced()
                if not d in dfa.States:
                    d_idx = dfa.addState(d)
                    stack.append((d, d_idx))
                else:
                    d_idx = dfa.stateIndex(d)
                dfa.addTransition(state_idx, sigma, d_idx)
            if state.ewp():
                dfa.addFinal(state_idx)
        return dfa

    def toNFA(self, nfa_method="nfaPD"):
        """NFA that accepts the regular expression's language.
        :param nfa_method: """
        return self.__getattribute__(nfa_method)()

    def toDFA(self):
        """DFA that accepts the regular expression's language

        .. versionadded 0.9.6"""
        return self.toNFA().toDFA()

    def compare(self, r, cmp_method="compareMinimalDFA", nfa_method="nfaPosition"):
        """Compare with another regular expression for equivalence.
        :param r:
        :param cmp_method:
        :param nfa_method:
        """
        if cmp_method == "compareMinimalDFA":
            return self.compareMinimalDFA(r, nfa_method)

    def equivalentP(self, other):
        """Tests equivalence

        :param other:
        :rtype: bool

        .. versionadded: 0.9.6"""
        if issubclass(type(other), fa.OFA):
            return other.equivalentP(self)
        return self.compare(other)

    def compareMinimalDFA(self, r, nfa_method="nfaPosition"):
        """Compare with another regular expression for equivalence through minimal DFAs.
        :param r:
        :param nfa_method: """
        fa0 = self.toNFA(nfa_method).toDFA()
        fa1 = r.toNFA(nfa_method).toDFA()
        return fa0 == fa1

    def evalWordP(self, word):
        """Verifies if a word is a member of the language represented by the regular expression.

        :param str word: the word
        :rtype: bool"""

        return self.wordDerivative(word).ewp()

    def reversal(self):
        """Reversal of regexp

        :rtype: regexp"""
        return self.__copy__()


class specialConstant(regexp):
    """Base class for Epsilon and EmptySet

    .. inheritance-diagram:: specialConstant"""

    def __init__(self, sigma=None):
        """
        :param sigma: """
        self.Sigma = sigma

    def __copy__(self):
        """
        :return: """
        return self

    def setOfSymbols(self):
        """
        :return: """
        return set()

    def alphabeticLength(self):
        """
        :return: """
        return 0

    def _marked(self, pos):
        """
        :param pos:
        :return: """
        return self, pos

    def unmarked(self):
        """The unmarked form of the regular expression. Each leaf in its syntactical tree becomes a regexp(),
        the epsilon() or the emptyset().

        :rtype: (general) regular expression"""
        return self

    def first(self, parent_first=None):
        """
        :param parent_first:
        :return: """
        if parent_first is None:
            return []
        return parent_first

    def last(self, parent_last=None):
        """
        :param parent_last:
        :return: """
        if parent_last is None:
            return []
        return parent_last

    def followLists(self, lists=None):
        """
        :param lists:
        :return: """
        if lists is None:
            return {}
        return lists

    def followListsD(self, lists=None):
        """
        :param lists:
        :return: """
        if lists is None:
            return {}
        return lists

    def followListsStar(self, lists=None):
        """
        :param lists:
        :return: """
        if lists is None:
            return {}
        return lists

    def derivative(self, sigma):
        """
        :param sigma:
        :return: """
        return emptyset(self.Sigma)

    def wordDerivative(self, word):
        """
        :param word:
        :return: """
        return self

    def linearForm(self):
        """
        :return: """
        return {}

    def _memoLF(self):
        """
        :return: """
        return self._lf

    def _delAttr(self, attr):
        """

        :param attr:
        :return:"""
        pass

    _lf = {}

    def support(self):
        """
        :return:"""
        return set()

    def reversal(self):
        """Reversal of regexp

        :rtype: regexp"""
        return self.__copy__()


class epsilon(specialConstant):
    """Class that represents the empty word.

    .. inheritance-diagram:: epsilon"""

    def __repr__(self):
        """
        :return: str"""
        return "epsilon()"

    def __str__(self):
        """
        :return: str"""
        return Epsilon

    _strP = __str__

    def rpn(self):
        """
        :return: str"""
        return Epsilon

    def __hash__(self):
        """
        :return: """
        return hash(Epsilon)

    def epsilonP(self):
        """
        :rtype: bool"""
        return True

    def measure(self, from_parent=None):
        """
        :param from_parent:
        :return: measures"""
        if not from_parent:
            return [0, 1, 1, 0]
        from_parent[1] += 1
        from_parent[2] += 1
        return from_parent

    def epsilonLength(self):
        """
        :rtype: int """
        return 1

    def ewp(self):
        """
        :rtype: bool"""
        return True

    def nfaThompson(self):
        """
        :rtype: NFA """
        aut = fa.NFA()
        s0 = aut.addState()
        s1 = aut.addState()
        aut.setInitial([s0])
        if self.Sigma is not None:
            aut.setSigma(self.Sigma)
        else:
            aut.setSigma([])
        aut.setFinal([s1])
        aut.addTransition(s0, Epsilon, s1)
        return aut

    def _nfaGlushkovStep(self, nfa, initial, final):
        """
        :param nfa:
        :param initial:
        :param final:
        :return: """
        final.update(initial)
        return initial, final

    def _nfaFollowEpsilonStep(self, conditions):
        """
        :param conditions:
        :return: """
        nfa, initial, final = conditions
        nfa.addTransition(initial, Epsilon, final)

    def snf(self, _hollowdot=False):
        """
        :param _hollowdot:
        :return: """
        if _hollowdot:
            return emptyset(self.Sigma)
        return self

    def partialDerivatives(self, sigma):
        """
        :param sigma:
        :return: """
        return set()


class emptyset(specialConstant):
    """Class that represents the empty set.

    .. inheritance-diagram:: emptyset"""

    def __repr__(self):
        """
        :return: """
        return "emptyset()"

    def __str__(self):
        """
        :return: """
        return EmptySet

    def rpn(self):
        """
        :return: """
        return EmptySet

    _strP = __str__

    def __hash__(self):
        """
        :return: """
        return hash(EmptySet)

    def emptyP(self):
        """
        :return: """
        return True

    def epsilonP(self):
        """
        :return: """
        return False

    def measure(self, from_parent=None):
        """
        :param from_parent:
        :return: """
        if not from_parent:
            return [0, 1, 0, 0]
        from_parent[1] += 1
        return from_parent

    def epsilonLength(self):
        """
        :return: """
        return 0

    def ewp(self):
        """
        :return: """
        return False

    def nfaThompson(self):
        aut = fa.NFA()
        s0 = aut.addState()
        s1 = aut.addState()
        aut.setInitial([s0])
        aut.setFinal([s1])
        if self.Sigma is not None:
            aut.setSigma(self.Sigma)
        return aut

    def _nfaGlushkovStep(self, nfa, initial, final):
        return initial, final

    def _nfaFollowEpsilonStep(self, conditions):
        pass

    def snf(self, _hollowdot=False):
        return self

    def partialDerivatives(self, sigma):
        return set()


class connective(regexp):
    """Base class for concatenation, and disjunction operations.

    .. inheritance-diagram:: connective"""

    def __init__(self, arg1, arg2, sigma=None):
        self.arg1 = arg1
        self.arg2 = arg2
        self.Sigma = sigma

    def __repr__(self):
        return "%s(%s,%s)" % (self.__class__.__name__,
                              repr(self.arg1), repr(self.arg2))

    def __copy__(self):
        return self.__class__(self.arg1.__copy__(), self.arg2.__copy__(), copy.copy(self.Sigma))

    def _setSigma(self, s):
        self.arg1.setSigma(self.Sigma, s)
        self.arg2.setSigma(self.Sigma, s)

    def unmarked(self):
        return self.__class__(self.arg1.unmarked(), self.arg2.unmarked())

    def _marked(self, pos):
        (r1, pos1) = self.arg1._marked(pos)
        (r2, pos2) = self.arg2._marked(pos1)
        return self.__class__(r1, r2), pos2

    def setOfSymbols(self):
        setOS = self.arg1.setOfSymbols()
        setOS.update(self.arg2.setOfSymbols())
        return setOS

    def measure(self, from_parent=None):
        if not from_parent:
            from_parent = [0, 0, 0, 0]
        measure = self.arg1.measure(from_parent)
        starh, measure[3] = measure[3], 0
        measure = self.arg2.measure(measure)
        measure[1] += 1
        measure[3] = max(measure[3], starh)
        return measure

    def alphabeticLength(self):
        return self.arg1.alphabeticLength() + self.arg2.alphabeticLength()

    def treeLength(self):
        return 1 + self.arg1.treeLength() + self.arg2.treeLength()

    def epsilonLength(self):
        return self.arg1.epsilonLength() + self.arg2.epsilonLength()

    def starHeight(self):
        return max(self.arg1.starHeight(), self.arg2.starHeight())

    def _cross(self, lists):
        """ Computes the pairs lastxfirst and firstxlast of the arguments

        :param lists:
        :return: pairs as a dictionary
        :rtype: dictionary"""
        for symbol in self.arg1.last():
            if not symbol in lists:
                lists[symbol] = self.arg2.first()
            else:
                lists[symbol] += self.arg2.first()
        for symbol in self.arg2.last():
            if not symbol in lists:
                lists[symbol] = self.arg1.first()
            else:
                lists[symbol] += self.arg1.first()
        return lists


class disj(connective):
    """Class for disjuction operation on regular expressions.

    .. inheritance-diagram:: disj"""

    def __str__(self):
        return "%s + %s" % (self.arg1._strP(), self.arg2._strP())

    def _strP(self):
        return "(%s + %s)" % (self.arg1._strP(), self.arg2._strP())

    def rpn(self):
        return "+%s%s" % (self.arg1.rpn(), self.arg2.rpn())

    def ewp(self):
        return self.arg1.ewp() or self.arg2.ewp()

    def first(self, parent_first=None):
        parent_first = self.arg1.first(parent_first)
        return self.arg2.first(parent_first)

    def last(self, parent_last=None):
        parent_last = self.arg1.last(parent_last)
        return self.arg2.last(parent_last)

    def followLists(self, lists=None):
        if lists is None:
            lists = {}
        self.arg1.followLists(lists)
        return self.arg2.followLists(lists)

    def followListsD(self, lists=None):
        if lists is None:
            lists = {}
        self.arg1.followListsD(lists)
        return self.arg2.followListsD(lists)

    def followListsStar(self, lists=None):
        if lists is None:
            lists = {}
        self.arg1.followListsStar(lists)
        self.arg2.followListsStar(lists)
        return self._cross(lists)

    def reduced(self, hasEpsilon=False):
        left = self.arg1.reduced(hasEpsilon or self.arg2.ewp())
        right = self.arg2.reduced(hasEpsilon or left.ewp())
        if left.emptyP():
            return right
        if right.emptyP():
            return left
        if left.epsilonP() and (hasEpsilon or right.ewp()):
            return right
        if right.epsilonP() and (hasEpsilon or left.ewp()):
            return left
        if left is self.arg1 and right is self.arg2:
            return self
        reduced = disj(left, right, self.Sigma)
        reduced._reduced = True
        return reduced

    _reducedS = reduced

    def derivative(self, sigma):
        left = self.arg1.derivative(sigma)
        right = self.arg2.derivative(sigma)
        return disj(left, right, self.Sigma)

    def partialDerivatives(self, sigma):
        pdset = self.arg1.partialDerivatives(sigma)
        pdset.update(self.arg2.partialDerivatives(sigma))
        return pdset

    def linearForm(self):
        arg1_lf = self.arg1.linearForm()
        arg2_lf = self.arg2.linearForm()
        lf = {}
        for head in set(list(arg1_lf.keys()) + list(arg2_lf.keys())):
            tails = arg1_lf.get(head, set()) | arg2_lf.get(head, set())
            if tails != set():
                lf[head] = tails
        return lf

    def _delAttr(self, attr):
        if hasattr(self, attr):
            delattr(self, attr)
            self.arg1._delAttr(attr)
            self.arg2._delAttr(attr)

    def _memoLF(self):
        if hasattr(self, "_lf"):
            return
        self.arg1._memoLF()
        self.arg2._memoLF()
        self._lf = {}
        for head in self.arg1._lf:
            self._lf[head] = set(self.arg1._lf[head])
        for head in self.arg2._lf:
            try:
                self._lf[head].update(self.arg2._lf[head])
            except KeyError:
                self._lf[head] = set(self.arg2._lf[head])

    def snf(self, hollowdot=False):
        return disj(self.arg1.snf(hollowdot), self.arg2.snf(hollowdot), self.Sigma)

    def nfaThompson(self):
        """ Returns an NFA (Thompson) that accepts the RE.

    :rtype: NFA

    .. graphviz::

       digraph dij {
        "0" -> "si1" [label=e];
        "si1" -> "sf1" [label="arg1"];
        "sf1" -> "1" [label=e];
        "0" -> "si2" [label=e];
        "si2" -> "sf2" [label="arg2"];
        "sf2" -> "1" [label=e];
        }"""
        au = fa.NFA()
        if self.Sigma is not None:
            au.setSigma(self.Sigma)
        s0, s1 = au.addState(), au.addState()
        au.setInitial([s0])
        au.setFinal([s1])
        si1, sf1 = au._inc(self.arg1.nfaThompson())
        au.addTransition(s0, Epsilon, si1)
        au.addTransition(sf1, Epsilon, s1)
        si2, sf2 = au._inc(self.arg2.nfaThompson())
        au.addTransition(s0, Epsilon, si2)
        au.addTransition(sf2, Epsilon, s1)
        return au

    def _nfaGlushkovStep(self, nfa, initial, final):
        _, newFinal = self.arg1._nfaGlushkovStep(nfa, initial, set(final))
        _, final = self.arg2._nfaGlushkovStep(nfa, initial, final)
        final.update(newFinal)
        return initial, final

    def _nfaFollowEpsilonStep(self, conditions):
        self.arg1._nfaFollowEpsilonStep(conditions)
        self.arg2._nfaFollowEpsilonStep(conditions)

    def reversal(self):
        """Reversal of regexp
        :rtype: regexp"""
        return disj(self.arg1.reversal(), self.arg2.reversal(), sigma=self.Sigma)

class power(regexp):
    """Class for power operation  on regular expressions.

    .. inheritance-diagram:: power"""

    def __init__(self, arg, n=1, sigma=None):
        self.arg = arg
        self.pw = n
        self.Sigma = sigma

    def __str__(self):
        return "%s^(%s)" % (self.arg._strP(), self.pw)

    _strP = __str__

    def __repr__(self):
        return "power(%s,%s)" % repr(self.arg, self.pw)

    def __copy__(self):
        return power(copy.copy(self.arg), self.pw, copy.copy(self.Sigma))

    def setOfSymbols(self):
        return self.arg.setOfSymbols()

    def reversal(self):
        """
            Reversal of regexp
        :rtype: regexp"""
        return power(self.arg.reversal(), self.pw, self.Sigma)


class star(regexp):
    """Class for iteration operation (aka Kleene star, or Kleene closure) on regular expressions.

    .. inheritance-diagram:: star"""

    def __init__(self, arg, sigma=None):
        self.arg = arg
        self.Sigma = sigma

    def __str__(self):
        return "%s*" % self.arg._strP()

    _strP = __str__

    def __repr__(self):
        return "star(%s)" % repr(self.arg)

    def __copy__(self):
        return star(copy.copy(self.arg), copy.copy(self.Sigma))

    def rpn(self):
        return "*%s" % self.arg.rpn()

    def setOfSymbols(self):
        return self.arg.setOfSymbols()

    def _setSigma(self, s):
        self.arg.setSigma(self.Sigma, s)

    def measure(self, from_parent=None):
        if not from_parent: from_parent = [0, 0, 0, 0]
        measure = self.arg.measure(from_parent)
        measure[1] += 1
        measure[3] += 1
        return measure

    def alphabeticLength(self):
        return self.arg.alphabeticLength()

    def treeLength(self):
        return 1 + self.arg.treeLength()

    def epsilonLength(self):
        return self.arg.epsilonLength()

    def starHeight(self):
        return 1 + self.arg.starHeight()

    def first(self, parent_first=None):
        return self.arg.first(parent_first)

    def last(self, parent_first=None):
        return self.arg.last(parent_first)

    def followLists(self, lists=None):
        lists = self.arg.followLists(lists)
        for symbol in self.arg.last():
            if not symbol in lists:
                lists[symbol] = self.arg.first()
            else:
                lists[symbol] += self.arg.first()
        return lists

    def followListsD(self, lists=None):
        return self.arg.followListsStar(lists)

    def followListsStar(self, lists=None):
        return self.arg.followListsStar(lists)

    def unmarked(self):
        return star(self.arg.unmarked())

    def _marked(self, pos):
        (r1, pos1) = self.arg._marked(pos)
        return star(r1), pos1

    def reduced(self, hasEpsilon=False):
        rarg = self.arg._reducedS(True)
        if rarg.epsilonP() or rarg.emptyP():
            return epsilon(self.Sigma)
        if self.arg is rarg:
            return self
        reduced = star(rarg, self.Sigma)
        return reduced

    # noinspection PyUnusedLocal
    def _reducedS(self, hasEpsilon=False):
        return self.arg._reducedS(True)

    def derivative(self, sigma):
        d = self.arg.derivative(sigma)
        return concat(d, self, self.Sigma)

    def partialDerivatives(self, sigma):
        arg_pdset = self.arg.partialDerivatives(sigma)
        pds = set()
        for pd in arg_pdset:
            if pd.emptyP():
                pds.add(emptyset(self.Sigma))
            elif pd.epsilonP():
                pds.add(self)
            else:
                pds.add(concat(pd, self, self.Sigma))
        return pds

    def linearForm(self):
        arg_lf = self.arg.linearForm()
        lf = {}
        for head in arg_lf:
            lf[head] = set()
            for tail in arg_lf[head]:
                if tail.emptyP():
                    lf[head].add(emptyset(self.Sigma))
                elif tail.epsilonP():
                    lf[head].add(self)
                else:
                    lf[head].add(concat(tail, self, self.Sigma))
        return lf

    def _delAttr(self, attr):
        if hasattr(self, attr):
            delattr(self, attr)
            self.arg._delAttr(attr)

    def _memoLF(self):
        if hasattr(self, "_lf"):
            return
        self.arg._memoLF()
        self._lf = {}
        for head in self.arg._lf:
            pd_set = set()
            self._lf[head] = pd_set
            for tail in self.arg._lf[head]:
                if tail.emptyP():
                    pd_set.add(emptyset(self.Sigma))
                elif tail.epsilonP():
                    pd_set.add(self)
                else:
                    pd_set.add(concat(tail, self, self.Sigma))

    def ewp(self):
        return True

    def snf(self, _hollowdot=False):
        if _hollowdot:
            return self.arg.snf(True)
        return star(self.arg.snf(True), self.Sigma)

    def nfaThompson(self):
        """ Returns a NFA that accepts the RE.

    :rtype: NFA

    .. graphviz::

       digraph foo {
        "0" -> "1" [label=e];
        "0" -> "a" [label=e];
        "a" -> "b" [label=A];
        "b" -> "1" [label=e];
        "1" -> "0" [label=e];
        }"""

        sun = self.arg.nfaThompson()
        au = sun.dup()
        (s0, s1) = (au.addState(), au.addState())
        if self.Sigma is not None:
            au.setSigma(self.Sigma)
        au_initial = au.Initial.pop()
        au.addTransition(s0, Epsilon, s1)
        au.addTransition(s1, Epsilon, s0)
#        au.addTransition(list(au.Final)[0], Epsilon, au_initial)
        au.addTransition(s0, Epsilon, au_initial)
        au.addTransition(list(au.Final)[0], Epsilon, s1)  # we know by contruction
        au.setInitial([s0])  # that there is only one final state,
        au.setFinal([s1])  # and only one initial state
        return au

    def _nfaGlushkovStep(self, nfa, initial, final):
        previous_trans = {}
        for i_state in initial:
            if i_state in nfa.delta:
                previous_trans[i_state] = nfa.delta[i_state]
                del nfa.delta[i_state]
        new_initial, final = self.arg._nfaGlushkovStep(nfa, initial, final)
        for i_state in initial:
            if i_state in nfa.delta:
                for symbol in nfa.delta[i_state]:
                    for target in nfa.delta[i_state][symbol]:
                        for f_state in final:
                            nfa.addTransition(f_state, symbol, target)
        for i_state in previous_trans:
            for sym in previous_trans[i_state]:
                for target in previous_trans[i_state][sym]:
                    nfa.addTransition(i_state, sym, target)
        final.update(initial)
        return new_initial, final

    def _nfaFollowEpsilonStep(self, conditions):
        nfa, initial, final = conditions
        if initial is final:
            iter_state = final
        else:
            iter_state = nfa.addState()
        self.arg._nfaFollowEpsilonStep((nfa, iter_state, iter_state))
        tomerge = nfa.epsilonPaths(iter_state, iter_state)
        nfa.mergeStatesSet(tomerge)
        if initial is not final:
            nfa.addTransition(initial, Epsilon, iter_state)
            nfa.addTransition(iter_state, Epsilon, final)

    def reversal(self):
        """Reversal of regexp

        :rtype: regexp"""
        return star(self.arg.reversal(), sigma=self.Sigma)


class concat(connective):
    """Class for catenation operation on regular expressions.

    .. inheritance-diagram:: concat"""

    def __str__(self):
        return "%s %s" % (self.arg1._strP(), self.arg2._strP())

    def _strP(self):
        return "(%s %s)" % (self.arg1._strP(), self.arg2._strP())

    def rpn(self):
        return ".%s%s" % (self.arg1.rpn(), self.arg2.rpn())

    def ewp(self):
        return self.arg1.ewp() and self.arg2.ewp()

    def first(self, parent_first=None):
        if self.arg1.ewp():
            return self.arg2.first(self.arg1.first(parent_first))
        else:
            return self.arg1.first(parent_first)

    def last(self, parent_last=None):
        if self.arg2.ewp():
            return self.arg2.last(self.arg1.last(parent_last))
        else:
            return self.arg2.last(parent_last)

    def followLists(self, lists=None):
        lists = self.arg1.followLists(lists)
        self.arg2.followLists(lists)
        for symbol in self.arg1.last():
            if symbol not in lists:
                lists[symbol] = self.arg2.first()
            else:
                lists[symbol] += self.arg2.first()
        return lists

    def followListsD(self, lists=None):
        lists = self.arg1.followListsD(lists)
        self.arg2.followListsD(lists)
        for symbol in self.arg1.last():
            if symbol not in lists:
                lists[symbol] = self.arg2.first()
            else:
                lists[symbol] += self.arg2.first()
        return lists

    def followListsStar(self, lists=None):
        if lists is None:
            lists = {}
        if self.arg1.ewp():
            if self.arg2.ewp():
                self.arg1.followListsStar(lists)
                self.arg2.followListsStar(lists)
            else:
                self.arg1.followListsD(lists)
                self.arg2.followListsStar(lists)
        elif self.arg2.ewp():
            self.arg1.followListsStar(lists)
            self.arg2.followListsD(lists)
        else:
            self.arg1.followListsD(lists)
            self.arg2.followListsD(lists)
        return self._cross(lists)

    def reduced(self, hasEpsilon=False):
        left = self.arg1.reduced()
        right = self.arg2.reduced()
        if left.emptyP() or right.emptyP():
            return emptyset(self.Sigma)
        if left.epsilonP():
            if hasEpsilon:
                return self.arg2.reduced(True)
            return right
        if right.epsilonP():
            if hasEpsilon:
                return self.arg1.reduced(True)
            return left
        if left is self.arg1 and right is self.arg2:
            return self
        reduced = concat(left, right, self.Sigma)
        return reduced

    _reducedS = reduced

    def derivative(self, sigma):
        left = concat(self.arg1.derivative(sigma), self.arg2, self.Sigma)
        if self.arg1.ewp():
            right = self.arg2.derivative(sigma)
            return disj(left, right, self.Sigma)
        return left

    def partialDerivatives(self, sigma):
        pds = set()
        for pd in self.arg1.partialDerivatives(sigma):
            if pd.emptyP():
                pds.add(emptyset(self.Sigma))
            elif pd.epsilonP():
                pds.add(self.arg2)
            else:
                pds.add(concat(pd, self.arg2, self.Sigma))
        if self.arg1.ewp():
            pds.update(self.arg2.partialDerivatives(sigma))
        return pds

    def linearForm(self):
        arg1_lf = self.arg1.linearForm()
        lf = {}
        for head in arg1_lf:
            lf[head] = set()
            for tail in arg1_lf[head]:
                if tail.emptyP():
                    lf[head].add(emptyset(self.Sigma))
                elif tail.epsilonP():
                    lf[head].add(self.arg2)
                else:
                    lf[head].add(concat(tail, self.arg2, self.Sigma))
        if self.arg1.ewp():
            arg2_lf = self.arg2.linearForm()
            for head in arg2_lf:
                if head in lf:
                    lf[head].update(arg2_lf[head])
                else:
                    lf[head] = set(arg2_lf[head])
        return lf

    def _memoLF(self):
        if hasattr(self, "_lf"):
            return
        self.arg1._memoLF()
        self._lf = {}
        for head in self.arg1._lf:
            pd_set = set()
            self._lf[head] = pd_set
            for tail in self.arg1._lf[head]:
                if tail.emptyP():
                    pd_set.add(emptyset(self.Sigma))
                elif tail.epsilonP():
                    pd_set.add(self.arg2)
                else:
                    pd_set.add(concat(tail, self.arg2, self.Sigma))
        if self.arg1.ewp():
            self.arg2._memoLF()
            for head in self.arg2._lf:
                if head in self._lf:
                    self._lf[head].update(self.arg2._lf[head])
                else:
                    self._lf[head] = set(self.arg2._lf[head])

    def snf(self, _hollowdot=False):
        if not _hollowdot:
            return concat(self.arg1.snf(), self.arg2.snf(), self.Sigma)
        if self.ewp():
            return disj(self.arg1.snf(True), self.arg2.snf(True), self.Sigma)
        if self.arg1.ewp():
            return concat(self.arg1.snf(), self.arg2.snf(True), self.Sigma)
        if self.arg2.ewp():
            return concat(self.arg1.snf(True), self.arg2.snf(), self.Sigma)
        return concat(self.arg1.snf(), self.arg2.snf(), self.Sigma)

    def nfaThompson(self):  # >(0)--arg1-->(1)--->(2)--arg2-->((3))
        au = fa.NFA()
        if self.Sigma is not None:
            au.setSigma(self.Sigma)
        s0, s1 = au._inc(self.arg1.nfaThompson())
        s2, s3 = au._inc(self.arg2.nfaThompson())
        au.setInitial([s0])
        au.setFinal([s3])
        au.addTransition(s1, Epsilon, s2)
        return au

    def _nfaGlushkovStep(self, nfa, initial, final):
        initial, final = self.arg1._nfaGlushkovStep(nfa, initial, final)
        return self.arg2._nfaGlushkovStep(nfa, final, set())

    def _nfaFollowEpsilonStep(self, conditions):
        nfa, initial, final = conditions
        interm = nfa.addState()
        self.arg1._nfaFollowEpsilonStep((nfa, initial, interm))
        # At this stage, if the intermediate state has a single
        # incoming transition, and it's through Epsilon, then the
        # source becomes the new intermediate state:
        new_interm = nfa.unlinkSoleIncoming(interm)
        if new_interm is not None:
            interm = new_interm
        self.arg2._nfaFollowEpsilonStep((nfa, interm, final))
        # At this stage, if the intermediate state has a single
        # outgoing transition, and it's through Epsilon, then we merge
        # it with the target.
        if nfa.hasTransitionP(interm, Epsilon, final):
            return
        target = nfa.unlinkSoleOutgoing(interm)
        if target is not None:
            nfa.mergeStates(target, interm)

    def reversal(self):
        """Reversal of regexp
        :rtype: regexp"""
        return concat(self.arg2.reversal(), self.arg1.reversal(), sigma=self.Sigma)


class position(regexp):
    """Class for marked regular expression symbols.

    .. inheritance-diagram:: position"""

    def __init__(self, xxx_todo_changeme, sigma=None):
        (sym, pos) = xxx_todo_changeme
        self.val = (sym, pos)
        self.Sigma = sigma

    def __repr__(self):
        return "position%s" % repr(self.val)

    def __copy__(self):
        return position(self.val)

    def setOfSymbols(self):
        return {self.val}

    def unmarked(self):
        return regexp(self.val[0])

    def symbol(self):
        return self.val[0]


class ParseReg1(Yappy):
    """

    .. inheritance-diagram:: ParseReg1"""

    def __init__(self, no_table=0, table='.tablereg'):
        """  """
        grammar = [("r", ["r", "|", "c"], self.OrSemRule),
                   ("r", ["c"], self.DefaultSemRule),
                   ("c", ["c", "s"], self.ConcatSemRule),
                   ("c", ["s"], self.DefaultSemRule),
                   ("s", ["s", "*"], self.StarSemRule),
                   ("s", ["f"], self.DefaultSemRule),
                   ("f", ["b"], self.DefaultSemRule),
                   ("f", ["(", "r", ")"], self.ParSemRule),
                   ("b", ["id"], self.BaseSemRule),
                   ("b", [EmptySet], self.BaseSemRule),
                   ("b", [Epsilon], self.BaseSemRule)]
        tokenize = [("\s+", ""),
                    (Epsilon, lambda x: (x, x)),
                    (EmptySet, lambda x: (x, x)),
                    ("[A-Za-z0-9]", lambda x: ("id", x)),
                    ("\|", lambda x: (x, x)),
                    ("\+", lambda x: ("|", x)),
                    ("\*", lambda x: (x, x)),
                    ("\(|\)", lambda x: (x, x))]
        Yappy.__init__(self, tokenize, grammar, table, no_table)

    def DefaultSemRule(self, lst, context=None):
        return lst[0]

    def BaseSemRule(self, lst, context=None):
        if "sigma" in context:
            sigma = context["sigma"]
        else:
            sigma = None
        if lst[0] == Epsilon:
            return epsilon(sigma)
        if lst[0] == EmptySet:
            return emptyset(sigma)
        return regexp(lst[0], sigma)

    def ParSemRule(self, lst, context=None):
        return lst[1]

    def OrSemRule(self, lst, context=None):
        if "sigma" in context:
            sigma = context["sigma"]
        else:
            sigma = None
        return disj(lst[0], lst[2], sigma)

    def ConcatSemRule(self, lst, context=None):
        if "sigma" in context:
            sigma = context["sigma"]
        else:
            sigma = None
        return concat(lst[0], lst[1], sigma)

    def StarSemRule(self, lst, context=None):
        if "sigma" in context:
            sigma = context["sigma"]
        else:
            sigma = None
        return star(lst[0], sigma)

    def DoPrint(self, lst, context=None):
        print(lst[0])
        return lst[0]


class ParseReg(ParseReg1):
    """

    .. inheritance-diagram:: ParseReg"""

    def __init__(self, no_table=0, table='tableambreg'):
        """A parser for regular expressions with ambiguous rules: not working  """

        grammar = """
    reg -> reg + reg {{ self.OrSemRule }} |
         reg reg {{ self.ConcatSemRule // 200 left }} |
         reg * {{ self.StarSemRule }} |
         ( reg ) {{self.ParSemRule }} |
         id {{ self.BaseSemRule }};
    """

        tokenize = [(Epsilon, lambda x: ("id", x)),
                    (EmptySet, lambda x: ("id", x)),
                    ("[A-Za-z0-9]", lambda x: ("id", x)),
                    ("[+|]", lambda x: ("+", x), ("+", 100, 'left')),
                    ("[*]", lambda x: (x, x), ("*", 300, 'left')),
                    ("\(|\)", lambda x: (x, x))]

        Yappy.__init__(self, tokenize, grammar, table, no_table)


class ParseReg2(ParseReg1):
    """

    .. inheritance-diagram:: ParseReg2"""

    def __init__(self, no_table=0, table='tableambreg2'):
        grammar = """
    reg -> reg + reg {{ self.OrSemRule}}|
         reg reg {{ self.ConcatSemRule // 200 left }} |
         reg * {{ self.StarSemRule }} |
         ( reg ) {{self.ParSemRule}} |
         id {{ self.BaseSemRule }} ;
    """
        tokenize = [("\s+", ""),
                    (Epsilon, lambda x: ("id", x), ("id", 400, 'left')),
                    (EmptySet, lambda x: ("id", x), ("id", 400, 'left')),
                    ("[A-Za-z0-9]", lambda x: ("id", x), ("id", 400, 'left')),
                    ("[+|]", lambda x: ("+", x), ("+", 100, 'left')),
                    ("[*]", lambda x: (x, x), ("*", 300, 'left')),
                    ("\(|\)", lambda x: (x, x))]

        Yappy.__init__(self, tokenize, grammar, table, no_table)


def str2regexp(s, parser=ParseReg1, no_table=1, sigma=None, strict=False):
    """ Reads a regexp from string.

    :arg s:  the string representation of the regular expression
    :type s: string
    :arg parser: a parser generator for regexps
    :type parser: Yappy
    :arg no_table:
    :type no_table: integer
    :arg sigma: alphabet of the regular expression
    :type sigma: list or set of symbols
    :arg strict: if True tests if the symbols of the regular expression are included in the sigma
    :type strict: boolean
    :rtype: regexp"""

    s = re.sub("\s+", "", s)
    d = parser(no_table)
    try:
        reg = d.input(s, context={"sigma": sigma})
    except LRParserError:
        raise regexpInvalid(s)
    if sigma is not None:
        reg.setSigma(sigma, strict)
    elif strict:
        reg.setSigma(reg.setOfSymbols())
    return reg


def rpn2regexp(s, sigma=None, strict=False):
    """Reads a regexp from a RPN representation

    .. productionlist:: Representation R
       R: .RR | +RR | \*R | L | @
       L: [a-z] | [A-Z]

    :param s: RPN representation
    :type s: string
    :rtype: regexp

    .. note:: This method uses python stack... thus depdth limitations apply"""
    (nf, reg) = _rpn2re(re.sub("@epsilon", "@", s), 0, sigma)
    if sigma is not None:
        reg.setSigma(sigma, strict)
    elif strict:
        reg.setSigma(reg.setOfSymbols())
    return reg


def _rpn2re(s, i, sigma=None):
    """

    :param s:
    :param i:
    :return:
    """
    if s[i] in "+.":
        (i1, arg1) = _rpn2re(s, i + 1)
        (i2, arg2) = _rpn2re(s, i1)
        if s[i] == ".":
            return i2, concat(arg1, arg2, sigma)
        else:
            return i2, disj(arg1, arg2, sigma)
    if s[i] == "*":
        (i1, arg1) = _rpn2re(s, i + 1)
        return i1, star(arg1, sigma)
    if s[i] == "@":
        return i + 1, epsilon(sigma)
    else:
        return i + 1, regexp(s[i], sigma)
