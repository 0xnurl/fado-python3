# -*- coding: utf-8 -*-
"""**Finite automata manipulation.**

Deterministic and non-deterministic automata manipulation, conversion and evaluation.

.. *Authors:* Rogério Reis & Nelma Moreira

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
from __future__ import print_function
from __future__ import absolute_import
from __future__ import division
from __future__ import unicode_literals
from future import standard_library
standard_library.install_aliases()
from builtins import map
from builtins import str
from builtins import range
from builtins import *
from past.utils import old_div
from builtins import object
from copy import copy
from collections import deque

from . import reex
from .common import *
from .unionFind import UnionFind
from . import graphs


class SemiDFA(Drawable):
    # noinspection PyUnresolvedReferences
    """Class of automata without initial or final states

        :var States: list of states
        :type States: list of objects
        :var delta: transition function
        :type delta: dict
        :var Sigma: alphabet set
        :type Sigma: set of str"""

    def __init__(self):
        self.States = []
        self.delta = {}
        self.Sigma = set()

    def dotDrawState(self, sti, sep="\n"):
        """Dot representation of a state

        :param sti: state index
        :type sti: int
        :param sep: separator
        :type sep: str        
        :rtype: str """
        return "node [shape = circle]; \"{0:s}\";{1:s}".format(self.States[sti].__str__(), sep)

    @staticmethod
    def dotDrawTransition(st1, lbl1, st2, sep="\n"):
        """Draw a transition in dot format

        :param st1: departing state
        :type st1: str
        :param lbl1: label
        :type lbl1: str
        :param st2: arriving state
        :type st2: str
        :param sep: separator
        :type sep: str
        :rtype: str """
        return "\"{0:s}\" -> \"{1:s}\" [label = \"{2:s}\"];{3:s} ".format(st1, st2, lbl1, sep)

    def dotFormat(self, size="20,20", direction="LR", sep="\n"):
        """Dot format of automata

        :param size: image size
        :type size: str
        :param direction: direction of drawing
        :type size: str
        :param sep: separator
        :type sep: str
        :rtype: str """
        s = "digraph finite_state_machine {{{0:s}".format(sep)
        s += "rankdir={0:s};{1:s}".format(direction, sep)
        s += "size=\"{0:s}\";{1:s}".format(size, sep)
        for si in range(len(self.States)):
            sn = str(self.States[si])
            s += "node [shape = point]; \"dummy{0:s}\"{1:s}".format(sn, sep)
            s += self.dotDrawState(si)
            s += "\"dummy{0:s}\" -> \"{1:s}\";{2:s}".format(sn, str(self.States[si]), sep)
        for si in range(len(self.States)):
            for s1 in self.Sigma:
                s += self.dotDrawTransition(str(self.States[si]), str(s1), str(self.States[self.delta[si][s1]]))
        s += "}}{0:s}".format(sep)
        return s


# noinspection PyUnresolvedReferences
class FA(Drawable):
    """Base class for Finite Automata.

    :var States: set of states
    :type States: list of objects
    :var Sigma: alphabet set
    :type Sigma: set of str
    :var Initial: the initial state
    :var Final: set of final states
    :type Final: set of int
    :var delta: the transition function

    .. note::
       This is just an abstract class.
       **Not to be used directly!!**"""

    def __init__(self):
        self.States = []
        self.Sigma = set()
        self.Initial = None
        self.Final = set()
        self.delta = {}

    def __repr__(self):
        """'Official' string representation

        :returns: str"""
        return 'FA({0:>s})'.format(self.__str__())

    def __str__(self):
        """'Informal' string representation

        :rtype: str"""
        # noinspection PyProtectedMember
        a = self._s_States
        b = self._s_Sigma
        c = self._s_lstInitial()
        d = self._s_Final
        e = str(self._lstTransitions())
        return str((a, b, c, d, e))

    @abstractmethod
    def __eq__(self, other):
        pass

    @abstractmethod
    def __ne__(self, other):
        pass

    @abstractmethod
    def evalSymbol(self):
        """Evaluation of a single symbol"""
        pass

    @property
    def _s_States(self):
        return [str(x) for x in self.States]

    @property
    def _s_Sigma(self):
        return [str(x) for x in self.Sigma]

    @property
    def _s_Final(self):
        return [str(self.States[x]) for x in self.Final]

    def __len__(self):
        """Size: number of states

        :rtype: int"""
        return len(self.States)

    def dotDrawState(self, sti, sep="\n"):
        """ Draw a state in dot format

        :arg sti: index of the state
        :arg sep: separator
        :type sep: str
        :type sti: int
        :rtype: str """
        if sti in self.Final:
            return "node [shape = doublecircle]; \"{0:s}\";".format(str(self.States[sti]), sep)
        else:
            return "node [shape = circle]; \"{0:s}\";{1:s}".format(str(self.States[sti]), sep)

    def same_nullability(self, s1, s2):
        """Tests if this two states have the same nullability

        :param s1: state index
        :param s2: state index
        :type s1: int
        :type s2: int
        :rtype: bool"""
        return (s1 in self.Final) is (s2 in self.Final)

    @abstractmethod
    def succintTransitions(self):
        """Colapsed transitions"""
        pass

    @abstractmethod
    def dotDrawTransition(self, st1, sym, st2, sep):
        """Draw a transition in dot format

        :param str st1: departing state
        :param str sym: label
        :param str st2: arriving state
        :param str sep: separator"""
        pass

    def initialSet(self):
        """The set of initial states

        :returns: the set of the initial states
        :rtype: set of States"""
        return self.Initial

    def initialP(self, state):
        """ Tests if a state is initial

        :param int state: state index
        :rtype: bool"""
        return state in self.Initial

    def finalP(self, state):
        """ Tests if a state is final

        :param int state: state index
        :rtype: bool"""
        return state in self.Final

    def finalsP(self, states):
        """ Tests if al the states in a set are final

        :param set states: set of state indexes
        :rtype: bool

        .. versionadded:: 1.0"""
        return states.issubset(self.Final)

    def _namesToString(self):
        """All state names are transformed in strings"""
        n = []
        for s in self.States:
            n.append(str(s))
        self.States = n
        return self

    def hasStateIndexP(self, st):
        """Checks if a state index pertains to an FA

        :param int st: index of the state
        :rtype: bool"""
        if st > (len(self.States) - 1):
            return False
        else:
            return True

    def addState(self, name=None):
        """Adds a new state to an FA. If no name is given a new name is created.

        :param object name: Name of the state to be added
        :returns: Current number of states (the new state index)
        :rtype: int
        :raises DuplicateName: if a state with that name already exists"""
        if name is None:
            iname = len(self.States)
            name = str(iname)
            while iname in self.States or name in self.States:
                iname += 1
                name = str(iname)
            self.States.append(name)
            return len(self.States) - 1
        elif name in self.States:
            raise DuplicateName(self.stateIndex(name))
        else:
            self.States.append(name)
            return len(self.States) - 1

    def deleteState(self, sti):
        """Remove the given state and the transitions related with that state.

        :param int sti: index of the state to be removed
        :raises DFAstateUnknown: if state index does not exist"""
        if sti >= len(self.States):
            raise DFAstateUnknown(sti)
        else:
            if sti in list(self.delta.keys()):
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

    def words(self, stringo=True):
        """Lexicografical word generator

        .. attention:: does not generate the empty word

        :param bool stringo: are words strings?

        .. versionadded:: 0.9.8"""

        def _translate(l, r, s1=True):
            if s1:
                s = ""
                for z in l:
                    s += r[z]
                return s
            else:
                return [r[y] for y in l]

        import itertools

        ss = list(self.Sigma)
        ss.sort()
        n = len(ss)
        n0 = 1
        while True:
            for x in itertools.product(list(range(n)), repeat=n0):
                yield _translate(x, ss, stringo)
            n0 += 1

    def equivalentP(self, other):
        """Test equivalence

        :param other: the other automata
        :rtype: bool

        .. versionadded:: 0.9.6"""
        return self == other

    def setInitial(self, stateindex):
        """Sets the initial state of a FA

        :param int stateindex: index of the initial state"""
        self.Initial = stateindex

    def setFinal(self, statelist):
        """Sets the final states of the FA

        :param int|list|set statelist: a list (or set) of final states indexes

        .. caution::
           it erases any previous definition of the final state set."""
        self.Final = set(statelist)

    def addFinal(self, stateindex):
        """A new state is added to the already defined set of final states.

        :param stateindex: index of the new final state
        :type stateindex: int"""
        self.Final.add(stateindex)

    def delFinals(self):
        """Deletes all the information about final states."""
        self.Final = set([])

    def delFinal(self, st):
        """Deletes a state from the final states list

        :param int st: state to be marked as not final"""
        self.Final = self.Final - {st}

    def setSigma(self, symbolSet):
        """Defines the alphabet for the FA.

        :param list|set symbolSet: alphabet symbols"""
        self.Sigma = set(symbolSet)

    def addSigma(self, sym):
        """Adds a new symbol to the alphabet.

        :param str sym: symbol to be added
        :raises DFAepsilonRedefenition: if sym is Epsilon

        .. note::
            * There is no problem with duplicate symbols because Sigma is a Set.
            * No symbol Epsilon can be added."""
        if sym == Epsilon:
            raise DFAepsilonRedefinition()
        self.Sigma.add(sym)

    def stateIndex(self, name, autoCreate=False):
        """Index of given state name.

        :param object name: name of the state
        :param bool autoCreate: flag to create state if not already done
        :returns: state index
        :rtype: int
        :raises DFAstateUnknown: if the state name is unknown and autoCreate==False

        .. note::
           Replaces stateName

        .. note::
           If the state name is not known and flag is set creates it on the fly

        .. versionadded:: 1.0"""
        if name in self.States:
            return self.States.index(name)
        else:
            if autoCreate:
                return self.addState(name)
            else:
                raise DFAstateUnknown(name)

    @deprecated
    def stateName(self, name, autoCreate=False):
        """Index of given state name.

        :param object name: name of the state
        :param bool autoCreate: flag to create state if not already done
        :returns: state index
        :rtype: int
        :raises DFAstateUnknown: if the state name is unknown and autoCreate==False

        .. deprecated:: 1.0
           Use: :func:`stateIndex` instead"""
        return self.stateIndex(name, autoCreate)

    def indexList(self, lstn):
        """Converts a list of stateNames into a set of stateIndexes.

        :param list lstn: list of names
        :returns: the list of state indexes
        :rtype: Set of int
        :raises DFAstateUnknown: if a state name is unknown"""
        lst = set()
        for s in lstn:
            lst.add(self.stateIndex(s))
        return lst

    def plus(self):
        """Plus of a FA (star without the adding of epsilon)

        .. versionadded:: 0.9.6"""
        return self.star(True)

    def disjunction(self, other):
        """A simple literate invocation of __or__

        :param other: the other FA"""
        return self.__or__(other)

    def disj(self, other):
        """Another simple literate invocation of __or__

        :param other: the other FA

        .. versionadded:: 0.9.6"""
        return self.__or__(other)

    def union(self, other):
        """A simple literate invocation of __or__

        :param other: right hand operand"""
        return self.__or__(other)

    def conjunction(self, other):
        """A simple literate invocation of __and__

        :param other: the other FA

        .. versionadded:: 0.9.6"""
        return self.__and__(other)

    def renameState(self, st, name):
        """Rename a given state.

        :param int st: state index
        :param object name: name
        :return: self

        .. note::
            Deals gacefully both with int and str names in the case of name collision.

        .. attention::
           the object is modified in place"""
        if name != self.States[st]:
            if name in self.States:
                if isinstance(name, int):
                    while name in self.States:
                        name += name + 1
                elif isinstance(name, str):
                    while name in self.States:
                        name += "+"
                else:
                    raise DuplicateName
            self.States[st] = name
        return self

    def renameStates(self, nameList=None):
        """Renames all states using a new list of names.

        :param list nameList: list of new names
        :raises DFAerror: if provided list is too short
        :return: self

        .. note::
           If no list of names is given, state indexes are used.

        .. attention::
           the object is modified in place"""
        if nameList is None:
            self.States = list(range(len(self.States)))
        else:
            if len(nameList) < len(self.States):
                raise DFAerror
            else:
                for i in range(len(self.States)):
                    self.renameState(i, nameList[i])
        return self

    def eliminateDeadName(self):
        """Eliminates dead state name (common.DeadName) renaming the state

        .. attention::
           works inplace

        .. versionadded:: 1.2"""
        try:
            i = self.stateIndex(DeadName)
        except DFAstateUnknown:
            return self
        self.renameState(i, str(len(self.States)))
        return self

    def noBlankNames(self):
        """Eliminates blank names

        :return: self

        .. attention::
           in place transformation"""
        for i in range(len(self.States)):
            if self.States[i] == "":
                self.States[i] = str(i)
        return self

    def reversal(self):
        """Returns a NFA that recognizes the reversal of the language

        :returns: NFA recognizing reversal language
        :rtype: NFA"""
        rev = NFA()
        rev.setSigma(self.Sigma)
        rev.States = list(self.States)
        self.reverseTransitions(rev)
        rev.setFinal([self.Initial])
        rev.setInitial(self.Final)
        return rev

    def countTransitions(self):
        """Evaluates the size of FA transitionwise

        :returns: the number of transitions
        :rtype: int

        .. versionchanged:: 1.0"""
        return sum([len(self.delta[i]) for i in self.delta])

    def inputS(self, i):
        """Input labels coming out of state i

        :param int i: state
        :returns: set of input labels
        :rtype: set of str

        .. versionadded:: 1.0"""
        return set(self.delta.get(i, {}))

    @abstractmethod
    def succintTransitions(self):
        """Collapsed transitions
        :rtype: list"""
        pass

    def dotFormat(self, size="20,20", direction="LR", sep="\n"):
        """ A dot representation

        :param str direction: direction of drawing
        :param str size: size of image
        :param str sep: line separator
        :return: the dot representation
        :rtype: str

        .. versionadded:: 0.9.6

        .. versionchanged:: 0.9.8"""
        s = "digraph finite_state_machine {{{0:s}".format(sep)
        s += "rankdir={0:s};{1:s}".format(direction, sep)
        s += "size=\"{0:s}\";{1:s}".format(size, sep)
        s += "node [shape = point]; dummy{0:s}".format(sep)
        niStates = [i for i in range(len(self.States)) if i != self.Initial]
        s += self.dotDrawState(self.Initial)
        s += "dummy -> \"{0:s}\"{1:s}".format(str(self.States[self.Initial]), sep)
        for sti in niStates:
            s += self.dotDrawState(sti)
        for si in self.succintTransitions():
            s += self.dotDrawTransition(si[0], si[1], si[2])
        s += "}}{0:s}".format(sep)
        return s


class OFA(FA):
    """ Base class for one-way automata
    .. inheritance-diagram:: OFA"""

    @abstractmethod
    def succintTransitions(self):
        """Collapsed transitions"""
        pass

    @abstractmethod
    def evalSymbol(self):
        """Eval symbol"""
        pass

    @abstractmethod
    def addTransition(self, st1, sym, st2):
        """Add transition
        :param int st1: departing state
        :param str sym: label
        :param int st2: arriving state"""
        pass

    @abstractmethod
    def __ne__(self, other):
        pass

    @abstractmethod
    def __eq__(self, other):
        pass

    @abstractmethod
    def stateChildren(self, s):
        """ To be implemented below

        :param s: state
        :rtype: list"""
        pass

    def _deleteRefTo(self, src, sym, dest):
        """Delete transition

        :param int src: source state
        :param str sym: label
        :param int dest: target state"""
        if self.delta.get(src, {}).get(sym, None) == dest:
            del (self.delta[src][sym])

    @staticmethod
    def dotDrawTransition(st1, label, st2, sep="\n"):
        """ Draw a transition in Dot Format

        :param str st1: starting state
        :param str st2: ending state
        :param str label: symbol
        :param str sep: separator
        :rtype: str"""
        return "\"{0:s}\" -> \"{1:s}\" [label = \"{2:s}\"];{3:s} ".format(st1, st2, label, sep)

    @abstractmethod
    def initialComp(self):
        """Initial component

        :rtype: list"""
        pass

    @abstractmethod
    def _getTags(self):
        pass

    @abstractmethod
    def usefulStates(self):
        """ To be implemented below """
        pass

    @abstractmethod
    def deleteStates(self, del_states):
        """ To be implemented below

        :param del_states: states to be deleted
        :type del_states: list
        """
        pass

    @abstractmethod
    def toGFA(self):
        """ To be implemented below
        """
        pass

    @abstractmethod
    def finalCompP(self, s):
        """To be implemented below

        :param s: state
        :rtype: list"""
        pass

    @abstractmethod
    def uniqueRepr(self):
        """Abstract method"""
        pass

    def emptyP(self):
        """ Tests if the automaton accepts a empty language

        :rtype: bool

        .. versionadded:: 1.0"""
        a = self.initialComp()
        for s in a:
            if self.finalP(s):
                return False
        return True

    def dump(self):
        """Returns a python representation of the object

        :returns: the python representation (Tags,States,Sigma,delta,Initial,Final)
        :rtype: tuple """
        tags = self._getTags()
        sig = list(self.Sigma)
        I = [i for i in forceIterable(self.Initial)]
        F = [i for i in self.Final]
        dt = []
        for i in range(self.__len__()):
            for c in self.delta.get(i, []):
                if c == Epsilon:
                    ci = -1
                else:
                    ci = sig.index(c)
                for j in forceIterable(self.delta[i][c]):
                    dt.append((i, ci, j))
        return tags, self.States, sig, dt, I, F

    def completeP(self):
        """Checks if it is a complete FA (if delta is total)

        :return: bool"""
        if not self.Sigma:
            return True
        ss = len(self.Sigma)
        for s, _ in enumerate(self.States):
            if s not in self.delta:
                return False
            ni = set(self.delta[s])
            if len(ni) != ss:
                return False
        return True

    def complete(self, dead=DeadName):
        """Transforms the automata into a complete one. If Sigma is empty nothing is done.

        :param str dead: dead state name
        :return: the complete FA
        :rtype: DFA

        .. note::
           Adds a dead state (if necessary) so that any word can be processed with the automata. The new state is
           named ``dead``, so this name should never be used for other purposes.

        .. attention::
           The object is modified in place.

        .. versionchanged:: 1.0"""
        if self.completeP():
            return self
        ss = len(self.Sigma)
        f = True
        Bin = self.stateIndex(dead, True)
        for s, _ in enumerate(self.States):
            if s not in self.delta:
                self.delta[s] = {}
            ni = list(self.delta[s].keys())
            if len(ni) != ss:
                for c in self.Sigma:
                    if c not in ni:
                        self.addTransition(s, c, Bin)
                        f = False
        if f:
            self.deleteState(Bin)
        return self

    def trim(self):
        """Removes the states that do not lead to a final state, or, inclusively,
        that can't be reached from the initial state. Only useful states
        remain.

        .. attention:
            only applies to non empty languages

        .. attention::
           in place transformation"""
        useful = self.usefulStates()
        del_states = [s for s in range(len(self.States)) if s not in useful]
        if del_states:
            self.deleteStates(del_states)
        return self

    def trimP(self):
        """Tests if the FA is trim: initially connected and co-accessible

        :return: bool"""
        for s, _ in enumerate(self.States):
            if not self.finalCompP(s):
                return False
        return len(self.States) == len(self.initialComp())

    def minimalBrzozowski(self):
        """Constructs the equivalent minimal DFA using Brzozowski's
        algorithm

        :return: equivalent minimal DFA
        :rtype: DFA"""
        return self.reversal().toDFA().reversal().toDFA()

    def minimalBrzozowskiP(self):
        """Tests if the FA is minimal using Brzozowski's algorithm

        :rtype: bool"""
        x = self.minimalBrzozowski()
        x.complete()
        return self.uniqueRepr() == x.uniqueRepr()

    def regexpSE(self):
        """A regular expression obtained by state elimination algorithm whose language is recognised by the FA.

        :return: the equivalent regular expression
        :rtype: regexp"""
        new = self.dup()
        new.trim()
        if not len(new.States):
            return reex.emptyset(copy(self.Sigma))
        if not len(new.Final):
            return reex.emptyset(copy(self.Sigma))
        if len(new.States) == 1 and len(new.delta) == 0:
            return reex.epsilon(copy(self.Sigma))
        elif type(new) == NFA and len(new.Initial) != 0 and len(new.delta) == 0:
            return reex.epsilon(copy(self.Sigma))
        gfa = new.toGFA()
        if len(gfa.Final) > 1:
            last = gfa.addState("Last")
            for s in gfa.Final:
                gfa.addTransition(s, Epsilon, last)
            gfa.setFinal([last])
        else:
            last = list(gfa.Final)[0]
        foo = {}
        lfoo = len(gfa.States) - 1
        foo[lfoo], foo[last] = last, lfoo
        gfa.reorder(foo)
        if lfoo != gfa.Initial:
            n = 2
            foo = {lfoo - 1: gfa.Initial, gfa.Initial: lfoo - 1}
            gfa.reorder(foo)
        else:
            n = 1
        lr = list(range(len(gfa.States) - n))
        gfa.eliminateAll(lr)
        gfa.completeDelta()
        if n == 1:
            return reex.star(gfa.delta[gfa.Initial][gfa.Initial], copy(self.Sigma)).reduced()
        ii = gfa.Initial
        fi = list(gfa.Final)[0]
        a = gfa.delta[ii][ii]
        b = gfa.delta[ii][fi]
        c = gfa.delta[fi][ii]
        d = gfa.delta[fi][fi]
        # bd*
        re1 = reex.concat(b, reex.star(d, copy(self.Sigma)), copy(self.Sigma))
        # a + bd*c
        re2 = reex.disj(a, reex.concat(re1, c, copy(self.Sigma)), copy(self.Sigma))
        # (a + bd*c)* bd*
        return reex.concat(reex.star(re2, copy(self.Sigma)), re1, copy(self.Sigma)).reduced()

    def allRegExps(self):
        """Evaluates the alphabetic length of the equivalent regular expression using every possible order of state
        elimination.

        :rtype: list of tuples (int, list of states)"""
        from itertools import permutations

        new = self.dup()
        new.trim()
        gfa = new.toGFA()
        for order in permutations(list(range(len(gfa.States)))):
            return self.re_stateElimination(copy(list(order))).alphabeticLength(), order

    def _isAcyclic(self, s, visited, strict):
        """Determines if from state s a cyclic is reached

        :param int s: state
        :param dict visited: marks visited states
        :param bool strict: if not True loops are allowed
        :rtype: bool"""
        if s not in visited:
            visited[s] = 1
            if s in self.delta:
                for dest in self.stateChildren(s, strict):
                    acyclic = self._isAcyclic(dest, visited, strict)
                    if not acyclic:
                        return False
                visited[s] = 2
            else:
                visited[s] = 2
                return True
        else:
            if visited[s] == 1:
                return False
        return True

    def acyclicP(self, strict=True):
        """ Checks if the FA is acyclic

        :param strict: if not True loops are allowed
        :type strict: bool
        :returns: True if the FA is acyclic
        :rtype: bool"""
        visited = {}
        for s in range(len(self.States)):
            acyclic = self._isAcyclic(s, visited, strict)
            if not acyclic:
                return False
        return True

    def _topoSort(self, s, visited, L):
        """Auxiliar for topological order"""
        if s not in visited:
            visited.append(s)
            if s in self.delta:
                # noinspection PyTypeChecker
                for dest in self.stateChildren(s, True):
                    self._topoSort(dest, visited, L)
            L.insert(0, s)

    def topoSort(self):
        """Topological order for the FA

        :returns: List of state indexes
        :rtype: list of int

        .. note::
           self loops are taken in consideration"""
        visited = []
        L = []
        for s in range(len(self.States)):
            self._topoSort(s, visited, L)
        return L

    def eliminateSingles(self):
        """Eliminates every state that only have one successor and one predecessor.

        :returns: GFA after eliminating states
        :rtype: GFA """
        # DFS to obtain {v:(e, s)} -> convert from {v:(e, s)} to {(e, s):v} -> eliminate all {(1, 1):v}
        gfa = self.toGFA()
        io = {}
        for i in range(len(self.States)):
            io[i] = [0, 0]
        gfa.DFS(io)
        new = {}
        for i in io:
            if (io[i][0], io[i][1]) in new:
                new[io[i]].append(i)
            else:
                new[io[i]] = [i]
        if (1, 1) not in new:
            return gfa
            # While there are singles, delete them
        while new[(1, 1)]:
            v = new[(1, 1)].pop()
            i = list(gfa.predecessors[v])[0]
            o = list(gfa.delta[v].items())[0][0]
            if o in gfa.delta[i]:
                gfa.delta[i][o] = reex.disj(reex.concat(gfa.delta[i][v], gfa.delta[v][o], copy(self.Sigma)),
                                            gfa.delta[i][o])
                new[io[i]].remove(i)
                new[io[o]].remove(o)
                # lists are unhashable
                e0, e1 = io[i]
                io[i] = (e0, e1 - 1)
                e0, e1 = io[o]
                io[o] = (e0 - 1, e1)
                if io[i] in new:
                    new[io[i]].append(i)
                else:
                    new[io[i]] = [i]
                if io[o] in new:
                    new[io[o]].append(o)
                else:
                    new[io[o]] = [o]
                gfa.predecessors[o].remove(v)
            else:
                gfa.delta[i][o] = reex.concat(gfa.delta[i][v], gfa.delta[v][o], copy(self.Sigma))
                gfa.predecessors[o].remove(v)
                gfa.predecessors[o].add(i)
            del gfa.delta[i][v]
            del gfa.delta[v][o]
            del gfa.delta[v]
            del gfa.predecessors[v]
            del io[v]
            # Clean up state indexes...
        newOrder = {}
        ind = 0
        for i in gfa.delta:
            if i not in newOrder:
                newOrder[i] = ind
            a = 0
            for j in gfa.delta[i]:
                if j not in newOrder:
                    a += 1
                    newOrder[j] = ind + a
            ind += a
        gfa.reorder(newOrder)
        gfa.States = gfa.States[:ind + 1]
        return gfa

    def SPRegExp(self):
        """ Checks if FA is SP (Serial-PArallel), and if so returns the regular expression whose language is recognised by the FA

        :returns: equivalent regular expression
        :rtype: regexp
        :raises NotSP: if the automaton is not Serial-Parallel

        .. seealso:: Moreira & Reis, Fundamenta Informatica, Series-Parallel automata and short regular expressions,
           n.91 3-4, pag 611-629.
           http://www.dcc.fc.up.pt/~nam/publica/spa07.pdf

        .. note::
           Automata must be Serial-Parallel"""
        v = 0  # just to satisfy the checker
        gfa = self.toGFA()
        gfa.lab = {}
        gfa.out_index = {}
        for i in range(len(gfa.States)):
            if i not in gfa.delta:
                gfa.out_index[i] = 0
            else:
                gfa.out_index[i] = len(gfa.delta[i])
        topoOrder = gfa.topoSort()
        for v in topoOrder:  # States should be topologically ordered
            i = len(gfa.predecessors[v])
            while i > 1:
                # noinspection PyProtectedMember
                i = gfa._simplify(v, i)
            if len(gfa.predecessors[v]):
                track = gfa.lab[(list(gfa.predecessors[v])[0], v)]
                rp = gfa.delta[list(gfa.predecessors[v])[0]][v]
            else:
                track = SPLabel([])
                rp = reex.epsilon(copy(self.Sigma))
            try:
                # noinspection PyProtectedMember
                gfa._do_edges(v, track, rp)
            except KeyError:
                pass
        return gfa.delta[list(gfa.predecessors[v])[0]][v]

    def reCG(self):
        """Regular expression from state elimination whose language is recognised by the FA. Uses a heuristic to choose
        the order of elimination.

        :returns: the equivalent regular expression
        :rtype: regexp"""
        new = self.dup()
        new.trim()
        gfa = new.toGFA()
        if not len(gfa.Final):
            return reex.emptyset(copy(self.Sigma))
        gfa.normalize()
        weights = {}
        for st in range(len(gfa.States)):
            if st != gfa.Initial and st not in gfa.Final:
                weights[st] = gfa.weight(st)
        for i in range(len(gfa.States) - 2):
            m = [(v, u) for (u, v) in list(weights.items())]
            m = min(m)
            m = m[1]
            # After 'm' is eliminated it's adjacencies might
            # change their indexes...
            adj = set([])
            for st in gfa.predecessors[m]:
                if st > m:
                    adj.add(st - 1)
                else:
                    adj.add(st)
            for st in gfa.delta[m]:
                if st > m:
                    adj.add(st - 1)
                else:
                    adj.add(st)
            gfa.eliminateState(m)
            for st in weights:
                if st > m:
                    weights[st - 1] = weights[st]
            for st in adj:
                if st != gfa.Initial and st not in gfa.Final:
                    weights[st] = gfa.weight(st)
            del weights[len(gfa.States) - 2]
        return gfa.delta[gfa.Initial][list(gfa.Final)[0]].reduced()

    def reCG_nn(self):
        """Regular expression from state elimination whose language is recognised by the FA. Uses a heuristic to choose
        the order of elimination. The FA is not normalized before the state elimination.

        :returns: the equivalent regular expression
        :rtype: regexp"""
        if not len(self.Final):
            return reex.emptyset(copy(self.Sigma))
        new = self.dup()
        new.trim()
        gfa = new.toGFA()
        if len(gfa.Final) > 1:
            last = gfa.addState("Last")
            for s in gfa.Final:
                gfa.addTransition(s, Epsilon, last)
            gfa.setFinal([last])
        else:
            last = list(gfa.Final)[0]
        foo = {}
        lfoo = len(gfa.States) - 1
        foo[lfoo], foo[last] = last, lfoo
        gfa.reorder(foo)
        if lfoo != gfa.Initial:
            n = 2
            foo = {lfoo - 1: gfa.Initial, gfa.Initial: lfoo - 1}
            gfa.reorder(foo)
        else:
            n = 1
        weights = {}
        for st in range(len(gfa.States)):
            if st != gfa.Initial and st not in gfa.Final:
                weights[st] = gfa.weight(st)
        for i in range(len(gfa.States) - n):
            m = [(v, u) for (u, v) in list(weights.items())]
            m = min(m)
            m = m[1]
            succs = set([])
            for a in gfa.delta[m]:
                if a != m:
                    succs.add(a)
            preds = set([])
            for a in gfa.predecessors[m]:
                if a != m:
                    preds.add(a)
            gfa.eliminate(m)
            # update predecessors for weight(st)...
            for s in succs:
                gfa.predecessors[s].remove(m)
                for s1 in preds:
                    gfa.predecessors[s].add(s1)
            del gfa.predecessors[m]
            for s in set(list(succs) + list(preds)):
                if s != gfa.Initial and s not in gfa.Final:
                    weights[s] = gfa.weight(s)
            del weights[m]
        gfa.completeDelta()
        if n == 1:
            return reex.star(gfa.delta[gfa.Initial][gfa.Initial], copy(self.Sigma)).reduced()
        # noinspection PyProtectedMember
        return gfa._re0()

    def re_stateElimination(self, order=None):
        """Regular expression from state elimination whose language is recognised by the FA. The FA is normalized before
        the state elimination.

        :param order: state elimination sequence
        :type order: list
        :returns: the equivalent regular expression
        :rtype: regexp"""
        if not order:
            order = []
        new = self.dup()
        new.trim()
        gfa = new.toGFA()
        if order is None:
            order = list(range(len(gfa.States)))
        if not len(gfa.Final):
            return reex.emptyset(copy(self.Sigma))
        gfa.normalize()
        while order:
            st = order.pop(0)
            for i in range(len(order)):
                if order[i] > st:
                    order[i] -= 1
            gfa.eliminateState(st)
        return gfa.delta[gfa.Initial][list(gfa.Final)[0]]

    def reDynamicCycleHeuristic(self):
        """ State elimination Heuristic based on the number of cycles that passes through each state. Here those
        numbers are evaluated dynamically after each elimination step

        :returns: an equivalent regular expression
        :rtype: regexp

        .. seealso::
           Nelma Moreira, Davide Nabais, and Rogério Reis. State elimination ordering strategies: Some experimental
           results. Proc. of 11th Workshop on Descriptional Complexity of Formal Systems (DCFS10),
           pages 169-180.2010. DOI: 10.4204/EPTCS.31.16"""
        if not len(self.Final):
            return reex.emptyset(copy(self.Sigma))
        new = self.dup()
        new.trim()
        cycles = new.evalNumberOfStateCycles()
        gfa = new.toGFA()
        if len(gfa.Final) > 1:
            last = gfa.addState("Last")
            for s in gfa.Final:
                gfa.addTransition(s, Epsilon, last)
            gfa.setFinal([last])
        else:
            last = list(gfa.Final)[0]
        foo = {}
        lfoo = len(gfa.States) - 1
        foo[lfoo], foo[last] = last, lfoo
        gfa.reorder(foo)
        if lfoo != gfa.Initial:
            n = 2
            foo = {lfoo - 1: gfa.Initial, gfa.Initial: lfoo - 1}
            gfa.reorder(foo)
        else:
            n = 1
        weights = {}
        for st in range(len(gfa.States)):
            if st != gfa.Initial and st not in gfa.Final:
                weights[st] = gfa.weightWithCycles(st, cycles)
        for i in range(len(gfa.States) - n):
            m = [(v, u) for (u, v) in list(weights.items())]
            m = min(m)
            m = m[1]
            succs = set([])
            for a in gfa.delta[m]:
                if a != m:
                    succs.add(a)
            preds = set([])
            for a in gfa.predecessors[m]:
                if a != m:
                    preds.add(a)
            gfa.eliminate(m)
            cycles = gfa.evalNumberOfStateCycles()
            # update predecessors for weight(st)...
            for s in succs:
                gfa.predecessors[s].remove(m)
                for s1 in preds:
                    gfa.predecessors[s].add(s1)
            del gfa.predecessors[m]
            for s in set(list(succs) + list(preds)):
                if s != gfa.Initial and s not in gfa.Final:
                    weights[s] = gfa.weightWithCycles(s, cycles)
            del weights[m]
        gfa.completeDelta()
        if n == 1:
            return reex.star(gfa.delta[gfa.Initial][gfa.Initial], copy(self.Sigma))
        # noinspection PyProtectedMember
        return gfa._re0()

    def reStaticCycleHeuristic(self):
        """State elimination Heuristic based on the number of cycles that passes through each state. Here those
        numbers are evaluated statically in the beginning of the process

        :returns: a equivalent regular expression
        :rtype: regexp

        .. seealso::
           Nelma Moreira, Davide Nabais, and Rogério Reis. State elimination ordering strategies: Some experimental
           results. Proc. of 11th Workshop on Descriptional Complexity of Formal Systems (DCFS10),
           pages 169-180.2010. DOI: 10.4204/EPTCS.31.16"""
        if not len(self.Final):
            return reex.emptyset(copy(self.Sigma))
        new = self.dup()
        new.trim()
        cycles = new.evalNumberOfStateCycles()
        gfa = new.toGFA()
        if len(gfa.Final) > 1:
            last = gfa.addState("Last")
            for s in gfa.Final:
                gfa.addTransition(s, Epsilon, last)
            gfa.setFinal([last])
        else:
            last = list(gfa.Final)[0]
        foo = {}
        lfoo = len(gfa.States) - 1
        foo[lfoo], foo[last] = last, lfoo
        gfa.reorder(foo)
        if lfoo != gfa.Initial:
            n = 2
            foo = {lfoo - 1: gfa.Initial, gfa.Initial: lfoo - 1}
            gfa.reorder(foo)
        else:
            n = 1
        weights = {}
        for st in range(len(gfa.States)):
            if st != gfa.Initial and st not in gfa.Final:
                weights[st] = gfa.weightWithCycles(st, cycles)
        for i in range(len(gfa.States) - n):
            m = [(v, u) for (u, v) in list(weights.items())]
            m = min(m)
            m = m[1]
            succs = set([])
            for a in gfa.delta[m]:
                if a != m:
                    succs.add(a)
            preds = set([])
            for a in gfa.predecessors[m]:
                if a != m:
                    preds.add(a)
            gfa.eliminate(m)
            for s in succs:
                gfa.predecessors[s].remove(m)
                for s1 in preds:
                    gfa.predecessors[s].add(s1)
            del gfa.predecessors[m]
            for s in set(list(succs) + list(preds)):
                if s != gfa.Initial and s not in gfa.Final:
                    weights[s] = gfa.weightWithCycles(s, cycles)
            del weights[m]
        gfa.completeDelta()
        if n == 1:
            return reex.star(gfa.delta[gfa.Initial][gfa.Initial], copy(self.Sigma))
        # noinspection PyProtectedMember
        return gfa._re0()

    def re_stateElimination_nn(self, order=None):
        """Regular expression from state elimination whose language is recognised by the FA. The FA is not normalized
        before the state elimination.

        :param order: state elimination sequence
        :type order: list
        :returns: the equivalent regular expression
        :rtype: regexp"""
        n = 0  # just to satisfy the checker
        if not order:
            order = []
        gfa = self.toGFA()
        if not len(gfa.Final):
            return reex.emptyset(copy(self.Sigma))
        if order is None:
            if len(gfa.Final) > 1:
                last = gfa.addState("Last")
                gfa.predecessors[last] = set([])
                for s in gfa.Final:
                    gfa.addTransition(s, Epsilon, last)
                    gfa.predecessors[last].add(s)
                gfa.setFinal([last])
            else:
                last = list(gfa.Final)[0]
            foo = {}
            lfoo = len(gfa.States) - 1
            foo[lfoo], foo[last] = last, lfoo
            gfa.reorder(foo)
            if lfoo != gfa.Initial:
                n = 2
                foo = {lfoo - 1: gfa.Initial, gfa.Initial: lfoo - 1}
                gfa.reorder(foo)
            else:
                n = 1
            order = list(range(len(gfa.States) - n))
        while order:
            st = order.pop(0)
            for i in range(len(order)):
                if order[i] > st:
                    order[i] -= 1
            gfa.eliminateState(st)
        gfa.completeDelta()
        if n == 1:
            return reex.star(gfa.delta[gfa.Initial][gfa.Initial],
                             copy(self.Sigma)).reduced()
        ii = gfa.Initial
        fi = list(gfa.Final)[0]
        a = gfa.delta[ii][ii]
        b = gfa.delta[ii][fi]
        c = gfa.delta[fi][ii]
        d = gfa.delta[fi][fi]
        # bd*
        re1 = reex.concat(b, reex.star(d, copy(self.Sigma)),
                          copy(self.Sigma))
        # a + bd*c
        re2 = reex.disj(a, reex.concat(re1, c, copy(self.Sigma)),
                        copy(self.Sigma))
        # (a + bd*c)* bd*
        return reex.concat(reex.star(re2, copy(self.Sigma)),
                           re1, copy(self.Sigma)).reduced()

    def cutPoints(self):
        """Set of FA's cut points

        :returns: set of states
        :rtype: set of int"""
        gfa = self.toGFA()
        gfa.normalize()
        # make gfa a graph instead of a digraph
        newEdges = []
        for a in gfa.delta:
            for b in gfa.delta[a]:
                newEdges.append((a, b))
        for i in newEdges:
            if i[1] not in gfa.delta:
                gfa.delta[i[1]] = {}
            else:
                gfa.delta[i[1]][i[0]] = 'x'
        for i in newEdges:
            if i[0] not in gfa.delta[i[1]]:
                gfa.delta[i[1]][i[0]] = 'x'
        # initializations needed for cut point detection
        gfa.c = 1
        gfa.num = {}
        gfa.visited = []
        gfa.parent = {}
        gfa.low = {}
        gfa.cuts = set([])
        gfa.assignNum(gfa.Initial)
        gfa.assignLow(gfa.Initial)
        # initial state is never a cut point so it should be removed
        gfa.cuts.remove(gfa.Initial)
        cutpoints = copy(gfa.cuts) - gfa.Final
        # remove self-loops and check if the cut points are in a loop
        gfa = self.toGFA()
        gfa.normalize()
        for i in gfa.delta:
            if i in gfa.delta[i]:
                del gfa.delta[i][i]
        cycles = gfa.evalNumberOfStateCycles()
        for i in cycles:
            if cycles[i] != 0 and i in cutpoints:
                cutpoints.remove(i)
        return cutpoints

    def evalNumberOfStateCycles(self):
        """Evaluates the number of cycles each state participates

        :returns: state->list of cycle lengths
        :rtype: dict"""
        cycles = {}
        seen = []
        for i, _ in enumerate(self.States):
            cycles[i] = 0
        (bkE, multipl) = self._DFSBackEdges()
        for (x, y) in bkE:
            self._chkForCycles(y, x, cycles, seen, multipl)
        return cycles

    def _chkForCycles(self, y, x, cycles, seen, multipl):
        """Used in evalNumberOfStateCycles"""
        s = y
        path = [x, y]
        stack = [y for y in self.stateChildren(s)]
        marked = [y]
        while stack:
            foo = stack.pop()
            if foo:
                s = foo.pop()
                stack.append(foo)
            else:
                path.pop()
                continue
            if s in marked:
                continue
            elif s == x:
                bar = self._normalizeCycle(path)
                if bar not in seen:
                    seen.append(bar)
                    m = 1
                    for i in range(len(path) - 1):
                        m *= max(1, multipl[(path[i], path[i + 1])])
                    m *= max(1, multipl[(path[-1], path[0])])
                    for i in path:
                        cycles[i] = cycles.get(i, 0) + m
                continue
            else:
                marked.append(s)
                path.append(s)
            stack.append([y for y in self.stateChildren(s)])
        return cycles

    @staticmethod
    def _normalizeCycle(c):
        """Normalizes a cycle with its first element at the begining

        :param list c: cycle"""
        m = min(c)
        i = c.index(m)
        return c[i:] + c[:i]

    def _DFSBackEdges(self):
        """Returns a pair (BE, M) whee BE is the set of backedges form a DFS starting with the initial state as pairs
         (s, d) and M is a map (i, j)->multiplicity

        :returns: as said above
        :rtype: tuple"""
        mStates = set()
        bEdges = set()
        pool = set()
        multipl = {}
        if type(self.Initial) == set:  # NFAs
            mStates += self.Initial
            pool += self.Initial
        else:  # DFAs
            mStates.add(self.Initial)
            pool.add(self.Initial)
        while pool:
            s = pool.pop()
            child = self.stateChildren(s)
            # noinspection PyTypeChecker
            for r in child:
                multipl[(s, r)] = child[r]
            for i in child:
                if i in mStates or i in pool:
                    bEdges.add((s, i))
                else:
                    pool.add(i)
                    mStates.add(i)
        return bEdges, multipl

    def eliminateStout(self, st):
        """Eliminate all transitions outgoing from a given state

        :param int st: the state index to loose all outgoing transitions

        .. attention::
           performs in place alteration of the automata

        .. versionadded:: 0.9.6"""
        if st in list(self.delta.keys()):
            del (self.delta[st])
        return self

    def dup(self):
        """ Duplicate OFA

        :returns: duplicate object
        """
        return deepcopy(self)


class NFA(OFA):
    """Class for Non-deterministic Finite Automata (epsilon-transitions allowed).

    .. inheritance-diagram:: NFA"""

    def uniqueRepr(self):
        """Dummy representation. Used DFA.uniqueRepr()
        :rtype: tuple"""
        return self.toDFA().uniqueRepr()

    def __init__(self):
        FA.__init__(self)
        self.Initial = set()

    def __repr__(self):
        """'Official' string representation
        :returns: str
        :rtype: str"""
        return "NFA({0:>s})".format(self.__str__())

    def _lstTransitions(self):
        l = []
        for x in self.delta:
            for k in self.delta[x]:
                for y in self.delta[x][k]:
                    l.append((self.States[x], k, self.States[y]))
        return l

    def _s_lstInitial(self):
        return [str(self.States[x]) for x in self.Initial]

    def _lstInitial(self):
        if self.Initial is None:
            raise DFAnoInitial()
        else:
            return [self.States[i] for i in self.Initial]

    @staticmethod
    def vDescription():
        """Generation of Verso interface description

        .. versionadded:: 0.9.5

        :return: the interface list"""
        return [("NFA", "Nondeterministic Finite Automata"),
                [("NFAFAdo", lambda x: saveToString(x), "FAdo"),
                 ("NFAdot", lambda x: x.dotFormat("&"), "dot")],
                ("NFA-to-DFA", ("NFA to DFA", "NFA to DFA"), 1, "NFA", "DFA", lambda *x: x[0].toDFA()),
                ("NFA-reversal", ("Reversal language NFA", "Reversal language NFA"), 1, "NFA", "NFA",
                 lambda *x: x[0].reversal())]

    def __or__(self, other):
        """ Disjunction of automata:  X | Y.

        :param NFA|DFA other: the right hand operand
        :raises FAdoGeneralError: if any operand is not an NFA

        .. versionchanged:: 1.2"""
        if isinstance(other, DFA):
            par2 = other.toNFA()
        elif not isinstance(other, NFA):
            raise FAdoGeneralError("Incompatible objects")
        elif other.epsilonP():
            par2 = other.dup().elimEpsilon()
        else:
            par2 = other
        if self.epsilonP():
            par1 = self.dup().elimEpsilon()
        else:
            par1 = self
        new = par1._copySkell(par2)
        ini = new.addState()
        new.Sigma = new.Sigma.union(other.Sigma)
        new.addInitial(ini)
        for s in par1.Initial:
            si = new.stateIndex((0, s))
            new.addTransition(ini, Epsilon, si)
        for s in par2.Initial:
            si = new.stateIndex((1, s))
            new.addTransition(ini, Epsilon, si)
        fin = new.addState()
        new.addFinal(fin)
        for s in par1.Final:
            si = new.stateIndex((0, s))
            new.addTransition(si, Epsilon, fin)
        for s in par2.Final:
            si = new.stateIndex((1, s))
            new.addTransition(si, Epsilon, fin)
        return new

    def __and__(self, other):
        """Conjunction of automata

        :param NFA|DFA other: the right hand operand
        :rtype: NFA
        :raises FAdoGeneralError: if any operand is not an NFA"""
        if isinstance(other, DFA):
            par2 = other.toNFA()
        elif not isinstance(other, type(self)):
            raise FAdoGeneralError("Incompatible objects")
        elif other.epsilonP():
            par2 = other.dup().elimEpsilon()
        else:
            par2 = other
        if self.epsilonP():
            par1 = self.dup().elimEpsilon()
        else:
            par1 = self
        new = par1.product(par2)
        for x in [(par1.States[a], par2.States[b]) for a in par1.Final for b in other.Final]:
            if x in new.States:
                new.addFinal(new.stateIndex(x))
        return new._namesToString()

    def __invert__(self):
        """Complement of the NFA (through conversion to DFA)

        :rtype: NFA"""
        foo = self.toDFA()
        return foo.__invert__().toNFA()

    @staticmethod
    def _getTags():
        """returns Tags for dump

        :rtype: list of str"""
        return ["NFA"]

    def concat(self, other, middle="middle"):
        """Concatenation of NFA

        :param str middle: glue state name
        :param NFA|DFA other: the other NFA
        :returns: the result of the concatenation
        :rtype: NFA"""
        if isinstance(other, DFA):
            par2 = other.toNFA()
        else:
            par2 = other
        new = self._copySkell(par2)
        for i in self.Initial:
            new.addInitial(new.stateIndex((0, i)))
        m = new.addState(middle)
        for i in self.Final:
            new.addTransition(new.stateIndex((0, i)), Epsilon, m)
        for i in par2.Initial:
            new.addTransition(m, Epsilon, new.stateIndex((1, i)))
        for i in par2.Final:
            new.addFinal(new.stateIndex((1, i)))
        return new

    def witness(self):
        """Witness of non emptyness

        :return: word
        :rtype: str"""
        done = set()
        notDone = set()
        pref = dict()
        for si in self.Initial:
            pref[si] = Epsilon
            notDone.add(si)
        while notDone:
            si = notDone.pop()
            done.add(si)
            if si in self.Final:
                return pref[si]
            for syi in self.delta.get(si, []):
                for so in self.delta[si][syi]:
                    if so in done or so in notDone:
                        continue
                    pref[so] = sConcat(pref[si], syi)
                    notDone.add(so)
        return None

    # noinspection PyUnresolvedReferences
    def shuffle(self, other):
        """Shuffle of a NFA

        :param other: an FA
        :type other: FA
        :returns: the resulting NFA
        :rtype: NFA"""
        if len(self.Initial) > 1:
            d1 = self._toNFASingleInitial().elimEpsilon()
        else:
            d1 = self
        if type(other) == NFA:
            if len(other.Initial) > 1:
                d2 = self._toNFASingleInitial().elimEpsilon()
            else:
                d2 = other
        else:
            d2 = other.toNFA()
        c = NFA()
        NSigma = d1.Sigma.union(d2.Sigma)
        c.setSigma(NSigma)
        c.States = [(i, j) for i in range(len(d1.States)) for j in range(len(d2.States))]
        c.addInitial(c.stateIndex((list(d1.Initial)[0], list(d2.Initial)[0])))
        for st in c.States:
            si = c.stateIndex(st)
            if d1.finalP(st[0]) and d2.finalP(st[1]):
                c.addFinal(si)
            for sym in c.Sigma:
                try:
                    lq = d1.evalSymbol([st[0]], sym)
                    for q in lq:
                        c.addTransition(si, sym, c.stateIndex((q, st[1])))
                except (DFAstopped, DFAsymbolUnknown):
                    pass
                try:
                    lq = d2.evalSymbol([st[1]], sym)
                    # noinspection PyTypeChecker
                    for q in lq:
                        c.addTransition(si, sym, c.stateIndex((st[0], q)))
                except (DFAstopped, DFAsymbolUnknown):
                    pass
        return c

    def star(self, flag=False):
        """Kleene star of a NFA

        :param flag: plus instead of star
        :type flag: Boolean
        :returns: the resulting NFA
        :rtype: NFA"""
        new = self.dup()
        ini = copy(new.Initial)
        fin = copy(new.Final)
        nf = new.addState()
        new.addFinal(nf)
        if not flag:
            ni = new.addState()
            new.setInitial([ni])
            new.addTransition(ni, Epsilon, nf)
        else:
            ni = new.addState()
            nni = new.addState()
            new.setInitial([nni])
            new.addTransition(nni, Epsilon, ni)
        new.addTransition(nf, Epsilon, ni)
        for i in ini:
            new.addTransition(ni, Epsilon, i)
        for i in fin:
            new.addTransition(i, Epsilon, nf)
        return new

    def __eq__(self, other):
        """ Test equivalence of two NFAs

        :param other: the other NFA
        :type other: NFA
        :rtype: bool"""
        return self.toDFA() == other.toDFA()

    def __ne__(self, other):
        """ Test non  equivalence of two NFAs

        :param other: the other NFA
        :type other: NFA
        :rtype: bool"""
        return not self == other

    def _copySkell(self, other):
        """Creates a new NFA with the skells of both NFAs

        Each state is named with its previous index is inscribed in a tuple (0,_) and (1,_) respectively

        :param NFA other: the other NFA
        :rtype: NFA

        .. attention::
           No initial and final states are assigned in the resulting NFA."""
        new = NFA()
        s = len(self.States)
        for i in range(s):
            new.addState((0, i))
        for i in self.delta:
            for c in self.delta[i]:
                for j in self.delta[i][c]:
                    new.addTransition(new.stateIndex((0, i)), c, new.stateIndex((0, j)))
        s = len(other.States)
        for i in range(s):
            new.addState((1, i))
        for i in other.delta:
            for c in other.delta[i]:
                for j in other.delta[i][c]:
                    new.addTransition(new.stateIndex((1, i)), c, new.stateIndex((1, j)))
        return new

    def setInitial(self, statelist):
        """Sets the initial states of an NFA

        :param set|list|int statelist: an iterable of initial state indexes"""
        self.Initial = set(statelist)

    def addInitial(self, stateindex):
        """Add a new state to the set of initial states.

        :param int stateindex: index of new initial state"""
        self.Initial.add(stateindex)

    def succintTransitions(self):
        """ Collects the transition information in a concat way suitable for graphical representation.
        :rtype: list"""
        foo = dict()
        for s in self.delta:
            for c in self.delta[s]:
                for s1 in self.delta[s][c]:
                    k = (s, s1)
                    if k not in foo:
                        foo[k] = []
                    foo[k].append(c)
        l = []
        for k in foo:
            cs = foo[k]
            s = "%s" % graphvizTranslate(str(cs[0]))
            for c in cs[1:]:
                s += ", %s" % graphvizTranslate(str(c))
            l.append((str(self.States[k[0]]), str(self.States[k[1]]), s))
        return l

    def deleteStates(self, del_states):
        """Delete given iterable collection of states from the automaton.

        :param set|list del_states: collection of int representing states

        .. note::
           delta function will always be rebuilt, regardless of whether the states list to remove is a suffix,
           or a sublist, of the automaton's states list."""
        rename_map = {}
        new_delta = {}
        new_final = set()
        new_states = []
        for state in del_states:
            if state in self.Initial:
                self.Initial.remove(state)
        for state in range(len(self.States)):
            if state not in del_states:
                rename_map[state] = len(new_states)
                new_states.append(self.States[state])
        for state in rename_map:
            if state in self.Final:
                new_final.add(rename_map[state])
            if state not in self.delta:
                continue
            if not len(self.delta[state]) == 0:
                new_delta[rename_map[state]] = {}
            for symbol in self.delta[state]:
                new_targets = set([rename_map[s] for s in self.delta[state][symbol]
                                   if s in rename_map])
                if new_targets:
                    new_delta[rename_map[state]][symbol] = new_targets
        self.States = new_states
        self.delta = new_delta
        self.Final = new_final
        self.Initial = set([rename_map.get(x, x) for x in self.Initial])

    def addTransition(self, sti1, sym, sti2):
        """Adds a new transition. Transition is from ``sti1`` to ``sti2`` consuming symbol ``sym``. ``sti2`` is a
        unique state, not a set of them.

        :param int sti1: state index of departure
        :param int sti2: state index of arrival
        :param str sym: symbol consumed"""
        if sym != Epsilon:
            self.Sigma.add(sym)
        if sti1 not in self.delta:
            self.delta[sti1] = {sym: {sti2}}
        elif sym not in self.delta[sti1]:
            self.delta[sti1][sym] = {sti2}
        else:
            self.delta[sti1][sym].add(sti2)

    def addEpsilonLoops(self):
        """Add epsilon loops to every state
        :return: self

        .. attention:: in-place modification

        .. versionadded:: 1.0"""
        for i in range(len(self.States)):
            self.addTransition(i, Epsilon, i)
        return self

    def addTransitionQ(self, srcI, dest, symb, qfuture, qpast):
        """Add transition to the new transducer instance.

        :param set qpast: past queue
        :param set qfuture: future queue
        :param symb: symbol
        :param dest: destination state
        :param int srcI: source state

        .. versionadded:: 1.0"""
        if dest not in qpast:
            qfuture.add(dest)
        i = self.stateIndex(dest, True)
        self.addTransition(srcI, symb, i)

    def delTransition(self, sti1, sym, sti2, _no_check=False):
        """Remove a transition if existing and perform cleanup on the transition function's internal data structure.

        :param int sti1: state index of departure
        :param int sti2: state index of arrival
        :param str sym: symbol consumed
        :param bool _no_check: dismiss secure code

        .. note::
           unused alphabet symbols will be discarded from Sigma."""
        if not _no_check and (sti1 not in self.delta or sym not in self.delta[sti1]):
            return
        self.delta[sti1][sym].discard(sti2)
        if not self.delta[sti1][sym]:
            del self.delta[sti1][sym]
            if all([sym not in x for x in iter(self.delta.values())]):
                self.Sigma.discard(sym)
            if not self.delta[sti1]:
                del self.delta[sti1]

    def reversal(self):
        """Returns a NFA that recognizes the reversal of the language

        :returns: NFA recognizing reversal language
        :rtype: NFA"""
        rev = NFA()
        rev.setSigma(self.Sigma)
        rev.States = self.States[:]
        self.reverseTransitions(rev)
        rev.setFinal(self.Initial)
        rev.setInitial(self.Final)
        return rev

    def reorder(self, dicti):
        """Reorder states indexes according to given dictionary.

        :param dicti: state name reorder
        :type dicti: dictionary

        .. note::
           dictionary does not have to be complete"""
        if len(list(dicti.keys())) != len(self.States):
            for i in range(len(self.States)):
                if i not in dicti:
                    dicti[i] = i
        delta = {}
        for s in self.delta:
            delta[dicti[s]] = {}
            for c in self.delta[s]:
                delta[dicti[s]][c] = set()
                for st in self.delta[s][c]:
                    delta[dicti[s]][c].add(dicti[st])
        self.delta = delta
        self.setInitial([dicti[x] for x in self.Initial])
        Final = set()
        for i in self.Final:
            Final.add(dicti[i])
        self.Final = Final
        states = list(range(len(self.States)))
        for i in range(len(self.States)):
            states[dicti[i]] = self.States[i]
        self.States = states

    def epsilonP(self):
        """Whether this NFA has epsilon-transitions

        :rtype: bool"""
        return any([Epsilon in x for x in iter(self.delta.values())])

    def epsilonClosure(self, st):
        """Returns the set of states epsilon-connected to from given state or set of states.

        :param int|set st: state index or set of state indexes
        :returns: the list of state indexes epsilon connected to ``st``
        :rtype: set of int

        .. attention::
           ``st`` must exist."""
        if type(st) is set:
            s2 = set(st)
        else:
            s2 = {st}
        s1 = set()
        while s2:
            s = s2.pop()
            s1.add(s)
            s2.update(self.delta.get(s, {}).get(Epsilon, set()) - s1)
        return s1

    def closeEpsilon(self, st):
        """Add all non epsilon transitions from the states in the epsilon closure of given state to given state.

        :param int st: state index"""
        targets = self.epsilonClosure(st)
        targets.remove(st)
        if not targets:
            return
        for target in targets:
            self.delTransition(st, Epsilon, target)
        not_final = st not in self.Final
        for target in targets:
            if target in self.delta:
                for symbol, states in list(self.delta[target].items()):
                    if symbol is Epsilon:
                        continue
                    for state in states:
                        self.addTransition(st, symbol, state)
            if not_final and target in self.Final:
                self.addFinal(st)
                not_final = False

    def eliminateTSymbol(self, symbol):
        """Delete all trasitions through a given symbol

        :param str symbol: the symbol to be excluded from delta

        .. attention::
           in place alteration of the automata

        .. versionadded:: 0.9.6"""
        for s in self.delta:
            if symbol in self.delta[s]:
                del (self.delta[s][symbol])
            if not self.delta[s]:
                del self.delta[s]

    def elimEpsilon(self):
        """Eliminate epsilon-transitions from this automaton.

        :rtype : NFA

        .. attention::
           performs in place modification of automaton

        .. versionchanged:: 1.1.1"""
        for state in range(len(self.States)):
            self.closeEpsilon(state)
        return self

    def evalWordP(self, word):
        """Verify if the NFA recognises given word.

        :param str word: word to be recognised
        :rtype: bool"""
        ilist = self.epsilonClosure(self.Initial)
        for c in word:
            ilist = self.evalSymbol(ilist, c)
            if not ilist:
                return False
        for f in self.Final:
            if f in ilist:
                return True
        return False

    def evalSymbol(self, stil, sym):
        """Set of states reacheable from given states through given symbol and epsilon closure.

        :param set|list stil: set of current states
        :param str sym: symbol to be consumed
        :returns: set of reached state indexes
        :rtype: set[int]
        :raises DFAsymbolUnknown: if symbol is not in alphabet"""
        if sym not in self.Sigma:
            raise DFAsymbolUnknown(sym)
        res = set()
        for s in stil:
            try:
                ls = self.delta[s][sym]
            except KeyError:
                ls = set()
            except NameError:
                ls = set()
            for t in ls:
                res.update(self.epsilonClosure(t))
        return res

    def minimal(self):
        """Evaluates the equivalent minimal DFA

        :returns:  equivalent minimal DFA
        :rtype: DFA"""
        return self.minimalDFA()

    def minimalDFA(self):
        """Evaluates the equivalent minimal complete DFA

        :returns: equivalent minimal DFA
        :rtype: DFA"""
        return self.minimalBrzozowski()

    def dup(self):
        """Duplicate the basic structure into a new NFA. Basically a copy.deep.

        :rtype: NFA"""
        new = NFA()
        new.setSigma(self.Sigma)
        new.States = self.States[:]
        new.Initial = self.Initial.copy()
        new.Final = self.Final.copy()
        for s in self.delta:
            new.delta[s] = {}
            for c in self.delta[s]:
                new.delta[s][c] = self.delta[s][c].copy()
        return new

    def _inc(self, fa):
        """Combine self with given FA with a single final state.

        :param fa: FA to be included
        :type fa: FA
        :returns: a pair of state indexes (initial and final of the resulting NFA)
        :rtype: pair of int

        .. note::
           State names are not preserved."""
        for s in range(len(self.States)):
            self.States[s] = (0, self.States[s])
        for c in fa.Sigma:
            self.addSigma(c)
        for s in range(len(fa.States)):
            self.addState((1, s))
        for s in fa.delta:
            for c in fa.delta[s]:
                for t in fa.delta[s][c]:
                    self.addTransition(self.stateIndex((1, s)), c, self.stateIndex((1, t)))
        return (self.stateIndex((1, uSet(fa.Initial))),
                self.stateIndex((1, uSet(fa.Final))))

    def reverseTransitions(self, rev):
        """Evaluate reverse transition function.

        :param rev: NFA in which the reverse function will be stored
        :type rev: NFA"""
        for s in self.delta:
            for a in self.delta[s]:
                for s1 in self.delta[s][a]:
                    rev.addTransition(s1, a, s)

    def initialComp(self):
        """Evaluate the connected component starting at the initial state.

        :returns: list of state indexes in the component
        :rtype: list of int"""
        lst = list(self.Initial)
        i = 0
        while True:
            try:
                foo = list(self.delta[lst[i]].keys())
            except KeyError:
                foo = []
            for c in foo:
                for _ in self.delta[lst[i]]:
                    for s in self.delta[lst[i]][c]:
                        if s not in lst:
                            lst.append(s)
            i += 1
            if i >= len(lst):
                return lst

    def finalCompP(self, s):
        """Verify whether there is a final state in strongly connected component containing given state.

        :param s: state index
        :type s: int
        :returns: :: bool"""
        if s in self.Final:
            return True
        lst = [s]
        i = 0
        while True:
            try:
                foo = list(self.delta[lst[i]].keys())
            except KeyError:
                foo = []
            for c in foo:
                for s in self.delta[lst[i]][c]:
                    if s not in lst:
                        if s in self.Final:
                            return True
                        lst.append(s)
            i += 1
            if i >= len(lst):
                return False

    def deterministicP(self):
        """Verify whether this NFA is actually deterministic

        :rtype: bool"""
        if len(self.Initial) != 1:
            return False
        for st in self.delta:
            for sy in self.delta[st]:
                if sy == Epsilon or len(self.delta[st][sy]) > 1:
                    return False
        return True

    def _toDFAd(self):
        """Transforms into a DFA assuming it is deterministic

    :returns: the FA in a DFA structure
    :rtype: DFA"""
        # The subset construction will consider only accessible states
        new = DFA()
        new.Sigma = self.Sigma
        # self must be trim
        old = self.dup()
        old.trim()
        s = len(old.States)
        for i in range(s):
            new.addState(str(i))
        for i in old.delta:
            for c in old.delta[i]:
                new.addTransition(new.stateIndex(str(i)), c, new.stateIndex("{0:d}".format(uSet(old.delta[i][c]))))
        new.setInitial(new.stateIndex(str(uSet(old.Initial))))
        for i in old.Final:
            new.addFinal(new.stateIndex(str(i)))
        return new

    def homogenousP(self, x):
        """Whether this NFA is homogenous; that is, for all states, whether all incoming transitions to that state
        are through the same symbol.

        :param x: dummy parameter to agree with the method in DFAr
        :rtype: bool"""
        return self.toNFAr().homogenousP(True)

    def stronglyConnectedComponents(self):
        """Strong components

        :rtype: list

        .. versionadded:: 1.0"""

        def _strongConnect(st):
            indices[st] = index[0]
            lowlink[st] = index[0]
            index[0] += 1
            s.append(st)
            inIndices[st] = True
            inS[st] = True
            links = [x for k in self.delta.get(st, {}) for x in self.delta[st][k]]
            # links = [self.delta[state][k] for k in self.delta.get(state, {})]
            for l in links:
                if not inIndices[l]:
                    _strongConnect(l)
                    lowlink[st] = min(lowlink[st], lowlink[l])
                elif inS[l]:
                    lowlink[st] = min(lowlink[st], indices[l])
            if lowlink[st] == indices[st]:
                component = []
                while True:
                    l = s.pop()
                    inS[l] = False
                    component.append(l)
                    if l == st:
                        break
                result.append(component)

        index = [0]
        indices = []
        lowlink = []
        s = []
        result = []
        inIndices = []
        inS = []
        for _ in self.States:
            inIndices.append(False)
            inS.append(False)
            indices.append(-1)
            lowlink.append(-1)
        for state in self.delta:
            if not inIndices[state]:
                _strongConnect(state)
        return result

    def dotFormat(self, size="20,20", direction="LR", sep="\n"):
        """ A dot representation
        :arg direction: direction of drawing
        :arg size: size of image
        :arg sep: line separator
        :return: the dot representation
        type sep: str
        :type direction: str
        :type size: str
        :rtype: str

        .. versionadded:: 0.9.6

        .. versionchanged:: 0.9.8"""

        s = "digraph finite_state_machine {{{0:s}".format(sep)
        s += "rankdir={0:s};{1:s}".format(direction, sep)
        s += "size=\"{0:s}\";{1:s}".format(size, sep)
        for si in self.Initial:
            sn = str(self.States[si])
            s += "node [shape = point]; \"dummy{0:s}\"{1:s}".format(sn, sep)
            s += self.dotDrawState(si)
            s += "\"dummy{0:s}\" -> \"{1:s}\";{2:s}".format(sn, str(self.States[si]), sep)
        niStates = [i for i in range(len(self.States)) if i not in self.Initial]
        for sti in niStates:
            s += self.dotDrawState(sti)
        for si in self.succintTransitions():
            s += self.dotDrawTransition(si[0], si[2], si[1])
        s += "}}{0:s}".format(sep)
        return s

    def wordImage(self, word, ist=None):
        """Evaluates the set of states reached consuming given word

        :param word: the word
        :type word: list of stings
        :param ist: starting state index (or set of)
        :type ist: int
        :returns: the set of ending states
        :rtype: Set of int
        """
        if not ist:
            ist = self.Initial
        ilist = self.epsilonClosure(ist)
        for c in word:
            ilist = self.evalSymbol(ilist, c)
            if not ilist:
                return []
        return ilist

    def product(self, other):
        """Returns a NFA (skeletom) resulting of the simultaneous execution of two DFA.

        :param other: the other automata
        :type other: NFA
        :rtype: NFA

        .. note::
           No final states are set.

        .. attention::
           - the name ``EmptySet`` is used in a unique special state name
           - the method uses 3 internal functions for simplicity of code (really!)"""

        def _sN(a, s):
            try:
                j = a.stateIndex(s)
            except DFAstateUnknown:
                return None
            return j

        def _kS(a, j):
            """

            :param a:
            :param j:
            :return:"""
            if j is None:
                return set()
            try:
                ks = list(a.delta[j].keys())
            except KeyError:
                return set()
            return set(ks)

        def _dealT(srcI, dest):
            """

            :param srcI: source state
            :param dest: destination state"""
            if not (dest in done or dest in notDone):
                iN = new.addState(dest)
                notDone.append(dest)
            else:
                iN = new.stateIndex(dest)
            new.addTransition(srcI, k, iN)

        new = NFA()
        new.setSigma(self.Sigma.union(other.Sigma))
        notDone = []
        done = []
        for s1 in [self.States[x] for x in self.Initial]:
            for s2 in [other.States[x] for x in other.Initial]:
                sname = (s1, s2)
                new.addState(sname)
                new.addInitial(new.stateIndex(sname))
                if (s1, s2) not in notDone:
                    notDone.append((s1, s2))
        while notDone:
            state = notDone.pop()
            done.append(state)
            (s1, s2) = state
            i = new.stateIndex(state)
            (i1, i2) = (_sN(self, s1), _sN(other, s2))
            (k1, k2) = (_kS(self, i1), _kS(other, i2))
            for k in k1.intersection(k2):
                for destination in [(self.States[d1], other.States[d2]) for d1 in self.delta[i1][k] for d2 in
                                    other.delta[i2][k]]:
                    _dealT(i, destination)
            for k in k1 - k2:
                for n in self.delta[i1][k]:
                    _dealT(i, (self.States[n], EmptySet))
            for k in k2 - k1:
                for n in other.delta[i2][k]:
                    _dealT(i, (EmptySet, other.States[n]))
        return new

    def _toNFASingleInitial(self):
        """Construct an equivalent NFA with only one initial state

        :rtype: NFA"""
        aut = self.dup()
        Initial = aut.addState()
        aut.delta[Initial] = {}
        aut.delta[Initial][Epsilon] = aut.Initial
        aut.setInitial([Initial])
        return aut

    def _deleteRefInDelta(self, src, sym, dest):
        """Deletion of a reference in Delta

        :param src: source state
        :type src: int
        :param sym: symbol
        :type sym: int
        :param dest: destination state
        :type dest: int"""
        if dest in self.delta[src][sym]:
            self.delta[src][sym].remove(dest)
        for k in range(dest + 1, len(self.States)):
            if k in self.delta[dest][sym]:
                self.delta[src][sym].remove(k)
                self.delta[src][sym].add(k - 1)
        if not len(self.delta[src][sym]):
            del self.delta[src][sym]
            if not len(self.delta[src]):
                del self.delta[src]

    def _deleteRefInitial(self, sti):
        """Deletes a state from the set of initial states.  The other states are renumbered.

        :param sti: state index
        :type sti: int"""
        if sti in self.Initial:
            self.Initial.remove(sti)
        for s in self.Initial:
            if sti < s:
                self.Initial.remove(s)
                self.Initial.add(s - 1)

    def toNFA(self):
        """ Dummy identity function

        :rtype: NFA"""
        return self

    def toDFA(self):
        """Construct a DFA equivalent to this NFA, by the subset construction method.

        :rtype: DFA

        .. note::
           valid to epsilon-NFA"""
        if self.deterministicP():
            return self._toDFAd()
        dfa = DFA()
        lStates = []
        stl = self.epsilonClosure(self.Initial)
        lStates.append(stl)
        dfa.setInitial(dfa.addState(stl))
        dfa.setSigma(self.Sigma)
        for f in self.Final:
            if f in stl:
                dfa.addFinal(0)
                break
        index = 0
        while True:
            slist = lStates[index]
            si = dfa.stateIndex(slist)
            for s in self.Sigma:
                stl = self.evalSymbol(slist, s)
                if not stl:
                    continue
                if stl not in lStates:
                    lStates.append(stl)
                    foo = dfa.addState(stl)
                    for f in self.Final:
                        if f in stl:
                            dfa.addFinal(foo)
                            break
                else:
                    foo = dfa.stateIndex(stl)
                dfa.addTransition(si, s, foo)
            if index == len(lStates) - 1:
                break
            else:
                index += 1
        return dfa

    def hasTransitionP(self, state, symbol=None, target=None):
        """Whether there's a transition from given state, optionally through given symbol,
        and optionally to a specific target.

        :param state: source state
        :type state: int
        :param symbol: optional transition symbol
        :type symbol: str
        :param target: optional target state
        :type target: int
        :returns: if there is a transition
        :rtype: bool"""
        if state not in self.delta:
            return False
        if symbol is None:
            return True
        if symbol not in self.delta[state]:
            return False
        if target is None:
            return self.delta[state][symbol] != set()
        else:
            return target in self.delta[state][symbol]

    def usefulStates(self, initial_states=None):
        """Set of states reacheable from the given initial state(s) that have a path to a final state.

        :param initial_states: set of initial states
        :type initial_states: set of int or list of int
        :returns: set of state indexes
        :rtype: set of int"""
        if initial_states is None:
            initial_states = self.Initial
        useful = set([s for s in initial_states
                      if s in self.Final])
        stack = list(initial_states)
        preceding = {}
        for i in stack:
            preceding[i] = []
        while stack:
            state = stack.pop()
            if state not in self.delta:
                continue
            for symbol in self.delta[state]:
                for adjacent in self.delta[state][symbol]:
                    is_useful = adjacent in useful
                    if adjacent in self.Final or is_useful:
                        useful.add(state)
                        if not is_useful:
                            useful.add(adjacent)
                            preceding[adjacent] = []
                            stack.append(adjacent)
                        inpath_stack = [p for p in preceding[state] if p not in useful]
                        preceding[state] = []
                        while inpath_stack:
                            previous = inpath_stack.pop()
                            useful.add(previous)
                            inpath_stack += [p for p in preceding[previous] if p not in useful]
                            preceding[previous] = []
                        continue
                    if adjacent not in preceding:
                        preceding[adjacent] = [state]
                        stack.append(adjacent)
                    else:
                        preceding[adjacent].append(state)
        if not useful and self.Initial:
            useful.add(min(self.Initial))
        return useful

    def eliminateEpsilonTransitions(self):
        """Eliminates all epslilon-transitions with no state addition

        .. attention::
           in-place modification"""
        for s in range(len(self.States)):
            if Epsilon in self.delta.get(s, []):
                for s1 in self.epsilonClosure(self.delta[s][Epsilon]):
                    if s1 in self.Final:
                        self.addFinal(s)
                    for a in self.delta.get(s1, []):
                        if a != Epsilon:
                            for s2 in self.delta[s1][a]:
                                self.addTransition(s, a, s2)
                foo = copy(self.delta[s][Epsilon])
                for s1 in foo:
                    self.delTransition(s, Epsilon, s1)
        self.trim()
        return self

    def autobisimulation(self):
        """Largest right invariant equivalence between states of the NFA

        :returns: Incomplete equivalence relation (transitivity, and reflexivity not calculated) as a set of
                    unordered pairs of states
        :rtype: Set of frozensets

        .. seealso:: Ilie&Yu, 2003"""
        n_states = len(self.States)
        undecided_pairs = set([frozenset((i, j))
                               for i in range(n_states)
                               for j in range(i + 1, n_states)])
        marked = set()
        for pair in undecided_pairs:
            a, b = pair
            if (a in self.Final) != (b in self.Final):
                marked.add(pair)

        def _desc_marked(d_p, sym, q1, mrkd):
            """

            :param d_p:
            :param sym:
            :param q1:
            :param mrkd:"""
            for d_q in self.delta[q1][sym]:
                yield frozenset((d_p, d_q)) in mrkd

        changed_marked = True
        while changed_marked:
            changed_marked = False
            undecided_pairs.difference_update(marked)
            for pair in undecided_pairs:
                p, q = pair
                if p in self.delta:
                    if q not in self.delta or (set(self.delta[p].keys()) != set(self.delta[q].keys())):
                        marked.add(pair)
                        changed_marked = True
                    else:
                        for symbol in self.delta[p]:
                            for desc_p in self.delta[p][symbol]:
                                if all(_desc_marked(desc_p, symbol, q, marked)):
                                    marked.add(pair)
                                    changed_marked = True
                                    break
                            if pair in marked:
                                break
                if pair not in marked and q in self.delta:
                    if p not in self.delta:
                        marked.add(pair)
                        changed_marked = True
                    else:
                        for symbol in self.delta[q]:
                            for desc_q in self.delta[q][symbol]:
                                if all(_desc_marked(desc_q, symbol, p, marked)):
                                    marked.add(pair)
                                    changed_marked = True
                                    break
                            if pair in marked:
                                break
        undecided_pairs.difference_update(marked)
        return undecided_pairs

    # noinspection PyUnusedLocal
    def autobisimulation2(self):
        """Alternative space-efficient definition of NFA.autobisimulation.

        :returns: Incomplete equivalence relation (reflexivity, symmetry, and transitivity not calculated) as a set
                  of pairs of states
        :rtype: list of tuples"""
        n_states = len(self.States)
        marked = set()
        for i in range(n_states):
            for j in range(i + 1, n_states):
                if (i in self.Final) != (j in self.Final):
                    marked.add((i, j))

        def _all_desc_marked(p, q, mrkd):
            """

            :param p:
            :param q:
            :param mrkd:"""
            for s in self.delta[p]:
                for desc_p in self.delta[p][s]:
                    all_marked = True
                    for desc_q in self.delta[q][s]:
                        if (desc_p, desc_q) not in mrkd and (desc_q, desc_p) not in mrkd:
                            all_marked = False
                            break
                    yield all_marked

        changed_marked = True
        while changed_marked:
            # noinspection PyUnusedLocal
            changed_marked = False
            for i in range(n_states):
                for j in range(i + 1, n_states):
                    if (i, j) in marked:
                        continue
                    if i not in self.delta and j not in self.delta:
                        continue
                    if set(self.delta.get(i, {}).keys()) != set(self.delta.get(j, {}).keys()):
                        marked.add((i, j))
                        changed_marked = True
                        continue
                    if any(_all_desc_marked(i, j, marked)) or any(_all_desc_marked(j, i, marked)):
                        marked.add((i, j))
                        changed_marked = True
                        continue
        return [(i, j)
                for i in range(n_states)
                for j in range(i + 1, n_states)
                if (i, j) not in marked]

    def equivReduced(self, equiv_classes):
        """Equivalent NFA reduced according to given equivalence classes.

        :param equiv_classes: Equivalence classes
        :type equiv_classes: UnionFind
        :returns: Equivalent NFA
        :rtype: NFA"""
        nfa = NFA()
        nfa.setSigma(self.Sigma)
        rename_map = {}
        for istate in self.Initial:
            equiv_istate = equiv_classes.find(istate)
            equiv_istate_renamed = nfa.addState(equiv_istate)
            rename_map[equiv_istate] = equiv_istate_renamed
            nfa.addInitial(equiv_istate_renamed)
        for state in self.delta:
            equiv_state = equiv_classes.find(state)
            if equiv_state not in rename_map:
                equiv_state_renamed = nfa.addState(equiv_state)
                rename_map[equiv_state] = equiv_state_renamed
            else:
                equiv_state_renamed = rename_map[equiv_state]
            for symbol in self.delta[state]:
                for target in self.delta[state][symbol]:
                    equiv_target = equiv_classes.find(target)
                    if equiv_target not in rename_map:
                        equiv_target_renamed = nfa.addState(equiv_target)
                        rename_map[equiv_target] = equiv_target_renamed
                    else:
                        equiv_target_renamed = rename_map[equiv_target]
                    nfa.addTransition(equiv_state_renamed, symbol, equiv_target_renamed)
        for state in self.Final:
            equiv_state = equiv_classes.find(state)
            if equiv_state not in rename_map:
                rename_map[equiv_state] = nfa.addState(equiv_state)
            nfa.addFinal(rename_map[equiv_state])
        return nfa

    def rEquivNFA(self):
        """Equivalent NFA obtained from merging equivalent states from autobisimulation of this NFA.

        :rtype: NFA

        .. note::
           returns copy of self if autobisimulation renders no equivalent states."""
        autobisimulation = self.autobisimulation()
        if not autobisimulation:
            return self.dup()
        equiv_classes = UnionFind(auto_create=True)
        for i in range(len(self.States)):
            equiv_classes.make_set(i)
        for i, j in autobisimulation:
            equiv_classes.union(i, j)
        return self.equivReduced(equiv_classes)

    def lEquivNFA(self):
        """Equivalent NFA obtained from merging equivalent states from autobisimulation of this NFA's reversal.

        :rtype: NFA

        .. note::
           returns copy of self if autobisimulation renders no equivalent states."""
        autobisimulation = self.reversal().autobisimulation()
        if not autobisimulation:
            return self.dup()
        equiv_classes = UnionFind(auto_create=True)
        for i in range(len(self.States)):
            equiv_classes.make_set(i)
        for i, j in autobisimulation:
            equiv_classes.union(i, j)
        return self.equivReduced(equiv_classes)

    def lrEquivNFA(self):
        """Equivalent NFA obtained from merging equivalent states from autobisimulation of this NFA,
        and from autobisimulation of its reversal; i.e., merges all states that are equivalent w.r.t. the largest
        right invariant and largest left invariant equivalence relations.

        :rtype: NFA

        .. note::
           returns copy of self if autobisimulations render no equivalent states."""
        l_nfa = self.lEquivNFA()
        lr_nfa = l_nfa.rEquivNFA()
        del l_nfa
        return lr_nfa

    def epsilonPaths(self, start, end):
        """All states in all paths (DFS) through empty words from a given starting state to a given ending state.

        :param start: start state
        :type start: int
        :param end: end state
        :type end: int
        :returns: states in epsilon paths from start to end
        :rtype: set of states"""
        inpaths = set()
        stack = [start]
        preceding = {start: []}
        while stack:
            state = stack.pop()
            if self.hasTransitionP(state, Epsilon):
                for adjacent in self.delta[state][Epsilon]:
                    if adjacent is end or adjacent in inpaths:
                        inpaths.add(state)
                        inpath_stack = [p for p in preceding[state] if p not in inpaths]
                        preceding[state] = []
                        while inpath_stack:
                            previous = inpath_stack.pop()
                            inpaths.add(previous)
                            inpath_stack += [p for p in preceding[previous] if p not in inpaths]
                            preceding[previous] = []
                        continue
                    if adjacent not in preceding:
                        preceding[adjacent] = [state]
                        stack.append(adjacent)
                    else:
                        preceding[adjacent].append(state)
        return inpaths

    def toNFAr(self):
        """NFA with the reverse mapping of the delta function.

        :returns: shallow copy with reverse delta function added
        :rtype: NFAr"""
        nfaR = NFAr()
        nfaR.setInitial(self.Initial)
        nfaR.setFinal(self.Final)
        nfaR.setSigma(self.Sigma)
        nfaR.States = list(self.States)
        for source in self.delta:
            for symbol in self.delta[source]:
                for target in self.delta[source][symbol]:
                    nfaR.addTransition(source, symbol, target)
        return nfaR

    def countTransitions(self):
        """Number of transitions of a NFA

        :rtype: int"""
        return sum([sum(map(len, iter(self.delta[t].values())))
                    for t in self.delta])

    def toGFA(self):
        """ Creates a GFA equivalent to NFA

        :returns: a GFA deep copy
        :rtype: GFA """
        gfa = GFA()
        gfa.setSigma(self.Sigma)
        # this should be optimized
        fa = self._toNFASingleInitial()
        gfa.Initial = uSet(fa.Initial)
        gfa.States = fa.States[:]
        gfa.setFinal(fa.Final)
        gfa.predecessors = {}
        for i in range(len(gfa.States)):
            gfa.predecessors[i] = set([])
        for s in fa.delta:
            for c in fa.delta[s]:
                for s1 in fa.delta[s][c]:
                    gfa.addTransition(s, c, s1)
        return gfa

    def stateChildren(self, state, strict=False):
        """Set of children of a state

        :param strict: if not strict a state is never its own child even if a self loop is in place
        :type strict: bool
        :param state: state id queried
        :type state: int
        :returns: children states
        :rtype: Set of int"""
        l = set([])
        if state not in list(self.delta.keys()):
            return l
        for c in self.Sigma:
            if c in self.delta[state]:
                l += self.delta[state][c]
        if not strict:
            if state in l:
                l.remove(state)
        return l

    def half(self):
        """Half operation

        .. versionadded:: 0.9.6"""
        a1 = self.dup()
        a1.renameStates()
        a2 = a1.dup().reversal()
        a4 = a2._starTransitions()
        a3 = a1.product(a4)
        l = []
        for n1, n2 in a3.States:
            if n1.__str__() == "@empty_set" or n2.__str__() == "@empty_set":
                l.append((n1, n2))
            if n1.__str__() == n2.__str__():
                a3.addFinal(a3.stateIndex((n1, n2)))
        a3.deleteStates(list(map(a3.stateIndex, l)))
        return a3

    def _starTransitions(self):
        new = NFA()
        for _ in self.States:
            new.addState()
        for s in self.delta:
            for c in self.delta[s]:
                for s1 in self.delta[s][c]:
                    for c1 in self.Sigma:
                        new.addTransition(s, c1, s1)
        for s in self.Initial:
            new.addInitial(s)
        for s in self.Final:
            new.addFinal(s)
        return new

    def subword(self):
        """
        returns a nfa that recognizes subword(L(self))

        :rtype: nfa
        """
        c = self.dup()
        c.trim()
        for s in c.delta:
            ss = set([])
            for sym in c.delta[s]:
                ss.update(c.delta[s][sym])
            if Epsilon not in c.delta[s]:
                c.delta[s][Epsilon] = set([])
            c.delta[s][Epsilon].update(ss)
        return c

    def enumNFA(self, n=None):
        """
        returns the set of words of words of length up to n accepted by self
        :param n: highest lenght or all words if finite
        :type n: int

        :rtype: list of strings or None

        .. note: use with care because the number of words can be huge
        """
        d = self.dup()
        d.elimEpsilon()
        e = EnumNFA(d)
        if n is None:
            return None
        words = []
        for i in range(n + 1):
            e.enumCrossSection(i)
            words += e.Words
        return words

    
# noinspection PyTypeChecker
class NFAr(NFA):
    """Class for Non-deterministic Finite Automata with reverse delta function added by construction.

    .. inheritance-diagram:: NFAr

    :var deltaReverse: the reversed transition function

    .. note::
       Includes efficient methods for merging states."""

    def __init__(self):
        super(NFAr, self).__init__()
        self.deltaReverse = {}

    def addTransition(self, sti1, sym, sti2):
        """Adds a new transition. Transition is from ``sti1`` to ``sti2`` consuming symbol ``sym``. ``sti2`` is a
        unique state, not a set of them. Reversed transition function  is also computed

        :param sti1: state index of departure
        :type sti1: int
        :param sti2: state index of arrival
        :type sti2: int
        :param sym: symbol consumed
        :type sym: str"""
        super(NFAr, self).addTransition(sti1, sym, sti2)
        if sti2 not in self.deltaReverse:
            self.deltaReverse[sti2] = {sym: {sti1}}
        elif sym not in self.deltaReverse[sti2]:
            self.deltaReverse[sti2][sym] = {sti1}
        else:
            self.deltaReverse[sti2][sym].add(sti1)

    def delTransition(self, sti1, sym, sti2, _no_check=False):
        """Remove a transition if existing and perform cleanup on the transition function's internal data structure
        and in the reversal transition function

        :param sti1: state index of departure
        :type sti1: int
        :param sti2: state index of arrival
        :type sti2: int
        :param sym: symbol consumed
        :type sym: str
        :param _no_check: dismiss secure code
        :type _no_check: bool"""
        super(NFAr, self).delTransition(sti1, sym, sti2, _no_check)
        if not _no_check and (sti2 not in self.deltaReverse or sym not in self.deltaReverse[sti2]):
            return
        self.deltaReverse[sti2][sym].discard(sti1)
        if not self.deltaReverse[sti2][sym]:
            del self.deltaReverse[sti2][sym]
            if not self.deltaReverse[sti2]:
                del self.deltaReverse[sti2]

    def deleteStates(self, del_states):
        """Delete given iterable collection of states from the automaton. Performe deletion in the transition
        function and its reversal.

        :param del_states: collection of int representing states
        :type del_states: set or list of int"""
        super(NFAr, self).deleteStates(del_states)
        new_deltaReverse = {}
        for target in self.delta:
            for symbol in self.delta[target]:
                for source in self.delta[target][symbol]:
                    if source not in new_deltaReverse:
                        new_deltaReverse[source] = {}
                    if symbol not in new_deltaReverse[source]:
                        new_deltaReverse[source][symbol] = set()
                    new_deltaReverse[source][symbol].add(target)
        self.deltaReverse = new_deltaReverse

    def mergeStates(self, f, t):
        """Merge the first given state into the second. If first state is an initial or final state,
        the second becomes respectively an initial or final state.

        :param f: index of state to be absorbed
        :type f: int
        :param t: index of remaining state
        :type t:  int

        .. attention::
           It is up to the caller to remove the disconnected
           state. This can be achieved with ```trim()``."""
        if f is t:
            return
        if f in self.delta:
            for symbol in self.delta[f]:
                for state in self.delta[f][symbol]:
                    self.deltaReverse[state][symbol].remove(f)
                    if state is f:
                        state = t
                    if state is t and symbol is Epsilon:
                        continue
                    self.addTransition(t, symbol, state)
                    if not self.deltaReverse[state][symbol]:
                        del (self.deltaReverse[state][symbol])
            del (self.delta[f])
        if f in self.deltaReverse:
            for symbol in self.deltaReverse[f]:
                for state in self.deltaReverse[f][symbol]:
                    if state is f:
                        state = t
                    else:
                        self.delta[state][symbol].remove(f)
                    if state is t and symbol is Epsilon:
                        continue
                    self.addTransition(state, symbol, t)
                    if not self.delta[state][symbol]:
                        del (self.delta[state][symbol])
            del (self.deltaReverse[f])
        if f in self.Initial:
            self.Initial.remove(f)
            self.addInitial(t)
        if f in self.Final:
            self.Final.remove(f)
            self.addFinal(t)

    def mergeStatesSet(self, tomerge, target=None):
        """Merge a set of states with a target merge state. If the states in the set have transitions among them,
        those transitions will be directly merged into the target state.

        :param tomerge: set of states to merge with target
        :type tomerge: Set of initegers
        :param target: optional target state
        :type target: int

        .. note::
           if target state is not given, the minimal index with be considered.

        .. attention::
           The states of the list will become unreacheable, but won't be removed. It is up to the caller to remove
           them. That can be achieved with ``trim()``."""
        if not tomerge:
            return
        if not target:
            target = min(tomerge)
        # noinspection PyUnresolvedReferences
        tomerge.discard(target)
        for state in tomerge:
            if state in self.delta:
                for symbol in self.delta[state]:
                    for s in self.delta[state][symbol]:
                        self.deltaReverse[s][symbol].discard(state)
                        if s in tomerge:
                            s = target
                        if symbol is Epsilon and s is target:
                            continue
                        self.addTransition(target, symbol, s)
            if state in self.deltaReverse:
                for symbol in self.deltaReverse[state]:
                    for s in self.deltaReverse[state][symbol]:
                        self.delta[s][symbol].discard(state)
                        if s in tomerge:
                            s = target
                        if symbol is Epsilon and s is target:
                            continue
                        self.addTransition(s, symbol, target)
                del (self.deltaReverse[state])
            if state in self.delta:
                del (self.delta[state])
        if target in self.delta:
            for symbol in self.delta[target]:
                for state in self.delta[target][symbol].copy():
                    if state in tomerge:
                        self.delta[target][symbol].discard(state)
                        if symbol is Epsilon:
                            continue
                        self.delta[target][symbol].add(target)
        if self.Initial.intersection(tomerge):
            self.addInitial(target)
        if self.Final.intersection(tomerge):
            self.addFinal(target)
        return target

    def homogenousP(self, inplace=False):
        """Checks is the automaton is homogenous, i.e.the transitions that reaches a state have all the same label.

        :arg inplace: if True performs epsilon transitions elimination
        :type inplace: bool
        :return: True if homogenous
        :rtype: bool"""
        nfa = self
        if self.epsilonP():
            if inplace:
                self.elimEpsilon()
            else:
                nfa = self.dup()
                nfa.elimEpsilon()
        return all([len(m) == 1 for m in nfa.deltaReverse.values()])

    def elimEpsilonO(self):
        """Eliminate epsilon-transitions from this automaton, with reduction of states through elimination of
        epsilon-cycles, and single epsilon-transition cases.

        :returns: itself
        :rtype:

        .. attention::
           performs inplace modification of automaton"""
        for state in self.delta:
            if state not in self.delta:
                continue
            merge_states = self.epsilonPaths(state, state)
            merge_states.add(self.unlinkSoleOutgoing(state))
            merge_states.add(self.unlinkSoleIncoming(state))
            merge_states.discard(None)
            if merge_states:
                if len(merge_states) == 1:
                    self.mergeStates(state, merge_states.pop())
                else:
                    self.mergeStatesSet(merge_states)
        super(NFAr, self).elimEpsilon()
        self.trim()
        return self

    def unlinkSoleIncoming(self, state):
        """If given state has only one incoming transition (indegree is one), and it's through epsilon,
        then remove such transition and return the source state.

        :param state: state to check
        :type state: int
        :returns: source state
        :rtype: int or None

        .. note::
           if conditions aren't met, returned source state is None, and automaton remains unmodified."""
        if not len(self.deltaReverse.get(state, [])) == 1 or not len(self.deltaReverse[state].get(Epsilon, [])) == 1:
            return None
        source_state = self.deltaReverse[state][Epsilon].pop()
        self.delTransition(source_state, Epsilon, state, True)
        return source_state

    def unlinkSoleOutgoing(self, state):
        """If given state has only one outgoing transition (outdegree is one), and it's through epsilon,
        then remove such transition and return the target state.

        :param state: state to check
        :type state: int
        :returns: target state
        :rtype: int or None

        .. note::
           if conditions aren't met, returned target state is None, and automaton remains unmodified."""
        if not len(self.delta.get(state, [])) == 1 or not len(self.delta[state].get(Epsilon, [])) == 1:
            return None
        target_state = self.delta[state][Epsilon].pop()
        self.delTransition(state, Epsilon, target_state, True)
        return target_state

    def toNFA(self):
        """Turn into an instance of NFA, and remove the reverse mapping of the delta function.

        :returns: shallow copy without reverse delta function
        :rtype: NFA"""
        nfa = NFA()
        nfa.Initial = self.Initial
        nfa.Final = self.Final
        nfa.delta = self.delta
        nfa.Sigma = self.Sigma
        nfa.States = self.States
        return nfa


# noinspection PyTypeChecker
class DFA(OFA):
    """ Class for Deterministic Finite Automata.

    .. inheritance-diagram:: DFA"""

    def __init__(self):
        super(DFA, self).__init__()
        self.delta_inv = None
        self.i = None

    @staticmethod
    def vDescription():
        """Generation of Verso interface description

        .. versionadded:: 0.9.5

        :return: the interface list"""
        return [("DFA", "Deterministic Finite Automata"),
                [("DFAFAdo", lambda x: saveToString(x), "FAdo"),
                 ("DFAdot", lambda x: x.dotFormat("&"), "dot")],
                ("DFA-complete-minimal", ("Complete minimal automata", "Complete minimal automata"), 1, "DFA", "DFA",
                 lambda *x: x[0].completeMinimal()),
                ("DFA-concatenation", ("Concatenate two DFAs", "Concatenate two DFAs"), 2, "DFA", "DFA", "DFA",
                 lambda *x: x[0].concat(x[1])),
                ("DFA-conjunction", ("Intersection of DFAs", "Intersection of DFAs"), 2, "DFA", "DFA", "DFA",
                 lambda *x: x[0].conjunction(x[1])),
                ("DFA-disjunction", ("Disjunction of DFAs", "Disjunction of DFAs"), 2, "DFA", "DFA", "DFA",
                 lambda *x: x[0].disjunction(x[1])),
                ("DFA-to-NFA", ("Convert to NFA", "Convert to NFA"), 1, "DFA", "NFA", lambda *x: x[0].toNFA()),
                ("DFA-acyclicP", ("Test if automata is acyclic", "Test if automata is acyclic"), 1, "DFA", "Bool",
                 lambda *x: x[0].acyclicP()),
                ("DFA-trim", ("Trim automata", "Trim automata"), 1, "DFA", None, lambda *x: x[0].trim()),
                ("DFA-trimP", ("Test if automata is trim", "Test if automata is trim"), 1, "DFA", "Bool",
                 lambda *x: x[0].trimP()),
                ("DFA-to-reversal-NFA", ("Reversal NFA", "Reversal NFA"), 1, "DFA", "NFA", lambda *x: x[0].reversal()),
                ("DFA-minimal-Brzozowski", ("Minimal (Brzozowski)", "Minimal (Brzozowski)"), 1, "DFA", "DFA",
                 lambda *x: x[0].minimalBrzozowski()),
                ("DFA-minimalP-Brzozowski", ("Test minimality (Brzozowski)", "Test minimality (Brzozowski)"), 1, "DFA",
                 "Bool",
                 lambda *x: x[0].minimalBrzozowskiP()),
                ("DFA-regexp-SE", ("Convert to RE", "Convert to RE by state elimination"), 1, "DFA", "RE",
                 lambda *x: x[0].regexpSE()),
                ("DFA-dump", ("dump", "dump"), 1, "DFA", "str", lambda *x: saveToString(x[0]))]

    def __repr__(self):
        """ DFA informal string representation"
        :returns: str
        :rtype: str"""
        return 'DFA({0:>s})'.format(self.__str__())

    def succintTransitions(self):
        """ Collects the transition information in a compact way suitable for graphical representation.
        :rtype: list of tupples

        .. versionadded:: 0.9.8"""
        foo = dict()
        for s in self.delta:
            for c in self.delta[s]:
                k = (s, self.delta[s][c])
                if k not in foo:
                    foo[k] = []
                foo[k].append(c)
        l = []
        for k in foo:
            cs = foo[k]
            s = "%s" % str(cs[0])
            for c in cs[1:]:
                s += ", %s" % str(c)
            l.append((str(self.States[k[0]]), s, str(self.States[k[1]])))
        return l

    def initialP(self, state):
        """ Tests if a state is initial

        :param state: state index
        :type state: int
        :rtype: bool"""
        return self.Initial == state

    @staticmethod
    def _getTags():
        """returns Tags for dump

        :rtype: list of str"""
        return ["DFA"]

    def initialSet(self):
        """The set of initial states

        :returns: the set of the initial states
        :rtype: set of States"""
        return {self.Initial}

    def Delta(self, state, symbol):
        """Evaluates the action of a symbol over a state

        :arg state: state index
        :type state: int
        :arg symbol: symbol
        :returns: the action of symbol over state
        :rtype: int"""
        try:
            r = self.delta[state][symbol]
        except KeyError:
            r = None
        return r

    def _deleteRefInDelta(self, src, sym, dest):
        """

        :param src:
        :param sym:
        :param dest:"""
        old = self.delta.get(src, {}).get(sym, -1)
        if dest == old:
            del self.delta[src][sym]
        elif old > dest:
            self.delta[src][sym] = old - 1
        if not len(self.delta[src]):
            del self.delta[src]

    def _deleteRefInitial(self, sti):
        """Deletes a state as Initial. If sti not Initial, Initial is renumbered if needed.

        :param sti: state index
        :type sti: int"""
        if sti < self.Initial:
            self.Initial -= 1
        if sti == self.Initial:
            self.Initial = None

    def deleteStates(self, del_states):
        """Delete given iterable collection of states from the automaton.

        :param del_states: collection of int representing states

        .. note::
           delta function will always be rebuilt, regardless of whether the states list to remove is a suffix,
           or a sublist, of the automaton's states list."""
        if not del_states:
            return
        rename_map = {}
        old_delta = self.delta
        self.delta = {}
        new_final = set()
        new_states = []
        for state in del_states:
            if self.initialP(state):
                self.Initial = None
        for state in range(len(self.States)):
            if state not in del_states:
                rename_map[state] = len(new_states)
                new_states.append(self.States[state])
        for state in rename_map:
            state_renamed = rename_map[state]
            if state in self.Final:
                new_final.add(state_renamed)
            if state not in old_delta:
                continue
            for symbol, target in old_delta[state].items():
                if target in rename_map:
                    self.addTransition(state_renamed, symbol, rename_map[target])
        self.States = new_states
        self.Final = new_final
        if self.Initial is not None:
            # noinspection PyNoneFunctionAssignment
            self.Initial = rename_map.get(self.Initial, None)

    def addTransition(self, sti1, sym, sti2):
        """Adds a new transition from ``sti1`` to ``sti2`` consuming symbol ``sym``.

        :param sti1: state index of departure
        :type sti1: int
        :param sti2: state index of arrival
        :type sti2: int
        :param sym: symbol consumed
        :type sym: str
        :raises DFAnotNFA: if one tries to add a non deterministic transition"""
        if sym == Epsilon:
            raise DFAnotNFA("Invalid epsilon transition from {0:>s} to {1:>s}.".format(str(sti1), str(sti2)))
        self.Sigma.add(sym)
        if sti1 not in self.delta:
            self.delta[sti1] = {sym: sti2}
        else:
            if sym in self.delta[sti1] and self.delta[sti1][sym] is not sti2:
                raise DFAnotNFA("extra transition from ({0:>s}, {1:>s})".format(str(sti1), sym))
            self.delta[sti1][sym] = sti2

    def delTransition(self, sti1, sym, sti2, _no_check=False):
        """Remove a transition if existing and perform cleanup on the transition function's internal data structure.

        :param _no_check: use unsecure code?
        :type _no_check: Boolean
        :param sti1: state index of departure
        :param sti2: state index of arrival
        :param sym: symbol consumed
        :type sti2: int
        :type sti1: int
        :type sym: str

        .. note::
           Unused alphabet symbols will be discarded from Sigma."""
        if not _no_check and (sti1 not in self.delta or sym not in self.delta[sti1]):
            return
        if self.delta[sti1][sym] is not sti2:
            return
        del self.delta[sti1][sym]
        if all([sym not in x for x in iter(self.delta.values())]):
            self.Sigma.discard(sym)
        if not self.delta[sti1]:
            del self.delta[sti1]

    def inDegree(self, st):
        """Returns the in-degree of a given state in an FA

        :param st: index of the state
        :type st: int

        :rtype: int"""
        in_deg = 0
        for s in range(len(self.States)):
            for a in self.Sigma:
                try:
                    if self.delta[s][a] == st:
                        in_deg += 1
                except KeyError:
                    pass
        return in_deg

    def syncPower(self):
        """Evaluates the power automata for the action of each symbol

        :return: The power automata being the set of all states the initial state and all singleton states final.
        :rtype: DFA"""
        new = DFA()
        new.setSigma(self.Sigma)
        a = set(range((len(self.States))))
        tbd = [a]
        done = []
        ia = new.addState(a)
        new.setInitial(ia)
        while tbd:
            a = tbd.pop()
            ia = new.stateIndex(a)
            done.append(a)
            for sy in new.Sigma:
                b = set([self.Delta(s, sy) for s in a])
                b.discard(None)
                if b not in done:
                    if b not in tbd:
                        tbd.append(b)
                        ib = new.addState(b)
                        if len(b) == 1:
                            new.addFinal(ib)
                    else:
                        ib = new.stateIndex(b)
                    new.addTransition(ia, sy, ib)
                else:
                    new.addTransition(ia, sy, new.stateIndex(b))
        return new

    def pairGraph(self):
        """Returns pair graph

        :rtype: DiGraphVM

        .. seealso::
           A graph theoretic approach to automata minimality. Antonio Restivo and Roberto Vaglica. Theoretical
           Computer Science, 429 (2012) 282-291. doi:10.1016/j.tcs.2011.12.049 Theoretical Computer Science,
           2012 vol. 429 (C) pp. 282-291. http://dx.doi.org/10.1016/j.tcs.2011.12.049"""
        g = graphs.DiGraphVm()
        for s1 in range(len(self.States)):
            for s2 in range(s1, len(self.States)):
                i1 = g.vertexIndex((self.States[s1], self.States[s2]), True)
                for sy in self.delta[s1]:
                    if sy in self.delta[s2]:
                        foo = [self.delta[s1][sy], self.delta[s2][sy]]
                        foo.sort()
                        i2 = g.vertexIndex((self.States[foo[0]], self.States[1]), True)
                        g.addEdge(i1, i2)
        return g

    def subword(self):
        """
         Returns a dfa that recognizes subword(L(self))

        :rtype: dfa

        .. versionadded:: 1.1
        """

        if not self.hasTrapStateP():
            return sigmaStarDFA(self.Sigma)
        return self.toNFA().subword().toDFA()

    def pref(self):
        """
        Returns a dfa that recognizes pref(L(self))

        :rtype: DFA

        .. versionadded:: 1.1
        """
        foo = self.dup()
        foo.trim()
        if foo.emptyP():
            return foo
        foo.setFinal(list(range(len(foo.States))))
        return foo

    def suff(self):
        """ Returns a dfa that recognizes suff(L(self))

        :rtype: DFA

        .. versionadded:: 0.9.8"""
        d = DFA()
        d.setSigma(self.Sigma)
        ini = self.usefulStates()
        lStates = []
        d.setInitial(d.addState(ini))
        lStates.append(ini)
        if not self.Final.isdisjoint(ini):
            d.addFinal(0)
        index = 0
        while True:
            slist = lStates[index]
            si = d.stateIndex(slist)
            for s in self.Sigma:
                stl = set([self.evalSymbol(s1, s) for s1 in slist if s in self.delta[s1]])
                if not stl:
                    continue
                if stl not in lStates:
                    lStates.append(stl)
                    foo = d.addState(stl)
                    if not self.Final.isdisjoint(stl):
                        d.addFinal(foo)
                else:
                    foo = d.stateIndex(stl)
                d.addTransition(si, s, foo)
            if index == len(lStates) - 1:
                break
            else:
                index += 1
        return d

    def infix(self):
        """ Returns a dfa that recognizes infix(L(a))

        :rtype: DFA
        """
        m = self.minimal()
        m.complete()
        Trap = None
        for i in range(len(m.States)):
            if m.finalP(i):
                continue
            f = 0
            for c in m.delta[i]:
                if m.delta[i][c] != i:
                    f = 1
                    break
            if f == 0:
                Trap = i
                break
        if Trap is None:
            return sigmaStarDFA(self.Sigma)
        else:
            d = DFA()
            d.setSigma(m.Sigma)
            ini = set(range(len(m.States))).difference({Trap})
            d.setInitial(d.addState(ini))
            lStates = [ini]
            d.addFinal(0)
            index = 0
            while True:
                slist = lStates[index]
                si = d.stateName(slist)
                for s in m.Sigma:
                    stl = set([m.evalSymbol(s1, s) for s1 in slist if s in m.delta[s1]])
                    if not stl:
                        continue
                    if stl not in lStates:
                        lStates.append(stl)
                        foo = d.addState(stl)
                        if stl != {Trap}:
                            d.addFinal(foo)
                    else:
                        foo = d.stateName(stl)
                    d.addTransition(si, s, foo)
                if index == len(lStates) - 1:
                    break
                else:
                    index += 1
        return d

    def hasTrapStateP(self):
        """ Tests if the automaton has a dead trap state

        :rtype: bool

        .. versionadded:: 1.1"""
        foo = self.minimal()
        if not foo.completeP():
            return True
        for i in range(len(foo.States)):
            if foo.finalP(i):
                continue
            f = 0
            for c in foo.delta[i]:
                if foo.delta[i][c] != i:
                    f = 1
                    break
            if f == 0:
                return True
        return False

    def _xA(self):
        """ Computes the minimal words that reach each state of DFA

        :rtype: dictionary with words"""
        xList = dict()
        todo = [i for i in range(len(self.States))]
        if isinstance(self.Initial, set):
            rank = self.Initial
        else:
            rank = {self.Initial}

        for i in rank:
            xList[i] = Epsilon
            todo.remove(i)
        while todo:
            nrank = set()
            for sym in self.Sigma:
                for i in rank:
                    if i in self.delta and sym in self.delta[i]:
                        ss = self.delta[i][sym]
                        if isinstance(ss, set):
                            for q in self.delta[i][sym]:
                                if q in todo:
                                    xList[q] = sConcat(xList[i], sym)
                                    todo.remove(q)
                                    nrank.add(q)
                        else:
                            q = ss
                            if q in todo:
                                xList[q] = sConcat(xList[i], sym)
                                todo.remove(q)
                                nrank.add(q)
            rank = nrank
        return xList

    def sop(self, other):
        """ Strange operation

        :param other: the other automaton
        :type other: DFA
        :rtype: DFA

        .. versionadded:: 1.2b2"""

        a = self.dup()
        b = other.dup()
        if not a.completeP() or not a.completeP() or a.Sigma != b.Sigma:
            raise DFAnotComplete()
        aux = NFA()
        idx = aux.addState((a.Initial, b.Initial, 0))
        aux.addInitial(idx)
        aux.setSigma(a.Sigma)
        pool, done = _initPool()
        _addPool(pool, done, idx)
        while pool:
            idx = pool.pop()
            done.add(idx)
            t = aux.States[idx]
            for c in a.Sigma:
                if t[2] == 0:
                    nt = (a.delta[t[0]][c], t[1], 0)
                    i = aux.stateIndex(nt, True)
                    _addPool(pool, done, i)
                    aux.addTransition(idx, c, i)
                    nt = (t[0], b.delta[t[1]][c], 1)
                    i = aux.stateIndex(nt, True)
                    _addPool(pool, done, i)
                    aux.addTransition(idx, c, i)
                else:
                    nt = (t[0], b.delta[t[1]][c], 1)
                    i = aux.stateIndex(nt, True)
                    _addPool(pool, done, i)
                    aux.addTransition(idx, c, i)
        new = DFA()
        t = set()
        for idx in aux.Initial:
            t.add(aux.States[idx])
        idx = new.addState(t)
        new.setInitial(idx)
        pool, done = _initPool()
        _addPool(pool, done, idx)
        while pool:
            idx = pool.pop()
            done.add(idx)
            t = new.States[idx]
            for c in aux.Sigma:
                dest = set()
                for s in t:
                    foo = aux.stateIndex(s)
                    for j in aux.delta[aux.stateIndex(s)].get(c, set()):
                        dest.add(aux.States[j])
                i = new.stateIndex(dest, True)
                _addPool(pool, done, i)
                new.addTransition(idx, c, i)
        for t in new.States:
            final = True
            for s in t:
                final = final and (s[0] in a.Final or s[1] in b.Final)
            if final:
                new.addFinal(new.stateIndex(t))
        return new

    def dist(self):
        """Evaluate the distinguishability language for a DFA

        :rtype: DFA

        .. seealso::
           Cezar Câmpeanu, Nelma Moreira, Rogério Reis:
           The distinguishability operation on regular languages. NCMA 2014: 85-100

        .. versionadded:: 0.9.8"""
        d = DFA()
        if not self.completeP():
            foo = self.dup()
            foo.complete()
        else:
            foo = self
        d.setSigma(foo.Sigma)
        ini = set(range(len(foo.States)))
        lStates = []
        d.setInitial(d.addState(ini))
        lStates.append(ini)
        if not foo.Final.isdisjoint(ini) and not ini.issubset(foo.Final):
            d.addFinal(0)
        index = 0
        while True:
            slist = lStates[index]
            si = d.stateIndex(slist)
            for s in foo.Sigma:
                stl = set([foo.evalSymbol(s1, s) for s1 in slist if s in foo.delta[s1]])
                if not stl:
                    continue
                if stl not in lStates:
                    lStates.append(stl)
                    new = d.addState(stl)
                    if not foo.Final.isdisjoint(stl) and not stl.issubset(foo.Final):
                        d.addFinal(new)
                else:
                    new = d.stateIndex(stl)
                d.addTransition(si, s, new)
            if index == len(lStates) - 1:
                break
            else:
                index += 1
        return d

    def distMin(self):
        """ Evaluates the list of minimal words that distinguish each pair of states

        :returns: set of minimal distinguishing words
        :rtype: FL

        .. versionadded:: 0.9.8

        .. attention::
            If the DFA is not minimal, the method loops forever"""
        from . import fl

        sz = len(self.States)
        if sz == 1:
            return fl.FL()
        distList = set()
        todo = [(s, s1) for s in range(sz) for s1 in range(s + 1, sz)]
        wrds = self.words()
        l = []
        for (i, j) in todo:
            if (i in self.Final) ^ (j in self.Final):
                l.append((i, j))
                distList.add(Epsilon)
        delFromList(todo, l)
        while True:
            for w in wrds:
                l = []
                for (i, j) in todo:
                    if self.evalWordP(w, i) ^ self.evalWordP(w, j):
                        l.append((i, j))
                        distList.add(w)
                delFromList(todo, l)
                if not todo:
                    return fl.FL(distList, self.Sigma)

    def distR(self):
        """Evaluate the right distinguishability language for a DFA

        :rtype: DFA

        ..seealso:: Cezar Câmpeanu, Nelma Moreira, Rogério Reis:
           The distinguishability operation on regular languages. NCMA 2014: 85-100"""
        foo = self.minimal()
        foo.complete()
        foo.delFinals()
        for i in range(len(foo.States)):
            f = 0
            for c in foo.delta[i]:
                if foo.delta[i][c] != i:
                    f = 1
                    break
            if f == 1:
                foo.addFinal(i)
        return foo

    def distTS(self):
        """Evaluate the two-sided distinguishability language for a DFA

        :rtype: DFA

        ..seealso:: Cezar Câmpeanu, Nelma Moreira, Rogério Reis:
           The distinguishability operation on regular languages. NCMA 2014: 85-100"""
        m = self.minimal()
        m.complete()
        Trap = set([])
        for i in range(len(m.States)):
            f = 0
            for c in m.delta[i]:
                if m.delta[i][c] != i:
                    f = 1
                    break
            if f == 0:
                Trap.add(i)
        if Trap == set([]) or len(Trap) == 2:
            return sigmaStarDFA(self.Sigma)
        else:
            d = DFA()
            d.setSigma(m.Sigma)
            ini = set(range(len(m.States))).difference(Trap)
            d.setInitial(d.addState(ini))
            lStates = [ini]
            d.addFinal(0)
            index = 0
            while True:
                slist = lStates[index]
                si = d.stateName(slist)
                for s in m.Sigma:
                    stl = set([m.evalSymbol(s1, s) for s1 in slist if s in m.delta[s1]])
                    if not stl:
                        continue
                    if stl not in lStates:
                        lStates.append(stl)
                        foo = d.addState(stl)
                        if stl != Trap:
                            d.addFinal(foo)
                    else:
                        foo = d.stateName(stl)
                    d.addTransition(si, s, foo)
                if index == len(lStates) - 1:
                    break
                else:
                    index += 1
        return d

    def distRMin(self):
        """Compute distRMin for DFA

        :rtype FL

        ..seealso:: Cezar Câmpeanu, Nelma Moreira, Rogério Reis:
           The distinguishability operation on regular languages. NCMA 2014: 85-100"""

        def _epstr(d):
            if d == Epsilon:
                return ''
            return d

        def _strep(d):
            if d == '':
                return Epsilon
            return d

        from . import fl

        m = self.minimal()
        rev = m.reversal().toDFA()
        rev.complete()
        sz = len(rev.States)
        if sz == 1:
            return fl.FL()
        dpreList = set()
        xlist = m._xA()
        for i in xlist:
            xlist[i] = _epstr(xlist[i])
        todo = [(s, s1) for s in range(sz) for s1 in range(s + 1, sz)]
        for (i, j) in todo:
            s1 = rev.States[i]
            s2 = rev.States[j]
            if s1 == DeadName:
                if s2 != DeadName:
                    md = min({xlist[k] for k in s2})
                    dpreList.add(md)
            elif s2 == DeadName:
                md = min({xlist[k] for k in s1})
                dpreList.add(md)
            else:
                d12 = s1 ^ s2
                md = min({xlist[k] for k in d12})
                dpreList.add(md)
            todo.remove((i, j))

        return fl.FL({_strep(i) for i in dpreList}, self.Sigma)

    def completeProduct(self, other):
        """Product structure

        :param other: the other DFA"""
        n = SemiDFA()
        n.States = set([(x, y) for x in self.States for y in other.States])
        n.Sigma = copy(self.Sigma)
        for (x, y) in n.States:
            for s in n.Sigma:
                if (x, y) not in n.delta:
                    n.delta[(x, y)] = {}
                n.delta[(x, y)][s] = (self.delta[x][s], other.delta[y][s])
        return n

    def syncWords(self):
        """Evaluates the regular expression corresponding to the synchronizing pwords of the automata.

        :return: a regular expression of the sync words of the automata
        :rtype: regexp"""
        return self.syncPower().reCG()

    def evalWordP(self, word, initial=None):
        """Verifies if the DFA recognises a given word

        :param word: word to be recognised
        :type word: list of symbols.
        :param initial: starting state index
        :type initial: int
        :rtype: bool"""
        if initial is None:
            state = self.Initial
        else:
            state = initial
        for c in word:
            try:
                state = self.evalSymbol(state, c)
            except DFAstopped:
                return False
        if state in self.Final:
            return True
        else:
            return False

    def evalSymbol(self, init, sym):
        """Returns the  state reached from given state through a given symbol.

        :param init: set of current states indexes
        :type init: set or list of int
        :param sym: symbol to be consumed
        :type sym: str
        :returns: reached state
        :rtype: int
        :raises DFAsymbolUnknown: if symbol not in alphabet
        :raises DFAstopped: if transition function is not defined for the given input"""
        if sym not in self.Sigma:
            raise DFAsymbolUnknown(sym)
        try:
            Next = self.delta[init][sym]
        except KeyError:
            raise DFAstopped()
        except NameError:
            raise DFAstopped()
        return Next

    def evalSymbolL(self, ls, sym):
        """Returns the set of states reached from a given set of states through a given symbol

        :param ls: set of states indexes
        :type ls: set of int
        :param sym: symbol to be read
        :type sym: str
        :returns: set of reached states
        :rtype: set of int"""
        return set([self.evalSymbol(s, sym) for s in ls])

    def reverseTransitions(self, rev):
        """Evaluate reverse transition function.

        :param rev: DFA in which the reverse function will be stored
        :type rev: DFA"""
        for s in self.delta:
            for a in self.delta[s]:
                rev.addTransition(self.delta[s][a], a, s)

    def initialComp(self):
        """Evaluates the connected component starting at the initial state.

        :returns: list of state indexes in the component
        :rtype: list of int"""
        lst = [self.Initial]
        i = 0
        while True:
            try:
                foo = list(self.delta[lst[i]].keys())
            except KeyError:
                foo = []
            for c in foo:
                s = self.delta[lst[i]][c]
                if s not in lst:
                    lst.append(s)
            i += 1
            if i >= len(lst):
                return lst

    def minimal(self, method="minimalHopcroft", complete=True):
        """Evaluates the equivalent minimal complete DFA

        :param method: method to use in the minimization
        :param complete: should the result be completed?
        :type complete: bool
        :returns: equivalent minimal DFA
        :rtype: DFA"""
        if complete:
            foo = self.__getattribute__(method)()
            foo.completeMinimal()
            return foo
        else:
            return self.__getattribute__(method)()

    def minimalP(self, method="minimalHopcroft"):
        """Tests if the DFA is minimal

        :param method: the minimization algorithm to be used
        :rtype: bool

        ..note: if DFA non complete test if  complete minimal has   one more state

        """
        foo = self.minimal(method)

        if self.completeP():
            foo.completeMinimal()
        else:
            if foo.completeP():
                return len(foo) - 1 == len(self)
        return len(foo) == len(self)

    def minimalMoore(self):
        """Evaluates the equivalent minimal automata with Moore's algorithm

        .. seealso::
           John E. Hopcroft and Jeffrey D. Ullman, Introduction to Automata Theory, Languages, and Computation, AW,
           1979

        :returns: minimal complete DFA
        :rtype: DFA"""
        trashIdx = None  # just to satisfy the checker
        scc = set(self.initialComp())
        new = DFA()
        new.setSigma(self.Sigma)
        if (len(self.Final & scc) == 0) or (len(self.Final) == 0):
            s = new.addState()
            new.setInitial(s)
            return new
        equiv = set()
        for i in [x for x in range(len(self.States)) if x in scc]:
            for j in [x for x in range(i) if x in scc]:
                if ((i in self.Final and j in self.Final) or
                        (i not in self.Final and j not in self.Final)):
                    equiv.add((i, j))
        if not self.completeP():
            Complete = False
            for i in [x for x in range(len(self.States))
                      if (x in scc and x not in self.Final)]:
                equiv.add((None, i))
        else:
            Complete = True
        stable = False
        while not stable:
            stable = True
            for (i, j) in equiv:
                for c in self.Sigma:
                    if i is None:
                        xi = None
                    else:
                        xi = self.delta.get(i, {}).get(c, None)
                    xj = self.delta.get(j, {}).get(c, None)
                    p = _sortWithNone(xi, xj)
                    if xi != xj and p not in equiv:
                        stable = False
                        equiv = equiv - {(i, j)}
                        break
        nStatEquiv = {}
        nNames = {}
        foo = list(equiv)
        foo.sort(_cmpPair2)
        for (i, j) in foo:
            r = _deref(nStatEquiv, j)
            nStatEquiv[i] = r
            nNames[r] = nNames.get(r, [r]) + [i]
        removed = list(nStatEquiv.keys())
        for i in [x for x in range(len(self.States)) if x not in removed]:
            new.addState(i)
        if Complete:
            for i in [x for x in range(len(self.States)) if x not in removed]:
                for c in self.Sigma:
                    xi = new.stateIndex(i)
                    j = self.delta[i][c]
                    xj = new.stateIndex(nStatEquiv.get(j, j))
                    new.addTransition(xi, c, xj)
        else:
            if None not in removed:
                trashIdx = new.addState()
                for c in self.Sigma:
                    new.addTransition(trashIdx, c, trashIdx)
            for i in [x for x in range(len(self.States)) if x not in removed]:
                xi = new.stateIndex(i)
                for c in self.Sigma:
                    # noinspection PyNoneFunctionAssignment
                    j = self.delta.get(i, {}).get(c, None)
                    if j is not None:
                        xj = new.stateIndex(nStatEquiv.get(j, j))
                        new.addTransition(xi, c, xj)
                    else:
                        new.addTransition(xi, c, trashIdx)
        for i in self.Final:
            if i not in removed:
                xi = new.stateIndex(nStatEquiv.get(i, i))
                new.addFinal(xi)
        new.setInitial(nStatEquiv.get(self.Initial, self.Initial))
        new.renameStates([nNames.get(x, x) for x in range(len(new.States) - 1)] + ["Dead"])
        return new

    def minimalNCompleteP(self):
        """Tests if a non necessarely complete DFA is minimal, i.e., if the DFA is non complete,
        if the minimal complete has only one more state.

        :returns: True if not minimal
        :rtype: bool

        .. attention::
            obsolete: use minimalP"""
        foo = self.minimal()
        foo.complete()
        if self.completeP():
            return len(foo) == len(self)
        else:
            return len(foo) == (len(self) + 1)

    def completeMinimal(self):
        """Completes a DFA assuming it is a minimal and avoiding de destruction of its minimality If the automaton is
        not complete, all the non final states are checked to see if tey are not already a dead state. Only in the
        negative case a new (dead) state is added to the automaton.

        :rtype: DFA

        .. attention::
           The object is modified in place. If the alphabet is empty nothing is done"""
        if not self.Sigma:
            return
        self.trim()
        deadS = None
        complete = True
        for s in range(len(self.States)):
            if s not in self.delta:
                complete = False
                if s not in self.Final:
                    deadS = s
                    break
            else:
                foo = True
                for d in self.Sigma:
                    if d not in self.delta[s]:
                        complete = False
                        if s in self.Final:
                            foo = False
                    else:
                        if self.delta[s][d] != s or s in self.Final:
                            foo = False
                if foo:
                    deadS = s
        if not complete:
            if deadS is None:
                deadS = self.addState("dead")
            for s in range(len(self.States)):
                for d in self.Sigma:
                    if s not in self.delta or d not in self.delta[s]:
                        self.addTransition(s, d, deadS)
        return self

    def minimalMooreSq(self):
        """Evaluates the equivalent minimal complete DFA using Moore's (quadratic) algorithm

        .. seealso::
           John E. Hopcroft and Jeffrey D. Ullman, Introduction to Automata Theory, Languages, and Computation, AW,
           1979

        :returns: equivalent minimal DFA
        :rtype: DFA"""
        duped = self.dup()
        duped.complete()
        n_states = len(duped.States)
        duped._mooreMarked = {}
        duped._moorePairList = {}
        for p in range(n_states):
            for q in range(n_states):
                duped._moorePairList[(p, q)] = []
                duped._mooreMarked[(p, q)] = False
                if (p in duped.Final) ^ (q in duped.Final):
                    duped._mooreMarked[(p, q)] = True
        for p in range(n_states):
            for q in range(n_states):
                if not ((p in duped.Final) ^ (q in duped.Final)):
                    exists_marked = False
                    for a in duped.Sigma:
                        foo = (duped.delta[p][a], duped.delta[q][a])
                        if duped._mooreMarked[foo]:
                            exists_marked = True
                            break
                    if exists_marked:
                        duped._mooreMarked[(p, q)] = True
                        duped._mooreMarkList(p, q)
                    else:
                        for a in duped.Sigma:
                            if duped.delta[p][a] != duped.delta[q][a]:
                                pair = (duped.delta[p][a], duped.delta[q][a])
                                duped._moorePairList[pair].append((p, q))
        eqstates = duped._mooreEquivClasses()
        duped.joinStates(eqstates)
        return duped

    def minimalMooreSqP(self):
        """Tests if a DFA is minimal using the quadratic version of Moore's algorithm

        :rtype: bool"""
        foo = self.minimalMooreSq()
        foo.complete()
        return self.uniqueRepr() == foo.uniqueRepr()

    # noinspection PyUnresolvedReferences
    def _mooreMarkList(self, p, q):
        """ Marks pairs of states already known to be not non-equivalent

        :param p:
        :param q:"""
        for (p_, q_) in self._moorePairList[(p, q)]:
            if not self._mooreMarked[(p_, q_)]:
                self._mooreMarked[(p_, q_)] = True
                self._mooreMarkList(p_, q_)

    # noinspection PyUnresolvedReferences
    def _mooreEquivClasses(self):
        """Returns equivalence classes

        :returns: list of equivalence classes
        :rtype:list"""
        uf = UnionFind(auto_create=True)
        # eqstates = []
        for p in range(len(self.States)):
            for q in range(p + 1, len(self.States)):
                if not self._mooreMarked[(p, q)]:
                    A = uf.find(p)
                    B = uf.find(q)
                    uf.union(A, B)
        classes = {}
        for p in range(len(self.States)):
            lider = uf.find(p)
            if lider in classes:
                classes[lider].append(p)
            else:
                classes[lider] = [p]
        return list(classes.values())

    def _compute_delta_inv(self):
        """Adds a delta_inv feature. Used by minimalHopcroft."""
        self.delta_inv = {}
        for s in range(len(self.States)):
            self.delta_inv[s] = dict([(a, []) for a in self.Sigma])
        for s1, to in list(self.delta.items()):
            for a, s2 in list(to.items()):
                self.delta_inv[s2][a].append(s1)

    def _undelta(self, states, x):
        """Traverses Automata backwards

        :param states: destination
        :param x: symbol
        :return: list of states"""
        lst = set([])
        for s in states:
            lst.update(self.delta_inv[s][x])
        return lst

    # noinspection PyUnresolvedReferences
    def _split(self, B, C, a):
        """Split classes in Hopcroft algorithm

        :param B:
        :param C:
        :param a:
        :return:"""
        foo = frozenset(self._undelta(C, a))
        bar = frozenset(self.states - foo)
        return B & foo, B & bar

    def minimalHopcroft(self):
        """Evaluates the equivalent minimal complete DFA using Hopcroft algorithm

        :returns: equivalent minimal DFA
        :rtype: DFA

        .. seealso::
           John Hopcroft,An n\log{n} algorithm for minimizing states in a  finite automaton.The Theory of Machines
           and Computations.AP. 1971"""
        duped = self.dup()
        duped.complete()
        duped._compute_delta_inv()
        duped.states = frozenset(range(len(duped.States)))
        final = frozenset(duped.Final)
        not_final = duped.states - final
        L = set([])
        if len(final) < len(not_final):
            P = {not_final, final}
            L.add(final)
        else:
            P = {final, not_final}
            L.add(not_final)
        while len(L):
            C = L.pop()
            for a in duped.Sigma:
                foo = copy(P)
                for B in foo:
                    (B1, B2) = duped._split(B, C, a)
                    P.remove(B)
                    if B1:
                        P.add(B1)
                    if B2:
                        P.add(B2)
                    if len(B1) < len(B2):
                        if B1:
                            L.add(B1)
                    else:
                        if B2:
                            L.add(B2)
        eqstates = []
        for i in P:
            if len(i) != 1:
                eqstates.append(list(i))
        duped.joinStates(eqstates)
        return duped

    def minimalHopcroftP(self):
        """Tests if a DFA is minimal

        :rtype: bool"""
        foo = self.minimalHopcroft()
        foo.complete()
        return self.uniqueRepr() == foo.uniqueRepr()

    def minimalNotEquivP(self):
        """Tests if the DFA is minimal by computing the set of distinguishable (not equivalent) pairs of states

        :rtype: bool"""
        all_pairs = set()
        for i in self.States:
            for j in range(i + 1, len(self.States)):
                all_pairs.add((i, j))
        not_final = set(self.States) - self.Final
        neq = set()
        for i in not_final:
            for j in self.Final:
                pair = _normalizePair(i, j)
                neq.add(pair)
        source = neq.copy()
        self._compute_delta_inv()
        while source:
            (p, q) = source.pop()
            for a in self.Sigma:
                p_ = self.delta_inv[p][a]
                q_ = self.delta_inv[q][a]
                for x in p_:
                    for y in q_:
                        pair = _normalizePair(x, y)
                        if pair not in neq:
                            neq.add(pair)
                            source.add(pair)
        equiv = all_pairs - neq
        return not equiv

    def minimalHKP(self):
        """Tests the DFA's minimality using Hopcroft and Karp's state equivalence algorithm

        :returns: bool

        .. seealso::
           J. E. Hopcroft and R. M. Karp.A Linear Algorithm for Testing Equivalence of Finite Automata.TR 71--114. U.
           California. 1971

        .. attention::
           The automaton must be complete."""
        pairs = set()
        for i in range(len(self.States)):
            for j in range(i + 1, len(self.States)):
                pairs.add((i, j))
        while pairs:
            equiv = True
            (p0, q0) = pairs.pop()
            sets = UnionFind(auto_create=True)
            sets.union(p0, q0)
            stack = [(p0, q0)]
            while stack:
                (p, q) = stack.pop()
                if (p in self.Final) ^ (q in self.Final):
                    equiv = False
                    break
                for a in self.Sigma:
                    r1 = sets.find(self.delta[p][a])
                    r2 = sets.find(self.delta[q][a])
                    if r1 != r2:
                        sets.union(r1, r2)
                        stack.append((r1, r2))
            if equiv:
                return False
        return True

    def minimalIncremental(self, minimal_test=False):
        """Minimizes the DFA with an incremental method using the Union-Find algorithm and memoized non-equivalence
        intermediate results

        :param minimal_test: starts by verifying that the automaton is not minimal?
        :type minimal_test: bool
        :returns: equivalent minimal DFA
        :rtype: DFA

        .. seealso::
           M. Almeida and N. Moreira and and R. Reis.Incremental DFA minimisation. CIAA 2010. LNCS 6482. pp 39-48. 2010"""
        duped = self.dup()
        duped.complete()
        duped.minimalIncr_neq = set()
        n_states = len(duped.States)
        for p in duped.Final:
            for q in range(n_states):
                if q not in duped.Final:
                    duped.minimalIncr_neq.add(_normalizePair(p, q))
        duped.minimalIncr_uf = UnionFind(auto_create=True)
        for p in range(n_states):
            for q in range(p + 1, n_states):
                if (p, q) in duped.minimalIncr_neq:
                    continue
                if duped.minimalIncr_uf.find(p) == duped.minimalIncr_uf.find(q):
                    continue
                duped.equiv = set()
                duped.path = set()
                if duped._minimalIncrCheckEquiv(p, q):
                    # when we are only interested in testing
                    # minimality, return None to signal a pair of
                    # equivalent states
                    if minimal_test:
                        return None
                    for (x, y) in duped.equiv:
                        duped.minimalIncr_uf.union(x, y)
                else:
                    duped.minimalIncr_neq |= duped.path
        classes = {}
        for p in range(n_states):
            lider = duped.minimalIncr_uf.find(p)
            if lider in classes:
                classes[lider].append(p)
            else:
                classes[lider] = [p]
        duped.joinStates(list(classes.values()))
        return duped

    # noinspection PyUnresolvedReferences
    def _minimalIncrCheckEquiv(self, p, q, rec_level=1):
        # p == q is a useless test; union-find offers this for free
        # because p == q => find(p) == find(q) and the recursive call
        # only happens when find(p) != find(q)

        # if p_ in self.Final ^ q_ in self.Final => (p_,
        # q_) are already on self.minimalIncr_neq
        # (initialization)
        if (p, q) in self.minimalIncr_neq:
            return False
            # cycle detected; the states must be equivalent
        if (p, q) in self.path:
            return True
        self.path.add((p, q))
        for a in self.Sigma:
            (p_, q_) = _normalizePair(self.minimalIncr_uf.find(self.delta[p][a]),
                                      self.minimalIncr_uf.find(self.delta[q][a]))
            if p_ != q_ and ((p_, q_) not in self.equiv):
                self.equiv.add((p_, q_))
                if not self._minimalIncrCheckEquiv(p_, q_, rec_level + 1):
                    return False
                else:
                    # if the states are equivalent, the 'path' doesn't
                    # really interest; by removing the states here, we
                    # can make 'path' a global variable and avoid any
                    # copy() operations. removing the last inserted
                    # item is necessary when the states are equivalent
                    # because the next recursive call (next symbol)
                    # needs an "empty path", ie, the states reached by
                    # the previous symbol cannot be considered
                    self.path.discard((p_, q_))
        self.equiv.add((p, q))
        return True

    def minimalIncrementalP(self):
        """Tests if a DFA is minimal

        :rtype: bool"""
        foo = self.minimalIncremental(minimal_test=True)
        if foo is None:
            return False
        return True

    def minimalWatson(self, test_only=False):
        """Evaluates the equivalent minimal complete DFA using Waton's incremental algorithm

        :param test_only: is it only to test minimality
        :type test_only: bool
        :returns: equivalent minimal DFA
        :rtype: DFA

        :raises  DFAnotComplete: if automaton is not complete

        ..attention::
          automaton must be complete"""
        duped = self.dup()
        duped.complete()
        duped.Equiv = UnionFind(auto_create=True)
        duped.Dist = set()
        nstates = len(self.States)
        max_depth = max(0, nstates - 2)
        for p in range(nstates):
            for q in range(p + 1, nstates):
                if duped.Equiv.find(p) == duped.Equiv.find(q):
                    continue
                if (p, q) in duped.Dist:
                    continue
                duped.minimalWatson_stack = set([])
                if duped._watson_equivP(p, q, max_depth):
                    # when we are only interested in testing
                    # minimality, return None to signal a pair of
                    # equivalent states
                    if test_only:
                        return None
                    duped.Equiv.union(p, q)
                else:
                    duped.Dist.add((p, q))
        classes = {}
        for p in duped.States:
            lider = duped.Equiv.find(p)
            if lider in classes:
                classes[lider].append(p)
            else:
                classes[lider] = [p]
        duped.joinStates(list(classes.values()))
        return duped

    # noinspection PyUnresolvedReferences
    def _watson_equivP(self, p, q, k):
        if not k:
            eq = not ((p in self.Final) ^ (q in self.Final))
        elif (p, q) in self.minimalWatson_stack:
            eq = True
        else:
            eq = not ((p in self.Final) ^ (q in self.Final))
            self.minimalWatson_stack.add((p, q))
            for a in self.Sigma:
                if not eq:
                    return eq
                try:
                    eq = eq and self._watson_equivP(self.delta[p][a], self.delta[q][a], k - 1)
                except KeyError:
                    raise DFAnotComplete
            self.minimalWatson_stack.remove((p, q))
        return eq

    def minimalWatsonP(self):
        """Tests if a DFA is minimal using Watson's incremental algorithm

        :rtype: bool"""
        foo = self.minimalWatson(test_only=True)
        if foo is None:
            return False
        return True

    def markNonEquivalent(self, s1, s2, data):
        """Mark states with indexes s1 and s2 in given map as non equivalent states. If any back-effects exist,
        apply them.

        :param s1: one state's index
        :type s1: int
        :param s2: the other state's index
        :type s2: int
        :param data: the matrix relating s1 and s2"""
        try:
            del (data[s1][0][data[s1][0].index(s2)])
        except ValueError:
            pass
        try:
            backEffects = data[s1][1][s2]
        except KeyError:
            backEffects = []
        for (sb1, sb2) in backEffects:
            del (data[s1][1][s2][data[s1][1][s2].index((sb1, sb2))])
            self.markNonEquivalent(sb1, sb2, data)

    def print_data(self, data):
        """Prints table of compatibility (in the context of the minimalization algorithm).

        :param data: data to print"""
        for s in range(len(self.States)):
            for s1 in range(0, s):
                if s1 in data[s]:
                    print("_ ", end=' ')
                else:
                    print("X ", end=' ')
            print(s)

    def joinStates(self, lst):
        """Merge a list of states.

        :param lst: set of equivalent states
        :type lst: iterable of state indexes."""
        lst.sort()
        subst = {}
        for sl in lst:
            sl.sort()
            if self.Initial in sl[1:]:
                self.setInitial(sl[0])
            for s in sl[1:]:
                subst[s] = sl[0]
        for s in self.delta:
            for c in self.delta[s]:
                if self.delta[s][c] in subst:
                    self.delta[s][c] = subst[self.delta[s][c]]
        for sl in lst:
            for s in sl[1:]:
                try:
                    foo = list(self.delta[s].keys())
                    for c in foo:
                        if c not in self.delta[subst[s]]:
                            if self.delta[s][c] in subst:
                                self.delta[subst[s]][c] = subst[self.delta[s][c]]
                            else:
                                self.delta[subst[s]][c] = self.delta[s][c]
                    del (self.delta[s])
                except KeyError:
                    pass
                if s in self.Final:
                    self.Final.remove(s)
        self.trim()

    def compat(self, s1, s2, data):
        """Tests compatibility between two states.

        :param data:
        :param s1: state index
        :type s1: int
        :param s2: state index
        :type s2: int
        :rtype: bool"""
        if s1 == s2:
            return False
        if s1 not in data[s2][0] or s2 not in data[s1][0]:
            return False
        if s1 in self.Final != s2 in self.Final:
            del (data[s1][data[s1].index(s2)])
            del (data[s2][data[s2].index(s1)])
            return True
        for s in self.Sigma:
            next1 = self.delta[s1][s]
            next2 = self.delta[s2][s]
            if (next1 not in data[next2]) or (next2 not in data[next1]):
                del (data[s1][data[s1].index(s2)])
                del (data[s2][data[s2].index(s1)])
                return True
        return False

    def dup(self):
        """Duplicate the basic structure into a new DFA. Basically a copy.deep.

        :rtype: DFA"""
        new = DFA()
        new.setSigma(self.Sigma)
        new.States = self.States[:]
        new.Initial = self.Initial
        new.Final = self.Final.copy()
        for s in list(self.delta.keys()):
            new.delta[s] = {}
            for c in self.delta[s]:
                new.delta[s][c] = self.delta[s][c]
        return new

    def equal(self, other):
        """Verify if the two automata are equivalent. Both are verified to be minimum and complete,
        and then one is matched against the other... Doesn't destroy either dfa...

        :param other: the other DFA
        :type other: DFA
        :rtype: bool"""
        return self.__eq__(other)

    def __eq__(self, other):
        """Tests equivalence of DFAs

        :param other: the other DFA
        :type other: DFA
        :return: bool"""
        dfa1, dfa2 = self.dup(), other.dup()
        dfa1 = dfa1.minimal()
        dfa2 = dfa2.minimal()
        dfa1.completeMinimal()
        dfa2.completeMinimal()
        if ((dfa1.Sigma != dfa2.Sigma and (len(dfa1.Sigma) != 0 or len(dfa2.Sigma) != 0)) or
                (len(dfa1.States) != len(dfa2.States)) or (len(dfa1.Final) != len(dfa2.Final)) or
                (dfa1._uniqueStr() != dfa2._uniqueStr())):
            return False
        else:
            return True

    def _lstTransitions(self):
        l = []
        for x in self.delta:
            for k in self.delta[x]:
                l.append((self.States[x], k, self.States[self.delta[x][k]]))
        return l

    def _lstInitial(self):
        """
        :return:
        :raise: DFAnoInitial if no initial state is defined """
        if self.Initial is None:
            raise DFAnoInitial()
        else:
            return self.States[self.Initial]

    def _s_lstInitial(self):
        return str(self._lstInitial())

    def notequal(self, other):
        """ Test non  equivalence of two DFAs

        :param other: the other DFA
        :type other: DFA
        :rtype: bool"""
        return self.__ne__(other)

    def __ne__(self, other):
        """ Tests non-equivalence of two DFAs

        :param other: the other DFA
        :type other: DFA
        :rtype: bool"""
        return not self == other

    def hyperMinimal(self, strict=False):
        """ Hyperminization of a minimal DFA

        :param strict: if strict=True it first minimizes the DFA
        :type  strict: bool
        :returns: an hyperminimal DFA
        :rtype: DFA

        .. seealso::
           M. Holzer and A. Maletti, An nlogn Algorithm for Hyper-Minimizing a (Minimized) Deterministic Automata,
           TCS 411(38-39): 3404-3413 (2010)

        .. note:: if strict=False minimality is assumed"""
        if strict:
            m = self.minimal()
        else:
            m = self.dup()
        comp, center, mark = m.computeKernel()
        ker = set([m.States[s] for s in mark])
        m._mergeStatesKernel(ker, m.aEquiv())
        return m

    def _mergeStatesKernel(self, ker, aequiv):
        """ Merge states of almost equivalent partition. Used by hyperMinimal.

        :param ker:
        :param aequiv: partition of almost equivalence"""
        for b in aequiv:
            try:
                q = (aequiv[b] & ker).pop()
            except KeyError:
                q = aequiv[b].pop()
            for p in aequiv[b] - ker:
                self.mergeStates(self.stateIndex(p), self.stateIndex(q))

    def computeKernel(self):
        """ The Kernel of a ICDFA is the set of states that accept  a non finite language.

        :returns: triple (comp, center , mark) where comp are the strongly connected components,
                  center the set of center states and mark the kernel states
        :rtype: tuple

        .. note:
           DFA must be initially connected

        .. seealso:
           Holzer and A. Maletti, An nlogn Algorithm for Hyper-Minimizing a (Minimized) Deterministic Automata,
           TCS 411(38-39): 3404-3413 (2010)"""

        def _SCC(t):
            ind[t] = self.i
            low[t] = self.i
            self.i += 1
            stack.append(t)
            for b in self.Sigma:
                # noinspection PyNoneFunctionAssignment
                t1 = self.delta.get(t, {}).get(b, None)
                if t1 is not None and t1 not in ind:
                    _SCC(t1)
                    low[t] = min([low[t], low[t1]])
                else:
                    if t1 in stack:
                        low[t] = min([low[t], ind[t1]])
            if low[t] == ind[t]:
                comp[t] = [t]
                p = stack.pop()
                while p != t:
                    comp[t].append(p)
                    p = stack.pop()

        def _DFS(t):
            mark[t] = 1
            for a1 in self.Sigma:
                # noinspection PyNoneFunctionAssignment
                t1 = self.delta.get(t, {}).get(a1, None)
                if t1 is not None and t1 not in mark:
                    _DFS(t1)

        ind = {}
        low = {}
        stack = []
        self.i = 0
        comp = {}
        center = set([s for s in self.delta for a in self.delta[s] if self.delta[s][a] == s])
        _SCC(self.Initial)
        for s in comp:
            if len(comp[s]) > 1:
                center.update(comp[s])
        mark = {}
        for s in center:
            mark[s] = 1
        for s in center:
            for a in self.Sigma:
                # noinspection PyNoneFunctionAssignment
                s1 = self.delta.get(s, {}).get(a, None)
                if s1 is not None and s1 not in mark:
                    _DFS(s1)
        del self.i
        return comp, center, mark

    def aEquiv(self):
        """ Computes almost equivalence, used by hyperMinimial

        :returns: partition of states
        :rtype: dictionary

        .. note::
           may be optimized to avoid dupped"""
        pi = {}
        dupped = self.dup()
        for q in dupped.States:
            pi[q] = {q}
        h = {}
        I = set(dupped.States)
        P = set(dupped.States)
        dupped._compute_delta_inv()
        while I != set([]):
            q = I.pop()
            succ = tuple([dupped.States[dupped.delta[dupped.stateIndex(q)][a]] for a in dupped.Sigma
                          if dupped.stateIndex(q) in dupped.delta and a in dupped.delta[dupped.stateIndex(q)]])
            if succ in h:
                p = h[succ]
                if len(pi[p]) >= len(pi[q]):
                    p, q = q, p
                P.remove(p)
                I.update([r for r in P for a in dupped.Sigma
                          if dupped.stateIndex(r) in dupped.delta_inv[dupped.stateIndex(p)][a]])
                dupped.mergeStates(dupped.stateIndex(p), dupped.stateIndex(q))
                dupped._compute_delta_inv()
                pi[q] = pi[q].union(pi[p])
                del (pi[p])
            h[succ] = q
        return pi

    def mergeStates(self, f, t):
        """Merge the first given state into the second. If the first state is an initial state the second becomes the
        initial state.

        :param f: index of state to be absorbed
        :type f: int
        :param t: index of remaining state
        :type t:  int

        .. attention::
           It is up to the caller to remove the disconnected state. This can be achieved with ```trim()``."""
        if f is not t:
            for state, to in list(self.delta.items()):
                for a, s in list(to.items()):
                    if f == s:
                        self.delta[state][a] = t
            if self.initialP(f):
                self.setInitial(t)
            self.deleteStates([f])

    def toADFA(self):
        """ Try to convert DFA to ADFA

        :return: the same automaton as a ADFA
        :rtype: ADFA
        :raises notAcyclic: if this is not an acyclic DFA

        .. versionadded:: 1.2"""
        from . import fl

        if not self.acyclicP():
            raise notAcyclic()
        else:
            new = fl.ADFA()
            new.Initial = self.Initial
            new.States = deepcopy(self.States)
            new.Sigma = deepcopy(self.Sigma)
            new.Final = deepcopy(self.Final)
            new.delta = deepcopy(self.delta)
            return new

    def toDFA(self):
        """Dummy function. It is already a DFA

        :returns: a self deep copy
        :rtype: DFA"""
        return self.dup()

    def _uniqueStr(self):
        """ Returns a canonical representation of the automaton.

        :returns: canonical representation of the skeleton and the list of final states, in a pair
        :rtype: pair of lists of int

        .. note:
           Automata is supposed to be a icdfa. It, now, should cope with non complete automata"""
        SSigma = list(self.Sigma)
        SSigma.sort()
        tf, tr = {}, {}
        string = []
        i, j = 0, 0
        tf[self.Initial], tr[0] = 0, self.Initial
        while i <= j:
            lst = []
            for c in SSigma:
                # noinspection PyNoneFunctionAssignment
                foo = self.delta.get(tr[i], {}).get(c, None)
                # foo = self.delta[tr[i]][c]
                if foo is None:
                    lst.append(-1)
                else:
                    if foo not in tf:
                        j += 1
                        tf[foo], tr[j] = j, foo
                    lst.append(tf[foo])
            string.append(lst)
            i += 1
        lst = []
        for s in self.Final:
            lst.append(tf[s])
        lst.sort()
        return string, lst

    def uniqueRepr(self):
        """Normalise unique string for the string icdfa's representation.

        .. seealso::
           TCS 387(2):93-102, 2007 http://www.ncc.up.pt/~nam/publica/tcsamr06.pdf

        :returns: normalised representation
        :rtype: list

        :raises DFAnotComplete: if DFA is not complete"""
        try:
            (a, b) = self._uniqueStr()
            n = len(a)
            finals = [0] * n
            for i in b:
                finals[i] = 1
            return [j for i in a for j in i], finals, n, len(self.Sigma)
        except KeyError:
            raise DFAnotComplete

    def __invert__(self):
        """ Returns a DFA that recognises the complementary language:  ~X. Basically change all non-final states to
        final and vice-versa. After ensuring that it is complete.

        :rtype: DFA"""
        fa = self.dup()
        fa.eliminateDeadName()
        fa.complete()
        fa.setFinal([])
        for s in range(len(fa.States)):
            if s not in self.Final:
                fa.addFinal(s)
        return fa

    def __or__(self, other, complete=True):
        if type(other) != type(self):
            raise FAdoGeneralError("Incompatible objects")
        fa = self.product(other, complete)
        for i in range(len(fa.States)):
            (i1, i2) = fa.States[i]
            if i1 in self.Final or i2 in other.Final:
                fa.addFinal(i)
        return fa._namesToString()

    def __sub__(self, other):
        return self & (~other)

    def simDiff(self, other):
        """Symetrical difference

        :param other:
        :return:"""
        # noinspection PyUnresolvedReferences
        return (self - other) | (other - self)

    def __and__(self, other, complete=True):
        if not isinstance(other, DFA):
            raise FAdoGeneralError("Incompatible objects")
        fa = self.product(other, complete)
        for i in range(len(fa.States)):
            (i1, i2) = fa.States[i]
            if i1 in self.Final and i2 in other.Final:
                fa.addFinal(i)
        return fa._namesToString()

    def product(self, other, complete=True):
        """ Returns a DFA resulting of the simultaneous execution of two DFA. No final states set.

        :param other: the other DFA
        :param complete: evaluate product as a complete DFA
        :type complete: bool
        :rtype: DFA"""
        NSigma = self.Sigma.union(other.Sigma)
        fa1, fa2 = self.dup(), other.dup()
        fa1.setSigma(NSigma)
        fa2.setSigma(NSigma)
        fa1.complete()
        fa2.complete()
        fa = DFA()
        fa.setSigma(NSigma)
        s = fa.addState((fa1.Initial, fa2.Initial))
        fa.setInitial(s)
        i = 0
        while True:
            i1, i2 = fa.States[i]
            for c in fa.Sigma:
                new = (fa1.delta[i1][c], fa2.delta[i2][c])
                foo = fa.stateIndex(new, True)
                fa.addTransition(i, c, foo)
            i += 1
            if i == len(fa.States):
                break
        if not complete:
            d1 = fa1.stateIndex(DeadName)
            d2 = fa2.stateIndex(DeadName)
            try:
                d = fa.stateIndex((d1, d2))
            except DFAstateUnknown:
                pass
            else:
                fa.deleteState(d)
        return fa

    def witness(self):
        """Witness of non emptyness

        :return: word
        :rtype: str"""
        done = set()
        notDone = set()
        pref = dict()
        si = self.Initial
        pref[si] = Epsilon
        notDone.add(si)
        while notDone:
            si = notDone.pop()
            done.add(si)
            if si in self.Final:
                return pref[si]
            for syi in self.delta.get(si, []):
                so = self.delta[si][syi]
                if so in done or so in notDone:
                    continue
                pref[so] = sConcat(pref[si], syi)
                notDone.add(so)
        return None

    def concat(self, fa2, strict=False):
        """Concatenation of two DFAs. If DFAs are not complete, they are completed.

        :param strict: should alphabets be checked?
        :type strict: Boolean
        :param fa2: the second DFA
        :type fa2: DFA
        :returns: the result of the concatenation
        :rtype: DFA
        :raises DFAdifferentSigma: if alphabet are not equal"""
        if strict and self.Sigma != fa2.Sigma:
            raise DFAdifferentSigma
        NSigma = self.Sigma.union(fa2.Sigma)
        d1, d2 = self.dup(), fa2.dup()
        d1.setSigma(NSigma)
        d2.setSigma(NSigma)
        d1.complete()
        d2.complete()
        if len(d1.States) == 0 or len(d1.Final) == 0:
            return d1
        if len(d2.States) <= 1:
            if not len(d2.Final):
                return d2
            else:
                new = DFA()
                new.setSigma(d1.Sigma)
                new.States = d1.States[:]
                new.Initial = d1.Initial
                new.Final = d1.Final.copy()
                for s in d1.delta:
                    new.delta[s] = {}
                    if new.finalP(s):
                        for c in d1.delta[s]:
                            new.delta[s][c] = s
                    else:
                        for c in d1.delta[s]:
                            new.delta[s][c] = d1.delta[s][c]
                return new
        c = DFA()
        c.setSigma(d1.Sigma)
        lStates = []
        i = (d1.Initial, set([]))
        lStates.append(i)
        j = c.addState(i)
        c.setInitial(j)
        if d1.finalP(d1.Initial):
            i[1].add(d2.Initial)
            if d2.finalP(d2.Initial):
                c.addFinal(j)
        while True:
            stu = lStates[j]
            s = c.stateIndex(stu)
            for sym in d1.Sigma:
                stn = (d1.evalSymbol(stu[0], sym), d2.evalSymbolL(stu[1], sym))
                if d1.finalP(stn[0]):
                    stn[1].add(d2.Initial)
                if stn not in lStates:
                    lStates.append(stn)
                    new = c.addState(stn)
                    if d2.Final & stn[1] != set([]):
                        c.addFinal(new)
                else:
                    new = c.stateIndex(stn)
                c.addTransition(s, sym, new)
            if j == len(lStates) - 1:
                break
            else:
                j += 1
        return c

    def star(self, flag=False):
        """Star of a DFA. If the DFA is not complete, it is completed.

        ..versionchanged: 0.9.6

        :param flag: plus instead of star
        :type flag: bool
        :returns: the result of the star
        :rtype: DFA"""
        j = None  # to keep the checker happy
        if len(self.States) == 1 and self.finalP(self.Initial):
            return self
        d = self.dup()
        d.complete()
        c = DFA()
        c.Sigma = d.Sigma
        if len(d.States) == 0 or len(d.Final) == 0:
            # Epsilon automaton
            s0, s1 = c.addState(0), c.addState(1)
            c.setInitial(s0)
            c.addFinal(s0)
            for sym in c.Sigma:
                c.addTransition(s0, sym, s1)
                c.addTransition(s1, sym, s1)
            return c
        F0 = d.Final - {d.Initial}
        if not flag:
            i = c.addState("initial")
            c.setInitial(i)
            c.addFinal(i)
            lStates = ["initial"]
            for sym in d.Sigma:
                stn = {d.evalSymbol(d.Initial, sym)}
                # correction
                if F0 & stn != set([]):
                    stn.add(d.Initial)
                if stn not in lStates:
                    lStates.append(stn)
                    new = c.addState(stn)
                    if d.Final & stn != set([]):
                        c.addFinal(new)
                else:
                    new = c.stateIndex(stn)
                c.addTransition(i, sym, new)
                j = 1
        else:
            i = c.addState({d.Initial})
            c.setInitial(i)
            if d.finalP(d.Initial):
                c.addFinal(i)
            lStates = [{d.Initial}]
            j = 0
        while True:
            stu = lStates[j]
            s = c.stateIndex(stu)
            for sym in d.Sigma:
                stn = d.evalSymbolL(stu, sym)
                if F0 & stn != set([]):
                    stn.add(d.Initial)
                if stn not in lStates:
                    # noinspection PyTypeChecker
                    lStates.append(stn)
                    new = c.addState(stn)
                    if d.Final & stn != set([]):
                        c.addFinal(new)
                else:
                    new = c.stateIndex(stn)
                c.addTransition(s, sym, new)
            if j == len(lStates) - 1:
                break
            else:
                j += 1
        return c

    def evalSymbolI(self, init, sym):
        """Returns the state reached from a given state.

        :arg init: current state
        :type init: int
        :arg sym: symbol to be consumed
        :type sym: str
        :returns: reached state or -1
        :rtype: set of int

        :raise DFAsymbolUnknown: if symbol not in alphabet

        .. versionadded:: 0.9.5

        .. note:: this is to be used with non complete DFAs"""
        if sym not in self.Sigma:
            raise DFAsymbolUnknown(sym)
        try:
            Next = self.delta[init][sym]
        except KeyError:
            return -1
        except NameError:
            return -1
        return Next

    def evalSymbolLI(self, ls, sym):
        """Returns the set of states reached from a given set of states through a given symbol

        :arg ls: set of current states
        :type ls: set of int
        :arg sym: symbol to be consumed
        :type sym: str
        :returns: set of reached states
        :rtype: set of int


        .. versionadded:: 0.9.5

        .. note:: this is to be used with non complete DFAs"""
        return set([self.evalSymbolI(s, sym) for s in ls if self.evalSymbolI(s, sym) != -1])

    def concatI(self, fa2, strict=False):
        """Concatenation of two DFAs.

        :param fa2: the second DFA
        :type fa2: DFA
        :arg strict: should alphabets be checked?
        :type strict: Boolean
        :returns: the result of the concatenation
        :rtype: DFA

        :raises DFAdifferentSigma: if alphabet are not equal

        .. versionadded:: 0.9.5

        .. note:: this is to be used with non complete DFAs"""
        if strict and self.Sigma != fa2.Sigma:
            raise DFAdifferentSigma
        NSigma = self.Sigma.union(fa2.Sigma)
        d1, d2 = self.dup(), fa2.dup()
        d1.setSigma(NSigma)
        d2.setSigma(NSigma)
        if len(d1.States) == 0 or len(d1.Final) == 0:
            return d1
        if len(d2.States) <= 1:
            if not len(d2.Final):
                return d2
        c = DFA()
        c.setSigma(d1.Sigma)
        lStates = []
        i = (d1.Initial, set([]))
        lStates.append(i)
        j = c.addState(i)
        c.setInitial(j)
        if d1.finalP(d1.Initial):
            i[1].add(d2.Initial)
            if d2.finalP(d2.Initial):
                c.addFinal(j)
        while True:
            stu = lStates[j]
            s = c.stateIndex(stu)
            for sym in d1.Sigma:
                stn = (d1.evalSymbolI(stu[0], sym), d2.evalSymbolLI(stu[1], sym))
                if not ((stn[0] == -1) & (stn[1] == {-1})) | ((stn[0] == -1) & (stn[1] == set([]))):
                    if d1.finalP(stn[0]):
                        stn[1].add(d2.Initial)
                    if stn not in lStates:
                        lStates.append(stn)
                        new = c.addState(stn)
                        if d2.Final & stn[1] != set([]):
                            c.addFinal(new)
                    else:
                        new = c.stateIndex(stn)
                    c.addTransition(s, sym, new)
            if j == len(lStates) - 1:
                break
            else:
                j += 1
        return c

    def starI(self):
        """Star of an incomplete DFA.

        .. varsionadded::: 0.9.5

        :returns: the Kleene closure DFA
        :rtype: DFA"""
        if len(self.Final) == 1 and self.finalP(self.Initial):
            return self
        d = self.dup()
        c = DFA()
        c.Sigma = d.Sigma
        if len(d.States) == 0 or len(d.Final) == 0:
            # Epsilon automaton
            s0, s1 = c.addState(0), c.addState(1)
            c.setInitial(s0)
            c.addFinal(s0)
            for sym in c.Sigma:
                c.addTransition(s0, sym, s1)
                c.addTransition(s1, sym, s1)
            return c
        F0 = d.Final - {d.Initial}
        i = c.addState("initial")
        c.setInitial(i)
        c.addFinal(i)
        lStates = ["initial"]
        for sym in d.Sigma:
            stn = {d.evalSymbolI(d.Initial, sym)}
            if (stn != set([])) & (stn != {-1}):
                # correction
                if F0 & stn != set([]):
                    stn.add(d.Initial)
                if stn not in lStates:
                    lStates.append(stn)
                    new = c.addState(stn)
                    if d.Final & stn != set([]):
                        c.addFinal(new)
                else:
                    new = c.stateIndex(stn)
                c.addTransition(i, sym, new)
        j = 1
        while True:
            stu = lStates[j]
            s = c.stateIndex(stu)
            for sym in d.Sigma:
                stn = d.evalSymbolLI(stu, sym)
                if stn != set([]):
                    if F0 & stn != set([]):
                        stn.add(d.Initial)
                    if stn not in lStates:
                        lStates.append(stn)
                        new = c.addState(stn)
                        if d.Final & stn != set([]):
                            c.addFinal(new)
                    else:
                        new = c.stateIndex(stn)
                    c.addTransition(s, sym, new)
            if j == len(lStates) - 1:
                break
            else:
                j += 1
        return c

    def shuffle(self, other, strict=False):
        """Shuffle of two languages: L1 W L2

        :param other: second automaton
        :type other: DFA
        :param strict: should the alphabets be necessary equal?
        :type strict: bool
        :rtype: DFA

        .. seealso::
           C. Câmpeanu, K. Salomaa and S. Yu, *Tight lower bound for the state complexity of shuffle of regular
           languages.* J. Autom. Lang. Comb. 7 (2002) 303–310."""
        if strict and self.Sigma != other.Sigma:
            raise DFAdifferentSigma
        NSigma = self.Sigma.union(other.Sigma)
        d1, d2 = self.dup(), other.dup()
        d1.setSigma(NSigma)
        d2.setSigma(NSigma)
        # d1.complete(); d2.complete()
        c = DFA()
        c.setSigma(d1.Sigma)
        j = c.addState({(d1.Initial, d2.Initial)})
        c.setInitial(j)
        if d1.finalP(d1.Initial) and d2.finalP(d2.Initial):
            c.addFinal(j)
        while True:
            s = c.States[j]
            sn = c.stateIndex(s)
            for sym in c.Sigma:
                stn = set()
                for st in s:
                    try:
                        stn.add((d1.evalSymbol(st[0], sym), st[1]))
                    except DFAstopped:
                        pass
                    try:
                        stn.add((st[0], d2.evalSymbol(st[1], sym)))
                    except DFAstopped:
                        pass
                if stn not in c.States:
                    new = c.addState(stn)
                    for sti in stn:
                        if d1.finalP(sti[0]) and d2.finalP(sti[1]):
                            c.addFinal(new)
                            break
                else:
                    new = c.stateIndex(stn)
                c.addTransition(sn, sym, new)
            if j == len(c.States) - 1:
                break
            else:
                j += 1
        return c

    def reorder(self, dicti):
        """Reorders states according to given dictionary. Given a dictionary (not necessarily complete)... reorders
        states accordingly.

        :param dicti
        :type dicti: dictionary"""
        if len(list(dicti.keys())) != len(self.States):
            for i in range(len(self.States)):
                if i not in dicti:
                    dicti[i] = i
        delta = {}
        for s in self.delta:
            delta[dicti[s]] = {}
            for c in self.delta[s]:
                delta[dicti[s]][c] = dicti[self.delta[s][c]]
        self.delta = delta
        self.Initial = dicti[self.Initial]
        Final = set()
        for i in self.Final:
            Final.add(dicti[i])
        self.Final = Final
        states = list(range(len(self.States)))
        for i in range(len(self.States)):
            states[dicti[i]] = self.States[i]
        self.States = states

    def regexp(self):
        """Returns a regexp for the current DFA considering the recursive method. Very inefficent.

        :returns: a regexp equivalent to the current DFA
        :rtype: regexp"""
        if self.Initial:
            foo = {0: self.Initial, self.Initial: 0}
            self.reorder(foo)
        n, nstates = len(self.Final), len(self.States) - 1
        if not n:
            return reex.emptyset(copy(self.Sigma))
        r = self._RPath(0, uSet(self.Final), nstates)
        for s in list(self.Final)[1:]:
            r = reex.disj(self._RPath(0, s, nstates), r, copy(self.Sigma))
        return r

    def _RPath(self, initial, final, m):
        """Recursive path. (Dijsktra algorithm) The recursive function that plays a central role in the creation of
        the RE from a DFA. This suppose that there are no disconnected states."""
        if m == -1:
            if initial == final:
                r = reex.epsilon(copy(self.Sigma))
                try:
                    for c in self.delta[initial]:
                        if self.delta[initial][c] == initial:
                            r = reex.disj(r,
                                          reex.regexp(c, copy(self.Sigma)),
                                          copy(self.Sigma))
                except KeyError:
                    pass
                return r.reduced()
            else:
                r = reex.emptyset(copy(self.Sigma))
                try:
                    for c in self.delta[initial]:
                        if self.delta[initial][c] == final:
                            if not r.emptyP():
                                r = reex.disj(r, reex.regexp(c, copy(self.Sigma)))
                            else:
                                r = reex.regexp(c, copy(self.Sigma))
                except KeyError:
                    pass
                return r.reduced()
        else:
            r = reex.disj(self._RPath(initial, final, m - 1),
                          reex.concat(self._RPath(initial, m, m - 1),
                                      reex.concat(reex.star(self._RPath(m, m, m - 1),
                                                            copy(self.Sigma)),
                                                  self._RPath(m, final, m - 1),
                                                  copy(self.Sigma)),
                                      copy(self.Sigma)), copy(self.Sigma))
        return r.reduced()

    def witnessDiff(self, other):
        """ Returns a witness for the difference of two DFAs and:

        +---+------------------------------------------------------+
        | 0 | if the witness belongs to the **other** language     |
        +---+------------------------------------------------------+
        | 1 | if the witness belongs to the **self** language      |
        +---+------------------------------------------------------+

        :param other: the other DFA
        :type other: DFA
        :returns: a witness word
        :rtype: list of symbols
        :raises DFAequivalent: if automata are equivalent"""
        x = ~self & other
        x = x.minimal()
        result = x.witness()
        v = 0
        if result is None:
            x = ~other & self
            x = x.minimal()
            result = x.witness()
            v = 1
            if result is None:
                raise DFAequivalent
        return result, v

    def usefulStates(self, initial_states=None):
        """Set of states reacheable from the given initial state(s) that have a path to a final state.

        :param initial_states: starting states
        :type initial_states: iterable of int

        :returns: set of state indexes
        :rtype: set of int"""
        # ATTENTION CODER: This is mostly a copy&paste of
        # NFA.usefulStates(), except that the inner loop for adjacent
        # states is removed, and default initial_states is a list with
        # self.Initial and is considered useful
        if initial_states is None:
            initial_states = [self.Initial]
            useful = set(initial_states)
        else:
            useful = set([s for s in initial_states
                          if s in self.Final])
        stack = list(initial_states)
        preceding = {}
        for i in stack:
            preceding[i] = []
        while stack:
            state = stack.pop()
            if state not in self.delta:
                continue
            for symbol in self.delta[state]:
                adjacent = self.delta[state][symbol]
                is_useful = adjacent in useful
                if adjacent in self.Final or is_useful:
                    useful.add(state)
                    if not is_useful:
                        useful.add(adjacent)
                        preceding[adjacent] = []
                        stack.append(adjacent)
                    inpath_stack = [p for p in preceding[state] if p not in useful]
                    preceding[state] = []
                    while inpath_stack:
                        previous = inpath_stack.pop()
                        useful.add(previous)
                        inpath_stack += [p for p in preceding[previous] if p not in useful]
                        preceding[previous] = []
                    continue
                if adjacent not in preceding:
                    preceding[adjacent] = [state]
                    stack.append(adjacent)
                else:
                    preceding[adjacent].append(state)
        return useful

    def finalCompP(self, s):
        """ Verifies if there is a final state in  strongly connected component containing ``s``.

        :param s: state
        :type s: int
        :returns: 1 if yes, 0 if no"""
        if s in self.Final:
            return True
        lst = [s]
        i = 0
        while True:
            try:
                foo = list(self.delta[lst[i]].keys())
            except KeyError:
                foo = []
            for c in foo:
                s = self.delta[lst[i]][c]
                if s not in lst:
                    if s in self.Final:
                        return True
                    lst.append(s)
            i += 1
            if i >= len(lst):
                return False

    def unmark(self):
        """Unmarked NFA that corresponds to a marked DFA: in which each alfabetic symbol is a tuple (symbol, index)

        :returns: a NFA
        :rtype: NFA"""
        nfa = NFA()
        nfa.States = list(self.States)
        nfa.setInitial([self.Initial])
        nfa.setFinal(self.Final)
        for s in self.delta:
            for marked_symbol in self.delta[s]:
                sym, pos = marked_symbol
                nfa.addTransition(s, sym, self.delta[s][marked_symbol])
        return nfa

    def toNFA(self):
        """Migrates a DFA to a NFA as dup()

        :returns: DFA seen as new NFA
        :rtype: NFA"""
        new = NFA()
        new.setSigma(self.Sigma)
        new.States = self.States[:]
        new.addInitial(self.Initial)
        new.Final = self.Final.copy()
        for s in self.delta:
            new.delta[s] = {}
            for c in self.delta[s]:
                new.delta[s][c] = {self.delta[s][c]}
        return new

    def toGFA(self):
        """ Creates a GFA equivalent to DFA

        :returns: GFA deep copy
        :rtype: GFA """
        gfa = GFA()
        gfa.setSigma(self.Sigma)
        gfa.States = self.States[:]
        gfa.setInitial(self.Initial)
        gfa.setFinal(self.Final)
        gfa.predecessors = {}
        for i in range(len(gfa.States)):
            gfa.predecessors[i] = set([])
        for s in self.delta:
            for c in self.delta[s]:
                gfa.addTransition(s, c, self.delta[s][c])
        return gfa

    def stateChildren(self, state, strict=False):
        """Set of children of a state

        :param strict: if not strict a state is never its own child even if a self loop is in place
        :param state: state id queried
        :type state: int
        :type strict: bool
        :returns: map children -> multiplicity
        :rtype: dictionary"""
        l = {}
        if state not in self.delta:
            return l
        for c in self.Sigma:
            if c in self.delta[state]:
                dest = self.delta[state][c]
                l[dest] = l.get(dest, 0) + 1
        if not strict and state in l:
            del l[state]
        return l

    def _smAtomic(self, monoid):
        """Evaluation of the atomic transformations of a DFA

        :arg monoid:
        :type monoid: bool
        :returns: list of transformations
        :rtype: set of list of int"""
        if not self.completeP():
            aut = self.dup()
            aut.complete()
        else:
            aut = self
        n = len(aut)
        mon = SSemiGroup()
        if monoid:
            a = tuple((x for x in range(n)))
            mon.elements.append(a)
            mon.words.append((None, None))
            mon.gen.append(0)
            mon.Monoid = True
        tmp = ([], [])
        for k in aut.Sigma:
            a = tuple((aut.delta[s][k] for s in range(n)))
            tmp = mon.add(a, None, k, tmp)
        if len(tmp[0]):
            mon.addGen(tmp)
        return mon

    def _ssg(self, monoid=False):
        """

        :param monoid:
        :type monoid: bool
        :return:"""
        sm = self._smAtomic(monoid)
        if not sm.gen[-1]:
            return sm
        if sm.Monoid:
            natomic = sm.gen[1]
            shift = 1
        else:
            natomic = sm.gen[0]
            shift = 0
        while True:
            ll = ([], [])
            if len(sm.gen) == 1:
                g0 = 0
            else:
                g0 = sm.gen[-2] + 1
            g1 = sm.gen[-1] + 1
            for (sym, t1) in enumerate(sm.elements[1:natomic + 1]):
                for (pr, t2) in enumerate(sm.elements[g0:g1]):
                    t12 = tuple((t2[t1[i]] for i in range(len(t1))))
                    ll = sm.add(t12, pr + g0, sm.words[sym + shift][1], ll)
            if len(ll[0]):
                sm.addGen(ll)
            else:
                break
        return sm

    def sMonoid(self):
        """Evaluation of the syntactic monoid of a DFA

        :returns: the semigroup
        :rtype: SSemiGroup"""
        return self._ssg(True)

    def sSemigroup(self):
        """Evaluation of the syntactic semigroup of a DFA

        :returns: the semigroup
        :rtype: SSemiGroup"""
        return self._ssg()

    def enumDFA(self, n=None):
        """
        returns the set of words of words of length up to n accepted by self
        :param n: highest length or all words if finite
        :type n: int

        :rtype: list of strings or None

        .. note: use with care because the number of words can be huge
        """
        if n is None:
            raise IndexError
        e = EnumDFA(self)
        words = []
        for i in range(n + 1):
            e.enumCrossSection(i)
            words += e.Words
        return words

class GFA(OFA):
    """ Class for Generalized Finite Automata: NFA with a unique initial state and transitions are labeled with regexp.

    .. inheritance-diagram:: GFA"""

    def finalCompP(self, s):
        raise NImplemented()

    def evalSymbol(self):
        raise NImplemented()

    def __eq__(self, other):
        raise NImplemented()

    def deleteStates(self, del_states):
        raise NImplemented()

    def initialComp(self):
        raise NImplemented()

    def _getTags(self):
        raise NImplemented()

    def __ne__(self, other):
        raise NImplemented()

    def succintTransitions(self):
        raise NImplemented()

    def toGFA(self):
        raise NImplemented()

    def usefulStates(self):
        raise NImplemented()

    def uniqueRepr(self):
        raise NImplemented()

    def __init__(self):
        super(GFA, self).__init__()
        self.predecessors = None

    def __repr__(self):
        """GFA string representation
        :rtype: str"""
        return 'GFA({0:>s})'.format(self.__str__())

    def addTransition(self, sti1, sym, sti2):
        """Adds a new transition from ``sti1`` to ``sti2`` consuming symbol ``sym``. Label of the transition function
         is a regexp.

        :param sti1: state index of departure
        :type sti1: int
        :param sti2: state index of arrival
        :type sti2: int
        :param sym: symbol consumed
        :type sym: str
        :raises DFAepsilonRedefenition: if sym is Epsilon"""
        try:
            self.addSigma(sym)
            sym = reex.regexp(sym, copy(self.Sigma))
        except DFAepsilonRedefinition:
            sym = reex.epsilon(copy(self.Sigma))
        if sti1 not in self.delta:
            self.delta[sti1] = {}
        if sti2 not in self.delta[sti1]:
            self.delta[sti1][sti2] = sym
        else:
            self.delta[sti1][sti2] = reex.disj(self.delta[sti1][sti2], sym, copy(self.Sigma))
        # TODO: write cleaner code and get rid of the general catch
        # noinspection PyBroadException
        try:
            self.predecessors[sti2].add(sti1)
        except:
            pass

    def reorder(self, dictio):
        """Reorder states indexes according to given dictionary.

        :param dictio: order
        :type dictio: dictionary

        .. note::
           dictionary does not have to be complete"""
        if len(list(dictio.keys())) != len(self.States):
            for i in range(len(self.States)):
                if i not in dictio:
                    dictio[i] = i
        delta = {}
        preds = {}
        for s in self.delta:
            delta[dictio[s]] = {}
            if dictio[s] not in preds:
                preds[dictio[s]] = set([])
            for s1 in self.delta[s]:
                delta[dictio[s]][dictio[s1]] = self.delta[s][s1]
                if dictio[s1] in preds:
                    preds[dictio[s1]].add(dictio[s])
                else:
                    preds[dictio[s1]] = {dictio[s]}
        self.delta = delta
        self.predecessors = preds

        self.Initial = dictio[self.Initial]
        Final = set()
        for i in self.Final:
            Final.add(dictio[i])
        self.Final = Final
        states = list(range(len(self.States)))
        for i in range(len(self.States)):
            states[dictio[i]] = self.States[i]
        self.States = states

    def eliminate(self, st):
        """Eliminate a state.

        :param st: state to be eliminated
        :type st: int"""
        if st in self.delta and st in self.delta[st]:
            r2 = copy(reex.star(self.delta[st][st], copy(self.Sigma)))
            del self.delta[st][st]
        else:
            r2 = None
        for s in self.delta:
            if st not in self.delta[s]:
                continue
            r1 = copy(self.delta[s][st])
            del self.delta[s][st]
            for s1 in self.delta[st]:
                r3 = copy(self.delta[st][s1])
                if r2 is not None:
                    r = reex.concat(r1, reex.concat(r2, r3, copy(self.Sigma)), copy(self.Sigma))
                else:
                    r = reex.concat(r1, r3, copy(self.Sigma))
                if s1 in self.delta[s]:
                    self.delta[s][s1] = reex.disj(self.delta[s][s1], r, copy(self.Sigma))
                else:
                    self.delta[s][s1] = r
        del self.delta[st]

    def eliminateAll(self, lr):
        """Eliminate a list of states.

        :param lr: list of states indexes
        :type lr: list"""
        for s in lr:
            self.eliminate(s)

    def dup(self):
        """ Returns a copy of a GFA

        :rtype: GFA"""
        new = GFA()
        new.States = copy(self.States)
        new.Sigma = copy(self.Sigma)
        new.Initial = self.Initial
        new.Final = copy(self.Final)
        new.delta = deepcopy(self.delta)
        new.predecessors = deepcopy(self.predecessors)
        return new

    def normalize(self):
        """ Create a single initial and final state with Epsilon transitions.

        .. attention::
           works in place"""
        first = self.addState("First")
        self.predecessors[first] = set([])
        self.addTransition(first, Epsilon, self.Initial)
        self.setInitial(first)

        last = self.addState("Last")
        self.predecessors[last] = set([])
        if len(self.Final) > 1:
            for s in self.Final:
                self.addTransition(s, Epsilon, last)
                self.predecessors[last].add(s)
        else:
            self.addTransition(list(self.Final)[0], Epsilon, last)
        self.setFinal([last])

    # noinspection PyUnresolvedReferences
    def _do_edges(self, v1, t, rp):
        """ Labels for testing if a automaton is SP. used by SPRegExp

        :param v1: state (node)
        :type v1: int
        :param t: a label
        :type t: SPlabel
        :param rp: regexp
        :type rp: regexp"""
        for v2 in self.delta[v1]:
            if self.out_index[v1] != 1:
                self.lab[(v1, v2)] = t.copy()
                self.lab[(v1, v2)].value.append(v1)
            else:
                self.lab[(v1, v2)] = t.ref()
                self.delta[v1][v2] = reex.concat(rp, self.delta[v1][v2], copy(self.Sigma))

    # noinspection PyUnresolvedReferences
    def _simplify(self, v2, i):
        """Used by SPRegExp.
        :param v2:
        :param i:
        :return:
        :raise NotSP:"""
        m, l = 0, []
        for v1 in self.predecessors[v2]:
            size = len(self.lab[(v1, v2)].val())
            if size == m:
                l.append(v1)
            elif size > m:
                m = size
                l = [v1]
        vi = l[-1]
        for vo in l[-2:]:
            if (self.lab[(vi, v2)].lastref() != self.lab[(vo, v2)].lastref()) and (
                    self.lab[(vi, v2)].val() == self.lab[(vo, v2)].val()):
                v = self.lab[(vi, v2)].val()[-1]
                self.out_index[v] -= 1
                self.lab[(vo, v2)] = self.lab[(vi, v2)].ref()
                self.delta[vi][v2] = reex.disj(self.delta[vo][v2], self.delta[vi][v2], copy(self.Sigma))
                if self.out_index[v] == 1:
                    self.lab[(vi, v2)].assign(self.lab[(vi, v2)].val()[:-1])
                    try:
                        self.delta[vi][v2] = reex.concat(self.delta[list(self.predecessors[v])[0]][v],
                                                         self.delta[vi][v2],
                                                         copy(self.Sigma))
                    except IndexError:
                        pass
                self.predecessors[v2].remove(vo)
                return i - 1
        raise NotSP

    def DFS(self, io):
        """Depth first search

        :param io:"""
        visited = []
        for s in range(len(self.States)):
            self.dfs_visit(s, visited, io)

    def dfs_visit(self, s, visited, io):
        """

        :param s: state
        :param visited: list od states visited
        :param io:"""
        if s not in visited:
            visited.append(s)
            if s in self.delta:
                for dest in self.delta[s]:
                    # lists are unhashable
                    (i, o) = io[s]
                    io[s] = (i, o + 1)
                    (i, o) = io[dest]
                    io[dest] = (i + 1, o)
                    self.dfs_visit(dest, visited, io)

    def weight(self, state):
        """Calculates the weight of a state based on a heuristic

        :param state: state
        :type state: int
        :returns: the weight of the state
        :rtype: int"""
        r = 0
        for i in self.predecessors[state]:
            if i != state:
                r += self.delta[i][state].alphabeticLength() * (len(self.delta[state]) - 1)
        for i in self.delta[state]:
            if i != state:
                r += self.delta[state][i].alphabeticLength() * (len(self.predecessors[state]) - 1)
        if state in self.delta[state]:
            r += self.delta[state][state].alphabeticLength() * (
                len(self.predecessors[state]) * len(self.delta[state]) - 1)
        return r

    def weightWithCycles(self, state, cycles):
        """

        :param state:
        :param cycles:
        :return:"""
        r = 0
        for i in self.predecessors[state]:
            if i != state:
                r += self.delta[i][state].alphabeticLength() * (len(self.delta[state]) - 1)
        for i in self.delta[state]:
            if i != state:
                r += self.delta[state][i].alphabeticLength() * (len(self.predecessors[state]) - 1)
        if state in self.delta[state]:
            r += self.delta[state][state].alphabeticLength() * (
                len(self.predecessors[state]) * len(self.delta[state]) - 1)
        r *= (cycles[state] + 1)
        return r

    def deleteState(self, sti):
        """ deletes a state from the GFA
        :param sti:"""
        newOrder = {}
        for i in range(sti, len(self.States) - 1):
            newOrder[i + 1] = i
        newOrder[sti] = len(self.States) - 1
        self.reorder(newOrder)
        st = len(self.States) - 1
        del self.delta[st]
        del self.predecessors[st]
        l = set([])
        for i in self.delta:
            if st in self.delta[i]:
                l.add(i)
        for i in l:
            del self.delta[i][st]
            if not len(self.delta[i]):
                del self.delta[i]
        for i in self.predecessors:
            if st in self.predecessors[i]:
                self.predecessors[i].remove(st)
        del self.States[st]

    def eliminateState(self, st):
        """ Deletes a state and updates the automaton

        :param st: the state to be deleted
        :type st: state index

        .. attention:
           works in place"""
        for i in self.predecessors[st]:
            for j in self.delta[st]:
                if i != st and j != st:
                    re = self.delta[i][st]
                    if st in self.delta[st]:
                        re = reex.concat(re, reex.star(self.delta[st][st], copy(self.Sigma)), copy(self.Sigma))
                    re = reex.concat(re, self.delta[st][j], copy(self.Sigma))
                    if j in self.delta[i]:
                        re = reex.disj(self.delta[i][j], re, copy(self.Sigma))
                    self.delta[i][j] = re
                    self.predecessors[j].add(i)
        self.deleteState(st)

    def completeDelta(self):
        """Adds empty set transitions between the automatons final and initial states in order to make it complete.
        It's only meant to be used in the final stage of SEA..."""
        for i in set([self.Initial] + list(self.Final)):
            for j in set([self.Initial] + list(self.Final)):
                if i not in self.delta:
                    self.delta[i] = {}
                if j not in self.delta[i]:
                    self.delta[i][j] = reex.emptyset(copy(self.Sigma))

    def stateChildren(self, state, strict=False):
        """Set of children of a state

        :param strict: a state is never its own children even if a self loop is in place
        :param state: state id queried
        :type state: int
        :type strict: bool
        :returns: map: children -> alphabetic length
        :rtype: dictionary"""
        l = {}
        if state not in self.delta:
            return l
        for c in self.delta[state]:
            l[c] = self.delta[state][c].alphabeticLength()
        if not strict and state in l:
            del l[state]
        return l

    def _re0(self):
        ii = self.Initial
        fi = list(self.Final)[0]
        a = self.delta[ii][ii]
        b = self.delta[ii][fi]
        c = self.delta[fi][ii]
        d = self.delta[fi][fi]

        # bd*
        re1 = reex.concat(b, reex.star(d), copy(self.Sigma))
        # a + bd*c
        re2 = reex.disj(a, reex.concat(re1, c, copy(self.Sigma)), copy(self.Sigma))
        # (a + bd*c)* bd*
        return reex.concat(reex.star(re2, copy(self.Sigma)), re1, copy(self.Sigma)).reduced()

    # noinspection PyUnresolvedReferences
    def assignNum(self, st):
        """

        :param st:"""
        self.num[st] = self.c
        self.c += 1
        self.visited.append(st)
        if st in self.delta:
            for d in self.delta[st]:
                if d not in self.visited:
                    self.parent[d] = st
                    self.assignNum(d)

    # noinspection PyUnresolvedReferences
    def assignLow(self, st):
        """

        :param st:"""
        self.low[st] = self.num[st]
        if st in self.delta:
            for d in self.delta[st]:
                if self.num[d] > self.num[st]:
                    self.assignLow(d)
                    if self.low[d] >= self.low[st]:
                        self.cuts.add(st)
                    self.low[st] = min(self.low[st], self.low[d])
                else:
                    if st in self.parent:
                        if self.parent[st] != d:
                            self.low[st] = min(self.low[st], self.num[d])
                    else:
                        self.low[st] = self.num[st]


# noinspection PyTypeChecker
class SSemiGroup(object):
    """Class support for the Syntactic SemiGroup.

    :var elements: list of tuples representing the transformations
    :var words: a list of pairs (index of the prefix transformation, index of the suffix char)
    :var gen: a list of the max index of each generation
    :var Sigma: set of symbols"""

    def __init__(self):
        self.elements = []
        self.words = []
        self.gen = []
        self.Monoid = False
        self.Sigma = {}

    def __len__(self):
        """Size of the semigroup

        :return: size of the semigroup
        :rtype: int """
        return len(self.elements)

    def __repr__(self):
        """SSemiGroup representation

        :rtype: str"""
        foo = "Semigroup:\n"
        for s in self.elements:
            foo += "%s \n" % str(s)
        return foo

    def WordI(self, i):
        """Representative of an element given as index

        :arg i: index of the element
        :type i: int
        :returns: the first word originating the element
        :rtype: str"""
        return self.WordPS(self.words[i][0], self.words[i][1])

    def WordPS(self, pref, sym):
        """Representative of an element given as prefix symb

        :arg pref: prefix index
        :type pref: int
        :arg sym: symbol index
        :type sym: int
        :returns: word
        :rtype: str"""
        if pref is None:
            if sym is None:
                return []
            else:
                return [sym]
        else:
            return self.WordPS(self.words[pref][0], self.words[pref][1]) + [sym]

    def add(self, tr, pref, sym, tmpLists):
        """Try to add a new transformation to the monoid

        :arg tr: transformation
        :type tr: tuple of int
        :arg pref: prefix of the generating word
        :type pref: int or None
        :arg sym: suffix symbol
        :type sym: int
        :arg tmpLists: this generation lists
        :type tmpLists: pairs of lists as (elements,words)"""
        if tr not in self.elements and tr not in tmpLists[0]:
            tmpLists[0].append(tr)
            tmpLists[1].append((pref, sym))
        return tmpLists

    def addGen(self, tmpLists):
        """Add a new generation to the monoid

        :arg tmpLists: the new generation data
        :type tmpLists: pair of lists as (elements, words)"""
        gn = len(tmpLists[0])
        self.elements += tmpLists[0]
        self.words += tmpLists[1]
        if len(self.gen) > 1:
            self.gen.append(self.gen[-1] + gn)
        else:
            self.gen.append(gn)


class EnumL(object):
    # noinspection PyUnresolvedReferences
    """Class for enumerate FA languages

        :var aut: Automaton of the language
        :type aut: DFA
        :var tmin: table for minimal words for each s in aut.States
        :type tmin: dict
        :var Words: list of words (if stored)
        :type Words: list
        :var Sigma: alphabet
        :type Sigma: list
        :type stack: deque

        .. versionadded:: 0.9.8

        .. seealso::
            Efficient enumeration of words in regular languages, M. Ackerman and J. Shallit,
            Theor. Comput. Sci. 410, 37, pp 3461-3470. 2009.
            http://dx.doi.org/10.1016/j.tcs.2009.03.018"""

    def __init__(self, aut, store=False):
        self.aut = aut
        self.tmin = {}
        self.stack = None
        self.Words = []
        self.Sigma = list(aut.Sigma)
        self.Sigma.sort()
        self.store = store
        self.initStack()

    @abstractmethod
    def initStack(self):
        """Abstract method"""
        pass

    @abstractmethod
    def minWordT(self, n):
        """Abstract method
        :param n:
        :type n: int"""
        pass

    def minWord(self, m):
        """ Computes the minimal word of length m accepted by the automaton
        :param m:
        :type m: int"""
        if len(self.tmin) == 0:
            self.minWordT(m)
        if m == 0:
            return ""
        possiblew = [self.tmin[q][m] for q in self.stack[0] if q in self.tmin and m in self.tmin[q]]
        if not possiblew:
            return None
        return min(possiblew)

    def iCompleteP(self, i, q):
        """Tests if state q is i-complete

        :param i: int
        :type i: int
        :param q: state index
        :type q: int"""
        return i in self.tmin[q] or (i == 0 and self.aut.finalP(q))

    @abstractmethod
    def fillStack(self, w):
        """Abstract method
        :param w:
        :type w: str"""
        pass

    @abstractmethod
    def nextWord(self, w):
        """Abstract method
        :param w:
        :type w: str"""
        pass

    def enumCrossSection(self, n):
        """ Enumerates the nth cross-section of L(A)

        :param n: nonnegative integer
        :type n: int
        """
        self.initStack()
        self.tmin = {}
        self.Words = []
        w = self.minWord(n)
        while w is not None:
            self.fillStack(w)
            self.Words.append(w)
            w = self.nextWord(w)
        self.tmin = {}
        self.initStack()

    def enum(self, m):
        """Enumerates the first m words of L(A) according to the lexicographic order if there are at least m words.
        Otherwise, enumerates all words accepted by A.

        :param m:
        :type m: int
        """
        i = 0
        lim = 1
        numCEC = 0
        s = len(self.aut)
        if not (not (isinstance(self.aut, DFA) and self.aut.finalP(self.aut.Initial))
                and not (isinstance(self.aut, NFA) and not self.aut.Initial.isdisjoint(self.aut.Final))):
            self.Words = [""]
            i += 1
            numCEC += 1
        else:
            self.Words = []
        while i < m and numCEC < s:
            self.initStack()
            self.tmin = {}
            w = self.minWord(lim)
            if w is None:
                numCEC += 1
            else:
                numCEC = 0
                while w is not None and i < m:
                    i += 1
                    self.Words.append(w)
                    self.fillStack(w)
                    w = self.nextWord(w)
            lim += 1
        self.tmin = {}
        self.initStack()


class EnumDFA(EnumL):
    """Class for enumerating languages defined by DFAs"""

    def minWordT(self, n):
        """ Computes for each state the minimal word of length i<n
        accepted by the automaton. Stores the values in tmin

        :param n: length of the word
        :type n: integer

        .. note:: Makinen algorithm for DFAs"""
        for i in range(len(self.aut)):
            if i not in self.tmin:
                self.tmin[i] = {}
            for sym in self.Sigma:
                if i in self.aut.delta and sym in self.aut.delta[i] and self.aut.finalP(self.aut.delta[i][sym]):
                    self.tmin.setdefault(i, {})[1] = sym
                    break
        for j in range(2, n + 1):
            for i in range(len(self.aut)):
                m = None
                if i in self.aut.delta:
                    for sym in self.Sigma:
                        if sym in self.aut.delta[i]:
                            q = self.aut.delta[i][sym]
                            if q in self.tmin and j - 1 in self.tmin[q]:
                                m = sym + self.tmin[q][j - 1]
                                break
                                # if nfa compare with others
                                # if m == None or sym+  self.tmin[q][j-1] < min
                if m is not None:
                    self.tmin[i][j] = m

    def fillStack(self, w):
        """ Computes S_1,...,S_n-1 where S_i is the set of (n-i)-complete states reachable from S_i-1

        :param w: word"""
        n = len(w)
        self.initStack()
        for i in range(1, n):
            s = set({})
            for j in self.stack[0]:
                if j in self.aut.delta and w[i - 1] in self.aut.delta[j] and \
                        self.iCompleteP(n - i, self.aut.delta[j][w[i - 1]]):
                    s.add(self.aut.delta[j][w[i - 1]])
            self.stack.appendleft(s)

    def initStack(self):
        """Initializes the stack with initial states """
        self.stack = deque([{self.aut.Initial}])

    def nextWord(self, w):
        """Given an word, returns next word on the nth cross-section of L(aut)
        according to the radix order

        :param w: word
        :type w: str
        :rtype: str"""
        n = len(w)
        for i in range(n, 0, -1):
            s = self.stack[0]
            b = self.Sigma[-1]
            flag = 0
            for j in s:
                if j in self.aut.delta:
                    for sym in self.Sigma:
                        if sym in self.aut.delta[j] and self.iCompleteP(n - i, self.aut.delta[j][sym]):
                            if w[i - 1] < sym:
                                if sym < b:
                                    b = sym
                                flag = 1
            if flag == 0:
                self.stack.popleft()
            else:
                s1 = set([])
                for j in s:
                    if j in self.aut.delta:
                        if b in self.aut.delta[j] and self.iCompleteP(n - i, self.aut.delta[j][b]):
                            s1.add(self.aut.delta[j][b])
                if i != n:
                    self.stack.appendleft(s1)
                mw = self.minWord(n - i)
                if mw is not None:
                    return w[0:i - 1] + b + mw
        return None


class EnumNFA(EnumL):
    """Class for enumerating languages defined by NFAs
    """

    def initStack(self):
        """Initializes the stack with initial states
        """
        self.stack = deque([self.aut.Initial])

    def minWordT(self, n):
        """ Computes for each state the minimal word of length i <= n
        accepted by the automaton. Stores the values in tmin.

        :param n: length of the word
        :type n: integer

        .. note: Makinen algorithm for NFAs"""
        for i in range(len(self.aut)):
            self.tmin[i] = {}
            for sym in self.Sigma:
                if i in self.aut.delta and sym in self.aut.delta[i]:
                    if not self.aut.delta[i][sym].isdisjoint(self.aut.Final):
                        self.tmin.setdefault(i, {})[1] = sym
                        break
        for j in range(2, n + 1):
            for i in range(len(self.aut)):
                m = None
                if i in self.aut.delta:
                    for sym in self.Sigma:
                        if sym in self.aut.delta[i]:
                            for q in self.aut.delta[i][sym]:
                                if q in self.tmin and j - 1 in self.tmin[q]:
                                    if m is None or sym + self.tmin[q][j - 1] < m:
                                        m = sym + self.tmin[q][j - 1]
                if m is not None:
                    self.tmin.setdefault(i, {})[j] = m

    def fillStack(self, w):
        """ Computes S_1,...,S_n-1 where S_i is the set of
        (n-i)-complete states reachable from S_i-1

        :param w: word"""
        n = len(w)
        self.initStack()
        for i in range(1, n):
            s = set([])
            for j in self.stack[0]:
                if j in self.aut.delta and w[i - 1] in self.aut.delta[j]:
                    for q in self.aut.delta[j][w[i - 1]]:
                        if self.iCompleteP(n - i, q):
                            s.add(q)
            if len(s) != 0:
                self.stack.appendleft(s)

    def nextWord(self, w):
        """Given an word, returns next word in the the nth cross-section of L(aut)
        according to the radix order

        :param w: word
        :type w: str"""
        n = len(w)
        for i in range(n, 0, -1):
            if len(self.stack) == 0:
                return None
            s = self.stack[0]
            b = self.Sigma[-1]
            flag = 0
            for j in s:
                if j in self.aut.delta:
                    for sym in self.Sigma:
                        if sym in self.aut.delta[j]:
                            for q in self.aut.delta[j][sym]:
                                if self.iCompleteP(n - i, q):
                                    if w[i - 1] < sym:
                                        if sym < b:
                                            b = sym
                                        flag = 1
            if flag == 0:
                self.stack.popleft()
            else:
                s1 = set([])
                for j in s:
                    if j in self.aut.delta and b in self.aut.delta[j]:
                        for q in self.aut.delta[j][b]:
                            if self.iCompleteP(n - i, q):
                                s1.add(q)
                if i != n:
                    self.stack.appendleft(s1)
                mw = self.minWord(n - i)
                if mw is not None:
                    return w[0:i - 1] + b + mw
        return None


def equivalentP(first, second):
    """Verifies if the two languages given by some representative (DFA, NFA or re) are equivalent

    :arg first: language
    :arg second: language
    :rtype: bool

    .. versionadded:: 0.9.6"""
    t1, t2 = type(first), type(second)
    if t1 == t2 or (issubclass(t1, reex.regexp) and issubclass(t2, reex.regexp)):
        return first.equivalentP(second)
    elif t1 == type(DFA()):
        return first == second.toDFA()
    elif t1 == type(NFA()):
        if t2 == type(DFA()):
            return first.toDFA() == second
        else:
            return first == second.toNFA()
    else:
        if t2 == type(NFA()):
            return first.toNFA() == second
        else:
            return first.toDFA() == second


def stringToDFA(s, f, n, k):
    """ Converts a string icdfa's representation to dfa.

    :param s: canonical string representation
    :type s: list
    :param f: bit map of final states
    :type f: list
    :param n: number of states
    :type n: int
    :param k: number of symbols
    :type k: int
    :returns: a complete dfa with Sigma [``k``], States [``n``]
    :rtype: DFA

    .. versionchanged:: 0.9.8 symbols are converted to str"""
    fa = DFA()
    fa.setSigma([])
    fa.States = list(range(n))
    j = 0
    i = 0
    while i < len(f):
        if f[i]:
            fa.addFinal(j)
        j += 1
        i += 1
    fa.setInitial(0)
    for i in range(n * k):
        if s[i] != -1:
            fa.addTransition(old_div(i, k), str(i % k), s[i])
    return fa


def _cmpPair2(a, b):
    """Auxiliary comparision for sorting lists of pairs. Sorting on the second member of the pair."""
    (x, y), (z, w) = a, b
    if y < w:
        return -1
    elif y > w:
        return 1
    elif x < z:
        return -1
    elif x > z:
        return 1
    else:
        return 0


def _normalizePair(p, q):
    if p < q:
        pair = (p, q)
    else:
        pair = (q, p)
    return pair


def _sortWithNone(a, b):
    if a is None:
        return a, b
    elif b is None:
        return b, a
    elif a >= b:
        return a, b
    else:
        return b, a


def _deref(mp, val):
    if val in mp:
        return _deref(mp, mp[val])
    else:
        return val


def _dictGetKeyFromValue(elm, dic):
    try:
        key = [i for i, j in list(dic.items()) if elm in j][0]
    except IndexError:
        key = None
    return key


def statePP(state):
    """Pretty print state

    :param state:
    :return:"""

    def _spp(st):
        t = type(st)
        if t == str:
            return copy(st).replace(' ', '')
        elif t == int:
            return str(st)
        elif t == tuple:
            bar = "("
            for s in st:
                bar += _spp(s) + ","
            return bar[:-1] + ")"
        elif t == set:
            bar = "{"
            for s in st:
                bar += _spp(s) + ","
            return bar[:-1] + "}"
        else:
            return str(st)

    foo = _spp(state)
    if len(foo) > 1:
        return '"' + foo + '"'
    else:
        return foo


def saveToString(aut, sep="&"):
    """Finite automata definition as a string using the input format.

    .. versionadded:: 0.9.5
    .. versionchanged:: 0.9.6 Names are now used instead of indexes.
    .. versionchanged:: 0.9.7 New format with quotes and alphabet

    :param aut: the FA
    :type aut: FA
    :arg sep: separation between `lines`
    :type sep: str
    :returns: the representation
    :rtype: str """
    buff = ""
    if aut.Initial is None:
        return "Error: no initial state defined"
    if isinstance(aut, DFA):
        buff += "@DFA "
        NFAp = False
    elif isinstance(aut, NFA):
        buff += "@NFA "
        NFAp = True
    else:
        raise DFAerror()
    if not NFAp and aut.Initial != 0:
        foo = {0: aut.Initial, aut.Initial: 0}
        aut.reorder(foo)
    for sf in aut.Final:
        buff += ("{0:>s} ".format(statePP(aut.States[sf])))
    if NFAp:
        buff += " * "
        for sf in aut.Initial:
            buff += ("{0:>s} ".format(statePP(aut.States[sf])))
    buff += sep
    for s in range(len(aut.States)):
        if s in aut.delta:
            for a in aut.delta[s]:
                if isinstance(aut.delta[s][a], set):
                    for s1 in aut.delta[s][a]:
                        buff += ("{0:>s} {1:>s} {2:>s}{3:>s}".format(statePP(aut.States[s]), str(a),
                                                                     statePP(aut.States[s1]), sep))
                else:
                    buff += ("{0:>s} {1:>s} {2:>s}{3:>s}".format(statePP(aut.States[s]), str(a),
                                                                 statePP(aut.States[aut.delta[s][a]]), sep))
        else:
            buff += "{0:>s} {1:>s}".format(statePP(aut.States[s]), sep)
    return buff


def sConcat(x, y):
    """ Concat words

    :param x: first word
    :param y: second word
    :return: concatenation word"""
    if x == Epsilon:
        return y
    elif y == Epsilon:
        return x
    else:
        return x + y


def sigmaStarDFA(sigma=None):
    """
    Given a alphabet S returns the minimal DFA for S*

    :param sigma: set of symbols
    :return: DFA

    .. versionadded:: 1.2"""
    if sigma is None:
        raise
    d = DFA()
    d.setSigma(sigma)
    i = d.addState()
    d.setInitial(i)
    d.addFinal(i)
    for a in d.Sigma:
        d.addTransition(i, a, i)
    return d


def _addPool(pool, done, val):
    """ Adds to a pool with exception list

    :param pool: pool to be added
    :type pool: set
    :param done: exception list
    :type done: set
    :param val: value"""
    if val in done:
        return
    else:
        pool.add(val)


def _initPool():
    """Initialize pool structure

    :return: pool and done objects
    :rtype: tuple"""
    return set(), set()
