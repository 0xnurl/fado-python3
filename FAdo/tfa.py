# -*- coding: utf-8 -*-
"""**Finite two-way automata manipulation.**

Deterministic and non-deterministic two-way automata manipulation, conversion and evaluation.

.. *Authors:* Rogério Reis & Nelma Moreira

.. *This is part of FAdo project*   http://fado.dcc.fc.up.pt.

.. *Copyright:* 2014 Rogério Reis & Nelma Moreira {rvr,nam}@dcc.fc.up.pt

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
from builtins import *
from builtins import object
from . import fa
from abc import abstractmethod
from .common import *


class WordEval(object):
    """Class for word evaluation configuration
    :type Aut: TFA"""
    def __str__(self):
        return str(self.Pos), str(self.Word), str(self.Aut), str(self.State)

    def __repr__(self):
        return self.__str__()

    def __init__(self, word, sti):
        self.Word = word
        self.RLi = len(self.Word) - 1
        self.Pos = None
        self.Trace = None
        self.Aut = None
        self.State = sti

    def _start(self, aut):
        """Initialises evaluation configuration

        :param aut: automaton"""
        self.Aut = aut
        self.State = self.Aut.Initial
        self.Pos = 0
        self.Trace = []

    def eval1(self):
        """Eval one step

        :raises TAFSignal: accordingly to execution"""
        if self.Pos == -1:
            sym = TFA.LMark
        elif self.Pos > self.RLi:
            sym = TFA.RMark
        else:
            sym = self.Word[self.Pos]
        (st, mv) = self.Aut.evalSymbol(self.State, sym)
        if (self.State, self.Pos, mv) in self.Trace:
            raise TFARejectLoop
        else:
            self.Trace.append((self.State, self.Pos, mv))
        if self.Pos > self.RLi:
            if self.Aut.finalP(st):
                raise TFAAccept
            else:
                raise TFARejectNonFinal
        self.State = st
        self.Pos += mv

    def eval(self, aut):
        """Evaluate the word

        :param aut: automaton
        :type aut: TFA

        :raises TFASignal: accordinliy to the evaluation"""
        self._start(aut)
        while True:
            self.eval1()


class TFA(fa.FA):
    """ Base class for two-way automata"""
    LMark = "@"
    RMark = "#"

    @abstractmethod
    def dotFormat(self, size):
        raise NotImplementedError

    @abstractmethod
    def succintTransitions(self):
        raise NotImplementedError

    @abstractmethod
    def dotDrawTransition(self, st1, sym, st2, sep):
        raise NotImplementedError

    def __ne__(self, other):
        raise NotImplementedError

    def __eq__(self, other):
        raise NotImplementedError

    @abstractmethod
    def evalSymbol(self):
        raise NotImplementedError

    Dir = ["R", "L"]

    @abstractmethod
    def addTransition(self):
        """Add Transition"""
        raise NotImplementedError


class TDFA(TFA):
    """ Class of Deterministic Two-Way Finite Automata"""

    @staticmethod
    def trD(mv):
        """ Translate mv from int to str

        :param mv: move
        :type mv: int
        :rtype: str"""
        if mv == 1:
            return "R"
        else:
            return "L"

    def addTransition(self, st1, sym, st2, mov):
        """Add transition to DFTA

        :param st1: starting state
        :param st2: ending state
        :param sym: symbol consumed (can be a border marker)
        :param mov: direction of the next move
        :type st1: int
        :type st2: inst"""
        if st1 not in self.delta:
            self.delta[st1] = dict()
            self.delta[st1][sym] = (st2, mov)
        else:
            self.delta[st1][sym] = (st2, mov)

    def succintTransitions(self):
        """ Collects the transition information in a compact way suitable for graphical representation.
        :rtype: list of tupples

        .. versionadded: 0.9.8"""
        foo = dict()
        for s in self.delta:
            for c in self.delta[s]:
                k = (s, self.delta[s][c][0])
                if k not in foo:
                    foo[k] = []
                foo[k].append(c, self.delta[s][c][1])
        l = []
        for k in foo:
            cs = foo[k]
            s = "%s,%s" % (str(cs[0][0]), self.trD(cs[0][1]))
            for c in cs[1:]:
                s += "; %s,%s" % (str(c[0]), self.trD(c[1]))
            l.append((str(self.States[k[0]]), s, str(self.States[k[1]])))
        return l

    def dotDrawTransition(self, st1, sym, st2, sep):
        pass

    def evalSymbol(self, init, sym):
        """Eval a symbol from a state

        :param init: starting state
        :type init: int
        :param sym: symbol read
        :returns: tupple (state,movement)
        :rtype: tuple
        :raises TFARejectBlocked: if transition is not valid"""
        if init not in self.delta or sym not in self.delta[init]:
            raise TFARejectBlocked
        return self.delta[init][sym]
