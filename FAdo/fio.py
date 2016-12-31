# -*- coding: utf-8 -*-
"""**In/Out.**

FAdo IO.

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
from builtins import range
from builtins import *
from .yappy_parser import Yappy, grules

from .common import Epsilon, DFAerror, TRError
from .fa import DFA, NFA, statePP
from .transducers import SFT, GFT, Transducer


class ParserFAdo(Yappy):
    """A parser for FAdo standard automata descriptions

    .. inheritance-diagram:: ParserFAdo"""

    def __init__(self, no_table=1, table=".tableFAdo"):
        tokenizer = [("\n+", lambda x: ("EOL", "EOL")),
                     ("#.*", ""),
                     ("\s+", ""),
                     #("@epsilon", lambda x: ("ids", "@epsilon")),
                     ("@epsilon", lambda x: ("ids", Epsilon)),
                     ("@NFA", lambda x: ("NFA", "NFA")),
                     ("@DFA", lambda x: ("DFA", "DFA")),
                     ("@TDFA", lambda x: ("TDFA", "TDFA")),
                     ("@Transducer", lambda x: ("TRANS", "TRANS")),
                     ("\*", lambda x: ("SEP", "SEP")),
                     ("\$", lambda x: ("DOLLAR", "DOLLAR")),
                     ("\^", lambda x: ("CARET", "CARET")),
                     ("<", lambda x: ("mv", "LEFT")),
                     (">", lambda x: ("mv", "RIGHT")),
                     ('"[A-Za-z0-9\(\)\[\]\{\}:\.,_-]+"', lambda x: ("id", x[1:-1])),
                     ("[A-Za-z0-9]+", lambda x: ("id", x))]
        grammar = grules([("r -> d r", self.defaultSemRule),
                          ("r -> n r", self.defaultSemRule),
                          ("r -> td r", self.defaultSemRule),
                          ("r -> tr r", self.defaultSemRule),
                          ("r -> dummy r", self.emptySemRule),
                          ("r -> ", self.emptySemRule),
                          ("d -> DFA l t1", self.startDFASemRule),
                          ("n -> NFA l t1n", self.startNFASemRule),
                          ("n -> NFA l1 i tn", self.startNFASemRule),
                          ("td -> TDFA l tt1", self.startTDFASemRule),
                          ("tr -> TRANS l5 ttr", self.startTRANSSemRule),
                          ("tr -> TRANS l3 ttri", self.startTRANSSemRule),
                          ("idt -> id", self.defaultSemRule),
                          ("idt -> ids", self.defaultSemRule),
                          ("l -> id l", self.finalSemRule),
                          ("l -> DOLLAR l2", self.emptySemRule),
                          ("l -> EOL", self.emptySemRule),
                          ("l1 -> id l1", self.finalSemRule),
                          ("l1 -> SEP", self.emptySemRule),
                          ("l2 -> id l2 ", self.addAlphabet),
                          ("l2 -> EOL", self.emptySemRule),
                          ("i -> id i", self.initialSemRule),
                          ("i -> DOLLAR l2", self.emptySemRule),
                          ("i -> EOL", self.emptySemRule),
                          ("l5 -> id l5", self.finalSemRule),
                          ("l5 -> DOLLAR it", self.emptySemRule),
                          ("l5 -> EOL", self.emptySemRule),
                          ("l3 -> id l3", self.finalSemRule),
                          ("l3 -> SEP l4", self.emptySemRule),
                          ("l4 -> id l4", self.initialSemRule),
                          ("l4 -> DOLLAR it", self.emptySemRule),
                          ("l4 -> EOL", self.emptySemRule),
                          ("it -> id it", self.addAlphabet),
                          ("it -> DOLLAR ot", self.emptySemRule),
                          ("it -> EOL", self.emptySemRule),
                          ("ot -> id ot ", self.addAlphabetOut),
                          ("ot -> EOL", self.emptySemRule),
                          ("t1 -> EOL t1", self.emptySemRule),
                          ("t1 -> id EOL t", self.firstDeclareState),
                          ("t1 -> id id id EOL t", self.firstTransitionSemRule),
                          ("t1 -> ", self.emptySemRule),
                          ("tt1 -> EOL tt1", self.emptySemRule),
                          ("tt1 - id EOL tt", self.firstDeclareState),
                          ("tt1 -> id ids id mv tt", self.firstTTransitionSemRule),
                          ("tt1 -> id id id mv tt", self.firstTTransitionSemRule),
                          ("tt1 -> id DOLLAR id mv tt", self.firstTTransitionSemRule),
                          ("tt1 -> id CARET id mv tt", self.firstTTransitionSemRule),
                          ("tt1 -> ", self.emptySemRule),
                          ("tt -> id EOL tt", self.declareState),
                          ("tt -> id ids is mv EOL tt", self.transitionTSemRule),
                          ("tt -> id id is mv EOL tt", self.transitionTSemRule),
                          ("tt -> id DOLLAR is mv EOL tt", self.transitionTSemRule),
                          ("tt -> id CARET is mv EOL tt", self.transitionTSemRule),
                          ("tt -> EOL tt", self.emptySemRule),
                          ("tt -> ", self.emptySemRule),
                          ("t1n -> EOL t1n", self.emptySemRule),
                          ("t1n -> id EOL tn", self.firstDeclareState),
                          ("t1n -> id id id EOL tn", self.firstTransitionSemRule),
                          ("t1n -> id ids id EOL tn", self.firstTransitionESemRule),
                          ("t1n -> ", self.emptySemRule),
                          ("t -> id EOL t", self.declareState),
                          ("t -> id id id EOL t", self.transitionSemRule),
                          ("t -> EOL t", self.emptySemRule),
                          ("t -> ", self.emptySemRule),
                          ("tn - EOL tn", self.emptySemRule),
                          ("tn -> id EOL tn", self.declareState),
                          ("tn -> id id id EOL tn", self.transitionSemRule),
                          ("tn -> id ids id EOL tn", self.transitionESemRule),
                          ("tn -> EOL tn", self.emptySemRule),
                          ("tn -> ", self.emptySemRule),
                          ("ttr - EOL ttr", self.emptySemRule),
                          ("ttr -> id EOL ttr", self.declareState),
                          ("ttr -> id idt idt id EOL ttrs", self.firstTransitionTransSemRule),
                          ("ttr -> ", self.emptySemRule),
                          ("ttrs -> id EOL ttrs", self.declareState),
                          ("ttrs -> id idt idt id EOL ttrs", self.transitionTransSemRule),
                          ("ttrs -> EOL ttrs", self.emptySemRule),
                          ("ttrs -> ", self.emptySemRule),
                          ("ttri - EOL ttri", self.emptySemRule),
                          ("ttri -> id EOL ttri", self.declareState),
                          ("ttri -> id idt idt id EOL ttri", self.transitionTransSemRule),
                          ("ttri -> EOL ttri", self.emptySemRule),
                          ("ttri -> ", self.emptySemRule),
                          ("dummy -> EOL", self.emptySemRule)
                          ])

        self.theList = []
        self.transitions = []
        self.initials = []
        self.states = set()
        self.finals = []
        self.alphabet = set()
        self.alphabetOut = set()
        self.TRtype = None
        Yappy.__init__(self, tokenizer, grammar, table, no_table)

    def initLocal(self):
        """Starts local structures for a new automata"""
        self.transitions = []
        self.initials = []
        self.states = set()
        self.finals = []
        self.alphabet = set()
        self.alphabetOut = set()

    # noinspection PyUnusedLocal
    @staticmethod
    def defaultSemRule(lst, context=None):
        """Defines the default semantic rule for Yappy
        :param list lst: list of the arguments semantics
        :param dict context: context for the semantic rules
        :returns: first argument semantics"""
        return lst[0]

    # noinspection PyUnusedLocal
    @staticmethod
    def emptySemRule(lst, context=None):
        """Defines the empty semantic rule for Yappy
        :param lst: lst of the arguments semantics
        :param dict context: context for the semantic rules
        :returns: empty list"""
        return []

    # noinspection PyUnusedLocal
    def startDFASemRule(self, lst, context=None):
        """


        :param context:
        :param lst:
        :param context:"""
        new = DFA()
        while self.states:
            x = self.states.pop()
            new.addState(x)
        new.Sigma = self.alphabet
        x = self.initials.pop()
        new.setInitial(new.stateIndex(x))
        while self.finals:
            x = self.finals.pop()
            new.addFinal(new.stateIndex(x))
        while self.transitions:
            (x1, x2, x3) = self.transitions.pop()
            new.addTransition(new.stateIndex(x1), x2, new.stateIndex(x3))
        self.theList.append(new)
        self.initLocal()

    # noinspection PyUnusedLocal
    def startTDFASemRule(self, lst, context=None):
        """

        :param lst:
        :param context:
        """
        pass

    # noinspection PyUnusedLocal
    def startNFASemRule(self, lst, context=None):
        """

        :param lst:
        :param context:"""
        new = NFA()
        new.Sigma = self.alphabet
        while self.states:
            x = self.states.pop()
            new.addState(x)
        while self.initials:
            x = self.initials.pop()
            new.addInitial(new.stateIndex(x))
        while self.finals:
            x = self.finals.pop()
            new.addFinal(new.stateIndex(x))
        while self.transitions:
            (x1, x2, x3) = self.transitions.pop()
            new.addTransition(new.stateIndex(x1), x2, new.stateIndex(x3))
        self.theList.append(new)
        self.initLocal()

    # noinspection PyUnusedLocal
    def startTRANSSemRule(self, lst, context=None):
            """

            :param lst:
            :param context:"""
            if self.TRtype is None:
                new = SFT()
            elif self.TRtype == "GFT":
                new = GFT()
            else: raise TRError
            new.Sigma = self.alphabet
            new.Output = self.alphabetOut
            while self.states:
                x = self.states.pop()
                new.addState(x)
            while self.initials:
                x = self.initials.pop()
                new.addInitial(new.stateIndex(x))
            while self.finals:
                x = self.finals.pop()
                new.addFinal(new.stateIndex(x))
            while self.transitions:
                (x1, x2, x3, x4) = self.transitions.pop()
                new.addTransition(new.stateIndex(x1), x2, x3, new.stateIndex(x4))
            self.theList.append(new)
            self.initLocal()

    # noinspection PyUnusedLocal
    def finalSemRule(self, lst, context=None):
        """

        :param lst:
        :param context:"""
        self.finals.append(lst[0])
        self.states.add(lst[0])

    # noinspection PyUnusedLocal
    def initialSemRule(self, lst, context=None):
        """

        :param lst:
        :param context:"""
        self.initials.append(lst[0])
        self.states.add(lst[0])

    # noinspection PyUnusedLocal
    def firstTransitionSemRule(self, lst, context=None):
        """

        :param lst:
        :param context:"""
        self.initials.append(lst[0])
        self.states.add(lst[0])
        self.states.add(lst[2])
        self.transitions.append((lst[0], lst[1], lst[2]))

    # noinspection PyUnusedLocal
    def firstTTransitionSemRule(self, lst, context=None):
        """

        :param lst:
        :param context:"""
        pass

    # noinspection PyUnusedLocal
    def firstTransitionTransSemRule(self, lst, context=None):
        """

        :param lst:
        :param context:"""
        self.initials.append(lst[0])
        self.states.add(lst[0])
        self.states.add(lst[3])
        if self.TRtype is None and (lst[1] != Epsilon and len(lst[1]) > 1) or (lst[2] != Epsilon and len(lst[2]) > 1):
            self.TRtype = "GFT"
        self.transitions.append((lst[0], lst[1], lst[2], lst[3]))

    # noinspection PyUnusedLocal
    def firstDeclareState(self, lst, context=None):
        """

        :param lst:
        :param context:"""
        self.states.add(lst[0])
        self.initials.append(lst[0])

    # noinspection PyUnusedLocal
    def addAlphabet(self, lst, context=None):
        """

        :param lst:
        :param context:"""
        self.alphabet.add(lst[0])

    # noinspection PyUnusedLocal
    def addAlphabetOut(self, lst, context=None):
        """

        :param lst:
        :param context:"""
        self.alphabetOut.add(lst[0])

    # noinspection PyUnusedLocal
    def declareState(self, lst, context=None):
        """

        :param lst:
        :param context:"""
        self.states.add(lst[0])

    # noinspection PyUnusedLocal
    def firstTransitionESemRule(self, lst, context=None):
        """

        :param lst:
        :param context:"""
        self.transitions.append((lst[0], Epsilon, lst[2]))
        self.initials.append(lst[0])
        self.states.add(lst[0])
        self.states.add(lst[2])

    # noinspection PyUnusedLocal
    def transitionSemRule(self, lst, context=None):
        """

        :param lst:
        :param context:"""
        self.transitions.append((lst[0], lst[1], lst[2]))
        self.states.add(lst[0])
        self.states.add(lst[2])

    # noinspection PyUnusedLocal
    def transitionTransSemRule(self, lst, context=None):
        """

        :param lst:
        :param context:"""
        if self.TRtype is None and (lst[1] != Epsilon and len(lst[1]) > 1) or (lst[2] != Epsilon and len(lst[2]) > 1):
            self.TRtype = "GFT"
        self.transitions.append((lst[0], lst[1], lst[2], lst[3]))
        self.states.add(lst[0])
        self.states.add(lst[3])

    # noinspection PyUnusedLocal
    def transitionTSemRule(self, lst, context=None):
        """

        :param lst:
        :param context:"""
        pass

    # noinspection PyUnusedLocal
    def transitionESemRule(self, lst, context=None):
        """

        :param lst:
        :param context:"""
        self.transitions.append((lst[0], Epsilon, lst[2]))
        self.states.add(lst[0])
        self.states.add(lst[2])

    def result(self):
        """

        :return:"""
        return self.theList


def readOneFromFile(fileName):
    """ Read the first of the FAdo objects from File

    :param fileName: name of the file
    :type fileName: str
    :rtype: DFA|FA|STF"""
    return readFromFile(fileName)[0]


def readFromFile(FileName):
    """Reads list of finite automata definition from a file.

    :param FileName: file name
    :type FileName: str
    :rtype: list

    The format of these files must be the as simple as possible:

    .. hlist::
       :columns: 1

       * ``#`` begins a comment
       * ``@DFA`` or ``@NFA`` begin a new automata (and determines its type) and must be followed by the list of the
         final states separated by blanks
       * fields are separated by a blank and transitions by a CR: ``state`` ``symbol`` ``new state``
       * in case of a NFA declaration, the "symbol" @epsilon is interpreted as a epsilon-transition
       * the source state of the first transition is the initial state
       * in the case of a NFA, its declaration ``@NFA``  can, after the declaration of the final states,
         have a ``*`` followed by the list of initial states
       * both, NFA and DFA, may have a declaration of alphabet starting with a ``$`` followed by the symbols of the
         alphabet
       * a line with a sigle name, decrares a state

    .. productionlist:: Fado Format
       FAdo: FA | FA CR FAdo
       FA: DFA | NFA | Transducer
       DFA: "@DFA" LsStates Alphabet CR dTrans
       NFA: "@NFA" LsStates Initials Alphabet CR nTrans
       Transducer: "@Transducer" LsStates Initials Alphabet Output CR tTrans
       Initials: "*" LsStates | \epsilon
       Alphabet: "$" LsSymbols | \epsilon
       Output: "$" LsSymbols | \epsilon
       nSymbol: symbol | "@epsilon"
       LsStates: stateid | stateid , LsStates
       LsSymbols: symbol | symbol , LsSymbols
       dTrans: stateid symbol stateid |
        :| stateid symbol stateid CR dTrans
       nTrans: stateid nSymbol stateid |
        :| stateid nSymbol stateid CR nTrans
       tTrans: stateid nSymbol nSymbol stateid |
        :| stateid nSymbol nSymbol stateid CR nTrans
    .. note::
       If an error occur, either syntactic or because of a violation of the declared automata type,
       an exception is raised

    .. versionchanged:: 0.9.6
    .. versionchanged:: 1.0"""

    parser = ParserFAdo()
    parser.inputfile(FileName)
    return parser.result()


def readOneFromString(s):
    """Reads one finite automata definition from a file.

    .. seealso::
        readFromFile for description of format

    :param str s: the string
    :rtype: DFA|NFA|SFT"""
    parser = ParserFAdo()
    parser.input(s)
    return parser.result()[0]


def saveToFile(FileName, fa, mode="a"):
    """ Saves a list finite automata definition to a file using the input format

    .. versionchanged:: 0.9.5
    .. versionchanged:: 0.9.6
    .. versionchanged:: 0.9.7 New format with quotes and alphabet

    :param FileName: file name
    :type FileName: str
    :param fa: the FA
    :type fa: list of FA
    :param mode: writing mode
    :type mode: str """

    #TODO: write the complete information into file according with the new format
    def _save_SFTransducer(tr):
        """Writes transducer to a file

        :param tr: the transducer
        :type tr: Transducer"""
        f.write("@Transducer ")
        for s in tr.Final:
            f.write("{0:>s} ".format(statePP(tr.States[s])))
        f.write("* ")
        for s in tr.Initial:
            f.write("{0:>s} ".format(statePP(fa.States[s])))
        f.write("\n")
        for sin in tr.delta:
            for syin in tr.delta[sin]:
                for (syout, sout) in tr.delta[sin][syin]:
                    f.write("{0:>s} {1:>s} {2:>s} {3:>s}\n".format(statePP(tr.States[sin]), str(syin), str(syout),
                                                                   statePP(tr.States[sout])))
        f.write("\n")

    def _saveFA(aut):
        """Writes one fa to a file

        :param aut: the automaton
        :type aut: FA or list"""
        if isinstance(aut, DFA):
            f.write("@DFA ")
            NFAp = False
        elif isinstance(aut, NFA):
            f.write("@NFA ")
            NFAp = True
        else:
            raise DFAerror()
        if not NFAp and aut.Initial != 0:
            foo = {0: aut.Initial, aut.Initial: 0}
            aut.reorder(foo)
        for sf in aut.Final:
            f.write("{0:>s} ".format(statePP(aut.States[sf])))
        if NFAp:
            f.write(" * ")
            for sf in aut.Initial:
                f.write("{0:>s} ".format(statePP(aut.States[sf])))
        f.write("\n")
        for s in range(len(aut.States)):
            if s in aut.delta:
                for a in list(aut.delta[s].keys()):
                    if isinstance(aut.delta[s][a], set):
                        for s1 in aut.delta[s][a]:
                            f.write(
                                "{0:>s} {1:>s} {2:>}\n".format(statePP(aut.States[s]), str(a), statePP(aut.States[s1])))
                    else:
                        f.write("{0:>s} {1:>s} {2:>s}\n".format(statePP(aut.States[s]), str(a),
                                                                statePP(aut.States[aut.delta[s][a]])))
            else:
                f.write("{0:>s} \n".format(statePP(aut.States[s])))

    try:
        f = open(FileName, mode)
    except IOError:
        raise DFAerror()
    if type(fa) == list:
        for d in fa:
            if isinstance(d, Transducer):
                _save_SFTransducer(d)
            else:
                _saveFA(d)
    else:
        if isinstance(fa, Transducer):
            _save_SFTransducer(fa)
        else:
            _saveFA(fa)
    f.close()


def _exportToTeX(FileName, fa):
    """ Saves a finite automatom definition to a latex tabular. Saves a finite automata definition to a file using
    the input format

    .. versionchanged:: 0.9.4

    :param FileName: file name
    :type FileName: str
    :param fa: the FA
    :type fa: FA
    :raises DFAerror: if a file error occurs"""
    try:
        f = open(FileName, "w")
    except IOError:
        raise DFAerror()
        #initial is the first one
    if fa.Initial:
        foo = {0: fa.Initial, fa.Initial: 0}
        fa.reorder(foo)
    f.write("$$\\begin{array}{r|")
    for i in range(len(fa.Sigma)):
        f.write("|c")
    f.write("}\n")
    for c in fa.Sigma:
        f.write("&{0:>s}".format(str(c)))
    f.write(" \\\\\hline\n")
    for s in range(len(fa.States)):
        if s in fa.delta:
            if fa.Initial == s:
                f.write("\\rightarrow")
            if s in fa.Final:
                f.write("\\star")
            f.write("{0:>s}".format(str(s)))
            for a in list(fa.delta[s].keys()):
                if isinstance(fa.delta[s][a], set):
                    f.write("&\{")
                    for s1 in fa.delta[s][a]:
                        f.write("{0:>s} ".format(str(s1)))
                    f.write("\}")
                else:
                    s1 = fa.delta[s][a]
                    f.write("&{0:>s}".format(str(s1)))
            f.write("\\\\\n")
    f.write("\end{array}$$")
    f.close()
