# -*- coding: utf-8 -*-
"""**GRAIL support.**

GRAIL formats support. This is an auxiliary module that sould be imported by
fa.py

.. *Authors:* Rogério Reis & Nelma Moreira

.. *This is part of FAdo project*   http://fado.dcc.fc.up.pt

.. versionadded:: 0.9.4

.. *Copyright:* 2011-2014 Rogério Reis & Nelma Moreira {rvr,nam}@dcc.fc.up.pt

.. This program is free software; you can redistribute it and/or modify it under the terms of the GNU General Public
   License as published by the Free Software Foundation; either version 2 of the License,
   or (at your option) any later version.

   This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied
    warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
    details.

   You should have received a copy of the GNU General Public License along with this program; if not,
   write to the Free Software Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA."""
from __future__ import absolute_import
from __future__ import unicode_literals
from __future__ import print_function
from __future__ import division

#__package__="FAdo"

from future import standard_library
standard_library.install_aliases()
from builtins import range
from builtins import *
from builtins import object
import os
import os.path
import subprocess

from .yappy_parser import Yappy, grules

from .fa import NFA, DFA
from .fl import DCFA
from . import common


class GrailCommandError(common.fnhException):
    """Error in the argument of a Grail call"""
    pass


class ParserGrail(Yappy):
    """A parser form GRAIL standard automata descriptions

  .. inheritance-diagram:: ParserGrail"""

    def __init__(self, no_table=1, table='.tableGrail'):
        grammar = grules([("r -> f EOL r", self.defaultSemRule),
                          ("r -> i EOL r", self.defaultSemRule),
                          ("r -> t EOL r", self.defaultSemRule),
                          ("r -> j EOL r", self.defaultSemRule),
                          ("r -> ", self.emptySemRule),
                          ("j -> IId equal integer", self.eqSemRule),
                          ("IId -> id", self.defaultSemRule),
                          ("IId -> integer", self.defaultSemRule),
                          ("f -> IId final", self.finalSemRule),
                          ("i -> start IId", self.initialSemRule),
                          ("t -> IId IId IId", self.automataTransitionSemRule)])
        tokenizer = [("\n+", lambda x: ("EOL", "EOL")),
                     ("\s+", ""),
                     ("lambda[A-Za-z0-9]+", lambda x: ("id", x)),
                     ("lambda", lambda x: ("id", "@epsilon")),
                     ("\(START\)", lambda x: ("start", "start")),
                     ("\(FINAL\)", lambda x: ("final", "final")),
                     ("\|-", ""),
                     ("-\|", ""),
                     ("=", lambda x: ("equal", "equal")),
                     ("[0-9]+", lambda x: ("integer", x)),
                     ("[A-Za-z][A-Za-z0-9]*", lambda x: ("id", x))]
        self.initials = set()
        self.finals = set()
        self.symbols = set()
        self.transitions = {}
        self.states = set()
        self.eq = {}
        Yappy.__init__(self, tokenizer, grammar, table, no_table)

    def defaultSemRule(self, lst, context=None):
        """ do nothing
        :param lst: """
        return lst[0]

    def emptySemRule(self, lst, context=None):
        """ ignore
        :param lst:
        :param context: """
        return []

    def finalSemRule(self, lst, context=None):
        """ final states
        :param context:
        :param lst: """
        self.states.add(lst[0])
        self.finals.add(lst[0])

    def initialSemRule(self, lst, context=None):
        """initial states
        :param context:
        :param lst: """
        self.states.add(lst[1])
        self.initials.add(lst[1])

    def eqSemRule(self, lst, context=None):
        """

        :param lst:
        :param context: """
        self.eq[lst[0]] = int(lst[2])

    def automataTransitionSemRule(self, lst, context=None):
        """ add a tranasition
        :param context:
        :param lst: """
        self.states.add(lst[0])
        self.states.add(lst[2])
        self.symbols.add(lst[1])
        if lst[0] not in list(self.transitions.keys()):
            self.transitions[lst[0]] = {}
        if lst[1] not in list(self.transitions[lst[0]].keys()):
            self.transitions[lst[0]][lst[1]] = set()
        self.transitions[lst[0]][lst[1]].add(lst[2])

    # noinspection PyUnresolvedReferences
    def getAutomata(self):
        """ deal with the information collected"""
        isDeterministic = True
        if len(self.initials) > 1 or "@epsilon" in self.states:
            isDeterministic = False
        else:
            for s in self.transitions:
                for c in self.transitions[s]:
                    if len(self.transitions[s][c]) > 1:
                        isDeterministic = False
                        break
                if not isDeterministic:
                    break
        if isDeterministic:
            if "l" in list(self.eq.keys()):
                fa = DCFA()
                fa.setLength = self.eq["l"]
            else:
                fa = DFA()
        else:
            fa = NFA()
        for s in self.states:
            fa.addState(s)
        fa.setFinal(fa.indexList(self.finals))
        if isDeterministic:
            fa.setInitial(fa.stateIndex(common.uSet(self.initials)))
            for s1 in self.transitions:
                for c in self.transitions[s1]:
                    fa.addTransition(fa.stateIndex(s1), c,
                                     fa.stateIndex(common.uSet(self.transitions[s1][c])))
        else:
            fa.setInitial(fa.indexList(self.initials))
            for s1 in self.transitions:
                for c in self.transitions[s1]:
                    for s2 in fa.indexList(self.transitions[s1][c]):
                        fa.addTransition(fa.stateIndex(s1), c, s2)
        return fa


def exportToGrail(fileName, fa):
    """ Saves a finite automatom definition to a file using Grail format

    :arg fileName: file name
    :type fileName: string
    :arg fa: the FA
    :type fa: FA"""
    try:
        f = open(fileName, "w")
    except IOError:
        raise common.DFAerror()
    FAToGrail(f, fa)
    f.close()


def FAToGrail(f, fa):
    """Saves a finite automatom definition to an open file using Grail format

    :arg f: opended file
    :type f: file
    :arg fa: the FA
    :type fa: FA"""
    for s in fa.initialSet():
        f.write("(START) |- %s\n" % s)
    for s in range(len(fa.States)):
        if s in fa.delta:
            for a in list(fa.delta[s].keys()):
                if isinstance(fa.delta[s][a], set):
                    for s1 in fa.delta[s][a]:
                        f.write("%s %s %s\n" % (s, a, s1))
                else:
                    f.write("%s %s %s\n" % (s, a, fa.delta[s][a]))
    for s in fa.Final:
        f.write("%s -| (FINAL)\n" % s)


def importFromGrailFile(fileName):
    """Imports a finite automaton from a file in GRAIL format

    The type of the object returned depends on the transition definiion red as well as the number of initial states
    declared

    :arg str fileName: file name
    :returns: the automata red
    :rtype: FA"""
    parser = ParserGrail()
    parser.inputfile(fileName)
    return parser.getAutomata()


def importFromGrailString(st):
    """Imports a finite automaton from a string in GRAIL format

    The type of the object returned depends on the transition definiion red as well as the number of initial states
    declared

    :arg str st: fstring
    :returns: the automata red
    :rtype: FA"""

    parser = ParserGrail()
    parser.input(st)
    return parser.getAutomata()


def FAFromGrail(buffer):
    """Imports a  finite automaton from a buffer in GRAIL format

  The type of the object returned depends on the transition definiion red as well as the number of initial states
  declared

  :arg str buffer: buffer file
  :returns: the automata red
  :rtype: FA"""
    parser = ParserGrail()
    parser.input(buffer)
    return parser.getAutomata()


# noinspection PyUnboundLocalVariable
class Grail(object):
    """A class for Grail execution"""

    def __init__(self):
        """
        .. versionchanged:: 0.9.8 tries to initialise execPath from fadorc """
        self.syntaxe = {"afacaten": ["afa", "afa", "afa"],
                        "afacomp": ["afa", "afa"],
                        "afaexec": ["afa", "word", "bool"],
                        "afainter": ["afa", "afa", "afa"],
                        "afareverse": ["afa", "afa"],
                        "afasize": ["afa", "int"],
                        "afastar": ["afa", "afa"],
                        "afatofm": ["afa", "fa"],
                        "afaunion": ["afa", "afa", "afa"],
                        "dfaunion": ["fa", "fa", "fa"],
                        "flappend": ["fl", "word", "fl"],
                        "flexec": ["fl", "word", "bool"],
                        "flfilter": ["fl", "fa", "fl"],
                        "fllq": ["fl", "word", "fl"],
                        "flprepen": ["fl", "word", "fl"],
                        "flprod": ["fl", "fl", "fl"],
                        "flrevers": ["fl", "fl"],
                        "flrq": ["fl", "word", "fl"],
                        "fltofm": ["fl", "fa"],
                        "fltore": ["fl", "re"],
                        "flunion": ["fl", "fl", "fl"],
                        "fmcat": ["fa", "fa", "fa"],
                        "fmcment": ["fa", "fa"],
                        "fmcomp": ["fa", "fa"],
                        "fmcross": ["fa", "fa", "fa"],
                        "fmdeterm": ["fa", "fa"],
                        "fmenum": ["fa", "fl"],
                        "fmexec": ["fa", "word", "bool"],
                        "fmmin": ["fa", "fa"],
                        "fmminrev": ["fa", "fa"],
                        "fmplus": ["fa", "fa"],
                        "fmreach": ["fa", "fa"],
                        "fmrenum": ["fa", "fa"],
                        "fmrevers": ["fa", "fa"],
                        "fmsize": ["fa", "int"],
                        "fmstar": ["fa", "fa"],
                        "fmstats": ["fa", "blurb"],
                        "fmtoafa": ["fa", "afa"],
                        "fmtofcm": ["fa", "ca"],
                        "fmtofcm0": ["fa", "ca"],
                        "fmtofcm2": ["fa", "ca"],
                        "fmtofl": ["fa", "fl"],
                        "fmtore": ["fa", "re"],
                        "fmunion": ["fa", "fa", "fa"],
                        "iscomp": ["fa", "bool"],
                        "isdeterm": ["fa", "bool"],
                        "isempty": ["re", "bool"],
                        "isnull": ["re", "bool"],
                        "isomorph": ["fa", "fa", "bool"],
                        "isuniv": ["fa", "bool"],
                        "liteafa": ["fa", "blurb"],
                        "recat": ["re", "re", "re"],
                        "remin": ["re", "re"],
                        "restar": ["re", "re"],
                        "retofl": ["re", "fl"],
                        "retofm": ["re", "fa"],
                        "reunion": ["re", "re", "re"]
                        }
        if os.path.isfile("fadorc.py"):
            try: from fadorc import grailPath
            except ImportError:
                return
            self.execPath = os.path.abspath(grailPath)

    def setExecPath(self, path):
        """Sets the path to the Grail executables

        :arg str path: the path to Grail executables"""
        self.execPath = os.path.abspath(path)

    def do(self, cmd, *args):
        """Execute Grail command

        :arg cmd: name of the command
        :type cmd: string
        :arg args: arguments

        :raises GrailCommandError: if the syntax is not correct an exception is raised
        :raise FAdoGeneralError: if Grail fails to execute something"""
        try:
            lsargs = self.syntaxe[cmd]
        except KeyError:
            raise GrailCommandError()
        if len(lsargs) != (len(args) + 1):
            raise GrailCommandError()
        cmdl = [os.path.join(self.execPath, cmd)]
        if len(lsargs) > 2:  # more than 2 args mean that input is handled by files and output by pipes
            largs = []
            for i, s in enumerate(lsargs[:-1]):
                largs.append(self._processArg(s, args[i]))
            for s in largs:
                cmdl.append(s)
            if lsargs[-1] != "bool":
                try:
                    process = subprocess.Popen(cmdl, stdout=subprocess.PIPE)
                except:
                    raise common.FAdoGeneralError("Grail execution error")
                self._cleanFiles(lsargs, largs)
            else:
                result = True
                try:
                    #  TODO: something is wrong with this value outf check it!
                    subprocess.check_call(cmdl, stdout=outf)
                except subprocess.CalledProcessError:
                    result = False
        else:  # 2 args mean that everithing can be done by pipes
            if lsargs[-1] == "bool":
                result = True
                try:
                    subprocess.check_call(cmdl)
                except subprocess.CalledProcessError:
                    result = False
            else:
                try:
                    process = subprocess.Popen(cmdl, stdin=subprocess.PIPE, stdout=subprocess.PIPE)
                except:
                    raise common.FAdoGeneralError("Grail execution error")
                self._processArgPipe(process.stdin, lsargs[0], args[0])
                # output processing
        if lsargs[-1] != "bool":
            result = self._parseResult(process.communicate(), lsargs[-1])
        return result

    @staticmethod
    def _cleanFiles(lsargs, largs):
        for i, s in enumerate(lsargs[:-1]):
            if s in ["fa"]:
                os.remove(largs[i])

    @staticmethod
    def _parseResult(pipe, aType):
        if aType == "fa" or aType == "ca":
            return FAFromGrail(pipe[0])
        if aType == "fl":
            return pipe[0].split('\n')
        if aType == "re":
            return pipe[0][:-1]

    def _processArgPipe(self, pipe, aType, aObject):
        if aType == "fa":
            FAToGrail(pipe, aObject)
        if aType == "re":
            pipe.write(aObject.__str__)
            pipe.write("\n")
        if aType == "fl":
            for wrd in aObject:
                pipe.write(wrd)
                pipe.write("\n")
        if aType == "word":
            pipe.write(aObject)

    def _processArg(self, aType, aObject):
        if aType == "fa":
            fname = common.tmpFileName()
            exportToGrail(fname, aObject)
            return fname
        if aType == "re":
            fname = common.tmpFileName()
            fo = open(fname, "w")
            fo.write(aObject.__str__)
            fo.write("\n")
            fo.close()
            return fname
        if aType == "fl":
            fname = common.tmpFileName()
            fo = open(fname, "w")
            for wrd in aObject:
                fo.write(wrd)
                fo.write("\n")
            fo.close()
            return fname
        if aType == "word":
            wrd = ""
            for s in aObject:
                wrd += s
            return '"%s"' % wrd
