# -*- coding: utf-8 -*-
"""
This is part of Yappy

parser.py -- Yet another  parser for python...

A LR parser generator, based on Aho and al. 1986, C{Compilers}
(aho86:_compil).

It currently builds C{SLR}, C{LR(1)} and  C{LALR(1)} parsing tables.

Copyright (C) 2000-2003 Rogério Reis & Nelma Moreira {rvr,nam}@ncc.up.pt
Version: $Id: parser.py,v 1.18 2006-07-19 09:52:06 rvr Exp $

This program is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.   

"""
from __future__ import print_function
from __future__ import unicode_literals
from __future__ import division
from __future__ import absolute_import

from past.builtins import cmp
from future import standard_library
standard_library.install_aliases()
from builtins import input
from builtins import str
from builtins import range
from builtins import *
from builtins import object
from types import *
import re
import sys
import string
import os
import os.path
import shelve
import dbm as whichdb


# set elements are mutable objects; we cannot use sets

# Globals

_DEBUG = 0

_Version = "1.9.4"

NIL = ""


class Lexer(object):
    """Class for lexical analyser to use with the parser

        :var rules: lexical rules
        @ivar operators: precedence and associativity for operators
        @type operators: dictionary

    """

    def __init__(self, rules_list):
        """
        By now lexer is kept as simple as possible, so order is really
        essential: i.e. if a keyword is substring of another its rule
        must appear after the larger keyword for the obvious
        reasons...

        :param rules_list: contains pairs C{(re,funct,op?)} where:
        
        *re*: is an uncompiled python regular expression

        *funct*: the name of
        a funcion that returns the pair C{(TOKEN, SPECIAL_VALUE)}, where C{TOKEN}
        is the token to be used by the parser and C{SPECIAL_VALUE} an eventual
        associated value. The argument is the matched string. If
        C{funct} equals C{""} the token is ignored. This can be
        used for delimiters.

        *op*: if present, is a tuple with operador
        information: C{(TOKEN,PRECEDENCE,ASSOC)} where C{PRECEDENCE} is an
        integer and C{ASSOC} the string 'left' or 'right'.

        """
        self.rules = []
        rnumber = 1
        for r in rules_list:
            try:
                rex = r[0]
                funct = r[1]
            except IndexError:
                raise LexicalError(rnumber, r)
            try:
                rec = re.compile(rex)
            except TypeError:
                raise LexicalRulesErrorRE(rex, rnumber)
            try:
                op, prec, assoc = r[2]
                if "operators" not in self.__dict__:
                    self.operators = dict()
                if op not in self.operators:
                    self.operators[op] = (prec, assoc)
            except IndexError:
                pass
            self.rules.append((rec, funct))
            rnumber = rnumber + 1
        if _DEBUG and "operators" in self.__dict__:
            print("operators %s" % self.operators)

    def scan(self, string):
        """Performs the lexical analysis on C{string}

        :return: a list of tokens (pairs *(TOKEN , SPEcial_VALUE )*), for
        recognized elements and *("@UNK", string )* for the others"""
        st = [string]
        for r in self.rules:
            st = self.scanOneRule(r, st)
        return self.scanUnknown(st)

    def scanOneRule(self, rule, st):
        """Scans space C{st} according only one rule

        :param rule: one rule C{(re,fun,op)}
        
        :param st: is a list of strings and already matched structures
        """
        re = rule[0]
        fun = rule[1]
        st1 = []
        for s in st:
            if not isinstance(s, str):
                st1.append(s)
            else:
                s1 = s
                while True:
                    m = re.search(s1)
                    if not m:
                        st1.append(s1)
                        break
                    else:
                        if m.start() != 0:
                            st1.append(s1[0:m.start()])
                        #                        if fun == "":
                        #                            st1.append(("",s1[m.start():m.end()]))
                        #                        else:
                        if fun != "":
                            st1.append(fun(*[s1[m.start():m.end()]]))
                        if m.end() == len(s1):
                            break
                        else:
                            s1 = s1[m.end():]
        return st1

    def scanUnknown(self, st):
        """Scans the resulting structure making Unknown strings

        Unknown parts will be of the form ("@UNK", string ) """
        st1 = []
        for s in st:
            if isinstance(s, str):
                st1.append(("@UNK", s))
            else:
                st1.append(s)
        return st1

    def readscan(self):
        """Scans a string read from stdin """
        st = input()
        if not st:
            raise IOError
        if isinstance(st, str):
            s = self.scan(st)
            return s


class YappyError(Exception):
    """Class for all Yappy exceptions"""
    pass


class StackUnderflow(YappyError):
    pass


class LexicalError(YappyError):
    """Class for all Yappy Lexical analyser exceptions"""

    def __init__(self, r, rule):
        self.value = "Error in rule number %s: %s" % (r, rule)

    def __str__(self):
        return "%s" % self.value


class LexicalRulesErrorRE(YappyError):
    """An error occured parsing the RE part of a lexical rule"""

    def __init__(self, re, no=0):
        self.value = 'Error in RE "%s" at rule n.%d' % (re, no)
        self.rule = no
        self.re = re

    def __str__(self):
        return "%s" % self.value


class GrammarError(YappyError):
    """Class for input grammar errors """

    def __init__(self, rule):
        self.value = 'Error in rule "%s" ' % rule

    def __str__(self):
        return "%s" % self.value


class SLRConflictError(YappyError):
    """Confliting actions in building SLR parsing table. Grammar
     is not SLR(0)"""

    def __init__(self, i, a):
        self.value = 'Confliting action[%d,%s] in SLR parsing table' % (i, a)
        self.item = i
        self.symbol = a

    def __str__(self):
        return "%s" % self.value


class LRConflictError(YappyError):
    """Conflicting actions in building LR parsing table. Grammar
     is not LR(1)"""

    def __init__(self, i, a):
        self.item = i
        self.symbol = a
        self.value = 'Confliting action[%d,%s] in LR(1) parsing table ' % (self.item, self.symbol)

    def __str__(self):
        return "%s" % (self.value)


class LRConflicts(YappyError):
    """Confliting actions in building LR parsing table. Grammar
     is not LR(1)"""

    def __init__(self):
        self.value = """ Warning>>> Several conflicting actions. Please
    consult self.Log for details"""

    def __str__(self):
        return "%s" % self.value


class LRParserError(YappyError):
    """An error occured in LR parsing program"""

    def __init__(self, s, a):
        self.item = s
        self.symbol = a
        self.value = 'Error in LR: (%s,%s) not found' % (self.item, self.symbol)

    def __str__(self):
        return "%s" % self.value


class SemanticError(YappyError):
    """An error occured in the application of a semantic action"""

    def __init__(self, m, n=0, r=None):
        self.value = m
        self.nrule = n
        self.rule = r

    def __str__(self):
        return "%s in semantic rule %d: %s" % (self.value, self.nrule, self.rule)


class TableError(YappyError):
    """Mismatch table version """

    def __init__(self, t):
        self.value = """A new table must be built.
        Please remove table shelve %s or set no_table to 0""" % t

    def __str__(self):
        return "%s" % self.value


class CFGrammar(object):
    """ Class for context-free grammars

        :var rules: grammar rules
        :var terminals: terminals symbols
        :var nonterminals: nonterminals symbols
        :var str start: start symbol
        :var ntr: dictionary of rules for each nonterminal
        
    """

    def __init__(self, grammar):
        """

        :param grammar: is a list for productions;
        each production is a  tuple C{(LeftHandside,RightHandside,SemFunc,Prec?)}
        with C{LeftHandside} nonterminal, C{RightHandside} list of symbols,
        C{SemFunc} syntax-direct semantics,  if present
        C{Prec (PRECEDENCE,ASSOC)} for ambiguous rules
        
        First production is for start symbol
        
        Special symbols: C{@S}, C{$}, C{#}
        """
        """ MUST BE IN THIS ORDER"""
        self.rules = grammar
        self.makenonterminals()
        self.maketerminals()
        self.start = self.rules[0][0]
        self.aug_start = "@S"
        self.rules.append((self.aug_start, [self.start], DefaultSemRule))
        self.endmark = '$'
        self.dummy = '#'
        self.terminals.append(self.endmark)
        self.terminals.append(self.dummy)
        self.nonterminals.append(self.aug_start)
        """ ritems are only for control ... not needed """
        self.ritems = []
        """ ntr[A] is the set of rules which has A as left side"""
        self.ntr = {}
        i = 0
        for r in self.rules:
            if r[0] not in self.ntr:
                self.ntr[r[0]] = [i]
            else:
                self.ntr[r[0]].append(i)
            for j in range(len(r[1]) + 1):
                self.ritems.append((i, j))
            i = i + 1

    def __str__(self):
        """Grammar rules
        
           :return: a string representing the grammar rules
        """
        s = ""
        for n in range(len(self.rules)):
            lhs = self.rules[n][0]
            rhs = self.rules[n][1]
            s = s + "%s | %s -> %s \n" % (n, lhs, " ".join(rhs))
        return "Grammar Rules:\n\n%s" % s

    def makeFFN(self):
        self.NULLABLE()
        self.FIRST_ONE()
        self.FOLLOW()

    def maketerminals(self):
        """Extracts *terminals* from the rules.
        *nonterminals* must already exist"""
        self.terminals = []
        for r in self.rules:
            for s in r[1]:
                if s not in self.nonterminals and s not in self.terminals:
                    self.terminals.append(s)

    def makenonterminals(self):
        """Extracts *nonterminals*  from grammar rules."""
        self.nonterminals = []
        for r in self.rules:
            if r[0] not in self.nonterminals:
                self.nonterminals.append(r[0])

    def NULLABLE(self):
        """Determines which nonterminals *X ->* []* """
        self.nullable = {}
        for s in self.terminals:
            self.nullable[s] = 0
        for s in self.nonterminals:
            self.nullable[s] = 0
            if s in self.ntr:
                for i in self.ntr[s]:
                    if not self.rules[i][1]:
                        self.nullable[s] = 1
                        break
        k = 1
        while k == 1:
            k = 0
            for r in self.rules:
                e = 0
                for i in r[1]:
                    if not self.nullable[i]:
                        e = 1
                        break
                if e == 0 and not self.nullable[r[0]]:
                    self.nullable[r[0]] = 1
                    k = 1


    def FIRST(self, s):
        """C{FIRST(s)} is the set of terminals that begin the strings
        derived from s """
        first = Set([])
        e = 0
        for i in range(len(s)):
            first.s_extend(self.first[s[i]])
            if not self.nullable[s[i]]:
                e = 1
                break
        if e == 0:
            self.nullable[" ".join(s)] = 1
        else:
            self.nullable[" ".join(s)] = 0
        return first

    def FIRST_ONE(self):
        """Determines  C{FIRST(s)}, for every symbol s, that is the set of
        terminals that begin the strings derived from s """
        self.first = {}
        self.nd = {}
        self.ms = Stack()
        for s in self.terminals:
            self.first[s] = Set([s])
        for s in self.nonterminals:
            if s in self.ntr and s not in self.first:
                self.FIRST_TRA(s, 1)

    def FIRST_TRA(self, s, d):
        """Transitive closure of *FIRST(X)* """
        self.ms.push(s)
        self.nd[s] = d
        """ calculating F1(s)"""
        self.first[s] = Set([])
        for i in self.ntr[s]:
            for y in self.rules[i][1]:
                if self.nullable[y]:
                    continue
                else:
                    if y in self.terminals:
                        self.first[s].append(y)
                    break
        """transitive closure"""
        for i in self.ntr[s]:
            for y in self.rules[i][1]:
                if y in self.nonterminals:
                    if y not in self.first:
                        self.FIRST_TRA(y, d + 1)
                    if y in self.nd and self.nd[y] != -1:
                        self.nd[s] = min(self.nd[s], self.nd[y])
                    self.first[s].s_extend(self.first[y])
                    if self.nullable[y]:
                        continue
                    else:
                        break
                else:
                    break
        if self.nd[s] == d:
            while 1:
                y = self.ms.pop()
                if y == s:
                    break
                self.first[y] = self.first[s].copy()
                self.nd[y] = -1

    def FIRST_NT(self, s):
        """ Recursivelly computes C{FIRST(X)} for a nonterminal  X"""
        if s not in self.ntr:
            return
        self.first[s] = Set([])
        for i in self.ntr[s]:
            r = self.rules[i][1]
            if not r:
                self.nullable[s] = 1
            else:
                e = 1
                for y in r:
                    if y not in self.first:
                        self.FIRST_NT(y)
                    self.first[s].s_extend(self.first[y])
                    if not self.nullable[y]:
                        e = 0
                        break
                if e == 1:
                    self.nullable[s] = 1

    def FOLLOW(self):
        """computes C{FOLLOW(A)} for all nonterminals: the set of terminals a
        that can appear immediately to the right of A in some sentential form."""
        self.follow = {self.start: Set([self.endmark])}
        for rule in self.rules:
            r = rule[1]
            for i in range(len(r)):
                if r[i] in self.nonterminals:
                    if r[i] not in self.follow:
                        self.follow[r[i]] = Set([])
                    j = i + 1
                    self.follow[r[i]].s_extend(self.FIRST(r[j:]))
        e = 1
        while e:
            e = 0
            for s in self.nonterminals:
                for i in self.ntr[s]:
                    r = self.rules[i][1]
                    try:
                        b = r[len(r) - 1]
                        if b in self.nonterminals and self.follow[b].s_extend(self.follow[s]):
                            e = 1
                    except IndexError:
                        pass
                    except KeyError:
                        pass
                    for k in range(len(r) - 1):
                        j = k + 1
                        if r[k] in self.nonterminals and self.nullable[" ".join(r[j:])]:
                            if self.follow[r[k]].s_extend(self.follow[s]):
                                e = 1
                            break

    def TransClose(self):
        """For each nonterminal C{s} determines the set of nonterminals
        a such that C{s ->* ar}, for some C{r}"""
        self.close_nt = {}
        self.nd = {}
        self.ms = Stack()
        for s in self.nonterminals:
            if s in self.ntr:
                if s not in self.close_nt:
                    self.TRAVERSE(s, 1)

    def TRAVERSE(self, s, d):
        """ """
        self.ms.push(s)
        self.nd[s] = d
        """ calculating F1(s)"""
        self.close_nt[s] = {s: Set([[]])}
        for i in self.ntr[s]:
            if not self.rules[i][1]:
                continue
            else:
                r = self.rules[i][1]
                for j in range(len(r)):
                    if r[j + 1:]:
                        f = self.FIRST(r[j + 1:])
                        ns = self.nullable[" ".join(r[j + 1:])]
                    else:
                        f = []
                        ns = 1
                    if r[j] in self.nonterminals:
                        if r[j] not in self.close_nt[s]:
                            self.close_nt[s][r[j]] = Set([[]])
                        if r[j + 1:]:
                            self.close_nt[s][r[j]].append((f, ns))
                        if not self.nullable[r[j]]:
                            break
                    else:
                        break
        """reflexive tansitive closure"""
        for i in self.ntr[s]:
            if not self.rules[i][1]:
                continue
            else:
                r = self.rules[i][1]
                for j in range(len(r)):
                    f = self.FIRST(r[j + 1:])
                    ns = self.nullable[" ".join(r[j + 1:])]
                    if r[j] in self.nonterminals:
                        if r[j] not in self.close_nt:
                            self.TRAVERSE(r[j], d + 1)
                        if r[j] in self.nd and self.nd[r[j]] != -1:
                            self.nd[s] = min(self.nd[s], self.nd[r[j]])
                        for k in list(self.close_nt[r[j]].keys()):
                            if k not in self.close_nt[s]:
                                self.close_nt[s][k] = Set([[]])
                            else:
                                for v in self.close_nt[s][k]:
                                    if not v:
                                        self.close_nt[s][k].append((f, ns))
                                    else:
                                        p, n = v
                                        if n:
                                            self.close_nt[s][k].append((p + f, ns))
                                        else:
                                            self.close_nt[s][k].append((p, n))
                        if not self.nullable[r[j]]:
                            break
                    else:
                        break
        if self.nd[s] == d:
            while 1:
                y = self.ms.pop()
                if y == s:
                    break
                self.close_nt[y] = self.close_nt[s].copy()
                self.nd[y] = -1

    def DERIVE_NT(self):
        """For each nonterminal C{s} determines the set of nonterminals
        a such that C{s ->* ar}, for some C{r}"""
        self.derive_nt = {}
        for s in self.nonterminals:
            if s in self.ntr and s not in self.derive_nt:
                self.DERIVE_ONE_NT(s)

    def DERIVE_ONE_NT(self, s):
        """For nonterminal C{s} determines the set of nonterminals
        a such that C{s -> ar}, for some C{r} """
        if s not in self.ntr:
            return
        self.derive_nt[s] = {s: Set([None])}
        for i in self.ntr[s]:
            if not self.rules[i][1]:
                continue
            else:
                r = self.rules[i][1]
                for j in range(len(r)):
                    if r[j] in self.nonterminals:
                        if r[j] not in self.derive_nt:
                            self.DERIVE_ONE_NT(r[j])
                        for k in list(self.derive_nt[r[j]].keys()):
                            if k not in self.derive_nt[s]:
                                self.derive_nt[s][k] = Set([])
                            for p in self.derive_nt[r[j]][k]:
                                if not p:
                                    self.derive_nt[s][k].append(r[j + 1:])
                                else:
                                    self.derive_nt[s][k].append(r[j + 1:].append(p))
                        if not self.nullable[r[j]]:
                            break
                    else:
                        break

    def DERIVE_T(self):
        """ """
        self.derive_ter = {}
        for s in self.terminals:
            self.derive_ter[s] = Set([s])
        e = 1
        while e:
            e = 0
            for s in self.nonterminals:
                for i in self.ntr[s]:
                    r = self.rules[i][1]
                    if r == []:
                        continue
                    for i in range(len(r)):
                        if r[i] in self.terminals:
                            if i < len(r) - 1:
                                if r[i + 1] in self.derive_ter:
                                    if s not in self.derive_ter:
                                        self.derive_ter[s] = Set([])
                                    if self.derive_ter[s].s_append(r[i]):
                                        e = 1
                                break
                            else:
                                if s not in self.derive_ter:
                                    self.derive_ter[s] = Set([])
                                if self.derive_ter[s].s_append(r[i]):
                                    e = 1

                                break
                        else:
                            """ non-terminal"""
                            if r[i] in self.derive_ter:
                                if s not in self.derive_ter:
                                    self.derive_ter[s] = Set([])
                                if self.derive_ter[s].s_extend(self.derive_ter[r[i]]) == 1:
                                    e = 1
                            if i > 0 and self.nullable[r[i]]:
                                continue
                            else:
                                break


class LRtable(object):
    """Class for construction of a *LR* table

        :var gr: a context-free grammar
        :var operators: operators
        :var  Log: Log report for LR table construction
    """

    def __init__(self, cfgr, operators=None, noconflicts=1, expect=0):
        """
        :param cfgr: a context-free grammar
        :param operators: operators
        :param noconflicts: if 0 LRtable conflicts are not resolved,
                   unless for spcecial operator rules 
        :type noconflicts: integer
        :param expect: exact number of expected LR shift/reduce conflicts
        :type expect: integer
        """
        self.gr = cfgr
        self.gr.makeFFN()
        self.operators = operators
        self.precedence = None
        self.rules_precedence()
        self.Log = LogLR(noconflicts, expect)
        self.make_action_goto()


    def make_action_goto(self):
        """ make C{action[i,X]} and C{goto[i,X]}
        All pairs C{(i,s)}  not in action and goto dictionaries are 'error' """
        c = list(self.items())
        if _DEBUG:
            print(self.print_items(c))
        self.ACTION = {}
        self.GOTO = {}
        #shelve not working with osets
        #self.Log.items = c 
        for i in range(len(c)):
            for item in c[i]:
                a = self.NextToDot(item)
                if a in self.gr.terminals:
                    state = self.goto(c[i], a)
                    try:
                        j = c.index(state)
                        self.add_action(i, a, 'shift', j)
                    except IndexError:
                        if _DEBUG:  print("no state")
                elif a == "":
                    """ Dot at right end """
                    l = self.gr.rules[item[0]][0]
                    if l != self.gr.aug_start:
                        self.dotatend(item, i)
                    else:
                        """ last rule """
                        self.add_action(i, self.gr.endmark, 'accept', [])
            for s in self.gr.nonterminals:
                state = self.goto(c[i], s)
                try:
                    j = c.index(state)
                    self.GOTO[(i, s)] = j
                except ValueError:
                    pass

    def rules_precedence(self):
        """Rule precedence obtained as the precedence of the right
        most terminal. """
        self.precedence = {}
        for i in range(len(self.gr.rules)):
            if len(self.gr.rules[i]) == 4:
                self.precedence[i] = self.gr.rules[i][3]
            else:
                self.precedence[i] = None
                if self.operators:
                    self.gr.rules[i][1].reverse()
                    for s in self.gr.rules[i][1]:
                        if s in self.operators:
                            self.precedence[i] = self.operators[s]
                            break
                    self.gr.rules[i][1].reverse()

        if _DEBUG:
            print("Precedence %s" % self.precedence)

    def add_action(self, i, a, action, j):
        """Set C{(action,j)} for state C{i} and symbol C{a} or  raise
        conflict error. Conficts are resolved using the following
        rules:
           - shift/reduce: if precedence/assoc information is available
        try to use it; otherwise conflict is resolved in favor of shift
           - reduce/reduce: choosing the production rule listed first
        """
        if (i, a) in self.ACTION and self.ACTION[(i, a)] != (action, j):
            action1, j1 = self.ACTION[(i, a)]
            if _DEBUG:
                print("LRconflit %s %s %s %s %s %s" % (action, j, action1, j1, i, a))
            if action1 == 'shift' and action == 'reduce':
                self.resolve_shift_reduce(i, a, j1, j)
            elif action == 'shift' and action1 == 'reduce':
                self.resolve_shift_reduce(i, a, j, j1)
            elif action == 'reduce' and action1 == 'reduce':
                if self.Log.noconflicts:
                    # RESOLVED by choosing first rule
                    if j > j1:
                        self.ACTION[(i, a)] = (action, j1)
                    else:
                        self.ACTION[(i, a)] = (action, j)
                    self.Log.add_conflict('rr', i, a, j1, j)
                else:
                    raise LRConflictError(i, a)
        else:
            self.ACTION[(i, a)] = (action, j)

    def resolve_shift_reduce(self, i, a, s, r):
        """Operators precedence resolution or standard option: shift

        :param s: rule for shift
        :param r: rule for reduce
        
        """
        try:
            if self.operators and a in self.operators and r in self.precedence and self.precedence[r]:
                prec_op, assoc_op = self.operators[a]
                if (self.precedence[r][0] > prec_op) or (
                            self.precedence[r][0] == prec_op and self.precedence[r][1] == 'left'):
                    self.ACTION[(i, a)] = ('reduce', r)
                    if _DEBUG: print("solved reduce %s" % r)
                else:
                    self.ACTION[(i, a)] = ('shift', s)
                    if _DEBUG: print("solved shift %s" % s)
            else:
                self.ACTION[(i, a)] = ('shift', s)
                if _DEBUG: print("solved shift %s" % s)
        except (AttributeError, TypeError, KeyError, NameError):
            if self.Log.noconflicts:
                # choose to shift
                self.ACTION[(i, a)] = ('shift', s)
                if _DEBUG: print("choose shift %s for action (%s,%s)" % (s, i, a))
                self.Log.add_conflict('sr', i, a, s, r)
                if _DEBUG: print(" %s for action (%s,%s)" % (self.Log.conflicts, i, a))

            else:
                raise LRConflictError(i, a)


class SLRtable(LRtable):
    """Class for construction of a C{SLR} table
    
 C{SLR} items represented by a pair of integers C{(number of
 rule,position of dot)}

 (aho86:_compil page 221) 
    """

    def dotatend(self, item, i):
        n, k = item
        l = self.gr.rules[item[0]][0]
        for a in self.gr.follow[l]:
            self.add_action(i, a, 'reduce', n)

    def closure(self, items):
        """The closure of a set of C{LR(0)} items C{I} is the set of
        items constructed from C{I} by the two rules:
           - every item of I is in closure(I)
           - If A -> s.Bt in closure(I) and B -> r, then add B ->.r to closure(I)
        (aho86:_compil page 223) 
        """
        added = {}
        for l in self.gr.nonterminals:
            added[l] = 0
        close = items[:]
        e = 1
        while e:
            e = 0
            for i in close:
                s = self.NextToDot(i)
                if s in self.gr.nonterminals and added[s] == 0 and s in self.gr.ntr:
                    for n in self.gr.ntr[s]:
                        close.append((n, 0))
                    added[s] = 1
                    e = 1
        return close

    def goto(self, items, s):
        """ goto(I,X) where I is a set of items and X a grammar symbol
        is the closure of the set of all items A -> sX.r such that
        A -> s.Xr is in I"""
        valid = Set([])
        for item in items:
            if self.NextToDot(item) == s:
                n, i = item
                valid.append((n, i + 1))
        return self.closure(valid)

    def items(self):
        """ An LR(0) item of a grammar G is a production of G with a dot at
            some position on the right hand side.
            It is represented by the rule number and the position of
            the dot
        
            @return: a set of sets of items
        """
        c = Set([self.closure(Set([(len(self.gr.rules) - 1, 0)]))])
        symbols = self.gr.terminals + self.gr.nonterminals
        e = 1
        while e:
            e = 0
            for i in c:
                for s in symbols:
                    valid = self.goto(i, s)
                    if valid != [] and valid not in c:
                        c.append(valid)
                        e = 1
        return c

    def print_items(self, c):
        """Print SLR items """
        s = ""
        j = 0
        for i in c:
            s = s + "I_%d: \n" % j
            for item in i:
                r, p = item
                lhs = self.gr.rules[r][0]
                rhs = self.gr.rules[r][1]
                s = s + "\t %s -> %s . %s \n" % (lhs, " ".join(rhs[:p]), " ".join(rhs[p:]))
            j += 1
        return s

    def NextToDot(self, item):
        """ returns symbol next to te dot or empty string"""
        n, i = item
        try:
            s = self.gr.rules[n][1][i]
        except IndexError:
            s = ""
        return s


class LR1table(LRtable):
    """
    Class for construction of a LR1 table
    
    Items are represented by a pair of integers (number of rule, position of dot)
    """

    def closure(self, items):
        """The closure of a set of C{LR(1)} items C{I} is the set of items construted
        from I by the two rules:
            - every item of C{I} is in C{closure(I)}
    
            - If C{[A -> s.Bt,a]} in C{closure(I)},for  C{B ->r} and
              each terminal C{b} in C{first(ta)}, add C{[B ->.r,b]}
              to C{closure(I)}
        """
        close = items
        e = 1
        while e:
            e = 0
            for i in close:
                s = self.NextToDot(i)
                sa = self.gr.FIRST(self.AfterDot(i))
                if s in self.gr.nonterminals and s in self.gr.ntr:
                    for n in self.gr.ntr[s]:
                        for b in sa:
                            e = close.append((n, 0, b))
        return close

    def goto(self, items, s):
        """ goto(I,X) where I is a set of items and X a grammar symbol
        is the closure of the set of all items (A -> sX.r,a) such that
        (A -> s.Xr,a) in I"""
        valid = Set([])
        for item in items:
            if self.NextToDot(item) == s:
                n, i, t = item
                valid.append((n, i + 1, t))
        return self.closure(valid)

    def items(self):
        """ An LR(1) item of a grammar G is a production of G with a dot at
            some position of the right hand side and a terminal:
            (rule_number,dot_position,terminal)
            (aho86:_compil page 231) 
        """
        c = Set([self.closure(Set([(len(self.gr.rules) - 1, 0, self.gr.endmark)]))])
        symbols = self.gr.terminals + self.gr.nonterminals
        e = 1
        while e:
            e = 0
            for i in c:
                for s in symbols:
                    valid = self.goto(i, s)
                    if valid != []:
                        if c.s_append(valid): e = 1
        return c

    def print_items(self, c):
        """Print C{LR(1)} items """
        s = ""
        j = 0
        for i in c:
            s = s + "I_%d: \n" % j
            for item in i:
                r, p, t = item
                lhs = self.gr.rules[r][0]
                rhs = self.gr.rules[r][1]
                s = s + "\t %s -> %s . %s , %s\n" % (lhs," ".join(rhs[:p]), " ".join(rhs[p:]), t)
            j += 1
        print(s)
        return s

    def NextToDot(self, item):
        """ returns symbol next to the dot or empty string"""
        n, i, t = item
        try:
            s = self.gr.rules[n][1][i]
        except IndexError:
            s = ""
        return s

    def AfterDot(self, item):
        """ returns symbol next to the dot or empty string"""
        n, i, t = item
        try:
            s = self.gr.rules[n][1][i + 1:]
        except IndexError:
            s = []
        s.append(t)
        return s

    def dotatend(self, item, i):
        n, k, t = item
        self.add_action(i, t, 'reduce', n)


class LALRtable1(LRtable):
    """Class for construction of C{LALR(1)} tables"""

    def make_action_goto(self):
        """ Make C{action[i,X]} and C{goto[i,X]}
        all pairs C{(i,s)}  not in action and goto dictionaries are 'error' """
        self.gr.DERIVE_NT()
        c = list(self.items())
        if _DEBUG:
            print(self.print_items(c))
        self.ACTION = {}
        self.GOTO = {}
        #shelve not working with osets
        #self.Log.items = c
        for i in range(len(c)):
            for item in list(c[i].keys()):
                a = self.NextToDot(item)
                if a in self.gr.terminals:
                    state = self.goto(c[i], a)
                    j = self.get_union(c, state)
                    if j != -1:
                        self.add_action(i, a, 'shift', j)
                elif a == "":
                    """ Dot at right end """
                    l = self.gr.rules[item[0]][0]
                    if l != self.gr.aug_start:
                        self.dotatend(item, c, i)
                    else:
                        """ last rule """
                        self.add_action(i, self.gr.endmark, 'accept', [])
            for s in self.gr.nonterminals:
                state = self.goto(c[i], s)
                j = self.get_union(c, state)
                if j != -1:
                    self.GOTO[(i, s)] = j

    def items(self):
        """ An C{LALR(1)} item of a grammar C{G} is a production of
        C{G}with a dot at some position of the right hand side and a
        list of terminals: is coded as a dictonary with key
        C{(rule_number,dot_position)} and value a set of terminals
        """
        i0 = {}
        i0[(len(self.gr.rules) - 1, 0)] = Set([self.gr.endmark])
        c = Set([self.closure(i0)])
        symbols = self.gr.terminals + self.gr.nonterminals
        e = 1
        while e:
            e = 0
            for i in c:
                for s in symbols:
                    if self.core_merge(c, self.goto(i, s)) == 1:
                        e = 1
        return c

    def print_items(self, c):
        """Print C{LALR(1)} items """
        s = ""
        j = 0
        for i in range(len(c)):
            s = s + "I_%d: \n" % i
            for item in list(c[i].keys()):
                r, p = item
                lhs = self.gr.rules[r][0]
                rhs = self.gr.rules[r][1]
                s = s + "\t %s -> %s . %s, %s \n" % (lhs, " ".join(rhs[:p]), " ".join(rhs[p:]), c[i][item])
        print(s)
        return s

    def goto(self, items, s):
        """ C{goto(I,X)} where C{I} is a set of items and C{X} a grammar symbol
        is the closure of the set of all items C{(A -> sX.r,a)} such that
        C{(A -> s.Xr,a)} in C{I}"""
        valid = {}
        for (n, i) in list(items.keys()):
            if self.NextToDot((n, i)) == s:
                if (n, i + 1) not in valid:
                    valid[(n, i + 1)] = Set([])
                for t in items[(n, i)]:
                    valid[(n, i + 1)].append(t)
        return self.closure(valid)


    def closure(self, items):
        """The closure of a set of C{LR(1)} items I is the set of items construted
        from I by the two rules:
           - every item of I is in closure(I)
    
           - If [A -> s.Bt,a] in closure(I),for  B ->r and each terminal b in
             first(ta), add [B ->.r,b] to closure(I)
        """
        e = 1
        while e:
            e = 0
            for i in list(items.keys()):
                s = self.NextToDot(i)
                if s in self.gr.nonterminals and s in self.gr.ntr:
                    l = self.AfterDot(i, items)
                    for n in self.gr.ntr[s]:
                        if (n, 0) not in items:
                            items[(n, 0)] = Set([])
                        if items[(n, 0)].s_extend(l) == 1:
                            e = 1
        return items

    def get_union(self, c, j):
        """ """
        for i in c:
            if list(i.keys()) == list(j.keys()):
                return c.index(i)
        return -1

    def core_merge(self, c, j):
        """ """
        if j == {} or j in c: return 0
        e = 2
        for i in c:
            if list(i.keys()) == list(j.keys()):
                e = 0
                for k in list(j.keys()):
                    if i[k].s_extend(j[k]) == 1:
                        e = 1
                break
        if e == 2:
            e = c.s_append(j)
        return e

    def NextToDot(self, item):
        """ returns symbol next to the dot or empty string"""
        n, i = item
        try:
            s = self.gr.rules[n][1][i]
        except IndexError:
            s = ""
        return s

    def AfterDot(self, item, items):
        """ returns FIRST of strings after the dot concatenated with lookahead"""
        n, i = item
        try:
            s = self.gr.rules[n][1][i + 1:]
        except IndexError:
            s = []
        sa = Set([])
        for a in items[item]:
            s.append(a)
            sa.s_extend(self.gr.FIRST(s))
            del s[len(s) - 1]
        return sa


    def dotatend(self, item, c, i):
        n, k = item
        for a in c[i][item]:
            self.add_action(i, a, 'reduce', n)


class LALRtable(LALRtable1):
    """Class for construction of LALR tables """

    def make_action_goto(self):
        """ collection of LR(0) items """
        self.gr.DERIVE_T()
        self.gr.TransClose()
        c = list(self.items())
        if _DEBUG:
            print(self.print_items(c))
        """ make action[i,X] and goto[i,X]
        all pairs (i,s)  not in action and goto dictionaries are 'error' """
        self.ACTION = {}
        self.GOTO = {}
        #shelve not working with osets
        #self.Log.items = c
        for i in range(len(c)):
            for item in list(c[i].keys()):
                C = self.NextToDot(item)
                if C in self.gr.nonterminals:
                    if C in self.gr.derive_ter:
                        for a in self.gr.derive_ter[C]:
                            if (i, a) in self.goto_ref:
                                j = self.goto_ref[(i, a)]
                                self.add_action(i, a, 'shift', j)
                    if C in self.gr.close_nt:
                        for A in list(self.gr.close_nt[C].keys()):
                            """Error: ignores end string s in C->*As"""
                            for p in self.gr.close_nt[C][A]:
                                r = self.AfterDotTer(item, c[i], p)
                                if A in self.gr.ntr:
                                    for k in self.gr.ntr[A]:
                                        if self.gr.rules[k][1] == []:
                                            for a in r:
                                                self.add_action(i, a, 'reduce', k)

                elif C in self.gr.terminals:
                    if (i, C) in self.goto_ref:
                        j = self.goto_ref[(i, C)]
                        self.add_action(i, C, 'shift', j)
                else:
                    """ Dot at right end """
                    l = self.gr.rules[item[0]][0]
                    if l != self.gr.aug_start:
                        self.dotatend(item, c, i)
                    else:
                        """ last rule """
                        self.add_action(i, self.gr.endmark, 'accept', [])
            for s in self.gr.nonterminals:
                state = self.goto(c[i], s)
                j = self.get_union(c, state)
                if j != -1:
                    self.GOTO[(i, s)] = j

    def items(self):
        """ An C{LALR(1)} kernel item of a grammar C{G} is a
        production of C{G} with a
        dot at some position of the right hand side (except the first) and a list
        of terminals: is coded as a dictionary with key 
        C{(rule_number,dot_position)} and value a set of terminals.
        """
        i0 = {}
        i0[(len(self.gr.rules) - 1, 0)] = Set([self.gr.endmark])
        c = Set([i0])
        symbols = self.gr.terminals + self.gr.nonterminals
        """ kernel LR(0) items """
        self.goto_ref = {}
        e = 1
        while e:
            e = 0
            for i in c:
                for s in symbols:
                    valid = self.goto(i, s)
                    if valid != {}:
                        if c.s_append(valid): e = 1

                        self.goto_ref[(c.index(i), s)] = c.index(valid)

        """ Discovering propagated and spontaneous lookaheads for
        kernel items k and grammar symbol s"""
        lh = {}
        for k in c:
            nk = c.index(k)
            lh[nk] = {}  #Set([])
            for (n, i) in list(k.keys()):
                lh[nk][(n, i)] = Set([])
                j = {}
                j[(n, i)] = Set([(self.gr.dummy)])
                j = self.closure(j)
                for s in symbols:
                    for (m1, j1) in list(j.keys()):
                        if self.NextToDot((m1, j1)) == s:
                            for a in j[(m1, j1)]:
                                if a == self.gr.dummy:
                                    lh[nk][(n, i)].append((self.goto_ref[(nk, s)], m1, j1 + 1))
                                else:
                                    c[self.goto_ref[(nk, s)]][(m1, j1 + 1)].append(a)
                del j
        """ Propagate lookaheads """
        #        c[0][(len(self.gr.rules) - 1,0)].s_append(self.gr.endmark)
        e = 1
        while e:
            e = 0
            for k in c:
                nk = c.index(k)
                for (n, i) in list(k.keys()):
                    for (m, n1, i1) in lh[nk][(n, i)]:
                        if c[m][(n1, i1)].s_extend(k[(n, i)]) == 1:
                            e = 1

        return c


    def goto(self, items, s):
        """ C{goto(I,X)} where I is a set of kernel items and X a
            grammar symbol is the closure of the set of all items (A
            -> sX.r,a) such that (A -> s.Xr,a) is in I"""
        valid = {}
        for (n, i) in list(items.keys()):
            x = self.NextToDot((n, i))
            if x == s:
                if (n, i + 1) not in valid:
                    valid[(n, i + 1)] = Set([])
            if x in self.gr.close_nt:
                for a in list(self.gr.close_nt[x].keys()):
                    if a in self.gr.ntr:
                        for k in self.gr.ntr[a]:
                            if self.gr.rules[k][1] != [] and self.gr.rules[k][1][0] == s:
                                valid[(k, 1)] = Set([])
        return valid

    def NextToDot(self, item):
        """ returns symbol next to the dot or empty string"""
        n, i = item
        try:
            s = self.gr.rules[n][1][i]
        except IndexError:
            s = ""
        return s

    def AfterDotTer(self, item, items, path):
        """ returns FIRST of strings after the dot
        concatenated with lookahead"""

        if path:
            p, n = path
            if not n:
                return p
        l, i = item
        try:
            f = self.gr.FIRST(self.gr.rules[l][1][i + 1:])
            ns = self.gr.nullable[" ".join(self.gr.rules[l][1][i + 1:])]
        except IndexError:
            f = []
            ns = 1
        if ns:
            return items[item]
        else:
            return f


class LogLR(object):
    """Class for LR table construction report:
        @ivar expect: number of shit/reduce conflicts expected
        @type expect: integer
        @ivar items: set of LR items
        @ivar conflicts: dictionary of conflicts occurred in LR table
                         construction: 'rr' and 'sr'
    """

    def __init__(self, noconflicts, expect):
        self.noconflicts = noconflicts
        self.expect = expect
        self.conflicts = {}
        self.items = None

    def add_conflict(self, type, i, a, value1, value2):
        try:
            self.conflicts[type].append((i, a, value1, value2))
        except KeyError:
            self.conflicts[type] = [(i, a, value1, value2)]


class LRparser(object):
    """Class for LR parser

       @ivar cfgr: context free grammar 
       @ivar rules: grammar rules
       @ivar terminals: grammar terminals
       @ivar nonterminals: grammar nonterminals
       @ivar table: LR parsing table
       @ivar ACTION: Action function
       @ivar GOTO: Goto function

       @ivar tokens: tokens to be parsed
       @ivar context: computational context
       @ivar output: list of grammar rules used for parsing C{tokens}
       (right derivation in reverse)
       @ivar stack:  LR stack with pairs C{(state,token)}
       
    """

    def __init__(self, grammar, table_shelve, no_table=1, tabletype=LALRtable, operators=None, noconflicts=1, expect=0,
                 **args):
        """
        :param grammar: is a list for productions;
        each production is a tuple *(LeftHandside,RightHandside,SemFunc,Prec?)*
        with *LeftHandside* nonterminal, *RightHandside* list of symbols,
        *SemFunc* syntax-direct semantics, if present
        *Prec (PRECEDENCE,ASSOC)* for ambiguous rules
        
        First production is for start symbol
        
        :param str table_shelve: file where parser is saved
        :param tabletype: type of LR table: C{SLR}, C{LR1}, C{LALR}
        :type tabletype: LRtable class
        :param int no_table: if 0 table_shelve is created anyway
        :param operators:  precedence and associativity for operators
        :type operators: dictionary
        :param int noconflicts: if 0 LRtable conflicts are not resolved,
        unless spcecial operator rules
        :param expect: exact number of expected LR shift/reduce conflicts
        :type expect: integer
        :param args: extra arguments; key *nosemrules* if 1 no
        semantic rules are applied
        :type args: dictionary

        """

        self.cfgr = CFGrammar(grammar)
        self.rules = self.cfgr.rules
        self.terminals = self.cfgr.terminals
        self.nonterminals = self.cfgr.nonterminals
        self.endmark = self.cfgr.endmark
        if 'nosemrules' in args:
            self.nosemrules = args['nosemrules']
        else:
            self.nosemrules = 0

        db = whichdb.whichdb(table_shelve)
        if not (db == None or db == "" or no_table == 0):
            try:
                d = shelve.open(table_shelve, 'w')
                self.ACTION = d['action']
                self.GOTO = d['goto']
                if 'version' in d:
                    if d['version'] < _Version:
                        raise TableError(table_shelve)
                try:
                    self.Log = d['log']
                except KeyError:
                    raise TableError(table_shelve)
                d.close()
            except Exception:
                if os.access(table_shelve, os.W_OK):
                    os.remove(table_shelve)
                d = {}
                self.table = tabletype(self.cfgr, operators, noconflicts, expect)
                d['version'] = _Version
                d['action'] = self.ACTION = self.table.ACTION
                d['goto'] = self.GOTO = self.table.GOTO
                d['log'] = self.Log = self.table.Log
                return
        else:
            try:
                d = shelve.open(table_shelve, 'n')
            except:
                if os.access(table_shelve, os.W_OK):
                    os.remove(table_shelve)
                try:
                    d = shelve.open(table_shelve, 'n')
                except:
                    d = {}
                    self.table = tabletype(self.cfgr, operators, noconflicts, expect)
                    d['version'] = _Version
                    d['action'] = self.ACTION = self.table.ACTION
                    d['goto'] = self.GOTO = self.table.GOTO
                    d['log'] = self.Log = self.table.Log
                    #d.close()
                    return
            self.table = tabletype(self.cfgr, operators, noconflicts, expect)
            d['version'] = _Version
            d['action'] = self.ACTION = self.table.ACTION
            d['goto'] = self.GOTO = self.table.GOTO
            d['log'] = self.Log = self.table.Log
            d.close()

    def __str__(self):
        """@return: the LR parsing table showing for each state the
        action and goto function """

        l = ([x[0] for x in list(self.ACTION.keys())])
        l.sort()
        a1 = "\nState\n"
        if len(self.terminals) < 20:
            for a in self.terminals:
                a1 += " \t%s" % a
            for i in Set(l):
                a3 = "\n%s" % i
                for a in self.terminals:
                    if (i, a) in self.ACTION:
                        if self.ACTION[i, a][0] == "shift":
                            x = "s"
                        else:
                            x = "r"
                        a2 = "\t%s%s" % (x, self.ACTION[i, a][1])
                    else:
                        a2 = "\t"
                    a3 = a3 + a2
                a1 = "%s%s" % (a1, a3)
            ac = a1
        else:
            for i in Set(l):
                a3 = "%s\n" % i
                for a in self.terminals:
                    if (i, a) in self.ACTION:
                        if self.ACTION[i, a][0] == "shift":
                            x = "s"
                        else:
                            x = "r"
                        a3 = a3 + "%s = %s%s\n" % (a, x, self.ACTION[i, a][1])
                a1 = "%s%s" % (a1, a3)
            ac = a1

        l = ([x[0] for x in list(self.GOTO.keys())])
        l.sort()
        a1 = "\nState\n"
        if len(self.nonterminals) < 20:
            for a in self.nonterminals:
                a1 = a1 + " \t%s" % a
            for i in Set(l):
                a3 = "\n%s" % i
                for a in self.nonterminals:
                    if (i, a) in self.GOTO:
                        a2 = "\t%s" % self.GOTO[(i, a)]
                    else:
                        a2 = "\t"
                    a3 = a3 + a2
                a1 = "%s%s" % (a1, a3)
        else:
            for i in Set(l):
                a3 = "%s\n" % i
                for a in self.nonterminals:
                    if (i, a) in self.GOTO:
                        a3 = a3 + "%s = %s\n" % (a, self.GOTO[(i, a)])
                a1 = "%s%s" % (a1, a3)
        go = a1
        return "Action table:\n %s\n Goto table:%s\n" % (ac, go)


    def parsing(self, tokens, context=None):
        """LR Parsing Algorithm (aho86:_compil, page 218)
        @param tokens:  pairs  (TOKEN, SPECIAL_VALUE)
        @param context: a computational context for semantic actions
        
        @return: parsed result
        """

        self.stack = Stack()
        self.stack.push((0, []))
        self.tokens = tokens
        self.tokens.append((self.endmark, self.endmark))
        self.context = context
        self.output = []
        self.ip = 0
        while 1:
            s = self.stack.top()[0]
            a = self.tokens[self.ip][0]
            if _DEBUG:
                print("Input: %s\nState: %s" % ([x[0] for x in self.tokens[self.ip:]], s))
                print("Stack: %s" % self.stack)
            try:
                if self.ACTION[s, a][0] == 'shift':
                    if _DEBUG: print("Action: shift\n")
                    self.stack.push((self.ACTION[s, a][1], self.tokens[self.ip][1]))
                    self.ip = self.ip + 1
                elif self.ACTION[s, a][0] == 'reduce':
                    n = self.ACTION[s, a][1]
                    if _DEBUG: print("Action: reduce %s %s\n" % (n, str(self.rules[n])))
                    semargs = [self.stack.pop()[1] for i in range(len(self.rules[n][1]))]
                    semargs.reverse()
                    if self.nosemrules:
                        reduce = []
                    else:
                        reduce = Reduction(self.rules[n][2], semargs, self.context)
                    del semargs
                    s1 = self.stack.top()[0]
                    a = self.rules[n][0]
                    self.stack.push((self.GOTO[s1, a], reduce))
                    self.output.append(n)
                elif self.ACTION[s, a] == ('accept', []):
                    break
                else:
                    raise LRParserError(s, a)
            except KeyError:
                if _DEBUG: print("Error in action: %s" % self.ACTION)
                raise LRParserError(s, a)
            except SemanticError as m:
                if _DEBUG: print("Semantic Rule %d %s" % (n, self.rules[n][2]))
                raise SemanticError(m, n, self.rules[n][2])
        return self.stack.top()[1]

    def parse_grammar(self, st, context, args):
        """
         Transforms a string  into a grammar description

        @param st: is a string representing the grammar rules, with
        default symbols as below. Fisrt rule for start.

        I{Example}::
             reg -> reg + reg E{lb}E{lb} self.OrSemRule   E{rb}E{rb}
             // priority 'left'|
                         ( reg ) E{lb}E{lb}self.ParSemRuleE{rb}E{rb} ;
        where:
       
         -  rulesym="->"  production symbol
         -  rhssep='' RHS symbols separator
         -  opsym='//' operator definition separator
         -  semsym=E{lb}E{lb} semantic rule start marker
         -  csemsym=E{rb}E{rb} semantic rule end marker
         -  rulesep='|' separator for multiple rules for a LHS
         -  ruleend=';' end marker for one LHS rule"""
        self.pg = Yappy_grammar(**args)
        self.pg.input(st, context)
        return self.pg.context['rules']

    def gsrules(self, rulestr, **sym):
        """
        Transforms a string  in a grammar description

        @param rulestr: is a string representing the grammar rules, with
        default symbols as below.

        @param sym: Dictionary with symbols used. Default ones:
                    -  rulesym="->"  production symbol
                    -  rhssep='' RHS symbols separator
                    -  opsym='//' operator definition separator
                    -  semsym=E{lb}E{lb} semantic rule start marker
                    -  csemsym=E{rb}E{rb} semantic rule end marker
                    -  rulesep='|' separator for multiple rules for a LHS
                    -  ruleend=';' end marker for one LHS rule
                    Example:
                    reg -> reg + reg E{lb}E{lb} self.OrSemRule // (priority,'left') E{rb}E{rb} |
                    ( reg ) E{lb}E{lb}self.ParSemRuleE{rb}E{rb} ; 
     """
        if not sym:
            sym = Dict(rulesym="->",
                       rhssep='',
                       opsym='//',
                       semsym='{{',
                       csemsym='}}',
                       rulesep='|',
                       ruleend=';')
        gr = []
        rl = rulestr.split(sym['ruleend'])
        for l in rl:
            m = re.compile(sym['rulesym']).search(l)
            if not m:
                continue
            else:
                if m.start() == 0:
                    raise GrammarError(l)
                else:
                    lhs = l[0:m.start()].strip()
                if m.end() == len(l):
                    raise GrammarError(l)
                else:
                    rhss = l[m.end():].strip()
                    if rhss == "[]":
                        rhs = []
                        sem = EmptySemRule
                        op = None
                    else:
                        rhss = l[m.end():].split(sym['rulesep'])
                        for rest in rhss:
                            rest = rest.strip()
                            if rhss == "[]":
                                rhs = []
                                sem = EmptySemRule
                                op = None
                            else:
                                m = re.search(sym['semsym'] + '(?P<opsem>.*)' + sym['csemsym'], rest)
                                if not m:
                                    rhs = rest.split()
                                    sem = DefaultSemRule
                                    op = None
                                else:
                                    if m.start() == 0:
                                        raise GrammarError(rest)
                                    else:
                                        rhs = rest[0:m.start()].strip().split()
                                    if m.group('opsem'):
                                        opsem = m.group('opsem').split(sym['opsym'])
                                        if len(opsem) == 1:
                                            sem = opsem[0].strip()
                                            op = None
                                        elif len(opsem) == 2:
                                            sem = opsem[0].strip()
                                            op = opsem[1].strip()
                                        else:
                                            raise GrammarError(rest)
                                    else:
                                        sem = DefaultSemRule
                                        op = None
                                if op == None:
                                    gr.append((lhs, rhs, eval(sem)))
                                else:
                                    gr.append((lhs, rhs, eval(sem), eval(op)))
        return gr


class LRBuildparser(object):
    """Class for LR parser: without shelve and semantic rules(obsolete)
    """

    def __init__(self, grammar):
        """
       """
        self.table = LALRtable(grammar)

    def parsing(self, tokens):
        """LR Parsing Algorithm
        """
        self.stack = Stack()
        self.stack.push(0)
        self.input = tokens
        self.input.append(self.table.gr.endmark)
        self.output = []
        self.ip = 0
        while 1:
            s = self.stack.top()
            a = self.input[self.ip]
            if (s, a) not in self.table.ACTION:
                raise LRParserError(s, a)
            elif self.table.ACTION[s, a][0] == 'shift':
                # self.stack.push(a)
                self.stack.push(self.table.ACTION[s, a][1])
                self.ip = self.ip + 1
            elif self.table.ACTION[s, a][0] == 'reduce':
                n = self.table.ACTION[s, a][1]
                for i in range(len(self.table.gr.rules[n][1])):
                    self.stack.pop()
                s1 = self.stack.top()
                a = self.table.gr.rules[n][0]
                #                self.stack.push(a)
                if (s1, a) not in self.table.GOTO:
                    raise LRParserError(s1, a)
                else:
                    self.stack.push(self.table.GOTO[s1, a])
                    self.output.append(n)
            elif self.table.ACTION[s, a] == ('accept', []):
                break
            else:
                raise LRParserError()


############# Auxiliares  ##################
def Dict(**entries):
    """Create a dict out of the argument=value arguments"""
    return entries


def grules(rules_list, rulesym="->", rhssep=None):
    """
    Transforms a list of rules in a grammar description. If a rule has
    no semantic rules, C{DefaultSemRule} is assumed.
    
    @param rules_list: is a list of pairs (rule,sem)
         where rule is a string  of the form:
           -  Word rulesym Word1 ... Word2
           -  Word rulesym []
    @param rulesym: LHS and RHS rule separator
    @param rhssep: RHS values separator (None for white chars)
    @return: a grammar description 
    """
    gr = []
    sep = re.compile(rulesym)
    for r in rules_list:
        if type(r) is str:
            rule = r
        else:
            rule = r[0]
        m = sep.search(rule)
        if not m:
            continue
        else:
            if m.start() == 0:
                raise GrammarError(rule)
            else:
                lhs = rule[0:m.start()].strip()
            if m.end() == len(rule):
                raise GrammarError(rule)
            else:
                rest = rule[m.end():].strip()
                if rest == "[]":
                    rhs = []
                else:
                    rhs = rest.split(rhssep)
        if type(r) is str:
            gr.append((lhs, rhs, DefaultSemRule))
        elif len(r) == 3:
            gr.append((lhs, rhs, r[1], r[2]))
        elif len(r) == 2:
            gr.append((lhs, rhs, r[1]))
        else:
            raise GrammarError(r)

    return gr


#######################################################

class Yappy(LRparser):
    """ A basic class for parsing.

        @ivar lex: a Lexer object
        """

    def __init__(self, tokenize, grammar, table='YappyTab', no_table=1,
                 tabletype=LALRtable, noconflicts=1, expect=0, **args):
        """@param tokenize: same as for L{Lexer}
        @param grammar: if a string C{parse_grammar} is called

        @param table: and no_table, tabletype same as for L{LRparser}

        @param args: dictionary where:
         - key C{tmpdir} is the directory where the parse table used by the Yappy Grammar is stored;
         -  key  C{usrdir} is the directory where the user tables are stored
         -  key  C{nosemrules} if 1 semantic actions are not applied"""
        self.lex = Lexer(tokenize)
        operators = None
        if "operators" in self.lex.__dict__:
            operators = self.lex.operators
        if type(grammar) is str:
            grammar = self.parse_grammar(grammar, {'locals': locals()}, args)
        if 'usrdir' in args and os.path.isdir(args['usrdir']):
            table = args['usrdir'].rstrip() + '/' + table
        if   os.path.dirname(table) == "" or os.path.exists(os.path.dirname(table)):
            LRparser.__init__(self, grammar,table, no_table, tabletype, operators, noconflicts, expect, **args)
        else:
            sys.stderr.write("Directory %s do not exist\n" % table)
            sys.exit()
        if (self.Log.noconflicts):
            if (('sr' in self.Log.conflicts and len(self.Log.conflicts['sr']) !=
                self.Log.expect)):
                print("LR conflicts: number %s value %s" % (len(self.Log.conflicts['sr']), self.Log.conflicts))
                print("""If it is Ok, set expect to the number of conflicts and build table again""")
            elif 'rr' in self.Log.conflicts:
                print("LR conflicts rr : number %s value %s" % (len(self.Log.conflicts['rr']), self.Log.conflicts['rr']))

    def input(self, str=None, context={}, lexer=0):
        """ Reads from stdin or string and retuns parsed result

            @param str: String to be parsed. If not given, reads from
            C{stdin}.
            @param context: some initial computational context
            @param lexer: if 1 only lexical analisys is performed  
            
            @return: a tuple C{(parsed result,context)} or
            only the C{parsed result}
            
        """
        if str:
            self.tokens = self.lex.scan(str)
        else:
            print("Input:  ", end=' ')
            self.tokens = self.lex.readscan()
        if lexer:
            return self.tokens
        self.context = context
        return self.parsing(self.tokens, self.context)

    def inputfile(self, FileName, context={}):
        """Reads input from file """
        try:
            file = open(FileName, "r")
        except IOError:
            raise YappyError()
        return self.input(file.read(), context)


    def parse_tree(self):
        """To be defined using output"""
        pass

    def test(self):
        """A test for each class"""
        pass


######### Semantic Grammar Rules ##############
def expandSemRule(strargs, strfun):
    regargs = re.compile(r'\$(\d+)')
    matchargs = regargs.finditer(strfun)
    for i in [(x.group(0), strargs + x.group(1) + "]") for x in matchargs]:
        strfun = string.replace(strfun, i[0], i[1])
    return strfun


def Reduction(fun, sargs, context={}):
    """Reduction function for semantic rules:
    - C{fun} can be:
      -- a function
      -- or a string with positional arguments C{$n} that is expanded
    and evaluated with C{eval}
    
    """
    if callable(fun):
        return fun(*[sargs, context])
    elif type(fun) is str:
        a = expandSemRule("sargs[", fun)
        l = context.get('locals', {})
        l.update(locals())
        return eval(a, context.get('globals', {}), l)
    else:
        raise SemanticError('Wrong type: %s' % fun)


def DefaultSemRule(sargs, context={}):
    """Default  semantic rule"""
    return sargs[0]


def EmptySemRule(sargs, context={}):
    return []


######Parser f,grammars ##################
class Yappy_grammar(Yappy):
    """ A parser for grammar rules. See C{test()} for an example. """

    def __init__(self, no_table=1, table='yappypar.tab', tabletype=LR1table, **args):
        grammar = grules([
            ("G -> RULE G", self.GRule),
            ("G -> []", EmptySemRule),
            ("RULE -> ID rulesym MULTI ruleend", self.RULERule),
            ("MULTI -> RHS rulesep MULTI", self.MULTIRule),
            ("MULTI -> RHS", self.MULTIRule),
            ("RHS -> []", EmptySemRule),  #RHS->OPSEM not allowed; epsilon-rule
            ("RHS -> RH OPSEM", self.RHSRule),
            ("RH -> ID RH", self.RHRule),
            ("RH -> ID", self.RHRule),
            ("OPSEM -> []", self.OPSEMRule),
            #      ("OPSEM -> semsym ID csemsym",self.OPSEMRule),#OPSEM->OP not allowed
            #      ("OPSEM -> semsym ID OP csemsym",self.OPSEMRule),
            ("OPSEM -> IDS", self.OPSEMRule1),
            ("OPSEM -> IDS OP", self.OPSEMRule1),
            ("OP -> opsym OPV", self.OPRule),
            ("OPV ->  ID  ID ", self.OPVRule)
        ])

        tokenize = [
            ("\{\{.*\}\}", lambda x: ("IDS", x[2:-2].strip())),
            ("\s+", ""),
            ("->", lambda x: ("rulesym", x)),
            ("\|", lambda x: ("rulesep", x)),
            (";", lambda x: ("ruleend", x)),
            #        ("}}",lambda x: ("csemsym",x)),
            #        ("{{",lambda x: ("semsym",x)),
            ("//", lambda x: ("opsym", x)),
            (".*", lambda x: ("ID", x))]
        if 'tmpdir' in args:
            args1 = {'usrdir': args['tmpdir'].rstrip('/')}
        else:
            args1 = {}
        Yappy.__init__(self, tokenize, grammar, table, no_table, **args1)


    def OPVRule(self, arg, context):
        """ """
        try:
            int(arg[0])
        except ValueError:
            raise SemanticError("Precedence must be an integer: %s given" % arg[0])
        if arg[1] != 'left' and arg[1] != 'right' and arg[1] != 'noassoc':
            raise SemanticError("Associativity must be 'left' or 'right' or 'noassoc': %s\
        given" % arg[1])
        return (int(arg[0]), arg[1])

    def OPRule(self, arg, context):
        return arg[1]

    def OPSEMRule(self, arg, context):
        if len(arg) == 4:
            return (arg[1], arg[2])
        if len(arg) == 3:
            return arg[1]
        if len(arg) == 0:
            return 'DefaultSemRule'

    def OPSEMRule1(self, arg, context):
        if len(arg) == 2:
            return (arg[0], arg[1])
        if len(arg) == 1:
            return arg[0]
        if len(arg) == 0:
            return 'DefaultSemRule'


    def RHRule(self, arg, context):
        if len(arg) == 1:
            return [arg[0]]
        if len(arg) == 2:
            return [arg[0]] + arg[1]

    def RHSRule(self, arg, context):
        return (arg[0], arg[1])

    def MULTIRule(self, arg, context):
        if len(arg) == 1:
            return [arg[0]]
        else:
            return [arg[0]] + arg[2]

    def RULERule(self, arg, context):
        lhs = arg[0]

        def grule(self, l):
            if l == []: return (lhs, [], EmptySemRule)
            if type(l[1]) is TupleType:
                return (lhs, l[0], eval(l[1][0], globals(), context['locals']), l[1][1])
            else:
                return (lhs, l[0], eval(l[1], globals(), context['locals']))

        return [grule(self, l) for l in arg[2]]

    def GRule(self, args, context):
        if 'rules' in context:
            context['rules'] = args[0] + context['rules']
        else:
            context['rules'] = args[0]
        return []

    def test(self):
        st = """
        reg -> reg + reg {{DefaultSemRule}} // 200 left  |
        reg reg {{DefaultSemRule}} // 200 left  |
        reg * {{DefaultSemRule}} |
        ( reg ) {{DefaultSemRule}} |
        id {{lambda l,c:l[0]}};
        reg -> ;
        a -> reg | reg ;
        """
        st1 = """
        reg -> reg + reg {{DefaultSemRule // 200 left}}  |
        reg reg {{DefaultSemRule // 200 left}}  |
        reg * {{DefaultSemRule}} |
        ( reg ) {{DefaultSemRule}} |
        id {{DefaultSemRule}};
        reg -> ;
        a -> reg | reg ;
        """
        self.input(st, {'locals': locals()})
        return self.context['rules']


class Stack(object):
    """ A simple class to implement stacks"""

    def __init__(self, start=[]):
        """Reverse initial stack objects"""
        self.stack = []
        for x in start: self.push(x)
        self.stack.reverse()

    def push(self, object):
        self.stack = [object] + self.stack

    def pop(self):
        if not self.stack:
            raise StackUnderflow()
        top, self.stack = self.stack[0], self.stack[1:]
        return top

    def top(self):
        """ Returns top of stack (not poping it)"""
        if not self.stack:
            raise StackUnderflow()
        return self.stack[0]

    def empty(self):
        """ Tests if stack is empty"""
        return not self.stack

    def popall(self):
        """ Empties stack"""
        self.stack = []

    def __repr__(self):
        return '[Stack:%s]' % self.stack

    def __cmp__(self, other):
        return cmp(self.stack, other.stack)

    def __len__(self):
        return len(self.stack)

    def __add__(self, other):
        return Stack(self.stack + other.stack)

    def __mul__(self, reps):
        return Stack(self.stack * reps)

    def __getitem__(self, offset):
        return self.stack[offset]

    def __getslice__(self, low, high):
        return Stack(self.stack[low: high])

    def __getattr__(self, name):
        return getattr(self.stack, name)


class Set(object):
    """ Sets: that is lists without order or repetition.

    May be used everywhere lists are used... because they rely on them."""

    def __init__(self, list=[]):
        foo = []
        for m in list:
            if not m in foo:
                foo.append(m)
        self.members = foo

    def __getitem__(self, index):
        return self.members[index]

    def __setitem__(self, index, value):
        self.members[index] = value

    def __getattr__(self, name):
        return getattr(self.members, name)

    def __add__(self, other):
        new = Set(self.members[:])
        for v in other:
            if not v in new:
                new.append(v)
        return new

    def __iadd__(self, other):
        return self + other

    def __radd__(self, other):
        return self + other

    def __sub__(self, other):
        new = Set(self.members[:])
        for v in other:
            try:
                del (new.members[new.index(v)])
            except ValueError:
                continue
        return new

    def __eq__(self, other):
        return self.__repr__() == repr(other)

    def __cmp__(self, other):
        if len(self) == len(other):
            if not len(self - other):
                return (0)
        return (1)

    def __len__(self):
        return len(self.members)

    def __str__(self):
        return str(self.members)

    def __repr__(self):
        return "Set %s" % str(self.members)

    def __getslice__(self, low, high):
        return Set(self.members[low:high])

    def __delslice__(self, low, high):
        for i in range(low, max(high + 1, len(self.members) - 1)):
            del self.members[i]

    def __delitem__(self, key):
        del self.members[key]

    def append(self, member):
        if not member in self.members:
            self.members.append(member)

    def s_append(self, member):
        e = 0
        if not member in self.members:
            self.members.append(member)
            e = 1
        return e

    def empty(self):
        return len(self.members) == 0

    def s_extend(self, other):
        e = 0
        for v in other:
            if not v in self:
                self.members.append(v)
                e = 1
        return e

    def sort(self):
        self.members.sort()

    def index(self, index):
        return self.members.index(index)

    def remove(self, v):
        try:
            del (self.members[self.index(v)])
        except ValueError:
            pass

    def copy(self):
        return Set(self.members[:])

    def first(self):
        return self.members[0]

    # duplicates a set (shallow copy)
    def dup(self):
        new = Set()
        new.members = self.members[:]
        return new
