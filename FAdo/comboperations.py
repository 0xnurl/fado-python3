# -*- coding: utf-8 -*-
"""**Several combined operations for DFAs**

Deterministic and non-deterministic automata manipulation, conversion and evaluation.

*Authors:* Rogério Reis & Nelma Moreira

*This is part of FAdo project*   http://fado.dcc.fc.up.pt

*Version:* 0.9.5

.. versionadded: 0.9.4

*Copyright:* 1999-2012 Rogério Reis & Nelma Moreira {rvr,nam}@dcc.fc.up.pt


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

from future import standard_library
standard_library.install_aliases()
from builtins import *
from .fa import *
from .common import *


def starConcat(fa1, fa2, strict=False):
    """ Star of concatenation of two languages: (L1.L2)*

    :param fa1: first automaton
    :param fa2: second automaton
    :param strict: should the alphabets be necessary equal?
    :type strict: Boolean
    :type fa1: DFA
    :type fa2: DFA
    :rtype: DFA

    .. seealso::
       Yuan Gao, Kai Salomaa, and Sheng Yu. 'The state complexity of two combined operations: Star of catenation and
       star of reversal'. Fundamenta Informaticae, 83:75–89, Jan 2008."""
    if strict and fa1.Sigma != fa2.Sigma:
        raise DFAdifferentSigma
    NSigma = fa1.Sigma.union(fa2.Sigma)
    d1, d2 = fa1.dup(), fa2.dup()
    d1.setSigma(NSigma)
    d2.setSigma(NSigma)
    d1.complete()
    d2.complete()
    if len(d1.States) > 1 and len(d2.States) == 1:
        if d2.finalP(d2.Initial):
            new = d1.addState()
            iold = d1.Initial
            d1.setInitial(new)
            d1.addFinal(new)
            for sym in d1.Sigma:
                d1.addTransition(new, sym, d1.delta[iold][sym])
                for s in d1.Final:
                    d1.delta[s][sym] = s
            return d1
        c = DFA()
        c.setSigma(d1.Sigma)
        s0, s1 = c.addState(0), c.addState(1)
        c.setInitial(s0)
        c.addFinal(s0)
        for sym in c.Sigma:
            c.addTransition(s0, sym, s1)
            c.addTransition(s1, sym, s1)
        return c
    if len(d2.States) > 1 and len(d1.States) == 1:
        if d1.finalP(d1.Initial):
            c = NFA()
            c.setSigma(d2.Sigma)
            c.States = d2.States[:]
            p1 = c.addState(0)
            p2 = c.addState(1)
            c.addInitial(p1)
            c.setFinal(list(d2.Final))
            for sym in c.Sigma:
                c.addTransition(p1, sym, d2.delta[d2.Initial][sym])
                c.addTransition(p1, sym, p2)
                c.addTransition(p2, sym, d2.delta[d2.Initial][sym])
                c.addTransition(p2, sym, p2)
                for s in d2.States:
                    c.addTransition(s, sym, d2.delta[s][sym])
            return c.toDFA()
            # Epsilon automaton
        c = DFA()
        c.setSigma(d1.Sigma)
        s0, s1 = c.addState(0), c.addState(1)
        c.setInitial(s0)
        c.addFinal(s0)
        for sym in c.Sigma:
            c.addTransition(s0, sym, s1)
            c.addTransition(s1, sym, s1)
        return c
    c = DFA()
    c.setSigma(d1.Sigma)
    lStates = []
    i = c.addState("initial")
    c.setInitial(i)
    c.addFinal(i)
    lStates.append(i)
    for sym in c.Sigma:
        s1 = {d1.evalSymbol(d1.Initial, sym)}
        s2 = set([])
        #Z1
        if s1 & d1.Final != set([]):
            s2.add(d2.Initial)
            if d2.finalP(d2.Initial):
                s1.add(d1.Initial)
        if d1.finalP(d1.Initial):
            s2.add(d2.evalSymbol(d2.Initial, sym))
            #Z2
            if s2 & d2.Final != set([]):
                s1.add(d1.Initial)
                s2.add(d2.Initial)
        stn = (s1, s2)
        if stn not in lStates:
            lStates.append(stn)
            new = c.addState(stn)
            if stn[1] & d2.Final != set([]):
                c.addFinal(new)
        else:
            new = c.stateIndex(stn)
        c.addTransition(i, sym, new)
    if len(c.States) == 1:
        return c
    j = 1
    while True:
        stu = lStates[j]
        s = c.stateIndex(stu)
        for sym in c.Sigma:
            stn = (d1.evalSymbolL(stu[0], sym),
                   d2.evalSymbolL(stu[1], sym))
            if stn[0] & d1.Final != set([]):
                stn[1].add(d2.Initial)
                if d2.finalP(d2.Initial):
                    stn[0].add(d1.Initial)
            if stn[1] & d2.Final != set([]):
                stn[0].add(d1.Initial)
                if d1.finalP(d1.Initial):
                    stn[1].add(d2.Initial)
            if stn not in lStates:
                lStates.append(stn)
                new = c.addState(stn)
                if stn[1] & d2.Final != set([]):
                    c.addFinal(new)
            else:
                new = c.stateIndex(stn)
            c.addTransition(s, sym, new)
        if j == len(lStates) - 1:
            break
        else:
            j += 1
    return c


def concatWStar(fa1, fa2, strict=False):
    """Concatenation combined with star: (L1.L2*)

    :param fa1: first automaton
    :param fa2: second automaton
    :param strict: should the alphabets be necessary equal?
    :type strict: bool
    :type fa1: DFA
    :type fa2: DFA
    :rtype: DFA

    .. seealso::
       Bo Cui, Yuan Gao, Lila Kari, and Sheng Yu. 'State complexity of two combined operations: Reversal-catenation
       and star-catenation'. CoRR, abs/1006.4646, 2010."""
    if len(fa1.States) == 0 or len(fa1.Final) == 0 or len(fa2.States) == 0 or len(fa2.Final) == 0 or \
       (len(fa1.States) == 1 and len(fa2.States) > 0):
        return fa1
    if strict and fa1.Sigma != fa2.Sigma:
        raise DFAdifferentSigma
    NSigma = fa1.Sigma.union(fa2.Sigma)
    d1, d2 = fa1.dup(), fa2.dup()
    d1.setSigma(NSigma)
    d2.setSigma(NSigma)
    d1.complete()
    d2.complete()
    if len(d2.Final) == 1 and d2.finalP(d2.Initial):
        return d1.concat(d2)
    c = DFA()
    c.setSigma(d1.Sigma)
    lStates = []
    if d1.finalP(d1.Initial):
        s2 = 1
    else:
        s2 = 0
    i = (d1.Initial, s2, set([]))
    lStates.append(i)
    j = c.addState(i)
    c.setInitial(j)
    if s2 == 1:
        c.addFinal(j)
    F0 = d2.Final - {d2.Initial}
    while True:
        stu = lStates[j]
        s = c.stateIndex(stu)
        for sym in c.Sigma:
            s1 = d1.evalSymbol(stu[0], sym)
            if d1.finalP(s1):
                s2 = 1
            else:
                s2 = 0
            if stu[1] == 1:
                s3 = {d2.evalSymbol(d2.Initial, sym)}
                # correction
                if s3 & F0 != set([]):
                    s3.add(d2.Initial)
            else:
                s3 = set([])
            s4 = d2.evalSymbolL(stu[2], sym)
            if s4 & F0 != set([]):
                s4.add(d2.Initial)
            stn = (s1, s2, s3.union(s4))
            if stn not in lStates:
                lStates.append(stn)
                new = c.addState(stn)
                if stn[1] == 1 or (d2.Final & stn[2] != set([])):
                    c.addFinal(new)
            else:
                new = c.stateIndex(stn)
            c.addTransition(s, sym, new)
        if j == len(lStates) - 1:
            break
        else:
            j += 1
    return c


def starWConcat(fa1, fa2, strict=False):
    """Star combined with concatenation: (L1*.L2)

    :param fa1: first automaton
    :param fa2: second automaton
    :param strict: should the alphabets be necessary equal?
    :type strict: Boolean
    :type fa1: DFA
    :type fa2: DFA
    :rtype: DFA

    .. seealso::
       Bo Cui, Yuan Gao, Lila Kari, and Sheng Yu. 'State complexity of catenation combined with star and reversal'.
       CoRR, abs/1008.1648, 2010"""
    if len(fa1.States) == 0 or len(fa1.Final) == 0 or len(fa2.States) == 0 or len(fa2.Final) == 0 \
       or (len(fa2.States) == 1 and len(fa1.States) > 0):
        return fa2
    if strict and fa1.Sigma != fa2.Sigma:
        raise DFAdifferentSigma
    NSigma = fa1.Sigma.union(fa2.Sigma)
    d1, d2 = fa1.dup(), fa2.dup()
    d1.setSigma(NSigma)
    d2.setSigma(NSigma)
    d1.complete()
    d2.complete()
    c = DFA()
    c.setSigma(d1.Sigma)
    if len(d1.Final) == 1 and d1.finalP(d1.Initial):
        i = (d1.Initial, {d2.Initial})
        j = c.addState(i)
        c.setInitial(j)
        if i[1] & d2.Final != set([]):
            c.addFinal(j)
        while True:
            s = c.States[j]
            for sym in c.Sigma:
                stn = (d1.evalSymbol(s[0], sym), d2.evalSymbolL(s[1], sym))
                if d1.initialP(s[0]):
                    stn[1].add(d2.Initial)
                try:
                    new = c.addState(stn)
                    if stn[1] & d2.Final != set([]):
                        c.addFinal(new)
                except DuplicateName:
                    new = c.stateIndex(stn)
                c.addTransition(s, sym, new)
            if j == len(c.States) - 1:
                break
            else:
                j += 1
        return c
        #  |Final1|>1
    j = c.addState(({d1.Initial}, {d2.Initial}))
    c.setInitial(j)
    if d2.finalP(d2.Initial):
        c.addFinal(j)
    while True:
        s = c.States[j]
        for sym in c.Sigma:
            stn = (d1.evalSymbolL(s[0], sym), d2.evalSymbolL(s[1], sym))
            if stn[0] & d1.Final != set([]):
                stn[1].add(d2.Initial)
                stn[0].add(d1.Initial)
            try:
                new = c.addState(stn)
                if stn[1] & d2.Final != set([]):
                    c.addFinal(new)
            except DuplicateName:
                new = c.stateIndex(stn)
            c.addTransition(j, sym, new)
        if j == len(c.States) - 1:
            break
        else:
            j += 1
    return c


def starDisj(fa1, fa2, strict=False):
    """Star of Union of two DFAs: (L1 + L2)*

    :param fa1: first automaton
    :param fa2: second automaton
    :param strict: should the alphabets be necessary equal?
    :type strict: Boolean
    :type fa1: DFA
    :type fa2: DFA
    :rtype: DFA

    .. seealso::
       Arto Salomaa, Kai Salomaa, and Sheng Yu. 'State complexity of combined operations'. Theor. Comput. Sci.,
       383(2-3):140–152, 2007."""
    if strict and fa1.Sigma != fa2.Sigma:
        raise DFAdifferentSigma
    NSigma = fa1.Sigma.union(fa2.Sigma)
    d1, d2 = fa1.dup(), fa2.dup()
    d1.setSigma(NSigma)
    d2.setSigma(NSigma)
    d1.complete()
    d2.complete()
    c = DFA()
    c.setSigma(NSigma)
    lStates = []
    if d1.Initial in d1.Final or d2.Initial in d2.Final:
        i = ({d1.Initial}, {d2.Initial})
    else:
        i = "initial"
    lStates.append(i)
    j = c.addState(i)
    c.setInitial(j)
    c.addFinal(j)
    for sym in c.Sigma:
        stn = ({d1.evalSymbol(d1.Initial, sym)}, {d2.evalSymbol(d2.Initial, sym)})
        if stn[0] & d1.Final or stn[1] & d2.Final:
            stn[0].add(d1.Initial)
            stn[1].add(d2.Initial)
        if stn not in lStates:
            lStates.append(stn)
            new = c.addState(stn)
            if stn[0] & d1.Final or stn[1] & d2.Final:
                c.addFinal(new)
        else:
            new = c.stateIndex(stn)
        c.addTransition(j, sym, new)
    if len(lStates) < 2:
        return c
    j = 1
    while True:
        stu = lStates[j]
        s = c.stateIndex(stu)
        for sym in c.Sigma:
            stn = (d1.evalSymbolL(stu[0], sym), d2.evalSymbolL(stu[1], sym))
            if stn[0] & d1.Final or stn[1] & d2.Final:
                stn[0].add(d1.Initial)
                stn[1].add(d2.Initial)
            if stn not in lStates:
                lStates.append(stn)
                new = c.addState(stn)
                if stn[0] & d1.Final or stn[1] & d2.Final:
                    c.addFinal(new)
            else:
                new = c.stateIndex(stn)
            c.addTransition(s, sym, new)
        if j == len(lStates) - 1:
            break
        else:
            j += 1
    return c


def starInter0(fa1, fa2, strict=False):
    """Star of Intersection  of two DFAs: (L1 & L2)*

    :param fa1: first automaton
    :param fa2: second automaton
    :param strict: should the alphabets be necessary equal?
    :type strict: Boolean
    :type fa1: DFA
    :type fa2: DFA
    :rtype: DFA

    .. seealso::
       Arto Salomaa, Kai Salomaa, and Sheng Yu. 'State complexity of combined operations'. Theor. Comput. Sci.,
       383(2-3):140–152, 2007."""
    if strict and fa1.Sigma != fa2.Sigma:
        raise DFAdifferentSigma
    NSigma = fa1.Sigma.union(fa2.Sigma)
    d1, d2 = fa1.dup(), fa2.dup()
    d1.setSigma(NSigma)
    d2.setSigma(NSigma)
    d1.complete()
    d2.complete()
    c = DFA()
    c.setSigma(NSigma)
    lStates = []
    if d1.finalP(d1.Initial) and d2.finalP(d2.Initial):
        i = ({d1.Initial}, {d2.Initial})
    else:
        i = "initial"
    lStates.append(i)
    j = c.addState(i)
    c.setInitial(j)
    c.addFinal(j)
    for sym in c.Sigma:
        stn = ({d1.evalSymbol(d1.Initial, sym)}, {d2.evalSymbol(d2.Initial, sym)})
        if stn[0] & d1.Final and stn[1] & d2.Final:
            stn[0].add(d1.Initial)
            stn[1].add(d2.Initial)
        if stn not in lStates:
            lStates.append(stn)
            new = c.addState(stn)
            if stn[0] & d1.Final and stn[1] & d2.Final:
                c.addFinal(new)
        else:
            new = c.stateIndex(stn)
        c.addTransition(j, sym, new)
    if len(lStates) < 2:
        return c
    j = 1
    while True:
        stu = lStates[j]
        s = c.stateIndex(stu)
        for sym in c.Sigma:
            stn = (d1.evalSymbolL(stu[0], sym), d2.evalSymbolL(stu[1], sym))
            if stn[0] & d1.Final and stn[1] & d2.Final:
                stn[0].add(d1.Initial)
                stn[1].add(d2.Initial)
            if stn not in lStates:
                lStates.append(stn)
                new = c.addState(stn)
                if stn[0] & d1.Final and stn[1] & d2.Final:
                    c.addFinal(new)
            else:
                new = c.stateIndex(stn)
            c.addTransition(s, sym, new)
        if j == len(lStates) - 1:
            break
        else:
            j += 1
    return c


def starInter(fa1, fa2, strict=False):
    """Star of Intersection  of two DFAs: (L1 & L2)*

    :param fa1: first automaton
    :param fa2: second automaton
    :param strict: should the alphabets be necessary equal?
    :type strict: Boolean
    :type fa1: DFA
    :type fa2: DFA
    :rtype: DFA """
    if strict and fa1.Sigma != fa2.Sigma:
        raise DFAdifferentSigma
    NSigma = fa1.Sigma.union(fa2.Sigma)
    d1, d2 = fa1.dup(), fa2.dup()
    d1.setSigma(NSigma)
    d2.setSigma(NSigma)
    d1.complete()
    d2.complete()
    c = DFA()
    c.setSigma(NSigma)
    lStates = []
    if d1.finalP(d1.Initial) and d2.finalP(d2.Initial):
        i = {(d1.Initial, d2.Initial)}
    else:
        i = "initial"
    lStates.append(i)
    j = c.addState(i)
    c.setInitial(j)
    c.addFinal(j)
    for sym in c.Sigma:
        stn = {(d1.evalSymbol(d1.Initial, sym), d2.evalSymbol(d2.Initial, sym))}
        for sub in stn:
            if d1.finalP(sub[0]) and d2.finalP(sub[1]):
                stn.add((d1.Initial, d2.Initial))
                break
        if stn not in lStates:
            lStates.append(stn)
            new = c.addState(stn)
            for sub in stn:
                if d1.finalP(sub[0]) and d2.finalP(sub[1]):
                    c.addFinal(new)
                    break
        else:
            new = c.stateIndex(stn)
        c.addTransition(j, sym, new)
    if len(lStates) < 2:
        return c
    j = 1
    while True:
        stu = lStates[j]
        s = c.stateIndex(stu)
        for sym in c.Sigma:
            stn = set([])
            flag = 1
            for sub in stu:
                one = (d1.evalSymbol(sub[0], sym), d2.evalSymbol(sub[1], sym))
                stn.add(one)
                if flag == 1 and d1.finalP(one[0]) and d2.finalP(one[1]):
                    stn.add((d1.Initial, d2.Initial))
                    flag = 0
            if stn not in lStates:
                lStates.append(stn)
                new = c.addState(stn)
                for sub in stn:
                    if d1.finalP(sub[0]) and d2.finalP(sub[1]):
                        c.addFinal(new)
                        break
            else:
                new = c.stateIndex(stn)
            c.addTransition(s, sym, new)
        if j == len(lStates) - 1:
            break
        else:
            j += 1
    return c


def disjWStar(f1, f2, strict=True):
    """Union with star: (L1 + L2*)

    :param f1: first automaton
    :param f2: second automaton
    :param strict: should the alphabets be necessary equal?
    :type strict: Boolean
    :type f1: DFA
    :type f2: DFA
    :rtype: DFA

    .. seealso::
       Yuan Gao and Sheng Yu. 'State complexity of union and intersection combined with star and reversal'. CoRR,
       abs/1006.3755, 2010."""
    if strict and f1.Sigma != f2.Sigma:
        raise DFAdifferentSigma
    return f1.star() | f2


def interWStar(f1, f2, strict=True):
    """Intersection with star: (L1 & L2*)

    :param f1: first automaton
    :param f2: second automaton
    :param strict: should the alphabets be necessary equal?
    :type strict: Boolean
    :type f1: DFA
    :type f2: DFA
    :rtype: DFA

    .. seealso::
       Yuan Gao and Sheng Yu. 'State complexity of union and intersection combined with star and reversal'. CoRR,
       abs/1006.3755, 2010."""
    if strict and f1.Sigma != f2.Sigma:
        raise DFAdifferentSigma
    return f1.star() & f2
