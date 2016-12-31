# -*- coding: utf-8 -*-
"""** Families of Languages **
"""
from __future__ import absolute_import
from __future__ import unicode_literals
from __future__ import print_function
from __future__ import division

from future import standard_library
standard_library.install_aliases()
from builtins import range
from builtins import *
from .fa import *

from .common import TestsError

def evenParity(n=3, sigma=["a", "b"]):
    """
     Words of length n with even number of sigma[1]s
    """
    if len(sigma) != 2:
        raise TestsError("Size of alphabet must be 2")
    a = DFA()
    a.setSigma(set(sigma))
    a.setInitial(a.addState("initial"))
    if n == 0:
        a.addFinal(0)
        return a
    e = a.addState((1, 0))
    o = a.addState((1, 1))
    a.addTransition(0, sigma[0], e)
    a.addTransition(0, sigma[1], o)
    for i in range(2, n):
        e = a.addState((i, 0))
        o = a.addState((i, 1))
        a.addTransition(a.stateIndex((i - 1, 0)), sigma[0], e)
        a.addTransition(a.stateIndex((i - 1, 0)), sigma[1], o)
        a.addTransition(a.stateIndex((i - 1, 1)), sigma[1], e)
        a.addTransition(a.stateIndex((i - 1, 1)), sigma[0], o)
    f = a.addState(len(a.States))
    a.addTransition(a.stateIndex((n - 1, 1)), sigma[1], f)
    a.addTransition(a.stateIndex((n - 1, 0)), sigma[0], f)
    a.addFinal(f)
    return a
