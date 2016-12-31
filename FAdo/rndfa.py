    # -*- coding: utf-8 -*-
"""**Random DFA generation**

ICDFA Random generation binding

.. *Authors:* Rogério Reis & Nelma Moreira

.. *This is part of FAdo project*  http://fado.dcc.fc.up.pt

.. *Version:* 0.9.8

.. *Copyright:* 1999-2013 Rogério Reis & Nelma Moreira {rvr,nam}@dcc.fc.up.pt

.. versionchanged:: 0.9.4 Interface python to the C code

.. versionchanged:: 0.9.6 Working with incomplete automata

.. versionchanged:: 0.9.8 distinct classes for complete and incomplete ICDFA

.. Contributions by
  - Marco Almeida

..  This program is free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA."""
from __future__ import absolute_import
from __future__ import division
from __future__ import unicode_literals
from __future__ import print_function

from future import standard_library
standard_library.install_aliases()
from builtins import next
from builtins import *
from past.utils import old_div
from builtins import object
import generator
from . import fa
from .common import *


class ICDFArgen(object):
    """Generic ICDFA random generator class

    .. seealso:: Marco Almeida, Nelma Moreira, and Rogério Reis. Enumeration and generation with a string automata
       representation. Theoretical Computer Science, 387(2):93-102, 2007"""
    def __next__(self):
        """Get the next generated DFA

        :returns: a random generated ICDFA
        :rtype: DFA"""
        a = next(self.gen)
        return fa.stringToDFA(a[0], a[1], self.n, self.k)


class ICDFArnd(ICDFArgen):
    """ Complete ICDFA random generator class

    This is the class for the uniform random generator for Initially Connected DFAs

    :var n: number of states
    :type n: integer
    :var k: size of the alphabet
    :type k: integer

    .. note::
        This is an abstract class, not to be used directly"""

    def __init__(self, n, k):
        self.gen = generator.icdfaRndGen(n, k)
        self.n, self.k = n, k

    def __str__(self):
        return "ICDFArnd %d %d" % (self.n, self.k)


class ICDFArndIncomplete(ICDFArgen):
    """ Incomplete ICDFA random generator class

    :var n: number of states
    :type n: integer
    :var k: size of alphabet
    :type k: integer
    :var bias: how often must the gost sink state appear (default None)
    :type bias: float

    :raises IllegalBias: if a bias >=1 or <=0 is provided"""
    def __init__(self, n, k, bias=None):
        if bias is None:
            self.gen = generator.icdfaRndGen(n, k, 1, 1)
        elif bias <= 0 or bias >= 1:
            raise IllegalBias()
        else:
            m = int(old_div((bias * n), (1 - bias)))
            self.gen = generator.icdfaRndGen(n, k, 1, m)
        self.n, self.k, self.bias = n, k, bias

    def __str__(self):
        return "ICDFArndIncomplete %d %d %d"%(self.n, self.k, self.bias)