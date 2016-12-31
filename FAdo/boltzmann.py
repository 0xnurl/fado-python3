# -*- coding: utf-8 -*-
""" General Boltzmann Generator environment

@author: Rogério Reis & Nelma Moreira

This is part of U{FAdo project <http://www.ncc.up.pt/FAdo>}.

@version: 0.9.5

Regular expression classes and manipulation

@copyright: 1999-2011 Rogério Reis & Nelma Moreira {rvr,nam}@dcc.fc.up.pt

B{Naming convention:} methods suffixed by P have boolean return.

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
Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA."""
from __future__ import division
from __future__ import unicode_literals
from __future__ import print_function
from __future__ import absolute_import

from future import standard_library
standard_library.install_aliases()
from builtins import str
from builtins import range
from builtins import *
from past.utils import old_div
import random
import math

from FAdo.reex import *


class emptyword(epsilon):
    def generating(self, x):
        return x

    def generating_s(self, x):
        return str(x)

    def sampler(self, x):
        """ None if empty"""
        return [epsilon()]


class singleton(regexp):
    def generating(self, x):
        return x

    def generating_s(self, x):
        return str(x)

    def sampler(self, x):
        """ None if empty"""
        return [self.val]


class union(disj):
    def __init__(self, *args):
        self.gen = {}
        disj.__init__(self, *args)

    def generating(self, x):
        return self.gen.setdefault(x, self.arg1.generating(x) + self.arg2.generating(x))

    def generating_s(self, x):
        return "(" + str(self.arg1.generating_s(x)) + "+" + str(self.arg2.generating_s(x)) + ")"

    def sampler(self, x):
        pa = self.arg1.generating(x) * 1.0 / (self.arg1.generating(x) + self.arg2.generating(x))
        if rnd_bernoulli(pa):
            return self.arg1.sampler(x)
        else:
            return self.arg2.sampler(x)


class prod(concat):
    def __init__(self, *args):
        self.gen = {}
        concat.__init__(self, *args)

    def generating(self, x):
        return self.gen.setdefault(x, self.arg1.generating(x) * self.arg2.generating(x))

    def generating_s(self, x):
        return str(self.arg1.generating_s(x)) + "*" + str(self.arg2.generating_s(x))

    def sampler(self, x):
        return self.arg1.sampler(x) + self.arg2.sampler(x)

    def string(self):
        return "(%s.%s)" % (self.arg1, self.arg2)


class seq(star):
    def __init__(self, *args):
        self.gen = {}
        star.__init__(self, *args)

    def generating(self, x):
        return self.gen.setdefault(x, old_div(1.0, (1 - self.arg.generating_s(x))))

    def generating_s(self, x):
        return str(1) + "/(" + str(1) + "-" + str(self.arg.generating_s(x)) + ")"

    def sampler1(self, x):
        if rnd_bernoulli(self.arg.generating(x)):
            a = self.sampler1(x)
            if a:
                return [self.arg.sampler(x)] + a
            else:
                return [self.arg.sampler(x)]
        else:
            return epsilon()

    def sampler(self, x):
        k = rnd_geometric(self.arg.generating(x))
        return [self.arg.sampler(x) for i in range(k + 1)]


    def string(self):
        return "(%s)*" % self.arg


def rnd_bernoulli(p):
    """
  p(0) = 1 - p; p(1) = p
  """
    u = random.random()
    if u <= p:
        return 1
    else:
        return 0


def rnd_bernoulli_l(l):
    """
  sum(l)=1

  """
    u = random.random()
    k = len(l)
    p = 0
    for i in range(k):
        p += l[i][0]
        if u <= p:
            return l[i][1](i)


def rnd_geometric(p):
    """
  p(k) =  p(1-p)^(k-1)
  """
    if p == 1 or p == 0:
        raise Exception
    u = random.random()
    pk = 1 - p
    s = 0
    k = 0
    while u > s:
        s += pk
        pk *= p
        k += 1
    return k


def rnd_geometric0(p):
    """
  p(k) =  p(1-p)^(k-1)

  """

    u = random.random()
    if p == 1:
        return 1
    else:
        return int(old_div(math.log(u), math.log(1 - p))) + 1


def rnd_poisson(l, t=0):
    """
  p(k) = {\mu^k \over k!} \exp(-\mu)
  """
    u = random.random()
    p = math.exp(-l)
    k = 0
    s = 0
    while u < s:
        s += p
        k += 1
        p = 1.0 * l * p / (k + 1)
    return k


def reject(g, x, n, e=0):
    while 1:
        a = g.sampler(x)
        if n * (1 - e) <= len(a) <= n * (1 + e):
            return a


def qui(k):
    return k * (1 - old_div(1, (math.exp(k))) + (old_div(k, math.exp(2 * k))))
