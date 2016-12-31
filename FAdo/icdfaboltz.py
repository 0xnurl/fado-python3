# -*- coding: utf-8 -*-
"""ICDFA Boltzmann generator

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
from __future__ import print_function
from __future__ import absolute_import
from __future__ import unicode_literals
from __future__ import division

from future import standard_library
standard_library.install_aliases()
from builtins import range
from builtins import *
from .boltzmann import *
from functools import reduce

debug = 0


def genficdfas(n, k):
    """

    :param n:
    :param k:
    :return: """

    def shiftFlags(n):
        """

        :param n: """
        global initial_flags
        if not n:
            flags[0] -= 1
        else:
            if flags[n] - 1 == flags[n - 1]:
                flags[n] = initial_flags[n]
                shiftFlags(n - 1)
            else:
                flags[n] -= 1

    def setFlags(states, symbols):
        """

        :param states:
        :param symbols: """
        global initial_flags
        for i in range(1, states):
            flags.append(symbols * i - 1)
        initial_flags = copy.deepcopy(flags)

    def islast(n, _):
        """

        :param n:
        :param _:
        :return: """
        for i in range(n - 1):
            if flags[i] != i:
                return 0
        return 1

    def genflags(n, _):
        """

        :param n:
        :param _:
        """
        nf = 1
        flags = []
        setFlags(n, k)
        print(flags)
        while not islast(n, k):
            shiftFlags(n - 2)
            nf += 1
            print(flags)
        print(nf)

    def genficdfa(n, _):
        """

        :param n:
        :param _:
        :return: """
        r1 = singleton(0)
        if flags[0]:
            g = reduce(prod, [r1 for _ in range(1, flags[0] + 1)])
        else:
            g = None
        for j in range(1, n):
            r1 = union(r1, singleton(j))

            if flags[j] - flags[j - 1] > 1:
                if g:
                    g = prod(g, prod(singleton(j), reduce(prod, [r1 for _ in
                                                          range(flags[j] - flags[j - 1] - 1)])))
                else:
                    g = prod(singleton(j), reduce(prod,
                                                  [r1 for _ in range(flags[j] - flags[j - 1] - 1)]))
            else:
                if g:
                    g = prod(g, singleton(j))
                else:
                    g = singleton(j)
        if debug:
            print(g)
        return g

    nf = 1
    flags = []
    initial_flags = []
    setFlags(n, k)
    flags = flags + [n * k]
    if debug:
        print(flags)
    ic = genficdfa(n, k)
    while not islast(n, k):
        shiftFlags(n - 2)
        if debug:
            print(flags)
        ic = union(ic, genficdfa(n, k))
        nf += 1
    if debug:
        print(nf)
    return ic


def genr1(n, k):
    """

    :param n:
    :param k:
    :return: """
    r1 = singleton(0)
    g = seq(r1)
    for j in range(1, n):
        r1 = union(r1, singleton(j))
        g = prod(g, prod(singleton(j), seq(r1)))
    return g

###using recursive formulas
nr = {}


def create_nr(k, n, t=0):
    """ t not treated"""
    nr[(k, n)] = {}
    for i in range((n - 1) * k - 1, n - 3, -1):
        r = reduce(union, [singleton(j) for j in range(n)])
        nr[(k, n)][(n - 1, i)] = prod(singleton(n - 1),
                                      reduce(prod, [r for j in range(n * k - 1 - i)]))

        #(n+t)**(k*n-1-i)
    for m in range(n - 2, 0, -1):
        for j in range(m * k - 1, m - 2, -1):
            r0 = reduce(union, [singleton(i) for i in range(m)])
            uu = union(nr[(k, n)][(m + 1, j + 1)], reduce(union,
                                                          [prod(reduce(prod, [r0 for l in range(i)]),
                                                                nr[(k, n)][(m + 1, j + i + 1)]) for i in range(1, k)]))

            nr[(k, n)][(m, j)] = prod(singleton(m), uu)

            #######################################

            #  for m in range(n-2,0,-1):

#     r0 = reduce(union,[singleton(i) for i in xrange(m)])
#     uu=union(nr[(k,n)][(m+1,m*k)], reduce(union,
#           [prod(reduce(prod,[r0 for l in range(i)]),nr[(k,n)][(m+1,m*k+i)])   for i in xrange(1,k)]))
#     nr[(k,n)][(m,m*k-1)] =prod(singleton(m),uu)
#     #sum([nt[(k,n)][(m+1,m*k+i)]*(m+1+t)**(i) for i in range(k)])
#     for i in range(m*k-2,m-2,-1):
#       nr[(k,n)][(m,i)] = union(prod(r0,nr[(k,n)][(m,i+1)]),nr[(k,n)][(m+1,i+1)])

def gen_icdfas(k, n, t=0):
    """ """
    create_nr(k, n, t)
    r0 = nr[(k, n)][(1, 0)]
    uu = reduce(union, [prod(reduce(prod, [singleton(0) for j in range(l)]), nr[(k, n)][(1, l)])
                        for l in range(1, k)])
    return union(r0, uu)


def test_23(m, x):
    a = singleton(0)
    b = singleton(1)
    c = singleton(2)
    ab = union(a, b)
    abc = union(a, union(b, c))
    r = union(prod(union(prod(a, b), prod(b, ab)), prod(union(prod(ab, c), prod(c, abc)), prod(abc, abc))),
              prod(b, prod(c, prod(abc, prod(abc, prod(abc, abc))))))
    print(r)
    for i in range(m):
        print(r.sampler(x))


def test_(k, n, m, x):
    a = gen_icdfas(k, n)
    #f=a.nfaPosition().toDFA().minimal()
    #print len(f.States)
    for i in range(m):
        print(a.sampler(x))

###Use: test_(k,n,m,x=0.5)
