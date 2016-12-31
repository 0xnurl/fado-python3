# -*- coding: utf-8 -*-
"""Hopcroft's Union & Find data structure

.. *Authors: Rogério Reis & Nelma Moreira

.. *This is part of FAdo project*  http://www.ncc.up.pt/FAdo.


.. *copyright:* 1999-2011 Rogério Reis & Nelma Moreira {rvr,nam}@dcc.fc.up.pt

.. *Contributions by* - Marco Almeida


.. This program is free software; you can redistribute it and/or modify
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
from __future__ import unicode_literals
from __future__ import division
from __future__ import absolute_import


from future import standard_library
standard_library.install_aliases()
from builtins import range
from builtins import *
from builtins import object
class UnionFind(object):
    """ Classical Union/Finf data structure """
    def __init__(self, auto_create=False):
        self.p = {}
        self.rank = {}
        self.auto_create = auto_create

    def make_set(self, x):
        self.p[x] = x
        self.rank[x] = 0

    def union(self, x, y):
        self.link(self.find(x), self.find(y))

    def link(self, x, y):
        if self.rank[x] > self.rank[y]:
            self.p[y] = x
        else:
            self.p[x] = y
            if self.rank[x] == self.rank[y]:
                self.rank[y] += 1

    def find(self, x):
        try:
            if x != self.p[x]:
                self.p[x] = self.find(self.p[x])
        except KeyError:
            if self.auto_create:
                # this should be a call to self.make_set(x);
                # function calls, however, are *very* expensive and
                # this piece of repeated code runs almost 50%
                # faster...
                self.p[x] = x
                self.rank[x] = 0
        return self.p[x]

    def copy(self):
        """ Duplicates the internal structure (deepcopy is too expensive) """
        copy = UnionFind()
        copy.p = self.p.copy()
        copy.rank = self.rank.copy()
        copy.auto_create = self.auto_create
        return copy

    def get_set(self, x):
        """Return the set with all
        :param x: value
        :rtype: list"""
        return [j for j in list(self.p.keys()) if self.find(j) == x]

    def get_sets(self):
        """ Return the sets we have (list of sets)"""
        d = {}
        for i in list(self.p.keys()):
            foo = self.find(i)
            if foo in d:
                d[foo].append(i)
            else:
                d[foo] = [i]
        return d

if __name__ == "__main__":
    N = 10
    s = UnionFind()

    for i in range(N):
        s.make_set(i)

    for i in range(N):
        print("%d \in %d" % (i, s.find(i)))
    print("\njoining even numbers...")
    for i in range(0, N-2, 2):
        s.union(i, i+2)
    print("result:")
    for i in range(N):
        print("%d \in %d" % (i, s.find(i)))
    print("\njoining odd numbers...")
    for i in range(1, N-1, 2):
        s.union(i, i+2)
    print("result:")
    for i in range(N):
        print("%d \in %d" % (i, s.find(i)))
    print("elements which do not exist:")
    for i in [24, 25]:
        print("%d \in %s" % (i, s.find(i)))
    print("elements which do not exist (creating):")
    for i in [24, 25]:
        print("%d \in %s" % (i, s.find(i, True)))
    print("membership:")
    for i in range(1, N+2):
        print("set to which %d belongs: %s" % (i, s.get_set(i)))
    print()
    print()
    print(s.sets())
