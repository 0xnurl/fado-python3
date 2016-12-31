# -*- coding: utf-8 -*-
"""**FAdo interface language and slave manager**

.. *Authors:* Rogério Reis & Nelma Moreira

.. This is part of U{FAdo project <http://www.ncc.up.pt/FAdo>}.

.. *Copyright:* 1999-2011 Rogério Reis & Nelma Moreira {rvr,nam}@dcc.fc.up.pt

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
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

Applications that want to use FAdo as a slave, just to process it objects should use
this language to interface with it.

.. note::
  Every object that is supposed to be available through this language, should be defined
  in objects and should have a method ``vDescription``, returning the following list

  0. A pair of descriptions, short and long, of the object

  1. A list of pairs

  1.0. A name of a format *(names should be unique)*

  1.1. The function that returns the string representation of the object in that format

  2. A tuple for each method provided

  2.0. Name of the command in verso

  2.1. A pair, short/long, descriptions of the method

  2.2. Number (n) of arguments of the method

  2.2+i. The type of the ith argument

  2.1+n. The return type ``None`` if does not return (in place transformation)

  2.2+n. The function implementing the method having a list as arguments

  3. and so on...
"""
from __future__ import print_function
from __future__ import absolute_import
from __future__ import unicode_literals
from __future__ import division

from future import standard_library
standard_library.install_aliases()
from builtins import *
from builtins import object
import sys

from .fa import *
from .common import *
from .yappy_parser import grules
from .yappy_parser import Yappy

#from yappy.parser import LR1table
from .fio import ParserFAdo


class ParserVerso(Yappy):
  """A parser for FAdo standard automata descriptions

  :var vi: virtual interaction session that knows how to communicate with the client
  :var objects: the list of objects known
  :var info: dictionary object -> (longdescription, [list of commands])
  :var fun: dictionary command -> (arity, return type, function)
  :var format: dictionary formatName -> function
  """
  def __init__(self, vsession, objects=None, no_table=0, table=".tableVerso"):
    """
    :param no_table: ignore the table if it exists
    :param table: name of the table
    """
    self.vi = vsession
    if objects is None:
      self.objects = [DFA,NFA]
    else:
      self.objects = objects
    tokenizer = [
      ("\n+", lambda x: ("EOL", "EOL")),
      ("#.*", ""),
      ("\s+", ""),
      ("@epsilon", lambda x: ("ids", "@epsilon")),
      ("info", lambda x: ("info","info")),
      ("new", lambda x: ("new","new")),
      ("from", lambda x: ("from", "from")),
      ("format", lambda x: ("format","format")),
      ("show", lambda x: ("show","show")),
      ("as", lambda x: ("as","as")),
      ("pop", lambda x: ("pop","pop")),
      ("swap", lambda x: ("swap", "swap")),
      ("reset", lambda x: ("reset","reset")),
      ("halt", lambda x: ("halt", "halt")),
      ("def", lambda x: ("def","def")),
      ("@DFA", lambda x: ("str",x)),
      ("@NFA", lambda x: ("str",x)),
      ("\$", lambda x: ("DOLLAR", "DOLLAR")),
      ("\*", lambda x: ("SEP", "SEP")),
      ("[A-Za-z&]+[0-9]*", lambda x: ("str", x)),
      ("[0-9]+", lambda x: ("int", int(x)))
    ]
    rules = [
      ("s -> l EOL", self.defaultSemRule),
      ("l -> info", self.infoShow),
      ("l -> info command", self.infoShowCommand),
      ("l -> new obid", self.newObjRule),
      ("l -> new obid def idl", self.newObjCRep),
      # TODO: implement reading from file
      ("l -> new obid from filename format id", self.defaultSemRule),
      ("l -> show as str", self.showObjectAsStr),
      ("l -> show as format",self.showObject),
      ("l -> pop", self.popRule),
      ("l -> swap int int", self.swapRule),
      ("l -> swap", self.swapRuleDflt),
      ("l -> reset", self.resetRule),
      ("l -> command", self.doCommand),
      ("l -> command idl", self.doCommand),
      ("l -> halt", self.haltRule),
      ("idl -> id idl", self.listRule),
      ("idl -> id", self.listRule),
      ("id -> str", self.defaultSemRule),
      ("id -> int", self.defaultSemRule),
      ("id -> ids", self.defaultSemRule),
      ("id -> SEP", self.defaultSemRule),
      ("id -> DOLLAR", self.defaultSemRule)
    ]
    self.info = {}
    # class -> (infoLong,[list of (format,description)],[list of commands])
    self.fun = {}
    # command -> (arity, return type, lambda code)
    self.show = {}
    # format -> lambda code
    for c in self.objects:
      x = c().vDescription()
      tokenizer.insert(-3,(x[0][0],(lambda z: lambda y: ("obid",z))(c)))
      self.info[x[0][0]] = (x[0][1],[],[])
      d = self.info[x[0][0]][1]
      for (name,rfun,desc) in x[1]:
        tokenizer.insert(-3,(name,(lambda z: lambda y: ("format",z))(name)))
        self.show[name] = rfun
        d.append((name,desc))
      d = self.info[x[0][0]][2]
      for f in x[2:]:
        d.append((f[0],f[1]))
        num = f[2]
        self.fun[f[0]] =  (num,f[1][0],f[1][1],f[3:4+num],f[-2],f[-1])
        tokenizer.insert(3,(f[0],(lambda z: lambda y: ("command",z))(f[0])))
    foo = tokenizer[3:-3]
    foo.sort(key=lambda x:len(x[0]))
    foo.reverse()
    tokenizer = tokenizer[:3] + foo + tokenizer[-3:]
    grammar = grules(rules)
    Yappy.__init__(self, tokenizer, grammar, table, no_table)

  def defaultSemRule(self, lst, context=None):
    """Default dummy rule"""
    return lst[0]

  def newObjCRep(self,lst, context=None):
    foo = ""
    for s in lst[3]:
      if type(s) is type(""):
        foo += s + " "
      else:
        foo += "%d"%s + " "
    parser = ParserFAdo()
    parser.input(foo.replace("&","\n"))
    a = parser.result()[0]
    if not isinstance(a,lst[1]):
      raise VersoError("Object type mismatch")
    self.vi.push(a)
    self.vi.out()

  def listRule(self,lst,context=None):
    if len(lst) == 1:
      return lst[0]
    if type(lst[1])  != type([]):
      return lst
    else:
      return [lst[0]]+lst[1]

  def showObjectAsStr(self,lst,context=None):
    """Show top of the stack"""
    self.vi.out(self.vi.stack[-1].dump().__str__())

  def resetRule(self,lst,context=None):
    """Reset interaction rule"""
    self.vi.reset()
    self.vi.out()

  def popRule(self,lst,context=None):
    """pop rule"""
    self.vi.pop()
    self.vi.out()

  def haltRule(self,lst,context=None):
    """halt of the process"""
    sys.exit(0)

  def swapRule(self,lst,context=None):
    """Swaps two items in stack"""
    x,y = lst[1],lst[2]
    l = len(self.vi.stack)
    if y < 0 or x < 0 or x > l or y > l:
      raise VersoError("Indexes out of range")
    else:
      self.vi.stack[-x], self.vi.stack[-y] = self.vi.stack[-y], self.vi.stack[-x]
      self.vi.out()

  def swapRuleDflt(self,lst,context=None):
    """Default swap on the top of stack"""
    if len(self.vi.stack) < 2:
      raise VersoError("Stack too short")
    else:
      self.vi.stack[-1], self.vi.stack[-2] = self.vi.stack[-2], self.vi.stack[-1]
      self.vi.out()

  def infoShow(self,lst,context=None):
    """Show general info on Verso"""
    s = "["
    for c in list(self.info.keys()):
      s += "('"+ c + "',["
      for name,desc in self.info[c][1]:
        s += "('" + name + "','" + desc + "'),"
      s = s[:-1] +  "],["
      for f in self.info[c][2]:
        s += ("'" + f[0] + "'" + ",")
      s = s[:-1] + "]),"
    s = s[:-1]
    s += "]"
    self.vi.out(s)

  def infoShowCommand(self,lst,context=None):
    """Show information about a command"""
    cmd = lst[1]
    s = "('" + cmd + "', ('" + self.fun[cmd][1]+"', '"+self.fun[cmd][2]+"'), "+self.fun[cmd][3].__str__() + ")"
    self.vi.out(s)

  def emptySemRule(self, lst, context=None):
    """Empty rule"""
    return []

  def newObjRule(self,lst,context=None):
    """New object rule"""
    self.vi.push(lst[1]())
    self.vi.out()

  def showObject(self,lst,context=None):
    """Show as format - implementation"""
    self.vi.out(self.show[lst[2]](self.vi.stack[-1]))

  def doCommand(self, lst, context=None):
    """Command execution"""
    ob = self.vi.stack[-1]
    argtl = self.fun[lst[0]][-3]
    if len(lst) > 1 and type(lst[1]) == type([]):
      ll = lst[1]
    else:
      ll = lst[1:]
    if len(argtl) >= 3 and argtl[1] not in ["int","str"]:
      ob1 = self.vi.stack[-2]
      r = self.fun[lst[0]][-1](ob,ob1,*ll)
    else:
      r = self.fun[lst[0]][-1](ob,*ll)
    rtype = self.fun[lst[0]][-2]
    if rtype in ["int","Bool"]:
      self.vi.out(r.__str__())
    elif rtype == "str":
      self.vi.out(r)
    elif rtype is None:
      self.vi.out("")
    else:
      self.vi.push(r)
      self.vi.out()

class interaction(object):
  def __init__(self,inName,outName):
    self.inName, self.outName = inName, outName
    self.stack = []
    if not DEBUG:
      self.reopen()

  def reopen(self):
    if not DEBUG:
      self.inCh = open(self.inName,"r")
      self.outCh = open(self.outName,"w",1)

  def out(self,output=""):
    if DEBUG:
      print(output)
    else:
      self.outCh.write(output)
      self.outCh.write("\n")
      self.outCh.flush()

  def reset(self):
    self.stack = []

  def push(self,v):
    self.stack.append(v)

  def pop(self):
    return self.stack.pop()

DEBUG =False

if __name__ == "__main__":
  if DEBUG is True:
    vi = interaction("xx1","xx2")
    parser = ParserVerso(vi)
    parser.input("new DFA def @DFA s0 & s0 t0 s1 & \n")
    parser.input("new DFA def @DFA 0 & 0 a 0 & 0 b 1 & 1 a 0 & 1 b 0 & \n")
    parser.input("new DFA def @DFA 0 & 0 a 0 & 0 b 1 & 1 a 0 & 1 b 0 & \n")
    parser.input("show as DFAFAdo \n")
    parser.input("show as DFAdot \n")
    parser.input("DFA-conjunction \n")
    parser.input("show as DFAdot \n")
    parser.input("show as DFAFAdo \n")
#    parser.input("info\n")
#    parser.input("DFA-add-state a\n")
#    parser.input("info DFA-setInitial\n")
#    parser.input("DFA-add-final 0\n")
#    parser.input("DFA-add-final 0\n")
#    parser.input("DFA-add-transition 0 a 0\n")
#    parser.input("DFA-add-state b\n")
#    parser.input("DFA-add-transition 0 b 1\n")
#    parser.input("DFA-add-transition 1 b 1\n")
#    parser.input("DFA-add-transition 1 a 0\n")
#    parser.input("DFA-dump\n")
    parser.input("info\n")
#    parser.input("show as DFAFAdo\n")
  else:
    vi = interaction(sys.argv[1],sys.argv[2])
    parser = ParserVerso(vi)
    while True:
      for l in vi.inCh:
        parser.input(l)
      vi.reopen()
