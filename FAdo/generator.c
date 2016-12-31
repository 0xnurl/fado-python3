//
// FADO icdfa generator
// Python wrapper
//
// @author: Rogério Reis & Nelma Moreira
//
// This is part of U{FAdo project <http://www.ncc.up.pt/FAdo>}.
//
// @copyright: 1999-2013 Rogério Reis & Nelma Moreira {rvr,nam}@dcc.fc.up.pt
//
// Contributions by
//  - Marco Almeida
//
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.


#include <Python.h>
#include "icdfa.h"
#include "icdfaGen.h"

typedef struct {
  PyObject_HEAD
  icdfagen_t gen;
  int inc;
} icdfaRndGen;


static void icdfaRndGen_del(icdfaRndGen *self);

static PyObject *icdfaRndGen_new(PyTypeObject *type, PyObject *args,
				 PyObject *kwds);

static int icdfaRndGen_init(icdfaRndGen *self, PyObject *args, PyObject *kwds);

static PyObject *icdfaRndGen_gen(icdfaRndGen *self);


static PyMethodDef generator_methods[] = {
  {"next", (PyCFunction)icdfaRndGen_gen, METH_NOARGS,
   "Returns the next generated automaton."},
  {NULL}  /* Sentinel */
};

static PyTypeObject icdfaRndGenType = {
  PyObject_HEAD_INIT(NULL)
  0,					/* ob_size*/
  "generator.icdfaRndGen.",		/* tp_name*/
  sizeof(icdfaRndGen),		        /* tp_basicsize*/
  0,					/* tp_itemsize*/
  (destructor)icdfaRndGen_del,	        /* tp_dealloc*/
  0,					/* tp_print*/
  0,					/* tp_getattr*/
  0,					/* tp_setattr*/
  0,					/* tp_compare*/
  0,					/* tp_repr*/
  0,					/* tp_as_number*/
  0,					/* tp_as_sequence*/
  0,					/* tp_as_mapping*/
  0,					/* tp_hash */
  0,					/* tp_call*/
  0,					/* tp_str*/
  0,					/* tp_getattro*/
  0,					/* tp_setattro*/
  0,					/* tp_as_buffer*/
  Py_TPFLAGS_DEFAULT|Py_TPFLAGS_BASETYPE, /* tp_flags*/
  "Fado ICDFA random object generator",   /* tp_doc */
  0,					/* tp_traverse */
  0,					/* tp_clear */
  0,				  /* tp_richcompare */
  0,		      /* tp_weaklistoffset */
  0,		      /* tp_iter */
  0,		      /* tp_iternext */
  generator_methods,			/* tp_methods */
  0,					/* tp_members */
  0,					/* tp_getset */
  0,					/* tp_base */
  0,					/* tp_dict */
  0,					/* tp_descr_get */
  0,					/* tp_descr_set */
  0,					/* tp_dictoffset */
  (initproc) icdfaRndGen_init,	/* tp_init */
  0,					/* tp_alloc */
  icdfaRndGen_new,   /* tp_new */
};

#ifndef PyMODINIT_FUNC	/* declarations for DLL import/export */
#define PyMODINIT_FUNC void
#endif

PyMODINIT_FUNC initgenerator(void) {
  PyObject* m;
  
  icdfaRndGenType.tp_new = PyType_GenericNew;
  if (PyType_Ready(&icdfaRndGenType) < 0)
    return;
  
  m = Py_InitModule3("generator", generator_methods,
		     "Fado object generator module.");

  Py_INCREF(&icdfaRndGenType);
  PyModule_AddObject(m, "icdfaRndGen", (PyObject *)&icdfaRndGenType);
}

static void icdfaRndGen_del(icdfaRndGen *self) {
  icdfaGenDel(self->gen);
  self->ob_type->tp_free((PyObject*)self);
}

static PyObject *icdfaRndGen_new(PyTypeObject *type, PyObject *args,
				 PyObject *kwds) {
  icdfaRndGen *self;
  self = (icdfaRndGen *)type->tp_alloc(type, 0);
  if (self != NULL) {
    self->gen = NULL;
  }
  return (PyObject *)self;
}

static int icdfaRndGen_init(icdfaRndGen *self, PyObject *args, PyObject *kwds) {
  int n_states=2, n_symbols=2, incomplete=0, ibias=1 ;
  
  if (! PyArg_ParseTuple(args, "|iiii", &n_states, &n_symbols, &incomplete, &ibias)) {
    return -1;
  }
  self->gen = icdfaGenInit(n_states, n_symbols, incomplete, ibias, 1);
  self->inc = (incomplete != 0) ? 1:0;
  return 0;
}

static PyObject *icdfaRndGen_gen(icdfaRndGen *self) {
  stringR *result = icdfaGenRandomS(self->gen,self->inc);
  int i, lim = result->n_states * result->n_symbols;
  PyObject *list = PyList_New(0);
  PyObject *rvalue = NULL, *arg ;
  if (list == NULL) goto error;
  for (i=0; i< lim; i++) {
    arg = PyInt_FromLong((long)result->delta[i]);
    if(PyList_Append(list, arg) == -1) goto error;
    Py_DECREF(arg);
  }
  PyObject *tp = PyTuple_New(2);
  PyTuple_SetItem(tp,0,list);
  list = PyList_New(0);
  for (i=0; i< result->n_states; i++) {
    arg = PyInt_FromLong((long) RANDOMBIT());
    if (PyList_Append(list, arg) == -1) goto error;
    Py_DECREF(arg);
  }
  PyTuple_SetItem(tp,1,list);
  rvalue = tp;
  tp = NULL;
 error:
  Py_XDECREF(tp);
  return rvalue;
}
