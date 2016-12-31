/*
 * icdfa.h: This file is part of libicdfa.
 *
 * libicdfa is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * libicdfa is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with libicdfa; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
 *
 * Copyright 2006-2013 Rogério Reis, Nelma Moreira, Marco Almeida
 * 
 * This is part of the FAdo project (http://www.ncc.up.pt/FAdo)
 */

#ifndef ICDFA_H
#define ICDFA_H

#ifdef HAVE_LIBXML2
#include <libxml/tree.h>
#define ICDFA_CHAR2XML(X) ((xmlChar*)X)
#endif

#include "icdfaCommon.h"
#include "zset.h"


typedef enum {CLASSIC, HOPCROFT, INCREMENTAL, BRZOZOWSKI} MINIMALP_ALGORITHM;

typedef struct hopcroft {
  partition_t L;
  zset_t *P;
  int k;
  zset_t nf;
  zset_t B;
  zset_t B1;
  zset_t B2;
  zset_t C;
  zset_t trans;
  zset_t c_trans;
} hopcroft_t;

typedef struct icdfa {
  int n_states;		        /**< number of states */
  int n_symbols;		/**< number of symbols */
  int size;			/**< ICDFA size (states*symbols) */
  state_t *automaton;		/**< ICDFA representation */
  zset_t states;		/**< states set */
  zset_t finals;		/**< final states set */
  zset_t symbols;		/**< alphabet */
  int incomplete;		/**< is the ICDFA incomplete? */
  BOOL_EX acyclic;		/**< is the ICDFA acyclic? */
  BOOL_EX minimal;		/**< is the ICDFA minimal? */
  hopcroft_t hop;		/**< Hopcroft's algorithm auxiliary structure */
} *icdfa_t;

#define ICDFA_NSTATES(X) ((X)->n_states)
#define ICDFA_NSYMBOLS(X) ((X)->n_symbols)
#define ICDFA_INCOMPLETE(X) (X)->incomplete
#define ICDFA_ACYCLIC(X) ((X)->acyclic)
#define ICDFA_MINIMAL(X) ((X)->minimal)
#define ICDFA_SIZE(X) (X)->size
#define ICDFA(X) ((X)->automaton)
#define ICDFA_FINAL_STATES(X) ((X)->finals)
#define ICDFA_STATES(X) (X)->states
#define ICDFA_SYMBOLS(X) (X)->symbols
#define ICDFA_ELEM(X, Y)  ((Y)->automaton[X])
#define ICDFA_HOPCROFT_STRUCT(X) ((X)->hop)
#define ICDFA_GLOBALS(X) ((X)->globals)

extern icdfa_t icdfaInit(int states, int symbols, int has_sink);
extern void icdfaDel(icdfa_t icdfa);
extern state_t icdfaFirstState(icdfa_t icdfa, int i, int j);
extern void icdfaShow(icdfa_t icdfa, char *sep);
extern void icdfaCopy(icdfa_t dst, icdfa_t src);
extern char* icdfaGetString(icdfa_t icdfa, int n);
extern void icdfaPretty(icdfa_t icdfa);
extern int icdfaMinimalP(icdfa_t icdfa, MINIMALP_ALGORITHM algorithm);
extern icdfa_t icdfaMinimize(icdfa_t icdfa);
extern void icdfaDeltaSet(icdfa_t icdfa, zset_t states, symbol_t x, zset_t out);
extern void icdfaUnDeltaSet(icdfa_t icdfa, zset_t states, symbol_t x, zset_t out);
extern int icdfaNextFinalCfg(zset_t finals, unsigned int n);
extern int icdfaNextFinalStates(icdfa_t icdfa);
extern void icdfaRndFinalsA(icdfa_t icdfa);
extern void icdfaRndFinals(icdfa_t icdfa, int f);
extern int icdfaInversibleP(icdfa_t icdfa);
extern int icdfaReversibleP(icdfa_t icdfa);
extern int icdfaStrongP(icdfa_t icdfa);
extern int icdfaAcyclicP(icdfa_t icdfa);
extern int icdfaTrimP(icdfa_t icdfa);
#ifdef HAVE_LIBXML2
extern xmlNodePtr icdfaXML(icdfa_t icdfa);
#endif

/************************************************
 * some simple functions that should be inlined *
 ************************************************/

/** 
 * Change the set of final states
 * 
 * @param icdfa an ICDFA
 * @param finals the new final states set
 */
INLINE_DECL void icdfaSetFinals(icdfa_t icdfa, zset_t finals)
{
  zsetCopy(ICDFA_FINAL_STATES(icdfa), finals);
  ICDFA_MINIMAL(icdfa) = MAYBE;
}

/** 
 * Change the ICDFA
 * 
 * @param icdfa an ICDFA
 * @param new the new ICDFA representation (an array of state_t)
 */
INLINE_DECL void icdfaUpdateAutomaton(icdfa_t icdfa, state_t *_new)
{
  memcpy(ICDFA(icdfa), _new, ICDFA_SIZE(icdfa)*sizeof(state_t));
  
  ICDFA_MINIMAL(icdfa) = MAYBE;
  ICDFA_ACYCLIC(icdfa) = MAYBE;
}

/** 
 * Change a transition
 * 
 * @param icdfa an ICDFA
 * @param i the position of the array which corresponds to the transition being updated
 * @param st the new state to which the transition goes
 */
INLINE_DECL void icdfaSetElem(icdfa_t icdfa, int i, state_t st)
{
  ICDFA(icdfa)[i] = st;
  ICDFA_MINIMAL(icdfa) = MAYBE;
  ICDFA_ACYCLIC(icdfa) = MAYBE;
}

/** 
 * Get the destination of a given transition
 * 
 * @param icdfa an ICDFA
 * @param i the position of the array which corresponds to the transition being
 * @return the state to which the transition goes
 */
INLINE_DECL state_t icdfaGetElem(icdfa_t icdfa, int i)
{
  return ICDFA(icdfa)[i];
}

/** 
 * Get the destination of a given transition
 * 
 * @param icdfa0 an ICDFA
 * @param icdfa1 an ICDFA
 * @return 1 if the ICDFAs are equal (same sequence); 0 otherwise
 */
INLINE_DECL state_t icdfaEqual(icdfa_t i0, icdfa_t i1)
{
  return (ICDFA_SIZE(i0) == ICDFA_SIZE(i1)) && (memcmp(ICDFA(i0), ICDFA(i1), ICDFA_SIZE(i0)*sizeof(state_t)) == 0);
}

#endif /* ICDFA_H */

