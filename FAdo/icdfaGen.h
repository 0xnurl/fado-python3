/*
 * icdfaGen.h: This file is part of libicdfa.
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
 * Copyright 2006-2011 Rogéio Reis, Nelma Moreira, Marco Almeida
 *
 * This is part of the FAdo project (http://www.ncc.up.pt/FAdo)
 */


#ifndef ICDFAGEN_H
#define ICDFAGEN_H

#include "icdfaCommon.h"

typedef int flag_t;

typedef struct icdfagen {
  icdfa_t icdfa;	    /**< the current ICDFA */
  icdfa_t last_icdfa;	    /**< the last possible ICDFA */
  flag_t *flags;	    /**< our flags */
  flag_t *initial_flags;    /**< initial flag setup */
  int nflags;		    /**< number of flags */
  int incomplete;	    /**< generate incomplete ICDFA */
  int	ibias;		    /**< bias for the incomplete transition */
  int bottom;		    /**< smallest state reference */
  /**/
  mpz_t ith; 		    /* ith automaton */
  mpz_t total; 		    /* maximum number of automata that can be generated */
                            /* for random generation */
  icdfa_t rnd; 		    /* random automaton */
  gmp_randstate_t rstate;
  mpz_t *grid;
} *icdfagen_t;

typedef struct stringR {
  int n_states;
  int n_symbols;
  state_t *delta;
  zset_t finals;
} stringR;

/* generator fields access */
#define ICDFAGEN_CURRENT(X) ((X)->icdfa)
#define LAST_ICDFA(X) ((X)->last_icdfa)
#define FLAGS(X) ((X)->flags)
#define INITIAL_FLAGS(X) ((X)->initial_flags)
#define N_FLAGS(X) ((X)->nflags)
#define ICDFAGEN_INCOMPLETE(X) ((X)->incomplete)
#define ICDFAGEN_IBIAS(X) ((X)->ibias)
#define ICDFAGEN_BOTTOM(X) ((X)->bottom)
#define TOTAL_ICDFA(X) ((X)->total)
#define ICDFAGEN_ITH(X) ((X)->ith)
/* icdfa usefull information */
#define ICDFAGEN_NSTATES(X) ICDFA_NSTATES(ICDFAGEN_CURRENT(X))
#define ICDFAGEN_NSYMBOLS(X) ICDFA_NSYMBOLS(ICDFAGEN_CURRENT(X))

/* random ICDFA stuff */
#define RND_ICDFA(X) ((X)->rnd)
#define RND_STATE(X) ((X)->rstate)
#define RND_GRID(X) ((X)->grid)
#define GRID_ELM(I, M,L,K) (*(RND_GRID(I)+(K)*((M)*(M)-(M))/2+(L)-((M)-1)*(M)/2))
  
extern icdfagen_t icdfaGenInit(int nstates, int nsymbols, int ac_only, int ibias, int random);
extern void icdfaGenDel(icdfagen_t icdfaGen);
/* extern void icdfaGenPrintFlags(void); */
/* extern icdfa_t icdfaGenNext(icdfagen_t icdfaGen); */
extern icdfa_t icdfaGenNextICDFA(icdfagen_t icdfaGen);
extern icdfa_t icdfaGenNextICDFAe(icdfagen_t icdfaGen);
extern icdfa_t icdfaGenRandom(icdfagen_t gen, int incomplete);
extern int icdfaGenIsLast(icdfagen_t icdfaGen);
extern void icdfaGenGetTotal(icdfagen_t gen, mpz_t total);
extern void icdfaGenShowFlags(icdfagen_t gen, char *sep);
extern stringR *icdfaGenRandomS(icdfagen_t gen, int incomplete);
/* extern void icdfaGenRndFinals(icdfagen_t gen, int f, zset_t finals); */
extern void icdfaGenFromInteger(icdfagen_t gen, mpz_t m);
extern void icdfaGenToInteger(icdfagen_t gen, mpz_t m);


/********************************************
 * some simple stuff that should be inlined *
 ********************************************/

/**
 * Get the current ICDFAe
 *
 * @param icdfaGen the generator
 *
 * @return an icdfa_t representing the last DFA that was generated
 */
INLINE_DECL icdfa_t icdfaGenCurrent(icdfagen_t icdfaGen)
{
  return ICDFAGEN_CURRENT(icdfaGen);
}

/**
 * Set the last ICDFAe to be generated
 *
 * @param gen the generator
 * @param last an array of states
 */
INLINE_DECL void icdfaGenSetLast(icdfagen_t gen, state_t *last)
{
  icdfaUpdateAutomaton(LAST_ICDFA(gen), last);
}

/* make the last generated ICDFA equal to _new */
INLINE_DECL void icdfaGenSetCurrent(icdfagen_t gen, state_t *_new)
{
  icdfaUpdateAutomaton(ICDFAGEN_CURRENT(gen), _new);
}

/* update the set of flags to _new */
INLINE_DECL void icdfaGenSetFlags(icdfagen_t gen, flag_t *_new)
{
  memcpy(FLAGS(gen), _new, N_FLAGS(gen) * sizeof(flag_t));
}

#endif /* ICDFAGEN_H */
