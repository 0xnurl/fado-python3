/*
 * icdfaGen.c: This file is part of libicdfa.
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
 * Copyright 2006-2013 Rogéio Reis, Nelma Moreira, Marco Almeida
 *
 * This is part of the FAdo project (http://www.ncc.up.pt/FAdo)
 */


#if HAVE_CONFIG_H
#include <config.h>
#endif
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <sys/time.h>
#include <time.h>
#include <gmp.h>
#include "icdfa.h"
#include "icdfaGen.h"


/*********************************
 * random ICDFA generation stuff *
 ********************************/

/* initialize the matrix (basic structure for the random generation
 * procedure) */
void gridInit(icdfagen_t gen, int n, int k, int t){
  // t is tha flag to select between complete and uncomplete automata
  // t = = means complete
  int i,m,l;
  mpz_t t1,t2,t3;
  
  mpz_init(t1);
  mpz_init(t2);
  mpz_init(t3);
  
  RND_GRID(gen) = (mpz_t *)calloc((k*(n-1)*n - n*n + 3*n - 2) / 2, sizeof(mpz_t));
  
  for(m=1; m<n; m++)
    for(l=m-1;l<m*k;l++){
      mpz_init(GRID_ELM(gen, m,l,k));
      mpz_set_ui(GRID_ELM(gen, m,l,k),0);
    }
  /*
   * initiate the table with values for T_{n-1,l}=n^{nk-l-1} (1<=l<=k)
   */
  for(i = (n - 1) * k - 1; i >= (n - 2); i--)
    mpz_ui_pow_ui(GRID_ELM(gen, n-1,i,k),n+t,k+((n-1)*k-1)-i);
    /*
     * now the recursion formula
     */
  for( m = n - 2; m >= 1; m--){
    mpz_set_ui(t1, 0);
    mpz_set_ui(t2, 1);
    for(i = 1; i <= k; i++){
      mpz_mul(t3,GRID_ELM(gen, m+1, m * k - 1 + i, k), t2);
      mpz_add(t1, t1, t3);
      mpz_mul_ui(t2, t2, m+1+t);
    }
    mpz_set(GRID_ELM(gen, m, m * k - 1 ,k), t1);
    mpz_set_ui(t1, 0);
    for(i = m * k - 2; i >= m - 1; i--){
      mpz_mul_ui(t1,GRID_ELM(gen, m, i + 1, k), m+1+t);
      mpz_add(GRID_ELM(gen, m, i, k), t1, GRID_ELM(gen, m+1, i+1, k));
    }
    }
    /* total */
    mpz_set_ui(t1, 0);
    for(i = 0; i < k; i++)
	mpz_add(t1, t1, GRID_ELM(gen, 0,i,k));

    mpz_set(TOTAL_ICDFA(gen), t1);

    mpz_clear(t1);
    mpz_clear(t2);
    mpz_clear(t3);
    /*  for(m=1;m<n;m++) */
    /* 	 for(l=m-1;l<m*k;l++) */
    /* 	  mpz_clear(GRID_ELM(gen, m,l,k)); */
}

/* initializes the necessary stuff for the random generation process */
void randomInit(icdfagen_t gen, int states, int symbols, int t){
  struct timeval foo;
  struct timezone bar;

  gmp_randinit_default(RND_STATE(gen));
  bar.tz_minuteswest = 0;
  gettimeofday(&foo, &bar);
  gmp_randseed_ui(RND_STATE(gen), (unsigned long)foo.tv_sec + foo.tv_usec);
  srand((unsigned int)foo.tv_sec+foo.tv_usec);
  RND_ICDFA(gen) = icdfaInit(states, symbols, ICDFAGEN_INCOMPLETE(gen));
  gridInit(gen, states, symbols, t);
}

/*
 * special version of RAND that deals with incompleteness and its bias
 */

int IRAND(int max, int bias){
	int foo;
	
	foo = RAND(max+bias);
	if (foo < bias) return -1;
	else return (foo - bias);
}

/* random flag */
int genRndFlag(icdfagen_t gen, int n, int k, int f, int b, int t){
  int i;
  mpz_t t1, t2, t3, mrandom;
  
  mpz_init(t1);
  mpz_init(t2);
  mpz_init(t3);
  mpz_init(mrandom);
  
  mpz_set_ui(t2,1);
  mpz_set_ui(t1,0);
  for(i = b; i <= f * k - 1; i++){
    mpz_mul(t3,t2,GRID_ELM(gen, f, i, k));
    mpz_add(t1, t1, t3);
    mpz_mul_ui(t2, t2, f + t);
  }

  mpz_urandomm(mrandom, RND_STATE(gen), t1);
  mpz_add_ui(mrandom,mrandom, 1);
  mpz_set_ui(t2, 1);
  for(i = b; i <= f * k - 1; i++){
    mpz_mul(t3, t2, GRID_ELM(gen, f, i, k));
    if (mpz_cmp(mrandom, t3) <= 0){
      mpz_clear(t1);
      mpz_clear(t2);
      mpz_clear(t3);
      mpz_clear(mrandom);
      return i;
    } 
    else {
      mpz_sub(mrandom, mrandom, t3);
      mpz_mul_ui(t2, t2, f + t);
    }
  }
  printf("Error! Please contact the authors with the example that generated this\n");
  return -1;
}

/* last possible ICDFA */
void setLastICDFA(icdfagen_t icdfaGen){
  int i;
  icdfa_t automaton = ICDFAGEN_CURRENT(icdfaGen);
  icdfa_t *last = &LAST_ICDFA(icdfaGen);

  *last = icdfaInit(ICDFA_NSTATES(automaton), ICDFA_NSYMBOLS(automaton),
		    ICDFAGEN_INCOMPLETE(icdfaGen));

  for (i = 0; i < ICDFA_NSTATES(*last) - 1; i++)
    /* 	ICDFA(*last)[i] = i + 1; */
    icdfaSetElem(*last, i, i+1);
  for (i = ICDFA_NSTATES(*last) - 1; i < ICDFA_SIZE(*last); i++)
    /* 	ICDFA(*last)[i] = ICDFA_NSTATES(*last) - 1; */
    icdfaSetElem(*last, i, ICDFA_NSTATES(*last) - 1);
}

void initializeICDFA(icdfagen_t icdfaGen){
  int i;
  icdfa_t icdfa = ICDFAGEN_CURRENT(icdfaGen);

  memset(ICDFA(icdfa), ICDFAGEN_BOTTOM(icdfaGen), 
															ICDFA_SIZE(icdfa) * sizeof(state_t));
  
  for (i = 1; i < ICDFA_NSTATES(icdfa); i++)
    ICDFA_ELEM(i * ICDFA_NSYMBOLS(icdfa) - 1, icdfa) = i;

  /* so that the first call to genNext() will produce a valid ICDFA */
  ICDFA_ELEM(ICDFA_SIZE(icdfa) - 1, icdfa) = ICDFAGEN_BOTTOM(icdfaGen) - 1;
  ICDFA_ACYCLIC(icdfa) = MAYBE;
  ICDFA_MINIMAL(icdfa) = MAYBE;
  zsetClear(ICDFA_FINAL_STATES(icdfa));
}

/* initial flag setup */
void setFlags(icdfagen_t icdfaGen){
  int i;
  icdfa_t automaton = ICDFAGEN_CURRENT(icdfaGen);

  FLAGS(icdfaGen) = (flag_t*) malloc(N_FLAGS(icdfaGen)*sizeof(flag_t));
  INITIAL_FLAGS(icdfaGen) = (flag_t*) malloc(N_FLAGS(icdfaGen) * sizeof(flag_t));

  /* initial_flags, is an array which *always* has the initial position */
	/* for each flag */
  for (i = 1; i < ICDFA_NSTATES(automaton); i++)
    INITIAL_FLAGS(icdfaGen)[i - 1] = FLAGS(icdfaGen)[i - 1] 
																			= ICDFA_NSYMBOLS(automaton) * i - 1;
}

int hasFlag(icdfagen_t g, flag_t e){
  int i;

  for (i = 0; i < N_FLAGS(g); i++)
    if (FLAGS(g)[i] == e)
      return 1;
  return 0;
}

/* true if, for the current flag setup, it is not possible to generate more automata */
int isFull(icdfagen_t icdfaGen){
  int i;
  icdfa_t icdfa = ICDFAGEN_CURRENT(icdfaGen);
  state_t state;
  flag_t start = 0, flag, last_flag;

  for (i = 0; i < N_FLAGS(icdfaGen); i++){
    flag = FLAGS(icdfaGen)[i];
    if (start < flag){
      state = icdfaFirstState(icdfa, start, flag);
      if (state < ICDFA(icdfa)[flag]-1)
	return 0;
      start = flag + 1;
    }
  }

  last_flag = FLAGS(icdfaGen)[N_FLAGS(icdfaGen) - 1];
  if (icdfaFirstState(icdfa, last_flag, ICDFA_SIZE(icdfa)) < N_FLAGS(icdfaGen))
    return 0;
  
  return 1;
}

flag_t nearestFlag(icdfagen_t gen, state_t st){
  int i;
  
  if (st < FLAGS(gen)[0])
    return FLAGS(gen)[0];

  for (i = 0; i < N_FLAGS(gen); i++)
    if (FLAGS(gen)[i] > st)
      return FLAGS(gen)[i];
  return -1;
}

int isFull2(icdfagen_t generator){
  state_t i;
  icdfa_t icdfa = ICDFAGEN_CURRENT(generator);

  /* lets start by checking the transitions "controled" by flags */
  for (i = 0; i < FLAGS(generator)[N_FLAGS(generator) - 1]; i++){
    if (! hasFlag(generator, i))
      if (ICDFA(icdfa)[i] < ICDFA(icdfa)[nearestFlag(generator, i)] - 1)
	return 0;
  }

  /* now, if all transitions are to the last state, we need to shift flags */
  for (i = FLAGS(generator)[N_FLAGS(generator) - 1]; i < ICDFA_SIZE(icdfa); i++)
    if (ICDFA(icdfa)[i] < ICDFA_NSTATES(icdfa) - 1)
      return 0;
  return 1;
}

/**/
void reset(icdfagen_t icdfaGen){
  flag_t i, k = 1;
  icdfa_t icdfa = ICDFAGEN_CURRENT(icdfaGen);

  for (i = 0; i < ICDFA_SIZE(icdfa); i++)
    if (hasFlag(icdfaGen, i))
      ICDFA(icdfa)[i] = k++;
    else
      ICDFA(icdfa)[i] = ICDFAGEN_BOTTOM(icdfaGen);
  
  /* makes the call to genNext() work */
  ICDFA(icdfa)[ICDFA_SIZE(icdfa)-1] = ICDFAGEN_BOTTOM(icdfaGen)-1;
  
  /* we changed the ICDFA structure */
  ICDFA_ACYCLIC(icdfa) = MAYBE;
  ICDFA_MINIMAL(icdfa) = MAYBE;
}

/* new flag setup */
void shiftFlags(icdfagen_t icdfaGen, int n){
  if (n == 0) {
    FLAGS(icdfaGen)[0]--;
  } 
  else {
    if (FLAGS(icdfaGen)[n]-1 == FLAGS(icdfaGen)[n-1]) {
      FLAGS(icdfaGen)[n] = INITIAL_FLAGS(icdfaGen)[n];
      shiftFlags(icdfaGen, n - 1);
    } 
    else
      FLAGS(icdfaGen)[n]--;
  }
  
  reset(icdfaGen);
}

/* state to which the transition goes at the ith flag */
state_t flagValue(icdfagen_t icdfaGen, int i){
  icdfa_t icdfa = ICDFAGEN_CURRENT(icdfaGen);
  flag_t flag, j;

  for (j = 1; j < N_FLAGS(icdfaGen); j++) {
    if (FLAGS(icdfaGen)[j] > i && FLAGS(icdfaGen)[j-1] < i) {
      flag = FLAGS(icdfaGen)[j];
      return (ICDFA(icdfa)[flag] - 1);
    }
  }

  flag = FLAGS(icdfaGen)[ICDFA_NSTATES(icdfa)-2];
  return ICDFA(icdfa)[flag];
}

/* next skeleton */
void nextICDFAe(icdfagen_t icdfaGen, int a, int b){
  icdfa_t icdfa = ICDFAGEN_CURRENT(icdfaGen);
  int i = a*ICDFA_NSYMBOLS(icdfa) + b;

  if (a < ICDFA_NSTATES(icdfa) - 1) {
    while (hasFlag(icdfaGen, i)) {
      b--;
      i--;
      if (b < 0) {
	b = ICDFA_NSYMBOLS(icdfa)-1;
	a--;
      }
    }
  }

  if (ICDFA(icdfa)[i] == flagValue(icdfaGen, i)) {
    icdfaSetElem(icdfa, i, ICDFAGEN_BOTTOM(icdfaGen));
    if (b == 0)
      nextICDFAe(icdfaGen, a-1, ICDFA_NSYMBOLS(icdfa) - 1);
    else
      nextICDFAe(icdfaGen, a, b - 1);
  } 
  else {
    if (ICDFAGEN_INCOMPLETE(icdfaGen) && a == 0 && i < FLAGS(icdfaGen)[0]){
      if (ICDFA(icdfa)[i] < ICDFA(icdfa)[FLAGS(icdfaGen)[0]]-1)
	icdfaSetElem(icdfa, i, ICDFA(icdfa)[i]+1);
      else {
	icdfaSetElem(icdfa, i, ICDFAGEN_BOTTOM(icdfaGen));
	nextICDFAe(icdfaGen, a, b-1);
      }
    } 
    else
      ICDFA(icdfa)[i]++;
  }
}


/**********************
 * exported functions *
 **********************/

/* initialization (constructor) */
extern icdfagen_t icdfaGenInit(int states, int symbols, int incomplete, int ibias, int random){
		
  icdfagen_t icdfaGen = (icdfagen_t) calloc(1, sizeof(struct icdfagen));
  icdfa_t *icdfa = &ICDFAGEN_CURRENT(icdfaGen);

  mpz_init(ICDFAGEN_ITH(icdfaGen));
  mpz_init(TOTAL_ICDFA(icdfaGen));
  mpz_set_ui(ICDFAGEN_ITH(icdfaGen), 0);
  ICDFAGEN_INCOMPLETE(icdfaGen) = incomplete;
	ICDFAGEN_IBIAS(icdfaGen) = ibias;
  ICDFAGEN_BOTTOM(icdfaGen) = incomplete ? -1 : 0;
  *icdfa = icdfaInit(states, symbols, incomplete);
  N_FLAGS(icdfaGen) = ICDFA_NSTATES(*icdfa)-1;
  initializeICDFA(icdfaGen);
  if (random)
    randomInit(icdfaGen, states, symbols, incomplete);
  else
    RND_GRID(icdfaGen) = NULL;
  setLastICDFA(icdfaGen);
  setFlags(icdfaGen);
  
  return icdfaGen;
}

/* memory cleanup (destructor)*/
extern void icdfaGenDel(icdfagen_t icdfaGen){
  int m, l, n, k;

  mpz_clear(ICDFAGEN_ITH(icdfaGen));
  mpz_clear(TOTAL_ICDFA(icdfaGen));
  icdfaDel(ICDFAGEN_CURRENT(icdfaGen));
  icdfaDel(LAST_ICDFA(icdfaGen));
  if (RND_GRID(icdfaGen)){
    n = ICDFA_NSTATES(RND_ICDFA(icdfaGen));
    k = ICDFA_NSYMBOLS(RND_ICDFA(icdfaGen));
    icdfaDel(RND_ICDFA(icdfaGen));
    gmp_randclear(RND_STATE(icdfaGen));
    for(m=1; m<n; m++)
      for(l=m-1; l< m*k; l++)
	mpz_clear(GRID_ELM(icdfaGen, m, l, k));
    free(RND_GRID(icdfaGen));
  }
  free(FLAGS(icdfaGen));
  free(INITIAL_FLAGS(icdfaGen));
  free(icdfaGen);
}

/* is this the last possible automaton? */
extern int icdfaGenIsLast(icdfagen_t icdfaGen){
  /*
    memcmp() is not significantly more efficient
    this way is a lot more readable
  */
  icdfa_t aut = ICDFAGEN_CURRENT(icdfaGen);
  icdfa_t last = LAST_ICDFA(icdfaGen);
  int i;

  for(i = 0; i < ICDFA_SIZE(aut); i++)
    if (ICDFA(aut)[i] != ICDFA(last)[i])
      return 0;
  
  return 1;
}

extern void icdfaGenGetTotal(icdfagen_t gen, mpz_t total){
  mpz_set(total, TOTAL_ICDFA(gen));
}

/* generate and return the next skeleton */
extern icdfa_t icdfaGenNextICDFAe(icdfagen_t icdfaGen){
  icdfa_t icdfa = ICDFAGEN_CURRENT(icdfaGen);

  /* finito */
  if (icdfaGenIsLast(icdfaGen))
    return NULL;

  /* we need a new flag setup */
  if (isFull(icdfaGen))
    shiftFlags(icdfaGen, N_FLAGS(icdfaGen) - 1);
  
  /* get the next ICDFA */
  nextICDFAe(icdfaGen, ICDFA_NSTATES(icdfa) - 1, ICDFA_NSYMBOLS(icdfa) - 1);
  
  /* we changed the ICDFA structure */
  ICDFA_ACYCLIC(icdfa) = MAYBE;
  ICDFA_MINIMAL(icdfa) = MAYBE;
  
  /* no more final states */
  zsetClear(ICDFA_FINAL_STATES(icdfa));
  return ICDFAGEN_CURRENT(icdfaGen);
}

extern icdfa_t icdfaGenNextICDFA(icdfagen_t icdfaGen){
  icdfa_t icdfa = ICDFAGEN_CURRENT(icdfaGen);

  /* we are done */
  if (icdfaGenIsLast(icdfaGen) &&
      zsetCardinality(ICDFA_FINAL_STATES(icdfa))==ICDFA_NSTATES(icdfa))
    return NULL;

  if (zsetCardinality(ICDFA_FINAL_STATES(icdfa)) == ICDFA_NSTATES(icdfa)){
    zsetClear(ICDFA_FINAL_STATES(icdfa));
    icdfaGenNextICDFAe(icdfaGen);
    ICDFA_MINIMAL(icdfa) = MAYBE;
  } 
  else
    icdfaNextFinalStates(icdfa);
  return icdfa;
}

/* compute and return a random ICDFA */
extern icdfa_t icdfaGenRandom(icdfagen_t gen, int incomplete){
  int i, j, f, t1=0;
  icdfa_t aut = RND_ICDFA(gen);
  state_t *pt = ICDFA(RND_ICDFA(gen));
  
  /* random ICDFA skeleton */
  if (!incomplete){
    for(i = 1; i < ICDFA_NSTATES(aut); i++){
      f = genRndFlag(gen, ICDFA_NSTATES(aut), ICDFA_NSYMBOLS(aut), i, t1,incomplete);
      FLAGS(gen)[i-1] = f;
      for(j=t1; j<f; j++){
				*pt++ = RAND(i);
      }
      *pt++ = i;
      t1 = f+1;
    }
    for(j = t1; j < ICDFA_NSYMBOLS(aut)*ICDFA_NSTATES(aut); j++)
      *pt++ = RAND(ICDFA_NSTATES(aut));
  } 
  else { // incomplete skeletom
    for(i = 1; i < ICDFA_NSTATES(aut); i++){
      f = genRndFlag(gen, ICDFA_NSTATES(aut), ICDFA_NSYMBOLS(aut), i, t1,incomplete);
      FLAGS(gen)[i-1] = f;
      for(j=t1; j<f; j++){
				*pt++ = IRAND(i, ICDFAGEN_IBIAS(gen));
      }
      *pt++ = i;
      t1 = f+1;
    }
    for(j = t1; j < ICDFA_NSYMBOLS(aut)*ICDFA_NSTATES(aut); j++)
      *pt++ = IRAND(ICDFA_NSTATES(aut), ICDFAGEN_IBIAS(gen));
  }
  
  /* random set of final states */
  icdfaRndFinalsA(RND_ICDFA(gen));
  /* icdfaRndFinals(RND_ICDFA(gen), RAND(ICDFA_NSTATES(aut))); */
  
  /* we changed the random ICDFA structure */
  ICDFA_ACYCLIC(aut) = MAYBE;
  ICDFA_MINIMAL(aut) = MAYBE;
  
  return RND_ICDFA(gen);
}

extern stringR *icdfaGenRandomS(icdfagen_t gen, int incomplete) {
  icdfa_t l = icdfaGenRandom(gen,incomplete);
  stringR *d = (stringR *)(malloc)(sizeof(stringR));
  d->n_states = l->n_states;
  d->n_symbols = l->n_symbols;
  d->delta = l->automaton;
  d->finals = l->finals;
  return d;
}

extern void icdfaGenShowFlags(icdfagen_t gen, char *sep){
  int i;

  if (gen) {
    for (i = 0; i < N_FLAGS(gen)-1; i++)
      printf("%d%s", FLAGS(gen)[i], sep);
    printf("%d", FLAGS(gen)[i]);
  }
}

/*****************************************
 * bijection between ICDFAs and integers *
 *****************************************/

/*
 * helper function to obtain an ICDFA from an integer
 * equation (4) from "Enumeration and Generation with String Automata Representation"
*/
 void prefixCount(mpz_t rop, int n, int k, int m, int j, int incomplete){
   int i, lim;
   mpz_t foo, bar;
   
   if (incomplete){
     if (m == n-1){
       mpz_set_ui(rop, n+1);
       mpz_pow_ui(rop, rop, n*k-1-j);
       return;
     }
     mpz_init_set_ui(foo, 0);
     mpz_init_set_ui(bar, 0);
     if (j == k*m-1){
       mpz_set_ui(rop, 0);
       for (i = 0; i < k; i++){
	 prefixCount(foo, n, k, m+1, m*k+i, incomplete);
	 mpz_ui_pow_ui(bar, m+2, i);
	 mpz_mul(foo, foo, bar);
	 mpz_add(rop, rop, foo);
       }
     } 
     else {
       prefixCount(foo, n, k, m, j+1, incomplete);
       mpz_mul_ui(foo, foo, m+2);
       prefixCount(bar, n, k, m+1, j+1, incomplete);
       mpz_add(rop ,foo, bar);
     }
     mpz_clear(foo);
     mpz_clear(bar);
   } 
   else {
     if (m == n-1)
       {
	 mpz_set_ui(rop, n);
	 mpz_pow_ui(rop, rop, n*k-1-j);
       } 
     else {
       mpz_set_ui(rop, 0);
       mpz_init_set_ui(foo, 0);
       mpz_init_set_ui(bar, 0);
       lim = (m+1)*k-j-2;
       for (i = 0; i <= lim; i++){
	 prefixCount(foo, n, k, m+1, j+i+1, incomplete);
	 mpz_ui_pow_ui(bar, m+1, i);
	 mpz_mul(foo, foo, bar);
	 mpz_add(rop, rop, foo);
       }
       mpz_clear(foo);
       mpz_clear(bar);
     }
   }
 }

extern void icdfaGenFromInteger(icdfagen_t gen, mpz_t m0){
  int i, j, n = ICDFAGEN_NSTATES(gen), k = ICDFAGEN_NSYMBOLS(gen);
  flag_t *flags = (flag_t*)calloc(n+1, sizeof(flag_t));
  state_t *icdfa = (state_t*)calloc(n*k, sizeof(state_t));
  mpz_t m, s, p, tmp, prefix, save;
  
  mpz_init_set(m, m0);
  mpz_init(s); mpz_init(p); mpz_init(tmp); mpz_init(prefix); mpz_init_set(save, m);
  
  memset(flags, 0-ICDFAGEN_INCOMPLETE(gen), (n+1)*sizeof(flag_t));
  memset(icdfa, 0-ICDFAGEN_INCOMPLETE(gen), n*k*sizeof(state_t));
  
  /* flags */
  mpz_set_ui(s, 1);
  for (i = 1; i < n; i++){
    j = i*k-1;
    mpz_ui_pow_ui(p, i+ICDFAGEN_INCOMPLETE(gen), j-flags[i-1]-1);
    /* p*s*N_{i,j} */
    mpz_mul(tmp, p, s);
    prefixCount(prefix, n, k, i, j, ICDFAGEN_INCOMPLETE(gen));
    mpz_mul(tmp, tmp, prefix);
    while (j >= i-1 && mpz_cmp(m, tmp) >= 0){
      mpz_sub(m, m, tmp);
      j--;
      mpz_div_ui(p, p, i+ICDFAGEN_INCOMPLETE(gen));
      mpz_mul(tmp, p, s);
      prefixCount(prefix, n, k, i, j, ICDFAGEN_INCOMPLETE(gen));
      mpz_mul(tmp, tmp, prefix);
    }
    mpz_ui_pow_ui(tmp, i+ICDFAGEN_INCOMPLETE(gen), j-flags[i-1]-1);
    mpz_mul(s, s, tmp);
    flags[i] = j;
    icdfa[j] = i;
  }
  
  /* idcfa */
  i = k*n-1;
  j = n-1;
  while (mpz_cmp_ui(m, 0) > 0 && j+ICDFAGEN_INCOMPLETE(gen) > 0){
    while (mpz_cmp_ui(m, 0) > 0 && i > flags[j]){
      mpz_mod_ui(tmp, m, j+1+ICDFAGEN_INCOMPLETE(gen));
      mpz_sub_ui(tmp, tmp, ICDFAGEN_INCOMPLETE(gen));
      icdfa[i] = (int)mpz_get_si(tmp);
      mpz_div_ui(m, m, j+1+ICDFAGEN_INCOMPLETE(gen));
      i--;
    }
    i--;
    j--;
  }
  icdfaGenSetFlags(gen, flags+1);
  icdfaGenSetCurrent(gen, icdfa);

  mpz_clear(m);
  mpz_clear(s); mpz_clear(p); mpz_clear(tmp); mpz_clear(prefix); mpz_clear(save);
  free(flags);
  free(icdfa);
}

/* these special cases exist only because, altough we never use
 * such flags, some equations use flag[1] to refer the first
 * reference to the state 1 and flag[n] to simplify some arithmetic
 * as far as the generator is concerned, flag[0] is the index of the
 * first reference to state 1 and flag[n] simply does not exist
 */

flag_t getFlagEx(icdfagen_t gen, int i){
	if (i == 0)
  	return -1;
  if (i == ICDFAGEN_NSTATES(gen))
    return ICDFAGEN_NSTATES(gen)*ICDFAGEN_NSYMBOLS(gen);
	return FLAGS(gen)[i-1];
}

/* equations (6)-(7) */
extern void icdfaGenToInteger(icdfagen_t gen, mpz_t ns){
  int i, j, b, p, n = ICDFAGEN_NSTATES(gen), k = ICDFAGEN_NSYMBOLS(gen);
  icdfa_t icdfa = ICDFAGEN_CURRENT(gen);
  mpz_t nf, nr, m, foo, prefix;
  
  mpz_init(nf); mpz_init(nr); mpz_init(m); mpz_init(foo); mpz_init(prefix);
  mpz_set_ui(nf, 0);
  for (i = n-1; i >= 0; i--){
    b = getFlagEx(gen, i) + 1;
    p = i + ICDFA_INCOMPLETE(icdfa);
    mpz_set_ui(m, 0);
    while (i > 0 && b <= i*k-1) {
      prefixCount(prefix, n, k, i, b, ICDFA_INCOMPLETE(icdfa));
      /* gmp_printf("# %Zd\n", prefix); */
      mpz_mul_ui(foo, prefix, p);
      mpz_add(m, m, foo);
      p *= i + ICDFA_INCOMPLETE(icdfa);
      b++;
    }
    mpz_ui_pow_ui(foo, i+1+ICDFA_INCOMPLETE(icdfa), getFlagEx(gen, i+1) - getFlagEx(gen, i)-1);
    mpz_mul(nf, nf, foo);
    mpz_add(nf, nf, m);
  }
  
  i = k*n-1;
  b = 1;
  mpz_set_ui(nr, 0);
  for (j = n-1; j >= 0; j--){
    while (i > getFlagEx(gen, j)) {
      mpz_add_ui(nr, nr, b*(icdfaGetElem(icdfa, i)+ICDFA_INCOMPLETE(icdfa)));
      b *= j+1+ICDFA_INCOMPLETE(icdfa);
      i--;
    }
    i--;
  }
  
  mpz_add(ns, nf, nr);
  mpz_clear(nf); mpz_clear(nr); mpz_clear(m); mpz_clear(foo); mpz_clear(prefix);
}
