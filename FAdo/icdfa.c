/*
 * icdfa.c: This file is part of libicdfa.
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
 * This is part of the FAdo project (http://www.dcc.fc.up.pt/FAdo)
 */


#if HAVE_CONFIG_H
#include <config.h>
#endif
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#ifdef HAVE_LIBXML2
#include <libxml/tree.h>
#endif
#include "icdfaCommon.h"
#include "zset.h"
#include "icdfa.h"


/* hopcroft stuff */
static void hopcroftInit(icdfa_t icdfa){
  int i, nStates;
  hopcroft_t *aux = &ICDFA_HOPCROFT_STRUCT(icdfa);

  nStates = ICDFA_INCOMPLETE(icdfa) ? (ICDFA_NSTATES(icdfa)+1) : ICDFA_NSTATES(icdfa);

  aux->P = (zset_t*)calloc(nStates, sizeof(zset_t));
  for (i = 0; i < nStates; i++)
    aux->P[i] = zsetInit(nStates);
  aux->L = partitionInit();
  aux->nf = zsetInit(nStates);
  aux->B1 = zsetInit(nStates);
  aux->B2 = zsetInit(nStates);
  aux->C = zsetInit(nStates);
  aux->trans = zsetInit(nStates);
  aux->c_trans = zsetInit(nStates);
}

static void hopcroftDel(icdfa_t icdfa){
  int i, nStates;
  hopcroft_t *aux = &ICDFA_HOPCROFT_STRUCT(icdfa);
  
  nStates = ICDFA_INCOMPLETE(icdfa) ? (ICDFA_NSTATES(icdfa)+1) : ICDFA_NSTATES(icdfa);
  
  for (i = 0; i < nStates; i++)
    zsetDel(aux->P[i]);
  free(aux->P);
  partitionDel(aux->L);
  zsetDel(aux->nf);
  zsetDel(aux->B1);
  zsetDel(aux->B2);
  zsetDel(aux->C);
  zsetDel(aux->trans);
  zsetDel(aux->c_trans);
}

/* initialization step */
static void hopcroftInitialize(icdfa_t icdfa){
  int i;
  zset_t C0, C1;
  hopcroft_t *aux = &ICDFA_HOPCROFT_STRUCT(icdfa);
  
  for (i = 0; i < ICDFA_NSTATES(icdfa); i++)
    zsetClear(aux->P[i]);
  partitionClear(aux->L);
  
  zsetDifference(aux->nf, ICDFA_STATES(icdfa), ICDFA_FINAL_STATES(icdfa));
  if (zsetCardinality(ICDFA_FINAL_STATES(icdfa)) < zsetCardinality(aux->nf)){
      C0 = aux->nf;
      C1 = ICDFA_FINAL_STATES(icdfa);
    }
  else {
    C1 = aux->nf;
    C0 = ICDFA_FINAL_STATES(icdfa);
  }
  
  zsetCopy(aux->P[0], C0);
  zsetCopy(aux->P[1], C1);
  partitionAdd(aux->L, C1);
  
  if (zsetCardinality(C0) > 0 && zsetCardinality(C1) > 0)
    aux->k = 2;
  else
    aux->k = 1;
}

static void hopcroftSplitterTransitions(icdfa_t icdfa, symbol_t a){
  hopcroft_t *aux = &ICDFA_HOPCROFT_STRUCT(icdfa);
  
  icdfaUnDeltaSet(icdfa, aux->C, a, aux->trans);
  zsetComplement(aux->c_trans, aux->trans);
}

static int hopcroft(icdfa_t icdfa){
  int i, size;
  symbol_t a;
  hopcroft_t *aux = &ICDFA_HOPCROFT_STRUCT(icdfa);
  
  hopcroftInitialize(icdfa);
  
  while (! partitionIsEmpty(aux->L)){
    partitionPop(aux->L, aux->C);
    for (a = 0; a < ICDFA_NSYMBOLS(icdfa); a++){
      /* this doesn't have to be calculated the next cycle */
      hopcroftSplitterTransitions(icdfa, a);
      size = aux->k;
      for (i = 0; i < size; i++){
	/* split */
	zsetIntersection(aux->B1, aux->P[i], aux->trans);
	zsetIntersection(aux->B2, aux->P[i], aux->c_trans);
	if (zsetCardinality(aux->B1) < zsetCardinality(aux->B2)){
	  zsetCopy(aux->P[i], aux->B2);
	  partitionAdd(aux->L, aux->B1);
	  if (! zsetIsEmpty(aux->B1))
	    zsetCopy(aux->P[aux->k++], aux->B1);
	}
	else {
	  zsetCopy(aux->P[i], aux->B1);
	  partitionAdd(aux->L, aux->B2);
	  if (! zsetIsEmpty(aux->B2))
	    zsetCopy(aux->P[aux->k++], aux->B2);
	}
      }
    }
  }
  return (aux->k == ICDFA_NSTATES(icdfa));
}

/* initialize (constructor) */
extern icdfa_t icdfaInit(int states, int symbols, int incomplete){
	
  int actual_states;
  icdfa_t icdfa = (icdfa_t) malloc(sizeof(struct icdfa));
  
  actual_states = incomplete ? (states+1) : states;
  
  ICDFA_NSTATES(icdfa) = states;
  ICDFA_NSYMBOLS(icdfa) = symbols;
  ICDFA_INCOMPLETE(icdfa) = incomplete;
  
  ICDFA_SIZE(icdfa) = states*symbols;
  
  ICDFA_STATES(icdfa) = zsetInit(actual_states);
  ICDFA_SYMBOLS(icdfa) = zsetInit(symbols);
  ICDFA_FINAL_STATES(icdfa) = zsetInit(actual_states);
  ICDFA_ACYCLIC(icdfa) = MAYBE;
  ICDFA_MINIMAL(icdfa) = MAYBE;
  
  hopcroftInit(icdfa);
  
  if (incomplete)
    ICDFA(icdfa) = (state_t *) calloc((ICDFA_SIZE(icdfa)+symbols), sizeof(state_t));
  else
    ICDFA(icdfa) = (state_t *) calloc(ICDFA_SIZE(icdfa), sizeof(state_t));
  
  /* initialize the sets os states and symbols */
  zsetAddRange(ICDFA_STATES(icdfa), 0, actual_states);
  zsetAddRange(ICDFA_SYMBOLS(icdfa), 0, symbols);
  
  return icdfa;
}

/* memory cleanup (destructor) */
extern void icdfaDel(icdfa_t icdfa){
  zsetDel(ICDFA_STATES(icdfa));
  zsetDel(ICDFA_SYMBOLS(icdfa));
  zsetDel(ICDFA_FINAL_STATES(icdfa));
  
  hopcroftDel(icdfa);
  
  free(ICDFA(icdfa));
  free(icdfa);
}

/* least state between i and j */
extern state_t icdfaFirstState(icdfa_t icdfa, int i, int j){
  state_t x = ICDFA_ELEM(i++, icdfa);
  
  while (i < j) {
    if (ICDFA_ELEM(i, icdfa) < x)
      x = ICDFA_ELEM(i, icdfa);
    i++;
  }
  
  return x;
}

/* make a copy of an ICDFA */
extern void icdfaCopy(icdfa_t dst, icdfa_t src){
  if (ICDFA_NSTATES(dst) == ICDFA_NSTATES(src) && ICDFA_NSYMBOLS(dst) == ICDFA_NSYMBOLS(src)){
    memcpy(ICDFA(dst), ICDFA(src), ICDFA_SIZE(src)*sizeof(state_t));
    ICDFA_INCOMPLETE(dst) = ICDFA_INCOMPLETE(src);
    zsetCopy(ICDFA_FINAL_STATES(dst), ICDFA_FINAL_STATES(src));
    ICDFA_ACYCLIC(dst) = ICDFA_ACYCLIC(src);
    ICDFA_MINIMAL(dst) = ICDFA_MINIMAL(src);
  }
}

/* simple pretty-print */
extern void icdfaShow(icdfa_t icdfa, char *sep){
  int i;
  
  if (icdfa == NULL)
    return;
  
  for (i = 0; i < ICDFA_SIZE(icdfa)-1; i++)
    printf("%d%s", ICDFA_ELEM(i, icdfa), sep);
  printf("%d", ICDFA_ELEM(i, icdfa));
}

/* xml output */
#ifdef HAVE_LIBXML2
extern xmlNodePtr icdfaXML(icdfa_t icdfa){
  int i;
  xmlNodePtr root, tmp, alpha, states, content, trans;
  char *str = icdfaGetString(icdfa, 0);
  
  root = xmlNewNode(NULL, ICDFA_CHAR2XML("automaton"));
  
  /* string */
  xmlNewChild(root, NULL, ICDFA_CHAR2XML("string_rep"), ICDFA_CHAR2XML(str));
  /* alphabet */ 
  alpha = xmlNewChild(root, NULL, ICDFA_CHAR2XML("alphabet"), NULL);
  sprintf(str, "%d", ICDFA_NSYMBOLS(icdfa));
  xmlNewProp(alpha, ICDFA_CHAR2XML("nsymbols"), ICDFA_CHAR2XML(str));
  for (i = 0; i < ICDFA_NSYMBOLS(icdfa); i++) {
    tmp = xmlNewChild(alpha, NULL, ICDFA_CHAR2XML("symbol"), NULL);
    sprintf(str, "%d", i);
    xmlNewProp(tmp, ICDFA_CHAR2XML("value"), ICDFA_CHAR2XML(str));
  }
  /* content */
  /* states */
  sprintf(str, "%d", ICDFA_NSTATES(icdfa));
  content = xmlNewChild(root, NULL, ICDFA_CHAR2XML("content"), NULL);
  xmlNewProp(content, ICDFA_CHAR2XML("nstates"), ICDFA_CHAR2XML(str));
  states = xmlNewChild(content, NULL, ICDFA_CHAR2XML("states"), NULL);
  for (i = 0; i < ICDFA_NSTATES(icdfa); i++) {
    tmp = xmlNewChild(states, NULL, ICDFA_CHAR2XML("state"), NULL);
    sprintf(str, "%d", i);
    xmlNewProp(tmp, ICDFA_CHAR2XML("number"), ICDFA_CHAR2XML(str));
    xmlNewProp(tmp, ICDFA_CHAR2XML("name"), ICDFA_CHAR2XML(str));
  }
  /* transitions */
  trans = xmlNewChild(content, NULL, ICDFA_CHAR2XML("transitions"), NULL);
  for (i = 0; i < ICDFA_SIZE(icdfa); i++) {
    tmp = xmlNewChild(trans, NULL, ICDFA_CHAR2XML("transition"), NULL);
    sprintf(str, "%d", i/ICDFA_NSYMBOLS(icdfa));
    xmlNewProp(tmp, ICDFA_CHAR2XML("src"), ICDFA_CHAR2XML(str));
    sprintf(str, "%d", ICDFA(icdfa)[i]);
    xmlNewProp(tmp, ICDFA_CHAR2XML("dst"), ICDFA_CHAR2XML(str));
    sprintf(str, "%d", i%ICDFA_NSYMBOLS(icdfa));	
    xmlNewProp(tmp, ICDFA_CHAR2XML("label"), ICDFA_CHAR2XML(str));
  }
  /* initial state */
  tmp = xmlNewChild(trans, NULL, ICDFA_CHAR2XML("initial"), NULL);
  xmlNewProp(tmp, ICDFA_CHAR2XML("state"), ICDFA_CHAR2XML("0"));
  /* final states */
  for (i = 0; i < ICDFA_NSTATES(icdfa); i++) {
    if (zsetHasElm(ICDFA_FINAL_STATES(icdfa), i)) {
      tmp = xmlNewChild(trans, NULL, ICDFA_CHAR2XML("final"), NULL);
      sprintf(str, "%d", i);	
      xmlNewProp(tmp, ICDFA_CHAR2XML("state"), ICDFA_CHAR2XML(str));
    }
  }
  
  free(str);
  return root;
}
#endif

/* "pretty"-print  */
extern void icdfaPretty(icdfa_t icdfa){
  int i, size;
  
  if (icdfa == NULL)
    return;
  
  size = ICDFA_INCOMPLETE(icdfa) ? (ICDFA_SIZE(icdfa)+ICDFA_NSYMBOLS(icdfa)) : 
    ICDFA_SIZE(icdfa);
  
  printf("[");
  for (i = 0; i < size; i++) {
    if (i % ICDFA_NSYMBOLS(icdfa) == 0) {
      if (i)
	printf("], [");
      else
	printf("[");
      printf("%d", ICDFA_ELEM(i, icdfa));
    }
    else
      printf(", %d", ICDFA_ELEM(i, icdfa));
  }
  printf("]]");
}

/* returns a string with the ICDFA representation (with final states) */
extern char* icdfaGetString(icdfa_t icdfa, int with_finals){
  int i=1, size, n = ICDFA_NSTATES(icdfa)-1;
  char *s;
  
  /* number of digits of the largest digit */
  while(n /= 10)
    i++;
  
  size = ICDFA_NSTATES(icdfa)*ICDFA_NSYMBOLS(icdfa)*(i + 1) + 1;
  if (with_finals)
    size += 2*zsetCardinality(ICDFA_FINAL_STATES(icdfa))*(i+3);
  
  if (! (s=(char*)calloc(size, sizeof(char))))
    return NULL;
  
  n=0;
  for (i = 0; i < ICDFA_SIZE(icdfa); i++) {
    n += 1;
    sprintf(s, "%s %d", s, ICDFA(icdfa)[i]);
  }
  
  if (with_finals) {
    sprintf(s, "%s;", s);
    for (i = 0; i < ICDFA_NSTATES(icdfa); i++)
      if (zsetHasElm(ICDFA_FINAL_STATES(icdfa), i))
	sprintf(s, "%s %d", s, i);
  }
  
  return s;
}


/* transition function for a set of states */
extern void icdfaDeltaSet(icdfa_t icdfa, zset_t states, symbol_t x, zset_t out){
  state_t i;
  
  zsetClear(out);
  zsetBeginIterate(states, i);
  zsetAdd(out, ICDFA(icdfa)[ICDFA_NSYMBOLS(icdfa)*i+x]);
  zsetEndIterate(states, i);
}

/* transition function inverse for a set of states */
extern void icdfaUnDeltaSet(icdfa_t icdfa, zset_t states, symbol_t x, zset_t out){
  state_t i;
  
  zsetClear(out);
  for (i = 0; i < ICDFA_NSTATES(icdfa); i++){
    if (zsetHasElm(states, ICDFA(icdfa)[i*ICDFA_NSYMBOLS(icdfa)+x]))
      zsetAdd(out, i);
  }
}

/* decide which algorithm to use */
static int minimize(icdfa_t icdfa, MINIMALP_ALGORITHM algorithm){
  int ret;
  
  switch(algorithm){
  case HOPCROFT:
  default:
    ret = hopcroft(icdfa);
  }
  
  return ret;
}

extern int icdfaMinimalP(icdfa_t icdfa, MINIMALP_ALGORITHM algorithm){
  int ret, size = ICDFA_SIZE(icdfa)+ICDFA_NSYMBOLS(icdfa);
  state_t i;
  
  if (ICDFA_MINIMAL(icdfa) != MAYBE)
    return ICDFA_MINIMAL(icdfa);
  
  if (ICDFA_INCOMPLETE(icdfa)){
    for (i = 0; i < size; i++)
      if (ICDFA(icdfa)[i] == -1 || i >= ICDFA_SIZE(icdfa))
	ICDFA(icdfa)[i] = ICDFA_NSTATES(icdfa);
    ICDFA_NSTATES(icdfa)++;
    ret = minimize(icdfa, algorithm);
    ICDFA_NSTATES(icdfa)--;
    for (i = 0; i < size; i++)
      if (ICDFA(icdfa)[i] == ICDFA_NSTATES(icdfa))
	ICDFA(icdfa)[i] = -1; /* change this and the previous -1 to BOTTOM!! */
  }
  else
    ret = minimize(icdfa, algorithm);
  
  return ret;
}

extern int icdfaInversibleP(icdfa_t icdfa){
  int i;
  state_t st;
  symbol_t sy;
  state_t *x;
  
  x = (state_t *)calloc(ICDFA_SIZE(icdfa), sizeof(state_t));
  for (i = 0; i < ICDFA_SIZE(icdfa); i++){
    st = ICDFA(icdfa)[i];
    sy = i%ICDFA_NSYMBOLS(icdfa);
    if (x[st*ICDFA_NSYMBOLS(icdfa)+sy] == 0) {
      x[st*ICDFA_NSYMBOLS(icdfa)+sy] = 1;
    }
    else {
      free(x);
      return 0;
    }
  }

  free(x);
  return 1;
}

extern int icdfaReversibleP(icdfa_t icdfa){
  state_t st, *foo;
  symbol_t sym;
  
  foo = (state_t*)calloc(ICDFA_NSTATES(icdfa), sizeof(state_t));
  
  for (sym = 0; sym < ICDFA_NSYMBOLS(icdfa); sym++){
    memset(foo, 0, ICDFA_NSTATES(icdfa)*sizeof(state_t));
    for (st = 0; st < ICDFA_NSTATES(icdfa); st++)
      if (foo[ICDFA(icdfa)[st*ICDFA_NSYMBOLS(icdfa)+sym]] == 0)
	foo[ICDFA(icdfa)[st*ICDFA_NSYMBOLS(icdfa)+sym]] = 1;
      else {
	free(foo);
	return 0;
      }
  }
  free(foo);
  return 1;
}

extern int icdfaNextFinalCfg(zset_t finals, unsigned int n){
  if (zsetCardinality(finals) == n+1)
    return 0;
  
  if (zsetHasElm(finals, n)) {
    zsetRemove(finals, n);
    return icdfaNextFinalCfg(finals, n-1);
  }
  
  zsetAdd(finals, n);
  
  return 1;
}

extern int icdfaNextFinalStates(icdfa_t icdfa){
  int r;
  
  r = icdfaNextFinalCfg(ICDFA_FINAL_STATES(icdfa), ICDFA_NSTATES(icdfa)-1);
  ICDFA_MINIMAL(icdfa) = MAYBE;
  return r;
}


/* This generates final states uniformly for a given
 * icdfa skeleton */
extern void icdfaRndFinalsA(icdfa_t icdfa){
  int *v, i, j=0, n;
  zset_t finals = ICDFA_FINAL_STATES(icdfa);
  
  n = ICDFA_NSTATES(icdfa);
  v = (int *)malloc(n*sizeof(int));
  
  for(i=0; i< n; i++)
    if (RANDOMBIT())
      v[j++] = i;
  
  
  zsetClear(finals);
  for(i=0;i<j;i++)
    zsetAdd(finals,v[i]);
  
  free(v);
}  

/* the method is as follows:
 * we permute elements of v f times; the permuted elements are used
 * for the final states 
 * (f is the number of final states) */
extern void icdfaRndFinals(icdfa_t icdfa, int f){
  int x, t=0, i, *v, n0, n;
  zset_t finals = ICDFA_FINAL_STATES(icdfa);
  
  n0 = n = ICDFA_NSTATES(icdfa);    
  v = (int*)malloc(n*sizeof(int));
  
  for (i = 0; i < n; i++)
    v[i] = i;
  
  while (f--){
    x = RAND(n);
    t = v[x];
    v[x] = v[n-1];
    v[n-1] = t;
    n--;
  }

  zsetClear(finals);
  for (i = n0-1; i > n-1; i--)
    zsetAdd(finals, v[i]);
  
  free(v);
}

static void dfsStrong(int x, int **matrix, int *visited, int n){
  int i;

  visited[x] = 1;
  for (i = 0; i < n; i++)
    if (matrix[x][i] && !visited[i])
      dfsStrong(i, matrix, visited, n);
}

/* */
extern int icdfaStrongP(icdfa_t icdfa){
  int i, k=0, strong=1;
  state_t src, dst;
  int **matrix, *visited;
  
  /* mem */
  matrix = (int**)calloc(ICDFA_NSTATES(icdfa), sizeof(int*));
  for (i = 0; i < ICDFA_NSTATES(icdfa); i++)
    matrix[i] = (int*)calloc(ICDFA_NSTATES(icdfa), sizeof(int));
  visited = (int*)calloc(ICDFA_NSTATES(icdfa), sizeof(int));
  
  /* matrix */
  for (i = 0; i < ICDFA_SIZE(icdfa); i++) {
    src = i/ICDFA_NSYMBOLS(icdfa);
    dst = ICDFA(icdfa)[i];
    matrix[dst][src] = 1;
  }
  
  /* dfs */
  for (i = 0; i < ICDFA_NSTATES(icdfa); i++) {
    if (! visited[i]) {
      k++;
      if (k == 2) {
	strong = 0;
	break;
      }
      dfsStrong(i, matrix, visited, ICDFA_NSTATES(icdfa));
    }
  }
  
  /* cleanup */
  for (i = 0; i < ICDFA_NSTATES(icdfa); i++)
    free(matrix[i]);
  free(matrix);
  free(visited);
  
  return strong;
}

static void dfsAcyclic(icdfa_t icdfa, state_t st, state_t *visited, state_t *mark, int *ret){
  state_t i, dst, l1, l2;
  
  visited[st] = 1;
  mark[st] = 1;
  
  l1 = st*ICDFA_NSYMBOLS(icdfa);
  l2 = l1 + ICDFA_NSYMBOLS(icdfa);
  
  for (i = l1; i < l2; i++){
    dst = ICDFA(icdfa)[i];
    /* 
     * when the icdfa is incomplete (and it must be to be acyclic)
     * -1 represents a transition to the dead state (liskovets)
     */
    if (dst != -1) {
      if (! visited[dst])
	dfsAcyclic(icdfa, dst, visited, mark, ret);
      else
	if (mark[dst])
	  *ret = 1;
    }
  }
  mark[st] = 0;
}

extern int icdfaAcyclicP(icdfa_t icdfa){
  int i, ac;
  state_t *visited, *mark;
  
  if (ICDFA_ACYCLIC(icdfa) != MAYBE)
    return ICDFA_ACYCLIC(icdfa);
  
  /* this will only happen when the user is stupid, but... */
  if (! ICDFA_INCOMPLETE(icdfa))
    return 0;
  
  visited = (state_t*)calloc(ICDFA_NSTATES(icdfa), sizeof(state_t));
  mark = (state_t*)calloc(ICDFA_NSTATES(icdfa), sizeof(state_t));
  
  for (i = 0; i < ICDFA_NSTATES(icdfa); i++)
    if (visited[i] == 0){
      ac = 0;
      dfsAcyclic(icdfa, i, visited, mark, &ac);
      /* has a cycle */
      if (ac){
	ICDFA_ACYCLIC(icdfa) = FALSE;
	free(visited);
	free(mark);
	return 0;
      }
    }

  ICDFA_ACYCLIC(icdfa) = TRUE;
  free(visited);
  free(mark);
  return 1;
}

static int CCompFinal(icdfa_t icdfa, state_t st){
  int c,l,i;
  state_t *visited, *mark, dst, l1, l2;
  
  if (zsetHasElm(ICDFA_FINAL_STATES(icdfa),st))
	return 1;
  
  visited = (state_t*)calloc(ICDFA_NSTATES(icdfa), sizeof(state_t));
  mark = (state_t*)calloc(ICDFA_NSTATES(icdfa), sizeof(state_t));
  
  visited[0] = st;
  mark[st] = 1;
  
  l = 1;
  i = 0;
  while (1) {
    st = visited[i];
    l1 = st*ICDFA_NSYMBOLS(icdfa);
    l2 = l1 + ICDFA_NSYMBOLS(icdfa);
    for (c = l1; c < l2; c++){
      dst = ICDFA(icdfa)[c];
      if (dst != -1) {
	if (!mark[dst]) {
	  if (zsetHasElm(ICDFA_FINAL_STATES(icdfa),dst)){ 
	    free(visited);
	    free(mark);
	    return 1;
	  }  
	  visited[l++]=dst;
	  mark[dst]=1;
	}
      }
    }
    i += 1;
    if (i >= l) {
      free(visited);
      free(mark);
      return 0;
    }
  }
}

extern int icdfaTrimP(icdfa_t icdfa){
  state_t i;
  
  for (i = 0; i < ICDFA_NSTATES(icdfa); i++) 
    if (!CCompFinal(icdfa,i))
      return 0;
  return 1;
}

