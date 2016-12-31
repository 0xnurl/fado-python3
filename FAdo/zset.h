/*  zset.h 
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
 *
 * Copyright 2006-2010 Rogério Reis, Nelma Moreira, Marco Almeida
 * 
 * This is part of the FAdo project (http://www.ncc.up.pt/FAdo)
 */

/**
 * @file   zset.h
 * @date   Thu Dec  7 18:33:24 2006
 * 
 * @brief  This is a very simple library to represent and handle (positive) integer sets
 *
 * We use a bitmap to represent each set. In order to have sets of arbitrary size,
 * our bitmaps are mpz_t integers from libgmp. Set theoretical operations are 
 * implemented with libmp's logical and bit manipulation functions.
 * Some trivial functions for set partition manipulation are also included. We use AVL
 * trees to represent each partition (with GLPed code from libavl).
 *
 */

#ifndef _ZSET_H
#define _ZSET_H


#include <string.h>
#include <stdlib.h>
#include <gmp.h>
#include "avl.h"

#ifdef INLINE
#define INLINE_DECL extern __inline__
#else
#define INLINE_DECL static
#endif


/******************************
 * positive integer set stuff *
 ******************************/

typedef unsigned long int set_elm_t; /**< type for the elements of a set (positive integers) */

typedef struct icdfaset {
    unsigned long int size;	/**< maximum number of elements on the set */
    mpz_t bitmap;		/**< libgmp integer representing the bitmap */
} *zset_t;			/**< The type for our set representation */

#define SET_SIZE(S) ((S)->size)
#define SET_DATA(S) ((S)->bitmap)

/** 
 * Initialize a new set
 * 
 * @param n a positive integer such that n-1 is the largest integer in the set
 * 
 * @return a new set
 */
INLINE_DECL zset_t zsetInit(unsigned long int n)
{
    zset_t s;

    s = (zset_t)malloc(sizeof(struct icdfaset));
    if (s) {
	mpz_init2(SET_DATA(s), n);
	SET_SIZE(s) = n;
    }

    return s;
}

/** 
 * Destroy a set and free memory
 * 
 * @param s set to be destroyed
 */
INLINE_DECL void zsetDel(zset_t s)
{
    mpz_clear(SET_DATA(s));
    free(s);
}

/** 
 * Remove all elements from set
 * 
 * @param s set to be emptied
 */
INLINE_DECL void zsetClear(zset_t s)
{
    mpz_set_ui(SET_DATA(s), 0);
}

/** 
 * Add an element to a set
 * 
 * @param s a set
 * @param e the element to be added
 */
INLINE_DECL void zsetAdd(zset_t s, set_elm_t e)
{
    mpz_setbit(SET_DATA(s), e);
}

/** 
 * Add a range of integers to a set
 * 
 * @param s the set
 * @param from the first integer to be added
 * @param to the last integer (this one will not be added)
 */
INLINE_DECL void zsetAddRange(zset_t s, set_elm_t from, set_elm_t to)
{
    while (from < to)
	mpz_setbit(SET_DATA(s), from++);
}

/** 
 * Remove an element from a set
 * 
 * @param s the set
 * @param e the element to be removed
 */
INLINE_DECL void zsetRemove(zset_t s, set_elm_t e)
{
    mpz_clrbit(SET_DATA(s), e);
}

/** 
 * Calculate the intersection of two sets
 * 
 * @param s the set which will hold the result
 * @param s1 a set
 * @param s2 a set
 */
INLINE_DECL void zsetIntersection(zset_t s, zset_t s1, zset_t s2)
{
    mpz_and(SET_DATA(s), SET_DATA(s1), SET_DATA(s2));
}

/** 
 * Calculate the union of two sets
 * 
 * @param s the set which will hold the result
 * @param s1 a set
 * @param s2 a set
 */
INLINE_DECL void zsetUnion(zset_t s, zset_t s1, zset_t s2)
{
    mpz_ior(SET_DATA(s), SET_DATA(s1), SET_DATA(s2));
}

/** 
 * Calculate the difference of two sets
 * 
 * @param s the set which will hold the result
 * @param s1 a set
 * @param s2 a set
 */
INLINE_DECL void zsetDifference(zset_t s, zset_t s1, zset_t s2)
{
/*      mpz_t t; */
/*      mpz_init2(t, SET_SIZE(s1)); */
/*      mpz_xor(t, SET_DATA(s1), SET_DATA(s2)); */
    mpz_com(SET_DATA(s), SET_DATA(s2));
    mpz_and(SET_DATA(s), SET_DATA(s1), SET_DATA(s));
/*     mpz_clear(t); */
}

/** 
 * Calculate the complement of a set
 * 
 * @param s1 the set which will hold the result (s2 complement)
 * @param s2 a set
 */
INLINE_DECL void zsetComplement(zset_t s1, zset_t s2)
{
    mpz_com(SET_DATA(s1), SET_DATA(s2));
}

/** 
 * Check if the set has a given element
 * 
 * @param s the set
 * @param e an integer
 * 
 * @return 1 if the element belongs to the set. 0 otherwise
 */
INLINE_DECL int zsetHasElm(zset_t s, set_elm_t e)
{
    return mpz_tstbit(SET_DATA(s), e);
}

/** 
 * Check if two sets are equal, i.e., have the same elements
 * 
 * @param s1 a set
 * @param s2 a set
 * 
 * @return 0 if the sets are different. an integer different from 0 otherwise
 */
INLINE_DECL int zsetIsEqual(zset_t s1, zset_t s2)
{
    return (mpz_cmp(SET_DATA(s1), SET_DATA(s2)) == 0);
}

/** 
 * Check if a set is empty, i.e., has no elements
 * 
 * @param s a set
 * 
 * @return 0 if there are elements in the set
 */
INLINE_DECL int zsetIsEmpty(zset_t s)
{
    return (mpz_popcount(SET_DATA(s)) == 0);
}

/** 
 * Count the number of elements of a given set
 * 
 * @param s a set
 * 
 * @return the number of elements in s
 */
INLINE_DECL unsigned long int zsetCardinality(zset_t s)
{
    return mpz_popcount(SET_DATA(s));
}

/** 
 * Check if a set is a singleton, i.e., has only one element
 * 
 * @param s a set
 * 
 * @return 0 if the set is not a singleton. otherwise, an integer different from 0
 */
INLINE_DECL int zsetIsSingleton(zset_t s)
{
    return (mpz_popcount(SET_DATA(s)) == 1);
}

/** 
 * Check if all elements of a given set belong to some other set
 * 
 * @param s1 a set
 * @param s2 a set
 * 
 * @return 1 if s1 is a subset of s2. 0 otherwise
 */
INLINE_DECL int zsetIsSubset(zset_t s1, zset_t s2)
{
    int r = 0;
    mpz_t foo;

    mpz_init2(foo, SET_SIZE(s1));
    mpz_and(foo, SET_DATA(s1), SET_DATA(s2));
    if (mpz_cmp(foo, SET_DATA(s1)) == 0)
	r = 1;
    mpz_clear(foo);
    return r;
}

/** 
 * Copy the all the elements of a set to another set. Both sets must have the same size
 * 
 * @param s1 a set
 * @param s2 a set
 *
 * s1 will become equal to s2
 */
INLINE_DECL void zsetCopy(zset_t s1, zset_t s2)
{
    mpz_set(SET_DATA(s1), SET_DATA(s2));
}

/** 
 * Macro to make things a little simpler when iterating through the elements of a set
 * 
 * @param Set a set
 * @param Elem variable to hold each of the elements
 * 
 * This block of code will iterate trough the elements of Set. On each iteration, Elem will
 * be assigned the value of the current element. It is similar to LISP's (dolist (var list))
 *
 */
#define zsetBeginIterate(Set, Elem)					\
    {									\
	unsigned long int _i, _k=mpz_popcount(SET_DATA(Set));		\
	Elem = -1;							\
	for (_i = 0; _i < _k; _i++) {					\
	    Elem = mpz_scan1(SET_DATA(Set), Elem+1);			\

/** 
 * Macro to end what setBeginIterate() started.
 * 
 * @param Set the set
 * @param Elem variable used to hold each of the elements
 * 
 * @return 
 */
#define zsetEndIterate(Set, Elem) } }

/** 
 * A sort of pretty-print
 * 
 * @param s a set
 */
INLINE_DECL void zsetShow(zset_t s, char *sep, int incFlag)
{
  unsigned long int i, gap=0;
  
  if (incFlag) gap =1;
    
    for (i = 0; i < SET_SIZE(s)-1-gap; i++)
	printf("%d%s", mpz_tstbit(SET_DATA(s), i), sep);
    printf("%d", mpz_tstbit(SET_DATA(s), i));
}

/***********************
 * set partition stuff *
 ***********************/

typedef zset_t part_node_t;
typedef avl_tree_t *partition_t; /**< set partition type (uses an AVL tree) */

INLINE_DECL int partitionCompare(const void* n1, const void* n2)
{
    return mpz_cmp(SET_DATA((zset_t)n1), SET_DATA((zset_t)n2));
}

INLINE_DECL void partitionFree(void* p)
{
    zsetDel((zset_t)p);
}

/** 
 * Initialize a set partition
 * 
 * 
 * @return a new set partition
 */
INLINE_DECL partition_t partitionInit(void)
{
    return avl_alloc_tree(partitionCompare, partitionFree);
}

/** 
 * Destroy a previously initialized partition and free all allocated memory
 * 
 * @param p the partition to be destroyed
 */
INLINE_DECL void partitionDel(partition_t p)
{
    avl_free_tree(p);
}

/** 
 * Clear all blocks of a partition
 * 
 * @param p a partition
 */
INLINE_DECL void partitionClear(partition_t p)
{
    avl_free_nodes(p);
}

/** 
 * Check if a partition is empty, i.e., has no blocks
 * 
 * @param p a partition
 * 
 * @return 0 if there are blocks in the partition
 */
INLINE_DECL int partitionIsEmpty(partition_t p)
{
    return (avl_count(p) == 0);
}

/** 
 * Add an element (block) to a partition
 * 
 * @param p a partition
 * @param s the block to add (must be a zset)
 */
INLINE_DECL void partitionAdd(partition_t p, zset_t s)
{
    zset_t foo;
     
    if (zsetIsEmpty(s))
	return;

    foo = zsetInit(SET_SIZE(s));
    zsetCopy(foo, s);
    if (! avl_insert(p, (void*)foo))
	zsetDel(foo);
}

/** 
 * Remove an element (block) from a partition
 * 
 * @param p a partition
 * @param s the block to remove (must be a zset)
 */
INLINE_DECL void partitionRemove(partition_t p, zset_t s)
{
    avl_delete(p, (void*)s);
}

/** 
 * Extract an an element (block) from a partition
 * 
 * @param p a partition
 * @param s the variable which will hold the extracted element
 * 
 * @return 1 if there is something to extract; 0 otherwise
 */
INLINE_DECL int partitionPop(partition_t p, zset_t s)
{
    zset_t foo;

    if (avl_count(p))
    {
	foo = (zset_t)avl_at(p, 0)->item;
   	zsetCopy(s, foo);
	partitionRemove(p, foo);
	return 1;
    }
    return 0;
}

/** 
 * Replace a block of the partition with another one
 * 
 * @param p a partition
 * @param s1 block to be replaced
 * @param s2 block that will replace s1
 */
INLINE_DECL void partitionReplace(partition_t p, zset_t s1, zset_t s2)
{
    partitionRemove(p, s1);
    partitionAdd(p, s2);
}

/** 
 * Count the number of blocks in a partition
 * 
 * @param p a partition
 * 
 * @return the number of elements in p
 */
INLINE_DECL int partitionCardinality(partition_t p)
{
    return avl_count(p);
}

/** 
 * Macro to make things a little simpler when iterating through the elements of a partition
 * 
 * @param P a partition
 * @param S set to hold each of the blocks
 * 
 * This piece of code will iterate trough the elements of P. On each iteration, S will
 * be assigned the value of the current block. It is similar to LISP's (dolist (var list))
 *
 */
#define partitionBeginIterate(P, S)				\
    {								\
	unsigned long int _i, _j = partitionCardinality(P);	\
	for (_i = 0; _i < _j; _i++) {				\
	    zsetCopy(S, (zset_t)avl_at(P, _i)->item);


/** 
 * Macro to end what partitionBeginIterate() started.
 * 
 * @param P the partition
 * @param S the set used to hold each of the blocks
 * 
 * @return 
 */
#define partitionEndIterate(P, S) } }

/** 
 * A sort of set partition pretty-print
 * 
 * @param p a partition
 */
INLINE_DECL void partitionShow(partition_t p, char *sep)
{
    unsigned long int i, n;
    
    n = avl_count(p)-1;

    printf("{ ");
    for (i = 0; i < n; i++) {
	putchar('{');
	zsetShow((zset_t)avl_at(p, i)->item, sep,0);
	printf("} ");
    }
    putchar('{');
    zsetShow((zset_t)avl_at(p, i)->item, sep,0);
    printf("} ");
    printf("}");
}

#endif /* _ZSET_H */
