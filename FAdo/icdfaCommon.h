/*
 * icdfaCommon.h: This file is part of libicdfa.
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
 * Copyright 2006-2011 Rogério Reis, Nelma Moreira, Marco Almeida
 *
 * This is part of the FAdo project (http://www.ncc.up.pt/FAdo)
 */


#ifndef ICDFA_COMMON_H
#define ICDFA_COMMON_H

#ifdef INLINE
#define INLINE_DECL extern __inline__
#else
#define INLINE_DECL static
#endif

/* extended boolean */
typedef enum {FALSE, TRUE, MAYBE} BOOL_EX;

/* these types are used by several files */
typedef int state_t;		/**< state type */
typedef int symbol_t;		/**< symbol type */

/* random int */
#define RAND(max) ((int) ((max) * (rand() / (RAND_MAX + 1.0))))
// Old version without bias
// #define IRAND(max) (RAND(max+1)-1)

/* random bit */
#define RANDOMBIT() ((int) (rand()>>2)%2)

#endif /* ICDFA_COMMON_H */
