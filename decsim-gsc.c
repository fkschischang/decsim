/*
 * decsim --- simulate a generalized staircase code with extended Hamming
 *            constituent codes and arbitrary encoder memory.
 *
 * Copyright 2023 Frank R. Kschischang <frank@ece.utoronto.ca>
 *
 * Written by Frank R. Kschischang, June 8-17, 2023,
 *    with later modifications made by Mohannad Shehadeh.
 * 
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/*
	Modified by Mohannad Shehadeh. 
	ONLY TESTED TO COMPILE WITH GCC AND NOT NECESSARILY COMPLIANT! 

	The changes are summarized as follows:

	1. A variant of the scheme with Golomb rulers
	rather than linear rulers was implemented. Instead of constraining
	adjacent blocks i - k for k = 0, 1, ..., M together, we constrain
	blocks i - GOLOMB[k] for k = 0, 1, ..., M together. The component
	code length remains the same but the memory requirement becomes 
	GOLOMB[M] which is the value assigned to the parameter MEMORY. 
	As before, conventional staircase codes are recovered when M = 1
	in which case MEMORY = 1. 
	2. The non-systematic parity-check matrix is replaced with a systematic
	one with two functions implementing the forward and inverse systematizing
	permutations. These are called synFromErrorloc which generates the columns
	of the parity-check matrix and errorlocFromSyn which inverts synFromErrorloc.
	Both the error locations and the syndromes are represented as unsigned 32-bit
	integers. When the component code length S*(M+1) is between powers of two, 
	it is possible that errorlocFromSyn is passed an out of range syndrome which 
	is not a column of the parity-check matrix due to code shortening. In this 
	case, the convention adopted is that errorlocFromSyn should return a value
	larger than S*(M+1)-1. Note that this does not require using any more bits 
	than would already be necessary to represent S*(M+1) error locations and is
	naturally accomplished by algebraic permutations.
	3. The unterminated/convolutional scheme is converted into a strict block
	coding scheme by specifying a frame length parameter F and performing a 
	pseudotermination procedure described further below. The frame length is
	expected to be much larger than the decoding window to mitigate the rate
	loss. Moreover, the gap to the hard-decision Shannon limit is calculated
	with respect to the block code rate rather than the unterminated rate. 
	Conversion into a strict block coding scheme allows for sound
	measurements of BERs and FERs in the waterfall regime where the dominant
	error events are error propagation events.  
	4. The -b command-line argument specifying a number of blocks to transmit
	is replaced with an -f command-line argument specifying a number of
	frames to transmit. 
	5. The -e parameter now specifies a number of frame errors to
	measure before stopping and a batch is defined in terms of a number 
	of frames. 
	6. The maximum memory is increased to 15. Arbitrary linear permutations
	can be specified by altering the definitions.
	7. A decoding sweep now comprises only checking component codewords
	whose entire span is in the receiver buffer.
	8. 64-bit integers are used for computing permutations to prevent
	overflow issues. 
	9. A significant change has been made where the modulo-(B=W+MEMORY) indexing
	was replaced with modulo-W indexing and all buffer sizes are now only W. The
	way the change was implemented is documented near the relevant functions. As
	a part of this, the syndromes associated with a modulo-W block index are now
	those corresponding to component codewards which START at that block. Importantly,
    we no longer reserve more memory than is actually needed or used.
*/

/*
   Key parameters:

   S:   Width of a staircase block; each square block contains S*S bits.
   M:   Memory parameter.  Extended Hamming codewords have length S*(M+1).
   W:   Decoding window size in number of staircase blocks. 
   F:   Frame length. Number of staircase blocks from which to form a frame.

   BatchSize: number of frames to process between error-count
              valuations.
   ErrorsToFind: minimum number of frame errors to find before stopping.
   SweepsPerBlock: maximum number of newest-to-oldest sweeps before
                   receiving next block.
   MaxBatches: maximum number of batches to send.

   Consider the parity-check matrix for an extended binary 
   Hamming code whose columns are the binary representations of 
   2*j + 1 for j = 0, 1, ..., 2^m-1 for some m. We consider the
   extended binary Hamming code obtained by permuting the columns
   of this parity-check matrix according to a pre-chosen 
   invertible affine transformation of the column index j performing
   integer arithmetic modulo 2^m. Such affine transformations
   guaranteeing systematicity were found for m = 3, 4, ..., 16.
   Component codes are taken to be one of these 14 codes shortened
   as needed. The purpose of using such algebraically defined 
   systematizing permutations is to preserve the simple LUT-free 
   syndrome generation and decoding associated with the unpermuted 
   naturally-ordered parity-check matrix which is unfortunately 
   not guaranteed to be systematic.
   
   Finally, we remark that, somewhat counter-intuitively, the choice 
   of column permutation for the extended Hamming parity-check matrix
   can have a slight but measurable impact on performance even in 
   the absence of shortening. This is because the ordering of the 
   columns can impact the spatial correlations between errors of
   odd weight greater than or equal to three and the consequent 
   miscorrections. As a result, expect slight performance 
   differences if different extended Hamming parity-check matrices
   are used. 
   
*/

/*
	FRAMING/PSEUDOTERMINATION PROCEDURE:
	
	Specify a frame length F in number of blocks to simulate the block 
	code obtained by the following pseudotermination procedure:  

	Once F blocks are received, F-W blocks should have been delivered/decoded
	with the last W sitting in the buffer.
	The last W of the F blocks delivered are assumed to contain fixed (zero) 
	S-by-(S-parity) information subblocks so that only the S-by-parity parity 
	subblocks need to be transmitted. As a result, the total number of bits 
	transmitted is (F-W)*S*S + W*S*parity of which 
	(F-W)*S*(S-parity) is information. The ratio of these two quantities is 
	the overall rate of the block code. 

	Alternatively, the framing rate loss is given by 
	R_framing  = ((F-W)*S)/((F-W)*S + W*parity)
	and the the nominal (unterminated scheme) rate is given by
	R_nominal = 1-parity/S. The overall rate of the resulting block code is 
	then given by R = R_nominal*R_framing. 
*/


/* The following parameters completely specify the code and decoding scheme: */
// Decoding window size is W, suggested value is 2*(MEMORY+1) to 5*(MEMORY+1)
// The MEMORY parameter is not to be modified directly, only via M 
#define S 179
#define M 4
#if (M == 0)
	//static const int GOLOMB[M+1] = {0};
    static const int MEMORY_MINUS_GOLOMB[M+1] = {0};
	#define MEMORY 0
#elif (M == 1)
	//static const int GOLOMB[M+1] = {0, 1};
    static const int MEMORY_MINUS_GOLOMB[M+1] = {1, 0};
	#define MEMORY 1
#elif (M == 2)
	//static const int GOLOMB[M+1] = {0, 1, 3};
    static const int MEMORY_MINUS_GOLOMB[M+1] = {3, 2, 0};
	#define MEMORY 3
#elif (M == 3)
	//static const int GOLOMB[M+1] = {0, 1, 4, 6};
    static const int MEMORY_MINUS_GOLOMB[M+1] = {6, 5, 2, 0};
	#define MEMORY 6
#elif (M == 4)
	//static const int GOLOMB[M+1] = {0, 1, 4, 9, 11};
    static const int MEMORY_MINUS_GOLOMB[M+1] = {11, 10, 7, 2, 0};
	#define MEMORY 11
#elif (M == 5)
	//static const int GOLOMB[M+1] = {0, 1, 4, 10, 12, 17};
    static const int MEMORY_MINUS_GOLOMB[M+1] = {17,  16,  13,  7,  5,  0};
	#define MEMORY 17
#elif (M == 6)
	//static const int GOLOMB[M+1] = {0, 1, 4, 10, 18, 23, 25};
    static const int MEMORY_MINUS_GOLOMB[M+1] = {25,  24,  21,  15,  7,  2,  0};
	#define MEMORY 25
#elif (M == 7)
	//static const int GOLOMB[M+1] = {0, 1, 4, 9, 15, 22, 32, 34};
    static const int MEMORY_MINUS_GOLOMB[M+1] = {34,  33,  30,  25,  19,  12,  2,  0};
	#define MEMORY 34
#elif (M == 8)
	//static const int GOLOMB[M+1] = {0, 1, 5, 12, 25, 27, 35, 41, 44};
    static const int MEMORY_MINUS_GOLOMB[M+1] = {44,  43,  39,  32,  19,  17,  9,  3,  0};
	#define MEMORY 44
#elif (M == 9)	
	//static const int GOLOMB[M+1] = {0, 1, 6, 10, 23, 26, 34, 41, 53, 55};
    static const int MEMORY_MINUS_GOLOMB[M+1] = {55,  54,  49,  45,  32,  29,  21,  14,  2,  0};
	#define MEMORY 55
#elif (M == 10)
	//static const int GOLOMB[M+1] = {0, 1, 4, 13, 28, 33, 47, 54, 64, 70, 72};
    static const int MEMORY_MINUS_GOLOMB[M+1] = {72,  71,  68,  59,  44,  39,  25,  18,  8, 2,  0};
	#define MEMORY 72
#elif (M == 11)
	//static const int GOLOMB[M+1] = {0, 2, 6, 24, 29, 40, 43, 55, 68, 75, 76, 85};
    static const int MEMORY_MINUS_GOLOMB[M+1] = {85,  83,  79,  61,  56,  45,  42,  30,  17,  10,  9,  0};
	#define MEMORY 85
#elif (M == 12)
	//static const int GOLOMB[M+1] = {0, 2, 5, 25, 37, 43, 59, 70, 85, 89, 98, 99, 106};
    static const int MEMORY_MINUS_GOLOMB[M+1] = {106,  104,  101,  81,  69,  63,  47,  36,  21,  17,  8,  7,  0};
	#define MEMORY 106
#elif (M == 13)
	//static const int GOLOMB[M+1] = {0, 4, 6, 20, 35, 52, 59, 77, 78, 86, 89, 99, 122, 127};
    static const int MEMORY_MINUS_GOLOMB[M+1] = {127,  123,  121,  107,  92,  75,  68,  50,  49,  41,  38,  28,  5,  0};
	#define MEMORY 127
#elif (M == 14)
	//static const int GOLOMB[M+1] = {0, 4, 20, 30, 57, 59, 62, 76, 100, 111, 123, 136, 144, 145, 151};
    static const int MEMORY_MINUS_GOLOMB[M+1] = {151,  147,  131,  121,  94,  92,  89,  75,  51,  40,  28,  15,  7, 6,  0};
	#define MEMORY 151
#elif (M == 15)
	//static const int GOLOMB[M+1] = {0, 1, 4, 11, 26, 32, 56, 68, 76, 115, 117, 134, 150, 163, 168, 177};
    static const int MEMORY_MINUS_GOLOMB[M+1] = {177,  176,  173,  166,  151,  145,  121,  109,  101,  62,  60,  43,  27,  14, 9,  0};
	#define MEMORY 177
#endif
#define W (3*(MEMORY+1))
#define F 1634
// Number of iterations (unless specified by command-line argument -s)
#define DefaultSweepsPerBlock 4


/* 	The following parameters are the simulation parameters unless 
	specified by command-line argument: */
#define DefaultBatchSize 100
#define DefaultErrorsToFind 10
#define DefaultMaxBatches 10000000

// How frequently to print simulation status in verbose mode
#define STATUS_FREQUENCY 0xf

/***********************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <math.h>
#include <unistd.h>
#define SS (S*S)

/********************************************************************
   PERMUTATIONS

   Bijections between position in a vector of length S*S
   and row/column indices in an S by S matrix.

   Different bijections are defined via linear transformations
   of row/column indices (i,j).  Consider the map

   (i,j) -> (i,j) [ a b ] = (i',j'), with operations in Z_S,
                  [ c d ]

   where ad-bc = 1 or -1 (or in general is an invertible element mod S).
   Let D = 1/(ad-bc) in Z_S.

   We then recover (i,j) from (i',j') via
   (i,j) = D * (i',j') [ d -b ].
                       [-c  a ]

   Let p be an element of {0,1, ..., S*S-1}, and let a,b,c,d be given.
   We map p to

   (i,j) = (p/S, p%S) [ a b ]
                      [ c d ]

         = ( (a*(p/S) + c*p)%S , (b*(p/S) + d*p)%S )

   We then recover p from (i,j) as follows.  Note that

   (p/S,p%S) =  D (i,j) [ d -b ] = (d*i - c*j, a*j - b*i) mod S
                        [ -c a ]
             =  ( D*( E*S + d*i - c*j )%S, D*(F*S + a*j - b*i)%S )
   where E must be chosen so that E*S + d*i - c*j is nonnegative and
         F must be chosen so that F*S + a*j - b*i is nonnegative.

   Then p = S*(p/S) + p%S.
*/

/// Permutation definitions
// Specify a, b, c, d, and invdet = 1/(ad-bc) 
// MUST USE NON-NEGATIVE MOD S REPRESENTATIVES FOR THESE VALUES  
// The permutation applied to the blocks is the INVERSE of the specified
// permutation, i.e., corresponding to the INVERSE of the matrix
// [a b]
// [c d]

#define A1 0
#define B1 1
#define C1 1
#define D1 0
#define INVDET1 (S-1)
 
#define A2 (S-1)
#define B2 0
#define C2 1
#define D2 1
#define INVDET2 (S-1)
 
#define A3 (S-2)
#define B3 (S*S-3)
#define C3 1
#define D3 2
#define INVDET3 (S-1)
 
#define A4 (S-3)
#define B4 (S*S-8)
#define C4 1
#define D4 3
#define INVDET4 (S-1)
 
#define A5 (S-4)
#define B5 (S*S-15)
#define C5 1
#define D5 4
#define INVDET5 (S-1)
 
#define A6 (S-5)
#define B6 (S*S-24)
#define C6 1
#define D6 5
#define INVDET6 (S-1)
 
#define A7 (S-6)
#define B7 (S*S-35)
#define C7 1
#define D7 6
#define INVDET7 (S-1)
 
#define A8 (S-7)
#define B8 (S*S-48)
#define C8 1
#define D8 7
#define INVDET8 (S-1)
 
#define A9 (S-8)
#define B9 (S*S-63)
#define C9 1
#define D9 8
#define INVDET9 (S-1)
 
#define A10 (S-9)
#define B10 (S*S-80)
#define C10 1
#define D10 9
#define INVDET10 (S-1)
 
#define A11 (S-10)
#define B11 (S*S-99)
#define C11 1
#define D11 10
#define INVDET11 (S-1)
 
#define A12 (S-11)
#define B12 (S*S-120)
#define C12 1
#define D12 11
#define INVDET12 (S-1)
 
#define A13 (S-12)
#define B13 (S*S-143)
#define C13 1
#define D13 12
#define INVDET13 (S-1)
 
#define A14 (S-13)
#define B14 (S*S-168)
#define C14 1
#define D14 13
#define INVDET14 (S-1)
 
#define A15 (S-14)
#define B15 (S*S-195)
#define C15 1
#define D15 14
#define INVDET15 (S-1)

// Permutation functions
int64_t pos_0(int64_t i, int64_t j) { return i*S + j; }
int64_t row_0(int64_t p) { return p/S; }
int64_t col_0(int64_t p) { return p%S; }

int64_t pos_1(int64_t i, int64_t j) { return S*((INVDET1*(D1*i - C1*(j-S)))%S) + (INVDET1*(A1*j - B1*(i-S)))%S; } 
int64_t row_1(int64_t p) { return (A1*(p/S) + C1*p)%S; } 
int64_t col_1(int64_t p) { return (B1*(p/S) + D1*p)%S; } 

int64_t pos_2(int64_t i, int64_t j) { return S*((INVDET2*(D2*i - C2*(j-S)))%S) + (INVDET2*(A2*j - B2*(i-S)))%S; } 
int64_t row_2(int64_t p) { return (A2*(p/S) + C2*p)%S; } 
int64_t col_2(int64_t p) { return (B2*(p/S) + D2*p)%S; } 

int64_t pos_3(int64_t i, int64_t j) { return S*((INVDET3*(D3*i - C3*(j-S)))%S) + (INVDET3*(A3*j - B3*(i-S)))%S; } 
int64_t row_3(int64_t p) { return (A3*(p/S) + C3*p)%S; } 
int64_t col_3(int64_t p) { return (B3*(p/S) + D3*p)%S; } 

int64_t pos_4(int64_t i, int64_t j) { return S*((INVDET4*(D4*i - C4*(j-S)))%S) + (INVDET4*(A4*j - B4*(i-S)))%S; } 
int64_t row_4(int64_t p) { return (A4*(p/S) + C4*p)%S; } 
int64_t col_4(int64_t p) { return (B4*(p/S) + D4*p)%S; } 

int64_t pos_5(int64_t i, int64_t j) { return S*((INVDET5*(D5*i - C5*(j-S)))%S) + (INVDET5*(A5*j - B5*(i-S)))%S; } 
int64_t row_5(int64_t p) { return (A5*(p/S) + C5*p)%S; } 
int64_t col_5(int64_t p) { return (B5*(p/S) + D5*p)%S; } 

int64_t pos_6(int64_t i, int64_t j) { return S*((INVDET6*(D6*i - C6*(j-S)))%S) + (INVDET6*(A6*j - B6*(i-S)))%S; } 
int64_t row_6(int64_t p) { return (A6*(p/S) + C6*p)%S; } 
int64_t col_6(int64_t p) { return (B6*(p/S) + D6*p)%S; } 

int64_t pos_7(int64_t i, int64_t j) { return S*((INVDET7*(D7*i - C7*(j-S)))%S) + (INVDET7*(A7*j - B7*(i-S)))%S; } 
int64_t row_7(int64_t p) { return (A7*(p/S) + C7*p)%S; } 
int64_t col_7(int64_t p) { return (B7*(p/S) + D7*p)%S; } 

int64_t pos_8(int64_t i, int64_t j) { return S*((INVDET8*(D8*i - C8*(j-S)))%S) + (INVDET8*(A8*j - B8*(i-S)))%S; } 
int64_t row_8(int64_t p) { return (A8*(p/S) + C8*p)%S; } 
int64_t col_8(int64_t p) { return (B8*(p/S) + D8*p)%S; } 

int64_t pos_9(int64_t i, int64_t j) { return S*((INVDET9*(D9*i - C9*(j-S)))%S) + (INVDET9*(A9*j - B9*(i-S)))%S; } 
int64_t row_9(int64_t p) { return (A9*(p/S) + C9*p)%S; } 
int64_t col_9(int64_t p) { return (B9*(p/S) + D9*p)%S; } 

int64_t pos_10(int64_t i, int64_t j) { return S*((INVDET10*(D10*i - C10*(j-S)))%S) + (INVDET10*(A10*j - B10*(i-S)))%S; } 
int64_t row_10(int64_t p) { return (A10*(p/S) + C10*p)%S; } 
int64_t col_10(int64_t p) { return (B10*(p/S) + D10*p)%S; } 

int64_t pos_11(int64_t i, int64_t j) { return S*((INVDET11*(D11*i - C11*(j-S)))%S) + (INVDET11*(A11*j - B11*(i-S)))%S; } 
int64_t row_11(int64_t p) { return (A11*(p/S) + C11*p)%S; } 
int64_t col_11(int64_t p) { return (B11*(p/S) + D11*p)%S; } 

int64_t pos_12(int64_t i, int64_t j) { return S*((INVDET12*(D12*i - C12*(j-S)))%S) + (INVDET12*(A12*j - B12*(i-S)))%S; } 
int64_t row_12(int64_t p) { return (A12*(p/S) + C12*p)%S; } 
int64_t col_12(int64_t p) { return (B12*(p/S) + D12*p)%S; } 

int64_t pos_13(int64_t i, int64_t j) { return S*((INVDET13*(D13*i - C13*(j-S)))%S) + (INVDET13*(A13*j - B13*(i-S)))%S; } 
int64_t row_13(int64_t p) { return (A13*(p/S) + C13*p)%S; } 
int64_t col_13(int64_t p) { return (B13*(p/S) + D13*p)%S; } 

int64_t pos_14(int64_t i, int64_t j) { return S*((INVDET14*(D14*i - C14*(j-S)))%S) + (INVDET14*(A14*j - B14*(i-S)))%S; } 
int64_t row_14(int64_t p) { return (A14*(p/S) + C14*p)%S; } 
int64_t col_14(int64_t p) { return (B14*(p/S) + D14*p)%S; } 

int64_t pos_15(int64_t i, int64_t j) { return S*((INVDET15*(D15*i - C15*(j-S)))%S) + (INVDET15*(A15*j - B15*(i-S)))%S; } 
int64_t row_15(int64_t p) { return (A15*(p/S) + C15*p)%S; } 
int64_t col_15(int64_t p) { return (B15*(p/S) + D15*p)%S; } 

typedef int64_t (*ZtoZ)(int64_t);  /* pointer to a function mapping int64_t to int64_t */
typedef int64_t (*ZZtoZ)(int64_t, int64_t);  /* ptr to function mapping (int64_t,int64_t) to int64_t */

/* The maximum encoder memory supported by the currently defined permutations */
/* If you define more permutations, please remember to change this value. */
#define MAXM 15

/* GLOBAL VARIABLES */

/* pointers to bijection functions */
ZZtoZ pos[MAXM+1] = {pos_0, pos_1, pos_2, pos_3, pos_4, pos_5, pos_6, pos_7, pos_8, pos_9, pos_10, pos_11, pos_12, pos_13, pos_14, pos_15};
ZtoZ  row[MAXM+1] = {row_0, row_1, row_2, row_3, row_4, row_5, row_6, row_7, row_8, row_9, row_10, row_11, row_12, row_13, row_14, row_15};
ZtoZ  col[MAXM+1] = {col_0, col_1, col_2, col_3, col_4, col_5, col_6, col_7, col_8, col_9, col_10, col_11, col_12, col_13, col_14, col_15};

// All circular buffer indexing is modulo W

// Receiver circular buffer of W blocks of S*S = SS bits:
unsigned char RXbuffer[SS*W];

/* Index of the "Newest" (most recently received)
   block in the circular buffer. */
uint32_t NewestBlock;

/*
 * Circular buffer of W groups of S syndromes
 * The group with modulo-W index i consists of the S syndromes
 * corresponding to the S component codewords which START at block i.
 * The MEMORY newest syndrome groups are partial syndromes since the
 * remainder of the corresponding component codewords has not been received yet.
 * The W-MEMORY oldest syndrome groups correspond to complete component codewords
 * in the RXbuffer and are decoded during an iteration.
*/
uint32_t Syndrome[S*W];

// Circular buffer of Hamming weights of each block for error-counting
uint32_t BlockWeight[W];

int parity; // Number of component code parity bits
// Variables and LUTs for defining systematizing permutation 
// via invertible affine transformation of column index:
uint32_t m; // Parent [2^m, 2^m - (m+1)] extended Hamming code parameter
uint32_t s; // shortening parameter to get [2^m - s, 2^m - (m+1) - s] code
// Parameters for defining affine transformation 
uint32_t mask;
uint32_t mb;
uint32_t a;
uint32_t b;
uint32_t ainv;
static const uint32_t aLUT[14] = {1,3,3,3,5,9,19,27,53,89,163,301,553,1065};
static const uint32_t bLUT[14] = {1,0,0,3,5,11,19,27,53,89,170,308,553,1155};
static const uint32_t ainvLUT[14] = {1,11,11,43,77,57,27,531,541,2025,4875,13989,14873,55321};


/* Pseudorandom Number Generation
 * START PCG SECTION *************************************************
 *
 * PCG Random Number Generation for C.
 *
 * Copyright 2014 Melissa O'Neill <oneill@pcg-random.org>
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * For additional information about the PCG random number generation scheme,
 * including its license and other licensing options, visit
 *
 *       http://www.pcg-random.org
 *
 *  The following lines (until "END PCG SECTION") are *MODIFIED* from
 *  the "basic C implementation" available from the site noted above.
 *
 *  The modification is to replace pointer-dereferencing with an actual
 *  variable name (as we only need a single, global, PRNG).
 */
typedef struct { uint64_t state;  uint64_t inc; } pcg32_random_t;
#define PCG32_INITIALIZER   { 0x853c49e6748fea9bULL, 0xda3e39cb94b95bdbULL }
static pcg32_random_t pcg32_global = PCG32_INITIALIZER;
uint32_t pcg32_random_r()
{
    uint64_t oldstate = pcg32_global.state;
    pcg32_global.state = oldstate * 6364136223846793005ULL
                                  + (pcg32_global.inc|1);
    uint32_t xorshifted = ((oldstate >> 18u) ^ oldstate) >> 27u;
    uint32_t rot = oldstate >> 59u;
    return (xorshifted >> rot) | (xorshifted << ((-rot) & 31));
}
void pcg32_srandom_r(uint64_t initstate, uint64_t initseq)
{
    pcg32_global.state = 0U;
    pcg32_global.inc = (initseq << 1u) | 1u;
    pcg32_random_r();
    pcg32_global.state += initstate;
    pcg32_random_r();
}
/*****************************  END PCG SECTION ****************/

/*********************************************************

To generate pseudorandom floating point numbers uniformly
distributed over [1,2), I make the following assumptions.

1.  Availability of a source of uniformly distributed random 32-bit binary
    words (aka uint32_tegers).  I am currently using Melissa E. O'Neill's
    PCG family, as described in

    Melissa E. O'Neill, "PCG: A Family of Simple Fast Space-Efficient
    Statistically Good Algorithms for Random Number Generation",
    Technical Report HMC-CS-2014-0905, Harvey Mudd College, Claremont, CA,
    Sep. 2014.  Available: https://www.cs.hmc.edu/tr/hmc-cs-2014-0905.pdf

    C and C++ language source code can be downloaded from
    https://www.pcg-random.org/

2.  A processor that adheres to the IEEE 754 Floating point standard;
    see https://en.wikipedia.org/wiki/IEEE_754 and references therein.
    The IEEE 754 standard represents a nonzero number x using
    -- a sign bit s (most significant bit)
    -- a binary exponent e
    -- an integer mantissa m of p bits (so an integer between 0 and 2^p-1),
    with
        x = (-1)^s * (1 + m*2^(-p))2^e

3.  From a source of random binary words (1), we can generate a floating
    point number uniformly distributed over all floating point numbers (2)
    in [1,2) by choosing s=0 and an exponent corresponding to e=0.

    For 32-bit floats, s=0 and e=0 corresponds to setting the most significant
    9 of 32 bits to 001111111.

    For 64-bit doubles, s=0 and e=0 corresponds to setting the most significant
    12 of 64 bits to 001111111111.

    To twiddle bits in C one can use type-punning as follows.

    #define F_ONE_MSB 0x3f800000
    #define F_MANTISSA 0x7fffff
    union { float r; uint32_t i; } x;
    x.i = (U32(rng_p) & F_MANTISSA) ^ F_ONE_MSB;

    or  (double version)

    #define D_ONE_MSB 0x3ff00000
    #define D_MANTISSA 0xfffff
    union { double r; uint32_t i[2]; } x;
    x.i[0] = U32(rng_p1);
    x.i[1] = (U32(rng_p2) & D_MANTISSA ) ^ D_ONE_MSB;

    For portability, it may be useful to include the following tests
    (perhaps when the PRNG is seeded):

    x.i = F_ONE_MSB;
    if (x.r != 1.0f)
    {
       fprintf(stderr,"Incompatible floating point representation -- sorry.\n");
       exit(1);
    }

    or (double version)

    x.i[0] = 0;
    x.i[1] = D_ONE_MSB;
    if (x.r != 1.0)
    {
       fprintf(stderr,"Incompatible floating point representation or endianness -- sorry.\n");
      exit(1);
    }

---------------


Simulation of a binary symmetric channel BSC(p), assuming 0 < p < 1.

To decide on which bits to flip, we take geometrically distributed jumps.

Claim:  if U is uniformly distributed over [1,2), then
  G = 1 + floor(log(2.0-U)/log(1.0-p)) is geometrically distributed
  on {1,2,3,...} with Pr(G=g) = (1-p)^(g-1) * p
  (i.e., G is the amount to jump to the next error).

Proof:  For any g in {1,2,3,...},
        Pr[G=g] = Pr[ g-1 <= log(2-U)/log(1-p) < g ]
                = Pr[ (g-1)*log(1-p) >= log(2-U) > g*log(1-p) ]
                = Pr[ exp((g-1)*log(1-p)) >= 2-U > exp(g*log(1-p)) ]
                = Pr[ (1-p)^(g-1) >= 2-U > (1-p)^g ]
                = (1-p)^(g-1) - (1-p)^g
                = (1-p)^(g-1) * (1 - (1-p))
                = (1-p)^(g-1) * p

*/


/*
// Naive but universal systematizing permutation
// Slow relative to the algebraically defined 
// permutations that we actually use

// This function returns the syndrome corresponding to an error location
// Equivalently, this function defines the columns of the parity-check matrix
uint32_t synFromErrorloc(uint32_t x) {
	static const uint32_t EXP2LUT[33] = 
	{0,1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,
	131072,262144,524288,1048576,2097152,4194304,8388608,16777216,
	33554432,67108864,134217728,268435456,536870912,1073741824,2147483648};
	if (x >= (S*(M+1) - parity)) { // if x is in parity position
		return (EXP2LUT[S*(M+1)-1-x]<<1)^0x01; 
	} else {
		for (uint32_t z = 1; z <= parity; ++z){
			if ((31-__builtin_clz(x+z+2)) ==  z)  {
				return ((x+z+2)<<1)^0x01;  
			}
		}
		return 4294967295; //should never happen
	} 
}
// This function returns the error location corresponding to a syndrome
// In the case of shortening, an out of range syndromes will yield
// a value greater than S*(M+1)-1
uint32_t errorlocFromSyn(uint32_t x) {
	uint32_t y;
	if (x > (2*((M+1)*S-1) + 1)) {
		return S*(M+1);
	}
	y = x>>1;
	if (y == 0) {
		return S*(M+1)-1;
	} else if ((y & (y - 1)) == 0) { // if y is a power of two
		return S*(M+1)-(31-__builtin_clz(y))-2;  
	} else {
		return y-(31-__builtin_clz(y))-2; 
	} 
}
*/


// Fast algebraically defined systematizing permutations
// This function returns the syndrome corresponding to an error location
// Equivalently, this function defines the columns of the parity-check matrix
static inline __attribute__((always_inline)) uint32_t synFromErrorloc(uint32_t x) {
	return (((a*x+b)&mask)<<1)^1; 
}
// This function returns the error location corresponding to a syndrome
// In the case of shortening, out of range syndromes will lead to a
// negative result which will wrap around to a value greater than
// S*(M+1)-1 since the type is unsigned. 
static inline __attribute__((always_inline)) uint32_t errorlocFromSyn(uint32_t x) {
	return (ainv*((x>>1)+mb))&mask;
}

/*
 * Functions for flipping the bit in a given position
 * by updating the state of the three circular buffers
 * RXbuffer, Syndrome, and BlockWeight.
 * We assume 0 <= block < W, and 0 <= posn < S*S.
 */
/*
 * We have two flipping functions. flip_old is for the
 * MEMORY oldest blocks for which we have fewer associated
 * syndromes since part of the corresponding component codewords
 * has been dumped/delivered.
 * We don't want to wrap around and modify the partial syndromes
 * corresponding to the MEMORY newest blocks in this case.
 * flip_old requires the "age" of a block which can be counted
 * and passed to it during a decoding sweep/iteration.
 * flip is for the W-MEMORY newest blocks.
 */

// Assumes block is NewestBlock-0, NewestBlock-1, ..., NewestBlock-(W-1-MEMORY)
// i.e., "age" of block is less than or equal to W-1-MEMORY
static inline __attribute__((always_inline)) void flip(uint32_t block, uint32_t posn) {
    int i, j, k;
    unsigned char *p = RXbuffer + block*SS + posn;
    if (*p) { /* is this a one? */
        --BlockWeight[block];
        *p = '\0';
    } else {
        ++BlockWeight[block];
        *p = '\1';
    }
    for (k=M; k >= 0; --k) {
        i = row[k](posn);
        j = col[k](posn);
        //Syndrome[((block-MEMORY+GOLOMB[k]+W)%W)*S+i] ^= synFromErrorloc((M-k)*S+j);
        Syndrome[((block-MEMORY_MINUS_GOLOMB[k]+W)%W)*S+i] ^= synFromErrorloc((M-k)*S+j);
    }
}
// Assumes block is NewestBlock-(W-1-MEMORY)-1, NewestBlock-(W-1-MEMORY)-2, ..., NewestBlock-(W-1-MEMORY)-MEMORY = NewestBlock-(W-1)
// i.e., "age" of block is greater than W-1-MEMORY, or block is one of the MEMORY oldest blocks
static inline __attribute__((always_inline)) void flip_old(uint32_t block, uint32_t posn, uint32_t age) {
    int i, j, k;
    unsigned char *p = RXbuffer + block*SS + posn;
    if (*p) { /* is this a one? */
        --BlockWeight[block];
        *p = '\0';
    } else {
        ++BlockWeight[block];
        *p = '\1';
    }
    k = M;
    while (1) {
        if (MEMORY_MINUS_GOLOMB[k]+age >= W) break;
        i = row[k](posn);
        j = col[k](posn);
        //Syndrome[((block-MEMORY+GOLOMB[k]+W)%W)*S+i] ^= synFromErrorloc((M-k)*S+j);
        Syndrome[((block-MEMORY_MINUS_GOLOMB[k]+W)%W)*S+i] ^= synFromErrorloc((M-k)*S+j);
        k--;
    }
}

/* The following function creates a new "newest" received block
   from a binary symmetric channel with crossover probability p.

   The following operations are performed.

   1.  The index of the newest block is incremented.
   3.  The buffer associated with the previous oldest block is zeroed.
   4.  The syndromes associated with the previous oldest block are zeroed.
   5.  The weight of the previous oldest buffer is set to zero.
   6.  Bits are randomly flipped (taking geometric jumps) in the
       newest block until the end of the block is reached.
*/

#define F_ONE_MSB 0x3f800000
#define F_MANTISSA 0x7fffff
static inline __attribute__((always_inline)) void ReceiveBlock(float p) {
    int posn;
    float k;
    union { float r; uint32_t i; } x;

    if (++NewestBlock >= W) NewestBlock = 0; // mod W increment
    memset(RXbuffer+NewestBlock*SS, 0, SS*sizeof(unsigned char));
    memset(Syndrome+NewestBlock*S, 0, S*sizeof(uint32_t));
    BlockWeight[NewestBlock] = 0;

    k = 1.0f/logf(1.0f-p);
    posn = -1;
    while (1) {
        x.i = (pcg32_random_r() & F_MANTISSA) ^ F_ONE_MSB;
        posn += 1 + (int) floor(k*logf(2.0f - x.r));
        if (posn >= SS) {
			break;
        } else {
			flip(NewestBlock, posn);
		}
    }
}
// Rejects bit flips unless they occur in the parity parity columns
// S-parity + 0, S-parity + 1, ..., S-parity + (parity-1) == S-1
static inline __attribute__((always_inline)) void ReceivePseudoterminationBlock(float p) {
    int posn;
    float k;
    union { float r; uint32_t i; } x;

    if (++NewestBlock >= W) NewestBlock = 0; // mod W increment
    memset(RXbuffer+NewestBlock*SS, 0, SS*sizeof(unsigned char));
    memset(Syndrome+NewestBlock*S, 0, S*sizeof(uint32_t));
    BlockWeight[NewestBlock] = 0;

    k = 1.0f/logf(1.0f-p);
    posn = -1;
    while (1) {
        x.i = (pcg32_random_r() & F_MANTISSA) ^ F_ONE_MSB;
        posn += 1 + (int) floor(k*logf(2.0f - x.r));
        if (posn >= SS) {
			break;
		} else if ((posn%S) >= (S-parity)) { 
			flip(NewestBlock, posn);
		}
    }
}


/*
   perform the initial set up:
    --- set up global variables in a state ready to receive first block
*/
static inline __attribute__((always_inline)) void Initialize() {
    /* zero global arrays */
    memset(RXbuffer, 0, S*S*W*sizeof(unsigned char));
    memset(Syndrome, 0, S*W*sizeof(uint32_t));
    memset(BlockWeight, 0, W*sizeof(uint32_t));
    NewestBlock = W-1;
}


/* Sweep through all syndromes; return the number of corrections performed. */

int sweep() {
    int i, j;    /* row, column of error location */
    int k;      /* loop index                    */
    int block;  /* block index                   */
    uint32_t syn;  /* syndrome value */
    uint32_t errorloc;  /* error location within codeword */
    int perm;   /* index of permutation to apply to (i,j) to get position */
    int count = 0;  /* number of corrections performed     */
    // The MEMORY number of syndrome groups with indices
    // NewestBlock-0, NewestBlock-1, ..., NewestBlock-(MEMORY-1)
    // are not yet completed.
    // Therefore, decoding starts at NewestBlock-MEMORY and decrements
    // covering W-MEMORY completed syndrome groups.
    // First, we do the W-2*MEMORY newest syndrome groups
    // and then the MEMORY oldest for a total of (W-MEMORY) syndrome groups
    // or (W-MEMORY)*S decodings
    block = (NewestBlock-MEMORY+W)%W;
    for (k=0; k < W-2*MEMORY; ++k) {
        for (i=0; i < S; ++i) {
            syn = Syndrome[block*S + i];
            if (syn & 0x01) {
                errorloc = errorlocFromSyn(syn);
                if (errorloc < S*(M+1)) {
                    j = errorloc % S;     /* j is the column index */
                    perm = M - errorloc/S;
                    //flip((block+MEMORY-GOLOMB[perm])%W, pos[perm](i, j));
                    flip((block+MEMORY_MINUS_GOLOMB[perm])%W, pos[perm](i, j));
                    count += 1;
                }
            }
        }
        if (--block < 0) block = W-1; // mod W decrement
    }
    for (k = W-2*MEMORY; k < W-MEMORY; ++k) {
        for (i=0; i < S; ++i) {
            syn = Syndrome[block*S + i];
            if (syn & 0x01) {
                errorloc = errorlocFromSyn(syn);
                if (errorloc < S*(M+1)) {
                    j = errorloc % S;     /* j is the column index */
                    perm = M - errorloc/S;
                    //flip_old((block+MEMORY-GOLOMB[perm])%W, pos[perm](i, j), k+GOLOMB[perm]);
                    //flip_old((block+MEMORY_MINUS_GOLOMB[perm])%W, pos[perm](i, j), k+GOLOMB[perm]);
					flip_old((block+MEMORY_MINUS_GOLOMB[perm])%W, pos[perm](i, j), k+MEMORY-MEMORY_MINUS_GOLOMB[perm]);
                    count += 1;
                }
            }
        }
        if (--block < 0) block = W-1; // mod W decrement
    }
    return count;
}

/* HELPER FUNCTIONS */
int pow2ge(int n)  /* find smallest nonnegative power of two >= n */
{
    int p = 0;
    int v = 1;
    while (v < n)
    {
        if (v < 0) return -1;   /* overflow */
        p += 1;
        v <<= 1;
    }
    return p;
}


#define TOL 1e-8
double H(double p)
{
    if (p <= 0.0 || p >= 1.0)
        return 0.0;
    else
        return -p*log2(p) - (1.0-p)*log2(1.0-p);
}
double R(double sigma)
{
    return 1.0 - H(0.5*erfc(0.7071067811865476/sigma));
}
double Rinv(double r)  /* find sigma so that R(sigma) = r */
{
    double left, right, mid, Rmid;
    if (r <= 0.0) return INFINITY;
    if (r >= 1.0) return 0.0;

    left = 0.0; right = 30.0; mid = 0.5*(left + right); Rmid = R(mid);
    while (fabs(Rmid-r)/r > TOL)
    {
       if (Rmid > r)  /* too much rate, increase mid */
           left = mid;
       else           /* not enough rate,  decrease mid */
           right = mid;
       mid = 0.5*(left + right);
       Rmid = R(mid);
    }
    return mid;
}
double erfcinv(double ee)  /* find x so that erfc(x) = ee */
{
    double left, right, mid, erfcmid;
    if (ee <= 0.0) return INFINITY;
    if (ee >= 1.0) return 0.5;

    left = 0.0; right = 10.0; mid = 0.5*(left + right); erfcmid = erfc(mid);
    while (fabs(erfcmid - ee)/ee > TOL)
    {
        if (erfcmid > ee)  /* too much error, increase mid */
            left = mid;
        else               /* not enough error, decrease mid */
            right = mid;
        mid = 0.5*(left + right);
        erfcmid = erfc(mid);
    }
    return mid;
}
double dbgaptoshannon(double R, double p)
{
    double sigmaS, sigmaP;
    sigmaS = Rinv(R);
    sigmaP = 0.7071067811865476/erfcinv(2.0*p);
    return 20.0*log10(sigmaS/sigmaP);
}


// Need to modify this to account for framing rate loss
#define SanityCheckBlocks 1000
void SanityCheck()  /* triggered by -C command line switch */
{
    int b, i, j, p;
    uint64_t ErrorCount;
    float pp, qq;
    double R; // Code rate
	double R_nominal; // Nominal code rate
	double R_framing; // Framing/pseudotermination rate loss 

    parity = pow2ge((M+1)*S) + 1;
	R_nominal = 1.0 - (double)parity/(double)S;
	R_framing = (double)((F-W)*S)/(double)((F-W)*S + W*parity);
	R = R_nominal*R_framing;

    printf("S=%d, M=%d, Hamming Code Length=%d, Parity bits=%d, Rate=%f\n",
           S, M, S*(M+1), parity, R);
    Initialize();
    /*  make sure that the bijections work properly */
    for (b=0; b < MAXM + 1; ++b) {
       printf("Checking bijection %d: ", b);
       for (p=0; p < SS; ++p) {
           i = row[b](p);
           j = col[b](p);
           if (pos[b](i, j) != p) {
               printf("** failed at p=%d\n", p);
               exit(1);
           }
       }
       for (i=0; i < S; ++i) {
		   for (j=0; j < S; ++j) {
		       p = pos[b](i, j);
		       if (row[b](p) != i || col[b](p) != j) {
		           printf("** failed at row %d, col %d\n", i, j);
		           exit(1);
		       }
		   }
       }
       printf("[OK]\n");
    }
    for (i=-2; i <= 2; ++i)
    {
        ErrorCount = 0UL;
        pp = pow(2.0, (double)i)*0.5*erfc(0.7071067811865476
                 /Rinv(R)/pow(10.0, -0.05));
        printf("Checking bit flip generation at p=%g:", pp);
        for (b=0; b < SanityCheckBlocks; ++b)
        {
            ReceiveBlock(pp);
            ErrorCount += BlockWeight[NewestBlock];
        }
        qq = (float)ErrorCount/SanityCheckBlocks/SS;
        printf(" measured %g", qq);
        if (fabs(pp-qq)/pp < 1e-2)
        {
            printf(" [OK]\n");
        }
        else
            printf(" ** failed **\n");
    }
}

int main(int argc, char **argv){
	
	// prng compatibility test
	union { float r; uint32_t i; } x;
    x.i = F_ONE_MSB;
    if (x.r != 1.0f)
    {
         fprintf(stderr,
             "Incompatible floating point representation -- sorry.\n");
         exit(1);
    }
    /* seed the prng using current system time and process ID */
    uint64_t PRNG_SEED = time(NULL) ^ (getpid()*getpid());
    printf("PRNG_SEED = %lu \n", PRNG_SEED);
    pcg32_srandom_r(PRNG_SEED, PRNG_SEED*17);
    //pcg32_srandom_r(time(NULL), time(NULL)*17);
    //pcg32_srandom_r(123456789,987654321);  /* for debugging */
	//pcg32_srandom_r(123,991);  /* for debugging */
	
    float p;  /* BSC crossover probability  */
    float g;  /* gap in dB to Shannon limit */
    double R; // Code rate
	double R_nominal; // Nominal code rate
	double R_framing; // Framing/pseudotermination rate loss 

    int VERBOSE = 0;  /* verbose mode if nonzero */
    uint64_t ActualBatchSize = DefaultBatchSize;
    uint64_t ActualMaxBatches = DefaultMaxBatches;
    uint64_t ActualErrorsToFind = DefaultErrorsToFind;
    int ActualSweepsPerBlock = DefaultSweepsPerBlock;
    uint64_t BlocksDecoded = 0; // blocks delivered
	uint64_t FramesDecoded = 0;
	
	
    int BitErrors = 0;
	int FrameErrors = 0;
	int prevBitErrors = 0; //for counting frame errors
    int batch;
	int frame; 
    int block;
    int sweepcnt;
    int i;
    int pdef = 0;

    time_t then, now;  /* to estimate throughput */

    if (M > MAXM)
    {
        fprintf(stderr, "Maximum supported memory = %d\n", MAXM);
        return 1;
    }
    
    
    m = (uint32_t) pow2ge((M+1)*S);
	if (m < 3 || m > 16) {
		printf("Component code length not supported! (m = %d)\n", m);
		return 1;
	}
	s = (1<<m)-((M+1)*S);
	a = aLUT[m-3];
	b = bLUT[m-3] + a*s;
	ainv = ainvLUT[m-3];
	mask = (1<<m)-1; 
	mb = (1<<m)-b;
	
	parity = ((int) m) + 1;
    
    R_nominal = 1.0 - (double)parity/(double)S;
	R_framing = (double)((F-W)*S)/(double)((F-W)*S + W*parity);
	R = R_nominal*R_framing;
	 

    /*** process command line arguments ***/
    if (argc < 2) goto usage;
    for (i=1; i < argc; ++i) /* process i'th argument */
    {
        if (i >= argc)  /* problem; print usage message */
            goto usage;
        else  /* expect to see a command-line switch */
        {
            if (argv[i][0] != '-')
                goto usage;
            else
            {
                switch (argv[i][1])
                {
                    case 'v':  /* set VERBOSE flag */
                        VERBOSE = 1;
                        break;
                    case 'p':  /* set crossover probability */
                        if (++i >= argc)
                            goto usage;
                        else
                        {
                            if (sscanf(argv[i], "%f", &p) != 1)
                            {
                                fprintf(stderr,
                                    "Invalid crossover probability \"%s\".\n",
                                    argv[i]);
                                goto usage;
                            }
                            if (p <= 0.0f || p > 0.5f)
                            {
                                fprintf(stderr,
                                    "Invalid crossover probability %f.\n", p);
                                goto usage;
                            }
                            g = dbgaptoshannon(R, p);
                        }
                        pdef = 1;
                        break;
                    case 'g':  /* set dB gap to Shannon limit */
                        if (++i >= argc)
                            goto usage;
                        else
                        {
                            if (sscanf(argv[i], "%f", &g) != 1)
                            {
                                fprintf(stderr,
                                    "Invalid gap to Shannon \"%s\".\n",
                                    argv[i]);
                                goto usage;
                            }
                            p = 0.5*erfc(0.7071067811865476/
                                Rinv(R)/pow(10.0, -0.05*g));
                        }
                        pdef = 1;
                        break;
                    case 'f':  /* set number of frames to decode */
                        if (++i >= argc)
                            goto usage;
                        else
                        {
                            if (sscanf(argv[i], "%lu", &ActualMaxBatches) != 1)
                            {
                                fprintf(stderr,
                                    "Invalid no. frames to decode \"%s\".\n",
                                    argv[i]);
                                goto usage;
                            }
                            ActualBatchSize = 1;
                            ActualErrorsToFind = 0xffffffffULL;
                        }
                        break;
                    case 'e':  /* set number of errors to find */
                        if (++i >= argc)
                            goto usage;
                        else
                        {
                            if (sscanf(argv[i], "%lu",
                                &ActualErrorsToFind) != 1)
                            {
                                fprintf(stderr,
                                    "Invalid errors to find \"%s\".\n",
                                    argv[i]);
                                goto usage;
                            }
                        }
                        break;
                    case 's':  /* set number of decoding sweeps per block */
                        if (++i >= argc)
                            goto usage;
                        else
                        {
                            if (sscanf(argv[i], "%d",
                                &ActualSweepsPerBlock) != 1)
                            {
                                fprintf(stderr,
                                    "Invalid sweeps per block \"%s\".\n",
                                    argv[i]);
                                goto usage;
                            }
                            if (ActualSweepsPerBlock <= 0)
                            {
                                fprintf(stderr,
                                    "Invalid sweeps per block %d.\n",
                                    ActualSweepsPerBlock);
                                goto usage;
                            }
                        }
                        break;
                    case 'C':  /* undocumented switch;  sanity checking */
                        SanityCheck();
                        return 0;
                    default:
                        fprintf(stderr,
                            "Unrecognized command-line argument \"%s\".\n",
                            argv[i]);
                        goto usage;
                }
            }
        }
    }
    if (!pdef)
    {
        fprintf(stderr, "One of p or g must be specified.\n");
        goto usage;
    }
	// End of processing command-line arguments

    if (VERBOSE)
    {
       /* print some useful information */
        fprintf(stderr,
            "Simulating M = %d, MEMORY = %d, S = %d, N = %d, %d parity bits, R = %lf\n",
            M, MEMORY, S, (M+1)*S, parity, R);
        fprintf(stderr,
            "at p = %g corresponding to gap-to-Shannon of %lf dB.\n",
            p, dbgaptoshannon(R, p));
		fprintf(stderr,
            "R_nominal = %lf and R_framing = %lf with F = %d.\n", R_nominal, R_framing, F);
		fprintf(stderr,"Each frame contains %d %d-by-%d information blocks\n", F-W, S, (S-parity));
		fprintf(stderr,"and %d %d-by-%d parity blocks.\n", F, S, parity);
        fprintf(stderr, "Decoding in batches of %lu frames.\n",
            ActualBatchSize);
        fprintf(stderr, "Peforming %d decoding sweeps per block.\n",
            ActualSweepsPerBlock);
        fprintf(stderr, "Decoding window = %d blocks = %g Mbits.\n",
            W, W*SS*1e-6);
        fprintf(stderr, "Maximum number of batches = %lu.\n", ActualMaxBatches);
        fprintf(stderr, "Will stop at %lu frame errors.\n", ActualErrorsToFind);
    }
		
	
	// Test systematizing permutation functions
	uint32_t test_1 = 1;
	for (uint32_t j = 0; j < (M+1)*S; ++j) {
		test_1 = test_1 && (errorlocFromSyn(synFromErrorloc(j)) == j);
		//printf("loc = %d syn = %u \n",j,  synFromErrorloc(j));
	}
	//printf("\ntest_1 result = %d\n\n", test_1);
	uint32_t loc_res;
	uint32_t syn_count = 0;
	uint32_t test_2 = 1;
	for (uint32_t j = 0; j < (1<<m); ++j) {
		loc_res = errorlocFromSyn(2*j+1);
		if (loc_res < (M+1)*S) {
			test_2 = test_2 && (synFromErrorloc(loc_res) == 2*j + 1);
			++syn_count;
		} 
		//printf("syn = %d loc = %u \n", 2*j+1, loc_res);
	}
	//printf("\ntest_2 result = %d\n", test_1);
	//printf("\nsyn_count = %u, should be %d \n\n", syn_count, (M+1)*S);
	if ((test_1&&test_2&&(syn_count == S*(M+1))) != 1) {
		printf("Systematizing permutation tests failed!\n");
		return 1;
	}
	//return 1;
	

	/**** start of simulation ****/
	
	// Redefined a batch to be a number of frames transmitted
	// Batch size is a number of frames
	then = time(NULL);
	for (batch=0; batch < ActualMaxBatches; ++batch) {
		for (frame=0; frame < ActualBatchSize; ++frame) {			
			Initialize(); // Reset buffers			
			prevBitErrors = BitErrors; 
			// Receive first W blocks
			for (block=0; block < W; ++block) { 
				ReceiveBlock(p); 
				for (sweepcnt = 0; sweepcnt < ActualSweepsPerBlock; ++sweepcnt) {
					if (!sweep()) {
						break;
					}
				}
			}
			// Receive the next F-W-W blocks while delivering
			// the first F-W-W information-bearing blocks
			for (block=0; block < (F-W-W); ++block) {
				++BlocksDecoded;
				BitErrors += BlockWeight[(NewestBlock+1)%W];
				ReceiveBlock(p); 
				for (sweepcnt = 0; sweepcnt < ActualSweepsPerBlock; ++sweepcnt) {
					if (!sweep()) {
						break;
					}
				}
			}
			// Receive the next W pseudotermination blocks while delivering
			// the last W information-bearing blocks
			for (block=0; block < W; ++block) {
				++BlocksDecoded;
				BitErrors += BlockWeight[(NewestBlock+1)%W];
				ReceivePseudoterminationBlock(p);
				for (sweepcnt = 0; sweepcnt < ActualSweepsPerBlock; ++sweepcnt) {
					if (!sweep()) {
						break;
					}
				}
			}
			// in total, F blocks have been received of which the last W 
			// were pseudotermination blocks 
			// in total, F-W information-bearing blocks were delivered
			
			++FramesDecoded;
			if (BitErrors != prevBitErrors) {
				FrameErrors += 1;
			}
			
			if (VERBOSE && !(FramesDecoded & STATUS_FREQUENCY)) {
				now = time(NULL);
				fprintf(stderr,
				"%d bit errors, %d frame errors in %lu frames delivered; %g bits/s = %g frames/s					\r", 
						BitErrors, FrameErrors, FramesDecoded, 
						(double)S*(S-parity)*(F-W)*FramesDecoded/(double)(now-then), 
						FramesDecoded/(double)(now-then));

			}
			
		} // End of batch loop
		
		if (FrameErrors >= ActualErrorsToFind)
           break;
	}
		
    if (VERBOSE) {
		fputc('\n', stderr);
	}
	
	printf("\nFINAL RESULTS:\n");
	printf("Parameters:\n");
	printf("Simulated M = %d, MEMORY = %d, S = %d, N = %d, %d parity bits, R = %lf\n",
            M, MEMORY, S, (M+1)*S, parity, R);
	printf("at p = %g corresponding to gap-to-Shannon of %lf dB.\n",
            p, dbgaptoshannon(R, p));
	printf("R_nominal = %lf and R_framing = %lf with F = %d.\n", R_nominal, R_framing, F);
	printf("Each frame contained %d %d-by-%d information blocks\n", F-W, S, (S-parity));
	printf("and %d %d-by-%d parity blocks.\n", F, S, parity);
	printf("Peformed %d decoding sweeps per block\n", ActualSweepsPerBlock);
	printf("with a decoding window of %d blocks = %g Mbits.\n", W, W*SS*1e-6);
	printf("Results:\n");
	printf(" %d bit errors, %d frame errors in\n", BitErrors, FrameErrors);
	printf(" %lu frames delivered each containing\n", FramesDecoded);
	printf(" %d %d-by-%d information blocks\n", F-W, S, (S-parity));
	printf(" and %d %d-by-%d parity blocks.\n", F, S, parity);
	printf(" Total of %lu = %g information bits delivered.\n", 
							(F-W)*S*(S-parity)*FramesDecoded, 
					(double)(F-W)*S*(S-parity)*FramesDecoded);
    printf(" BER = %g\n", (double)BitErrors/(F-W)/(S*(S-parity))/FramesDecoded);
	printf(" FER = %g\n", (double)FrameErrors/FramesDecoded);
	
    return 0;

usage:
    fprintf(stderr, "Usage: %s [-v] [-p p] [-g g] [-f f] [-e e] [-s s]\n",
              argv[0]);
    fprintf(stderr, "where p is the crossover probability, 0 < p <= 0.5;\n");
    fprintf(stderr, "where g is the gap (in dB) to the Shannon limit;\n");
    fprintf(stderr, "where f is the number of frames to decode;\n");
    fprintf(stderr, "where e is the minimum no. of frame errors to collect;\n");
    fprintf(stderr, "where s is the number of decoding sweeps per block;\n");
    fprintf(stderr, "and where -v turns on verbose progress reporting.\n");
    fprintf(stderr, "At least one of p or g must be specified.\n");
    fprintf(stderr, "Normally only one of f or e is specified.\n");
    fprintf(stderr, "Default mode: -e %d -s %d\n",
              DefaultErrorsToFind, DefaultSweepsPerBlock);
    return 1;
}
