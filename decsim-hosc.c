/*
	Copyright 2023-2024 Frank R. Kschischang and Mohannad Shehadeh <{frank,mshehadeh}@ece.utoronto.ca>

	Licensed under the Apache License, Version 2.0 (the "License");
	you may not use this file except in compliance with the License.
	You may obtain a copy of the License at

		http://www.apache.org/licenses/LICENSE-2.0

	Unless required by applicable law or agreed to in writing, software
	distributed under the License is distributed on an "AS IS" BASIS,
	WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
	See the License for the specific language governing permissions and
	limitations under the License.
*/

/*
	decsim-hosc is a simulator for higher-order staircase codes with
	extended Hamming component codes. When the parameter L is equal
	to 1, higher-order staircase codes are equivalent to generalized
	staircase codes which are simulated by decsim-gsc.

	decsim-hosc is accompanied by a pedagogical Julia model available
	at https://github.com/applecoffeecake/hosc-Julia
*/

/*
	Key parameters:

	L:	Number of square blocks from which to form a rectangle.
	T:	Sidelength of a square block; each square block contains T*T bits.
	M:	Memory parameter. Extended Hamming components have length L*T*(M+1).
	W:	Decoding window size in number of rectangles.
	F:	Frame length. Number of rectangles from which to form a frame.

	BatchSize: number of frames to process between error-count
				valuations.
	ErrorsToFind: minimum number of frame errors to find before stopping.
	SweepsPerBlock: number of decoding iterations before advancing window.
	MaxBatches: maximum number of batches to send.
*/

/*
	FRAMING/PSEUDOTERMINATION PROCEDURE:

	An unterminated codeword is a stream of T-by-(L*T) rectangles of which
	the first L*T-parity (L times T minus a variable called "parity")
	columns are information bits and the last parity columns are parity bits.

	Specify a frame length F in number of rectangles to simulate the block
	code obtained by the following pseudotermination procedure:  

	Once F rectangles are received, F-W rectangles should have been
	delivered/decoded with the last W sitting in the buffer.
	The last W of the F rectangles delivered are assumed to contain a fixed (zero)
	T-by-(L*T-parity) information portion so that only the T-by-parity
	parity portion needs to be transmitted.
	As a result, the total number of bits transmitted is
	(F-W)*T*(L*T) + W*T*parity of which (F-W)*T*(L*T-parity) is information.
	The ratio of these two quantities is the overall rate of the block code.

	Alternatively, the framing rate loss is given by 
	R_framing  = ((F-W)*(L*T))/((F-W)*(L*T) + W*parity)
	and the the nominal (unterminated scheme) rate is given by
	R_nominal = 1-parity/(L*T). The overall rate of the resulting block code is
	then given by R = R_nominal*R_framing. 
*/


// The following parameters completely specify the code and decoding scheme:
/*
 * Decoding window size is W: suggested value is 2*(1+SCOPE) to 5*(1+SCOPE).
 * PLEASE CHOOSE M TO BE LESS THAN OR EQUAL TO THE LEAST PRIME FACTOR OF T
 * WHEN T IS NOT EQUAL TO 1. OTHERWISE, A NON-SCATTERING, IMPROPER HIGHER-
 * ORDER STAIRCASE CODE IS FORMED LEADING TO A LARGE ERROR FLOOR.
 * HOWEVER, WHEN T = 1, YOU ARE ALLOWED TO CHOOSE ANY M AND YOU WILL STILL
 * HAVE A PROPER SPECIAL CASE OF HIGHER-ORDER STAIRCASE CODES.
 */
/*
 * Currently supported values of L and M are
 * if M = 1: all L up to 1000
 * if M = 2: all L up to 1000
 * if M = 3: all L up to 15
 * if M = 4: all L up to 10 excluding 9
 * if M = 5,6,7,8,9: L = 1
 */
#define L 7
#define T 25 // least prime factor of T must be greater than or equal to M
#define M 4
#include "dts-defs.h"
#define W (2*(1+SCOPE) + 1*(1+SCOPE)/4)
#define F (20000+W)
// Number of iterations (unless overridden by command-line argument -s)
#define DefaultSweepsPerBlock 1
// End of parameters specifying code and decoding scheme

// The following are simulation parameters; can be overridden by command-line argument:
#define DefaultBatchSize 100
#define DefaultErrorsToFind 10
#define DefaultMaxBatches 10000000

// How frequently to print simulation status in verbose mode
#define STATUS_FREQUENCY 0xf

// End of simulation parameters

/***********************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <math.h>
#include <unistd.h>

// Involution permutation option
// Forward permutation: multiplying by
// [-(k-1)   1-(k-1)^2]
// [   1        k-1   ]
// Inverse permutation: the same
//0 <= k <= M <= lpf(T) <= T
static inline __attribute__((always_inline)) int64_t pos(int64_t i, int64_t j, int64_t k) {
    return k == 0 ? i*T + j : (((T-(k-1))*i + j)%T)*T + ((T*T+1-(k-1)*(k-1))*i+(k-1)*j)%T;
}
static inline __attribute__((always_inline)) int64_t row(int64_t p, int64_t k) {
    return k == 0 ? p/T : ((T-(k-1))*(p/T) + p)%T;
}
static inline __attribute__((always_inline)) int64_t col(int64_t p, int64_t k) {
    return k == 0 ? p%T : ((T*T+1-(k-1)*(k-1))*(p/T)+(k-1)*p)%T;
}

// // Non-involution permutation option
// // Forward permutation: multiplying by
// // [   0         1    ]
// // [   1        k-1   ]
// // Inverse permutation:
// // [-(k-1)       1    ]
// // [   1         0    ]
// //0 <= k <= M <= lpf(T) <= T
// int64_t pos(int64_t i, int64_t j, int64_t k) {
//     return k == 0 ? i*T + j : j*T + (i+(k-1)*j)%T;
// }
// int64_t row(int64_t p, int64_t k) {
//     return k == 0 ? p/T : ((T-(k-1))*(p/T) + p)%T;
// }
// int64_t col(int64_t p, int64_t k) {
//     return k == 0 ? p%T : p/T;
// }


/* GLOBAL VARIABLES */

// All circular buffer indexing is modulo W

#define TT (T*T)
#define TLT (T*L*T)
#define LT (L*T)

// Receiver circular buffer of W rectangles of TLT bits.
// Within a rectangle are L blocks of TT bits with
// row-major order for bits within a block.
unsigned char RXbuffer[W*TLT];

/* Index of the "Newest" (most recently received)
   rectangle in the circular buffer. */
uint32_t NewestRect;

/*
 * Circular buffer of W groups of T syndromes.
 * The group with modulo-W index i consists of the T syndromes
 * corresponding to the T component codewords which START in rectangle i.
 * This group involves blocks from rectangle i to rectangle i + SCOPE.
 * It involves ALL blocks from the rectangle i + SCOPE, but DIFFERENT blocks
 * from rectangles i+SCOPE-1, i+SCOPE-2, ..., i+SCOPE-SCOPE.
 * Refer to the Julia model for more details:
 * 	https://github.com/applecoffeecake/hosc-Julia
 * The SCOPE newest syndrome groups are groups of partial syndromes since the
 * remainder of the corresponding component codewords has not been received yet.
 * The W-SCOPE oldest syndrome groups correspond to complete component codewords
 * in the RXbuffer and are decoded during an iteration.
*/
uint32_t Syndrome[W*T];

// Circular buffer of Hamming weights of each rectangle for error-counting
uint32_t RectWeight[W];

// Component code stuff:
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
// LT*(M+1)-1 since the type is unsigned.
static inline __attribute__((always_inline)) uint32_t errorlocFromSyn(uint32_t x) {
	return (ainv*((x>>1)+mb))&mask;
}

/*
 * Functions for flipping the bit in a given position
 * by updating the state of the three circular buffers
 * RXbuffer, Syndrome, and RectWeight.
 * We have 0 <= rect < T, 0 <= posn < T*T, 0 <= class <= L-1
 */
/*
 * The SCOPE oldest blocks have fewer associated syndromes
 * since part of the corresponding component codewords has been
 * dumped/delivered. We don't want to wrap around and modify the
 * partial syndromes corresponding to the SCOPE newest rectangles in
 * this case. For this reason, we pass the "age" of a rectangle which
 * can be counted during a decoding sweep/iteration.
 */
// c_class = L-1-class
// SCOPE-DTS[class][k] = SCOPE_MINUS_DTS_c[c_class][k]
static inline __attribute__((always_inline)) void flip(uint32_t rect, uint32_t c_class, uint32_t posn, uint32_t age) {
    int i, j, k;
    unsigned char *p = RXbuffer + rect*TLT + c_class*TT + posn;
    if (*p) { /* is this a one? */
        --RectWeight[rect];
        *p = '\0';
    } else {
        ++RectWeight[rect];
        *p = '\1';
    }
    k = M;
    while (1) {
        if (k < 0 || SCOPE_MINUS_DTS_c[c_class][k]+age >= W) break;
        i = row(posn,k);
        j = col(posn,k);
        Syndrome[((rect-SCOPE_MINUS_DTS_c[c_class][k]+W)%W)*T+i] ^= synFromErrorloc(((M-k)*L+c_class)*T+j);
        k--;
    }
}

/* The following function creates a new "newest" received rectangle
   from a binary symmetric channel with crossover probability p.
   The following operations are performed.
	1. The index of the newest rectangle is incremented and becomes
	   the location of the previous oldest block which is to be overwritten.
	2. The data, syndrome, and weight buffers are zeroed at this new index.
	3. Bits are randomly flipped (taking geometric jumps) in the newest
	   rectangle until the end of the rectangle is reached.
*/

#define F_ONE_MSB 0x3f800000
#define F_MANTISSA 0x7fffff
static inline __attribute__((always_inline)) void ReceiveRect(float p) {
    int rectposn;
    float k;
    union { float r; uint32_t i; } x;

    if (++NewestRect >= W) NewestRect = 0; // mod W increment
    memset(RXbuffer+NewestRect*TLT, 0, TLT*sizeof(unsigned char));
    memset(Syndrome+NewestRect*T, 0, T*sizeof(uint32_t));
    RectWeight[NewestRect] = 0;

    k = 1.0f/logf(1.0f-p);
    rectposn = -1;
    while (1) {
        x.i = (pcg32_random_r() & F_MANTISSA) ^ F_ONE_MSB;
        rectposn += 1 + (int) floor(k*logf(2.0f - x.r));
        if (rectposn >= TLT) {
			break;
        } else {
			flip(NewestRect, rectposn/TT, rectposn%TT, 0);
		}
    }
}
// Rejects bit flips unless they occur in the parity parity columns
// L*T-parity + 0, L*T-parity + 1, ..., L*T-parity + (parity-1)
static inline __attribute__((always_inline)) void ReceivePseudoterminationRect(float p) {
    int rectposn;
    float k;
    union { float r; uint32_t i; } x;

    if (++NewestRect >= W) NewestRect = 0; // mod W increment
    memset(RXbuffer+NewestRect*TLT, 0, TLT*sizeof(unsigned char));
    memset(Syndrome+NewestRect*T, 0, T*sizeof(uint32_t));
    RectWeight[NewestRect] = 0;

    k = 1.0f/logf(1.0f-p);
    rectposn = -1;
    while (1) {
        x.i = (pcg32_random_r() & F_MANTISSA) ^ F_ONE_MSB;
        rectposn += 1 + (int) floor(k*logf(2.0f - x.r));
        if (rectposn >= TLT) {
			break;
		} else if ((rectposn/TT)*T + (rectposn%TT)%T >= (LT-parity)) {
			flip(NewestRect, rectposn/TT, rectposn%TT, 0);
		}
    }
}


/*
   perform the initial set up:
    --- set up global variables in a state ready to receive first rectangle
*/
static inline __attribute__((always_inline)) void Initialize() {
    /* zero global arrays */
    memset(RXbuffer, 0, W*TLT*sizeof(unsigned char));
    memset(Syndrome, 0, W*T*sizeof(uint32_t));
    memset(RectWeight, 0, W*sizeof(uint32_t));
    NewestRect = W-1;
}


/* Sweep through all syndromes; return the number of corrections performed. */
// c_class = L-1-class
// SCOPE-DTS[class][perm] = SCOPE_MINUS_DTS_c[c_class][perm]
// DTS[class][perm] = SCOPE-SCOPE_MINUS_DTS_c[c_class][perm]
int sweep() {
    int i, j; // error coords within block
    int j_rect, c_class; // error column within rectangle, class (block label) within rectangle
    int k;      /* loop index                    */
    int rect;  /* rectangle index                   */
    uint32_t syn;  /* syndrome value */
    uint32_t errorloc;  /* error location within codeword */
    int perm;   /* index of permutation to apply to (i,j) to get position */
    int count = 0;  /* number of corrections performed     */
    // The SCOPE number of syndrome groups with indices
    // NewestRect-0, NewestRect-1, ..., NewestRect-(SCOPE-1)
    // are not yet completed.
    // Therefore, decoding starts at NewestRect-SCOPE and decrements
    // covering W-SCOPE completed syndrome groups.
    rect = (NewestRect-SCOPE+W)%W;
    for (k=0; k < W-SCOPE; ++k) {
        for (i=0; i < T; ++i) {
            syn = Syndrome[rect*T + i];
            if (syn & 0x01) {
                errorloc = errorlocFromSyn(syn);
                if (errorloc < LT*(M+1)) {
                    j_rect = errorloc % LT; // column within rect
                    perm = M - errorloc/LT; // rect within codeword span
                    j = j_rect%T;
                    c_class = j_rect/T;
                    flip((rect+SCOPE_MINUS_DTS_c[c_class][perm])%W, c_class, pos(i, j, perm), k+SCOPE-SCOPE_MINUS_DTS_c[c_class][perm]);
                    count += 1;
                }
            }
        }
        if (--rect < 0) rect = W-1; // mod W decrement
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
#define SanityCheckRectangles 10000
void SanityCheck()  /* triggered by -C command line switch */
{
    int b, i, j, p;
    uint64_t ErrorCount;
    float pp, qq;
    double R; // Code rate
	double R_nominal; // Nominal code rate
	double R_framing; // Framing/pseudotermination rate loss 

    parity = pow2ge((M+1)*LT) + 1;
	R_nominal = 1.0 - (double)parity/(double)LT;
	R_framing = (double)((F-W)*LT)/(double)((F-W)*LT + W*parity);
	R = R_nominal*R_framing;

    printf("L=%d, T=%d, M=%d, Hamming Code Length=%d, Parity bits=%d, Rate=%f\n",
           L, T, M, LT*(M+1), parity, R);
    Initialize();
    /*  make sure that the bijections work properly */
    for (b=0; b < M + 1; ++b) {
       printf("Checking bijection %d: ", b);
       for (p=0; p < T*T; ++p) {
           i = row(p,b);
           j = col(p,b);
           if (pos(i, j, b) != p) {
               printf("** failed at p=%d\n", p);
               exit(1);
           }
       }
       for (i=0; i < T; ++i) {
		   for (j=0; j < T; ++j) {
		       p = pos(i, j, b);
		       if (row(p,b) != i || col(p,b) != j) {
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
        for (b=0; b < SanityCheckRectangles; ++b)
        {
            ReceiveRect(pp);
            ErrorCount += RectWeight[NewestRect];
        }
        qq = (float)ErrorCount/SanityCheckRectangles/(TLT);
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
    printf("PRNG_SEED from time and pid: %lu \n", PRNG_SEED);
    pcg32_srandom_r(PRNG_SEED, PRNG_SEED*17);
    // pcg32_srandom_r(time(NULL), time(NULL)*17);
    // printf("SEED IGNORED\n");
    // pcg32_srandom_r(123456789,987654321);  /* for debugging */

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
    uint64_t RectsDecoded = 0; // rectangles delivered
	uint64_t FramesDecoded = 0;
	
	
    int BitErrors = 0;
	int FrameErrors = 0;
	int prevBitErrors = 0; //for counting frame errors
    int batch;
	int frame; 
    int rect;
    int sweepcnt;
    int i;
    int pdef = 0;

    time_t then, now;  /* to estimate throughput */
    
    m = (uint32_t) pow2ge((M+1)*LT);
	if (m < 3 || m > 16) {
		printf("Component code length not supported! (m = %d)\n", m);
		return 1;
	}
	s = (1<<m)-((M+1)*LT);
	a = aLUT[m-3];
	b = bLUT[m-3] + a*s;
	ainv = ainvLUT[m-3];
	mask = (1<<m)-1; 
	mb = (1<<m)-b;
	
	parity = ((int) m) + 1;
    
	if (parity >= LT) {
		printf("parity = %d, LT = %d: need parity < LT, LT too small!\n", parity, LT);
		return 1;
	}

    R_nominal = 1.0 - (double)parity/(double)LT;
	R_framing = (double)((F-W)*LT)/(double)((F-W)*LT + W*parity);
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
            "Simulating L = %d, M = %d, SCOPE = %d, T = %d, (M+1)LT = %d, %d parity bits,\nR = %lf",
            L, M, SCOPE, T, (M+1)*LT, parity, R);
        fprintf(stderr,
            " at p = %g corresponding to gap-to-Shannon of %lf dB.\n",
            p, dbgaptoshannon(R, p));
		fprintf(stderr,
            "R_nominal = %lf and R_framing = %lf with F = %d.\n", R_nominal, R_framing, F);
		fprintf(stderr,"Each frame contains %d %d-by-%d information chunks\n", F-W, T, (LT-parity));
		fprintf(stderr,"and %d %d-by-%d parity chunks.\n", F, T, parity);
        fprintf(stderr, "Decoding in batches of %lu frames.\n",
            ActualBatchSize);
        fprintf(stderr, "Peforming %d decoding iterations.\n",
            ActualSweepsPerBlock);
        fprintf(stderr, "Decoding window = %d rectangles = %g Mbits.\n",
            W, W*TLT*1e-6);
        fprintf(stderr, "Maximum number of batches = %lu.\n", ActualMaxBatches);
        fprintf(stderr, "Will stop at %lu frame errors.\n", ActualErrorsToFind);
    }

	/**** start of simulation ****/
	
	// Redefined a batch to be a number of frames transmitted
	// Batch size is a number of frames
	then = time(NULL);
	for (batch=0; batch < ActualMaxBatches; ++batch) {
		for (frame=0; frame < ActualBatchSize; ++frame) {			
			Initialize(); // Reset buffers			
			prevBitErrors = BitErrors; 
			// Receive first W rectangles
			for (rect=0; rect < W; ++rect) {
				ReceiveRect(p);
				for (sweepcnt = 0; sweepcnt < ActualSweepsPerBlock; ++sweepcnt) {
					if (!sweep()) {
						break;
					}
				}
			}
			// Receive the next F-W-W rectangles while delivering
			// the first F-W-W information-bearing rectangles
			for (rect=0; rect < (F-W-W); ++rect) {
				++RectsDecoded;
				BitErrors += RectWeight[(NewestRect+1)%W];
				ReceiveRect(p);
				for (sweepcnt = 0; sweepcnt < ActualSweepsPerBlock; ++sweepcnt) {
					if (!sweep()) {
						break;
					}
				}
			}
			// Receive the next W pseudotermination rectangles while delivering
			// the last W information-bearing rectangles
			for (rect=0; rect < W; ++rect) {
				++RectsDecoded;
				BitErrors += RectWeight[(NewestRect+1)%W];
				ReceivePseudoterminationRect(p);
				for (sweepcnt = 0; sweepcnt < ActualSweepsPerBlock; ++sweepcnt) {
					if (!sweep()) {
						break;
					}
				}
			}
			// in total, F rectangles have been received of which the last W
			// were pseudotermination rectangles
			// in total, F-W information-bearing rectangles were delivered
			
			++FramesDecoded;
			if (BitErrors != prevBitErrors) {
				FrameErrors += 1;
			}
			
			if (VERBOSE && !(FramesDecoded & STATUS_FREQUENCY)) {
				now = time(NULL);
				fprintf(stderr,
				"%d bit errors, %d frame errors in %lu frames delivered; %g bits/s = %g frames/s					\r", 
						BitErrors, FrameErrors, FramesDecoded, 
						(double)T*(LT-parity)*(F-W)*FramesDecoded/(double)(now-then),
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
	printf("Simulated L = %d, M = %d, SCOPE = %d, T = %d, (M+1)LT = %d, %d parity bits,\nR = %lf",
            L, M, SCOPE, T, (M+1)*LT, parity, R);
	printf(" at p = %g corresponding to gap-to-Shannon of %lf dB.\n",
            p, dbgaptoshannon(R, p));
	printf("R_nominal = %lf and R_framing = %lf with F = %d.\n", R_nominal, R_framing, F);
	printf("Each frame contained %d %d-by-%d information chunks\n", F-W, T, (LT-parity));
	printf("and %d %d-by-%d parity chunks.\n", F, T, parity);
	printf("Peformed %d iterations during decoding.\n", ActualSweepsPerBlock);
	printf("with a decoding window of %d blocks = %g Mbits.\n", W, W*TLT*1e-6);
	printf("Results:\n");
	printf(" %d bit errors, %d frame errors in\n", BitErrors, FrameErrors);
	printf(" %lu frames delivered each containing\n", FramesDecoded);
	printf(" %d %d-by-%d information chunks\n", F-W, T, (LT-parity));
	printf(" and %d %d-by-%d parity chunks.\n", F, T, parity);
	printf(" Total of %lu = %g information bits delivered.\n", 
							(F-W)*T*(LT-parity)*FramesDecoded,
					(double)(F-W)*T*(LT-parity)*FramesDecoded);
    printf(" BER = %g\n", (double)BitErrors/(F-W)/(T*(LT-parity))/FramesDecoded);
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
