#ifndef GMPFLOAT_H
#define GMPFLOAT_H
/****************************************
*  Computer Algebra System SINGULAR     *
****************************************/
/* $Id$ */
/*
* ABSTRACT: computations with GMP floating-point numbers
*/
#include "coeffs.h"

BOOLEAN  ngfGreaterZero(number za, const coeffs r);
BOOLEAN  ngfGreater(number a, number b, const coeffs r);
BOOLEAN  ngfEqual(number a, number b, const coeffs r);
BOOLEAN  ngfIsOne(number a, const coeffs r);
BOOLEAN  ngfIsMOne(number a, const coeffs r);
BOOLEAN  ngfIsZero(number za, const coeffs r);
number   ngfInit(int i, const coeffs r);
int      ngfInt(number &n, const coeffs r);
number   ngfNeg(number za, const coeffs r);
number   ngfInvers(number a, const coeffs r);
number   ngfAdd(number la, number li, const coeffs r);
number   ngfSub(number la, number li, const coeffs r);
number   ngfMult(number a, number b, const coeffs r);
number   ngfDiv(number a, number b, const coeffs r);
void     ngfPower(number x, int exp, number *lu, const coeffs r);
number   ngfCopy(number a);
number   ngf_Copy(number a, coeffs r);
const char *   ngfRead (const char *s, number *a, const coeffs r);
void     ngfWrite(number &a, const coeffs r);

#ifdef LDEBUG
BOOLEAN  ngfDBTest(number a, const char *f, const int l);
#endif
void     ngfDelete(number *a, const coeffs r);

nMapFunc  ngfSetMap(const coeffs src, const coeffs dst);

void setGMPFloatDigits( size_t digits, size_t rest );
number ngfMapQ(number from, const coeffs r);
#endif