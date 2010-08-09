/*****************************************************************************\
 * Computer Algebra System SINGULAR    
\*****************************************************************************/
/** @file f5c.cc
 * 
 * Implementation of variant F5e of Faugere's
 * F5 algorithm in the SINGULAR kernel. F5e reduces the computed Groebner 
 * bases after each iteration step, whereas F5 does not do this.
 *
 * ABSTRACT: An enhanced variant of Faugere's F5 algorithm .
 *
 * LITERATURE:
 * - F5 Algorithm:  http://www-calfor.lip6.fr/~jcf/Papers/F02a.pdf
 * - F5C Algorithm: http://arxiv.org/abs/0906.2967
 * - F5+ Algorithm: to be confirmed
 *
 * @author Christian Eder
 *
 * @internal @version \$Id$
 *
 **/
/*****************************************************************************/

#include "mod2.h"
#ifdef HAVE_F5C
#include <unistd.h>
#include "structs.h"
#include "kutil.h"
#include "omalloc.h"
#include "polys.h"
#include "polys-impl.h" // needed for GetBitFields
#include "p_polys.h"
#include "p_Procs.h"
#include "ideals.h"
#include "febase.h"
#include "kstd1.h"
#include "khstd.h"
#include "kbuckets.h"
#include "weight.h"
#include "intvec.h"
#include "prCopy.h"
#include "pInline1.h"
#include "f5c.h"
#include "timer.h"

#define F5EDEBUG  1
#define setMaxIdeal 64

/// NOTE that the input must be homogeneous to guarantee termination and
/// correctness. Thus these properties are assumed in the following.
ideal f5cMain(ideal F, ideal Q) 
{
  if(idIs0(F)) 
  {
    return idInit(1, F->rank);
  }
  // interreduction of the input ideal F
  F = kInterRed(F, NULL);

#if F5EDEBUG
  int j = 0;
  int k = 0;
  int* expVec   = new int[(currRing->N)+1];
  for( ; k<IDELEMS(F); k++)
  {
    Print("Poly: ");
    pWrite(pHead(F->m[k]));
    pGetExpV(F->m[k],expVec);
    Print("EXP VEC: ");
    for( ; j<currRing->N+1; j++)
    {
      Print("%d ",expVec[j]);
    }
    j = 0;
    Print("\n");
  }
#endif

  ideal r = idInit(1, F->rank);
  // save the first element in ideal r, initialization of iteration process
  r->m[0] = F->m[0];
  // counter over the remaining generators of the input ideal F
  int gen;
  for(gen=1; gen<IDELEMS(F); gen++) 
  {
    // computation of r: a groebner basis of <F[0],...,F[gen]> = <r,F[gen]>
    r = f5cIter(F->m[gen], r);
    // the following interreduction is the essential idea of F5e.
    // NOTE that we do not need the old rules from previous iteration steps
    // => we only interreduce the polynomials and forget about their labels
    r = kInterRed(r);
  }
  return r;
}



ideal f5cIter(poly p, ideal redGB) 
{
  int i;
  // create array of leading monomials of previously computed elements in redGB
  
  F5Rules* f5Rules = (F5Rules*) omalloc(sizeof(struct F5Rules));
  // malloc memory for slabel
  f5Rules->label  = (int**) omalloc(IDELEMS(redGB)*sizeof(int*));
  f5Rules->slabel = (unsigned long*) omalloc((currRing->N+1)*sizeof(unsigned long)); 
  for(i=0; i<IDELEMS(redGB); i++) 
  {
    f5Rules->label[i]  =  (int*) omalloc((currRing->N+1)*sizeof(int));
    pGetExpV(redGB->m[i], f5Rules->label[i]);
    f5Rules->slabel[i] =  ~ pGetShortExpVector(redGB->m[i]); // bit complement ~
  } 

#if F5EDEBUG
  int j = 0;
  int k = 0;
  Print("SIZE OF redGB: %d\n",IDELEMS(redGB));
  for( ; k<IDELEMS(redGB); k++)
  {
    Print("Poly: ");
    pWrite(pHead(redGB->m[k]));
    Print("EXP VEC: ");
    for( ; j<currRing->N+1; j++)
    {
      Print("%d ",f5Rules->label[k][j]);
    }
    Print("\n");
  }
#endif

  f5Rules->size = i++;
  // reduce and initialize the list of Lpolys with the current ideal generator p
  p = kNF(redGB, currQuotient, p);  
  /******************************
   * TO DO
   *****************************/
  Lpoly gCurr = {NULL, p, NULL, false};  
  gCurr.label = (int*) omalloc((currRing->N+1)*sizeof(int));
  for(i=0; i<currRing->N+1; i++)
  {
    gCurr.label[i] = 0;
  }
  
  // initializing the list of critical pairs for this iteration step 
  Cpair* critPairsFirst;
  Cpair* critPairsLast;
  critPairsFirst  = critPairsLast = NULL; 
  criticalPairInit(gCurr, redGB, *f5Rules, critPairsLast); 
  // free memory 
  //omfree(critPairsFirst); 
  //omfree(critPairsLast); 
  return redGB;
}



void criticalPairInit(const Lpoly& gCurr, const ideal redGB, const F5Rules& f5Rules, Cpair* critPairsFirst)
{
  int i, j;
  int* expVecNewElement = (int*) omalloc((currRing->N+1)*sizeof(int));
  int* expVecTemp       = (int*) omalloc((currRing->N+1)*sizeof(int));
  pGetExpV(gCurr.p, expVecNewElement); 
  // this must be changed for parallelizing the generation process of critical
  // pairs
  Cpair* critPairTemp;
  Cpair critPair    = {NULL, 0, NULL, 0, NULL, gCurr.p, NULL, 0, NULL, NULL};
  critPairTemp      = &critPair;
  // we only need to alloc memory for the 1st label as for the initial 
  // critical pairs all 2nd generators have label NULL in F5e
  critPairTemp->mlabel1  = (int*) omalloc((currRing->N+1)*sizeof(int));
  critPairTemp->mult1    = (int*) omalloc((currRing->N+1)*sizeof(int));
  critPairTemp->mult2    = (int*) omalloc((currRing->N+1)*sizeof(int));
  int temp;

  for(i=0; i<IDELEMS(redGB)-1; i++)
  {
    pGetExpV(redGB->m[i], expVecTemp); 
    // computation of the lcm and the corresponding multipliers for the critical
    // pair generated by the new element and elements of the previous iteration
    // steps, i.e. elements already in redGB
    for(j=1; j<=currRing->N; j++)
    {
      temp  = expVecTemp[j] - expVecNewElement[j];
      if(temp<0)
      {
        critPairTemp->mult1[j]   = -temp;  
        critPairTemp->mult2[j]   = 0; 
        critPairTemp->mlabel1[j] = gCurr.label[j] - temp;
      }
      else
      {
        critPairTemp->mult1[j]   = 0;  
        critPairTemp->mult2[j]   = temp;  
        critPairTemp->mlabel1[j] = gCurr.label[j];
      }
    }
    critPairTemp->smlabel1 = getShortExpVecFromArray(critPairTemp->mlabel1);
    
    if(!criterion1(critPairTemp->mlabel1, critPairTemp->smlabel1, f5Rules)) // testing the F5 Criterion
    {
      // completing the construction of the new critical pair and inserting it
      // to the list of critical pairs 
      critPairTemp->p2      = redGB->m[i];
      critPairsFirst        = insertCritPair(critPairTemp, critPairsFirst);
      //*critPair             = (Cpair*) omalloc(sizeof(Cpair));
      Cpair critPairNew     = {NULL, 0, NULL, 0, NULL, gCurr.p, NULL, 0, NULL, NULL};
      critPairTemp          = &critPairNew;
      critPairTemp->mlabel1 = (int*) omalloc((currRing->N+1)*sizeof(int));
      critPairTemp->mult1   = (int*) omalloc((currRing->N+1)*sizeof(int));
      critPairTemp->mult2   = (int*) omalloc((currRing->N+1)*sizeof(int));
    }
  }
  // same critical pair processing for the last element in redGB
  // This is outside of the loop to keep memory low, since we know that after
  // this element no new memory for a critical pair must be allocated.
  pGetExpV(redGB->m[IDELEMS(redGB)-1], expVecTemp); 
  // computation of the lcm and the corresponding multipliers for the critical
  // pair generated by the new element and elements of the previous iteration
  // steps, i.e. elements already in redGB
  for(j=1; j<=currRing->N; j++)
  {
    temp  = expVecTemp[j] - expVecNewElement[j];
    if(temp<0)
    {
      critPairTemp->mult1[j]   = -temp;  
      critPairTemp->mult2[j]   = 0; 
      critPairTemp->mlabel1[j] = gCurr.label[j] - temp;
    }
    else
    {
      critPairTemp->mult1[j]   = 0;  
      critPairTemp->mult2[j]   = temp;  
      critPairTemp->mlabel1[j] = gCurr.label[j];
    }
  }
  critPairTemp->smlabel1 = getShortExpVecFromArray(critPairTemp->mlabel1);
  
  if(!criterion1(critPairTemp->mlabel1, critPairTemp->smlabel1, f5Rules)) // testing the F5 Criterion
  {
    // completing the construction of the new critical pair and inserting it
    // to the list of critical pairs 
    for(j=1; j<=currRing->N, j++)
    {
      critPairTemp->labeldeg += critPairTemp->mlabel[j]; 
    }
    critPairTemp->p2  = redGB->m[IDELEMS(redGB)-1];
    critPairsFirst    = insertCritPair(critPairTemp, critPairsFirst);
  }
  omfree(expVecTemp);
  omfree(expVecNewElement);
}


// TODO: How to sort this list? Mergesort? Copy an array and Quicksort?
Cpair* insertCritPair(Cpair* critPair, Cpair* critPairsFirst)
{
  int i = 1;
  if(!critPairsFirst)
  {
    return critPair;
  }
  else
  {
    Cpair* temp = critPairsFirst;
    while(temp->next)
    {
      if(temp->next->ldeg < critPair->ldeg)
      {
        temp  = temp->next;
      }
      else
      {
        for( ; i<=currRing->N; i++)
        {
          // TODO: How to compare the exponent vectors by the given polynomial ordering?
        }
      }
    }
    critPair->next  = temp->next;
    temp->next       = critPair;
  }
  return critPairsFirst;
}



/// my own GetBitFields
/// @sa GetBitFields
static inline unsigned long GetBitFieldsF5e(long e,
                                         unsigned int s, unsigned int n)
{
#define Sy_bit_L(x)     (((unsigned long)1L)<<(x))
  unsigned int i = 0;
  unsigned long  ev = 0L;
  assume(n > 0 && s < BIT_SIZEOF_LONG);
  do
  {
    assume(s+i < BIT_SIZEOF_LONG);
    if (e > (long) i) ev |= Sy_bit_L(s+i);
    else break;
    i++;
  }
  while (i < n);
  return ev;
}



unsigned long getShortExpVecFromArray(int* a, ring r)
{
  unsigned long ev  = 0; // short exponent vector
  unsigned int  n   = BIT_SIZEOF_LONG / r->N; // number of bits per exp
  unsigned int  i   = 0,  j = 1;
  unsigned int  m1; // highest bit which is filled with (n+1)   

  if (n == 0)
  {
    if (r->N<2*BIT_SIZEOF_LONG)
    {
      n=1;
      m1=0;
    }
    else
    {
      for (; j<=(unsigned long) r->N; j++)
      {
        if (a[j] > 0) i++;
        if (i == BIT_SIZEOF_LONG) break;
      }
      if (i>0)
      ev = ~((unsigned long)0) >> ((unsigned long) (BIT_SIZEOF_LONG - i));
      return ev;
    }
  }
  else
  {
    m1 = (n+1)*(BIT_SIZEOF_LONG - n*r->N);
  }

  n++;
  while (i<m1)
  {
    ev |= GetBitFieldsF5e(a[j] , i, n);
    i += n;
    j++;
  }

  n--;
  while (i<BIT_SIZEOF_LONG)
  {
    ev |= GetBitFieldsF5e(a[j] , i, n);
    i += n;
    j++;
  }
  return ev;
}



inline bool criterion1(const int* mlabel1, const unsigned long smlabel1, const F5Rules& f5Rules)
{
  int i = 0;
  int j = currRing->N;
  for( ; i < f5Rules.size; i++)
  {
    if(!(smlabel1 & f5Rules.slabel[i]))
    {
      while(j)
      {
        if(mlabel1[j] > f5Rules.label[i][j])
        {
         break;
        }
        j--;
      }
      if(!j)
      {
        return true;
      }
      else 
      {
        j = currRing->N; 
      }
    }
  }
  return false;
}

#endif
// HAVE_F5C
