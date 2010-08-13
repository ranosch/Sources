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
#include "p_MemCmp.h"
#include "pInline2.h"
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
    Print("TEST Poly: ");
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
  /// define the global variables for fast exponent vector
  /// reading/writing/comparison
  int i = 0;
  /// declaration of global variables used for exponent vector
  int numVariables  = currRing->N;
  /// reading/writing/comparison
  int* shift              = (int*) omalloc((currRing->N+1)*sizeof(int));
  int* negBitmaskShifted  = (int*) omalloc((currRing->N+1)*sizeof(int));
  int* offsets            = (int*) omalloc((currRing->N+1)*sizeof(int));
  const unsigned long _bitmasks[4] = {-1, 0x7fff, 0x7f, 0x3};
  for( ; i<currRing->N+1; i++)
  {
    shift[i]                = (currRing->VarOffset[i] >> 24) & 0x3f;
    negBitmaskShifted[i]    = ~((currRing->bitmask & 
                                _bitmasks[(currRing->VarOffset[i] >> 30)]) 
                                << shift[i]);
    offsets[i]              = (currRing->VarOffset[i] & 0xffffff);
  }
  
  ideal r = idInit(1, F->rank);
  // save the first element in ideal r, initialization of iteration process
  r->m[0] = F->m[0];
  // counter over the remaining generators of the input ideal F
  for(i=1; i<IDELEMS(F); i++) 
  {
    // computation of r: a groebner basis of <F[0],...,F[gen]> = <r,F[gen]>
    r = f5cIter(F->m[i], r, numVariables, shift, negBitmaskShifted, offsets);
    // the following interreduction is the essential idea of F5e.
    // NOTE that we do not need the old rules from previous iteration steps
    // => we only interreduce the polynomials and forget about their labels
    Print("ELEMENTE IN R: %d\n", IDELEMS(r));
    r = kInterRed(r);
  }
    pWrite(r->m[0]);
  
  omfree(shift);
  omfree(negBitmaskShifted);
  omfree(offsets);
  
  return r;
}



ideal f5cIter(poly p, ideal redGB, int numVariables, int* shift, int* negBitmaskShifted, int* offsets)
{
  int i;
  // create array of leading monomials of previously computed elements in redGB
  
  F5Rules* f5Rules = (F5Rules*) omalloc(sizeof(struct F5Rules));
  // malloc memory for slabel
    Print("HERE %d  ",IDELEMS(redGB)); pWrite(redGB->m[0]);
  f5Rules->label  = (int**) omalloc(IDELEMS(redGB)*sizeof(int*));
    Print("HERE %d  ",IDELEMS(redGB)); pWrite(redGB->m[0]);
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
  Lpoly gCurr = {NULL, p, NULL, false};  
  gCurr.label = (int*) omalloc((currRing->N+1)*sizeof(int));
  for(i=0; i<currRing->N+1; i++)
  {
    gCurr.label[i] = 0;
  }
  
  // initializing the list of critical pairs for this iteration step 
  CpairDegBound* critPairsBounds = NULL;
  criticalPairInit( gCurr, redGB, *f5Rules, critPairsBounds, numVariables, shift,
                    negBitmaskShifted, offsets); 
  // free memory 
  //omfree(critPairsFirst); 
  //omfree(critPairsLast); 
  return redGB;
}



void criticalPairInit(const Lpoly& gCurr, const ideal redGB, 
                      const F5Rules& f5Rules, CpairDegBound* critPairsBounds, 
                      int numVariables, int* shift, int* negBitmaskShifted, 
                      int* offsets)
{
  int i, j;
  int* expVecNewElement = (int*) omalloc((currRing->N+1)*sizeof(int));
  int* expVecTemp       = (int*) omalloc((currRing->N+1)*sizeof(int));
  pGetExpV(gCurr.p, expVecNewElement); 
  // this must be changed for parallelizing the generation process of critical
  // pairs
  Cpair* critPairTemp;
  Cpair critPair    = {NULL, NULL, NULL, 0, NULL, gCurr.p, NULL, 0, NULL, NULL};
  critPairTemp      = &critPair;
  // we only need to alloc memory for the 1st label as for the initial 
  // critical pairs all 2nd generators have label NULL in F5e
  critPairTemp->mLabel1  = (int*) omalloc((currRing->N+1)*sizeof(int));
  critPairTemp->mult1    = (int*) omalloc((currRing->N+1)*sizeof(int));
  critPairTemp->mult2    = (int*) omalloc((currRing->N+1)*sizeof(int));
  int temp;
  long critPairDeg = 0;
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
        critPairTemp->mult1[j]    =   -temp;  
        critPairTemp->mult2[j]    =   0; 
        critPairTemp->mLabel1[j]  =   gCurr.label[j] - temp;
        critPairDeg               +=  (gCurr.label[j] - temp); 
      }
      else
      {
        critPairTemp->mult1[j]    =   0;  
        critPairTemp->mult2[j]    =   temp;  
        critPairTemp->mLabel1[j]  =   gCurr.label[j];
        critPairDeg               +=  gCurr.label[j]; 
      }
    }
    critPairTemp->smLabel1 = getShortExpVecFromArray(critPairTemp->mLabel1);
    
    if(!criterion1(critPairTemp->mLabel1, critPairTemp->smLabel1, f5Rules)) // testing the F5 Criterion
    {
      // completing the construction of the new critical pair and inserting it
      // to the list of critical pairs 
      critPairTemp->p2      = redGB->m[i];
      // now we really need the memory for the exp label
      critPairTemp->mLabelExp = (unsigned long*) omalloc(VARS*sizeof(unsigned long));
      getExpFromIntArray( critPairTemp->mLabel1, critPairTemp->mLabelExp, numVariables,
                          shift, negBitmaskShifted, offsets);
      insertCritPair(critPairTemp, critPairDeg, critPairsBounds);
      Cpair critPairNew     = {NULL, NULL, NULL, 0, NULL, gCurr.p, NULL, 0, NULL, NULL};
      critPairTemp          = &critPairNew;
      critPairTemp->mLabel1 = (int*) omalloc((currRing->N+1)*sizeof(int));
      critPairTemp->mult1   = (int*) omalloc((currRing->N+1)*sizeof(int));
      critPairTemp->mult2   = (int*) omalloc((currRing->N+1)*sizeof(int));
    }
    critPairDeg = 0;
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
      critPairTemp->mult1[j]    =   -temp;  
      critPairTemp->mult2[j]    =   0; 
      critPairTemp->mLabel1[j]  =   gCurr.label[j] - temp;
      critPairDeg               +=  (gCurr.label[j] - temp);
    }
    else
    {
      critPairTemp->mult1[j]    =   0;  
      critPairTemp->mult2[j]    =   temp;  
      critPairTemp->mLabel1[j]  =   gCurr.label[j];
      critPairDeg               +=  gCurr.label[j];
    }
  }
  critPairTemp->smLabel1 = getShortExpVecFromArray(critPairTemp->mLabel1);
  
  if(!criterion1(critPairTemp->mLabel1, critPairTemp->smLabel1, f5Rules)) // testing the F5 Criterion
  {
    // completing the construction of the new critical pair and inserting it
    // to the list of critical pairs 
    critPairTemp->p2  = redGB->m[IDELEMS(redGB)-1];
    // now we really need the memory for the exp label
    critPairTemp->mLabelExp = (unsigned long*) omalloc(VARS*sizeof(unsigned long));
    getExpFromIntArray( critPairTemp->mLabel1, critPairTemp->mLabelExp, numVariables,
                        shift, negBitmaskShifted, offsets);
    insertCritPair(critPairTemp, critPairDeg, critPairsBounds);
  }
  omfree(expVecTemp);
  omfree(expVecNewElement);
}



void criticalPairPrev(const Lpoly& gCurr, const ideal redGB, const F5Rules& f5Rules, 
                      const RewRules& rewRules, CpairDegBound* critPairsBounds,
                      int numVariables, int* shift, int* negBitmaskShifted, int* offsets)
{
  int i, j;
  int* expVecNewElement = (int*) omalloc((currRing->N+1)*sizeof(int));
  int* expVecTemp       = (int*) omalloc((currRing->N+1)*sizeof(int));
  pGetExpV(gCurr.p, expVecNewElement); 
  // this must be changed for parallelizing the generation process of critical
  // pairs
  Cpair* critPairTemp;
  Cpair critPair    = {NULL, NULL, NULL, 0, NULL, gCurr.p, NULL, 0, NULL, NULL};
  critPairTemp      = &critPair;
  // we only need to alloc memory for the 1st label as for the initial 
  // critical pairs all 2nd generators have label NULL in F5e
  critPairTemp->mLabel1  = (int*) omalloc((currRing->N+1)*sizeof(int));
  critPairTemp->mult1    = (int*) omalloc((currRing->N+1)*sizeof(int));
  critPairTemp->mult2    = (int*) omalloc((currRing->N+1)*sizeof(int));
  int temp;
  long critPairDeg = 0;
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
        critPairTemp->mult1[j]    =   -temp;  
        critPairTemp->mult2[j]    =   0; 
        critPairTemp->mLabel1[j]  =   gCurr.label[j] - temp;
        critPairDeg               +=  (gCurr.label[j] - temp); 
      }
      else
      {
        critPairTemp->mult1[j]    =   0;  
        critPairTemp->mult2[j]    =   temp;  
        critPairTemp->mLabel1[j]  =   gCurr.label[j];
        critPairDeg               +=  gCurr.label[j]; 
      }
    }
    critPairTemp->smLabel1 = getShortExpVecFromArray(critPairTemp->mLabel1);
    
    // testing the F5 Criterion
    if( !criterion1(critPairTemp->mLabel1, critPairTemp->smLabel1, f5Rules) && 
        !criterion2(critPairTemp->mLabel1, critPairTemp->smLabel1, rewRules) ) 
    {
      // completing the construction of the new critical pair and inserting it
      // to the list of critical pairs 
      critPairTemp->p2      = redGB->m[i];
      // now we really need the memory for the exp label
      critPairTemp->mLabelExp = (unsigned long*) omalloc(VARS*sizeof(unsigned long));
      getExpFromIntArray( critPairTemp->mLabel1, critPairTemp->mLabelExp, numVariables,
                          shift, negBitmaskShifted, offsets);
      insertCritPair(critPairTemp, critPairDeg, critPairsBounds);
      Cpair critPairNew     = {NULL, NULL, NULL, 0, NULL, gCurr.p, NULL, 0, NULL, NULL};
      critPairTemp          = &critPairNew;
      critPairTemp->mLabel1 = (int*) omalloc((currRing->N+1)*sizeof(int));
      critPairTemp->mult1   = (int*) omalloc((currRing->N+1)*sizeof(int));
      critPairTemp->mult2   = (int*) omalloc((currRing->N+1)*sizeof(int));
    }
    critPairDeg = 0;
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
      critPairTemp->mult1[j]    =   -temp;  
      critPairTemp->mult2[j]    =   0; 
      critPairTemp->mLabel1[j]  =   gCurr.label[j] - temp;
      critPairDeg               +=  (gCurr.label[j] - temp);
    }
    else
    {
      critPairTemp->mult1[j]    =   0;  
      critPairTemp->mult2[j]    =   temp;  
      critPairTemp->mLabel1[j]  =   gCurr.label[j];
      critPairDeg               +=  gCurr.label[j];
    }
  }
  critPairTemp->smLabel1 = getShortExpVecFromArray(critPairTemp->mLabel1);
  
  // testing the F5 Criterion
  if( !criterion1(critPairTemp->mLabel1, critPairTemp->smLabel1, f5Rules) && 
      !criterion2(critPairTemp->mLabel1, critPairTemp->smLabel1, rewRules) ) 
  {
    // completing the construction of the new critical pair and inserting it
    // to the list of critical pairs 
    critPairTemp->p2  = redGB->m[IDELEMS(redGB)-1];
    // now we really need the memory for the exp label
    critPairTemp->mLabelExp = (unsigned long*) omalloc(VARS*sizeof(unsigned long));
    getExpFromIntArray( critPairTemp->mLabel1, critPairTemp->mLabelExp, numVariables,
                        shift, negBitmaskShifted, offsets);
    insertCritPair(critPairTemp, critPairDeg, critPairsBounds);
  }
  omfree(expVecTemp);
  omfree(expVecNewElement);
}



void criticalPairCurr(const Lpoly& gCurr, const F5Rules& f5Rules, 
                      const RewRules& rewRules, CpairDegBound* critPairsBounds,
                      int numVariables, int* shift, int* negBitmaskShifted, 
                      int* offsets)
{
  int i, j;
  unsigned long* mLabelExp;
  int* expVecNewElement = (int*) omalloc((currRing->N+1)*sizeof(int));
  int* expVecTemp       = (int*) omalloc((currRing->N+1)*sizeof(int));
  pGetExpV(gCurr.p, expVecNewElement); 
  // this must be changed for parallelizing the generation process of critical
  // pairs
  Cpair* critPairTemp;
  Cpair critPair    = {NULL, NULL, NULL, 0, NULL, gCurr.p, NULL, 0, NULL, NULL};
  critPairTemp      = &critPair;
  // we need to alloc memory for the 1st & the 2nd label here
  // both elements are generated during the current iteration step
  critPairTemp->mLabel1  = (int*) omalloc((currRing->N+1)*sizeof(int));
  critPairTemp->mLabel2  = (int*) omalloc((currRing->N+1)*sizeof(int));
  critPairTemp->mult1    = (int*) omalloc((currRing->N+1)*sizeof(int));
  critPairTemp->mult2    = (int*) omalloc((currRing->N+1)*sizeof(int));
  // alloc memory for a temporary (non-integer/SINGULAR internal) exponent vector
  // for fast comparisons at the end which label is greater, those of the 1st or
  // those of the 2nd generator
  // Note: As we do not need the smaller exponent vector we do NOT store both in
  // the critical pair structure, but only the greater one. Thus the following
  // memory is freed before the end of criticalPairCurr()
  unsigned long* checkExp = (unsigned long*) omalloc(VARS*sizeof(unsigned long));
  int temp;
  long critPairDeg = 0;
  Lpoly* gCurrIter  = gCurr.next;
  while(gCurrIter->next)
  {
    pGetExpV(gCurrIter->p, expVecTemp); 
    // computation of the lcm and the corresponding multipliers for the critical
    // pair generated by the new element and elements of the previous iteration
    // steps, i.e. elements already in redGB
    for(j=1; j<currRing->N+1; j++)
    {
      temp  = expVecTemp[j] - expVecNewElement[j];
      if(temp<0)
      {
        critPairTemp->mult1[j]    =   -temp;  
        critPairTemp->mult2[j]    =   0; 
        critPairTemp->mLabel1[j]  =   gCurr.label[j] - temp;
        critPairTemp->mLabel2[j]  =   gCurrIter->label[j];
        critPairDeg               +=  (gCurr.label[j] - temp); 
      }
      else
      {
        critPairTemp->mult1[j]    =   0;  
        critPairTemp->mult2[j]    =   temp;  
        critPairTemp->mLabel1[j]  =   gCurr.label[j];
        critPairTemp->mLabel2[j]  =   gCurrIter->label[j] + temp;
        critPairDeg               +=  gCurr.label[j]; 
      }
    }
    critPairTemp->smLabel1 = getShortExpVecFromArray(critPairTemp->mLabel1);
    critPairTemp->smLabel2 = getShortExpVecFromArray(critPairTemp->mLabel2);
    
    // testing the F5 Criterion
    if( !criterion1(critPairTemp->mLabel1, critPairTemp->smLabel1, f5Rules) 
        && !criterion1(critPairTemp->mLabel2, critPairTemp->smLabel2, f5Rules) 
        && !criterion2(critPairTemp->mLabel1, critPairTemp->smLabel1, rewRules)   
        && !criterion2(critPairTemp->mLabel2, critPairTemp->smLabel2, rewRules)
      ) 
    {
      // completing the construction of the new critical pair and inserting it
      // to the list of critical pairs 
      critPairTemp->p2      = gCurrIter->p;
      // now we really need the memory for the exp label
      critPairTemp->mLabelExp = (unsigned long*) omalloc(VARS*sizeof(unsigned long));
      getExpFromIntArray( critPairTemp->mLabel1, critPairTemp->mLabelExp, numVariables,
                          shift, negBitmaskShifted, offsets);
      getExpFromIntArray( critPairTemp->mLabel2, checkExp, numVariables,
                          shift, negBitmaskShifted, offsets);
      
      // compare which label is greater and possibly switch the 1st and 2nd 
      // generator in critPairTemp
      expCmp(critPairTemp->mLabelExp, checkExp);
      
      insertCritPair(critPairTemp, critPairDeg, critPairsBounds);
      
      Cpair critPairNew     = {NULL, NULL, NULL, 0, NULL, gCurr.p, NULL, 0, NULL, NULL};
      critPairTemp          = &critPairNew;
      critPairTemp->mLabel1 = (int*) omalloc((currRing->N+1)*sizeof(int));
      critPairTemp->mult1   = (int*) omalloc((currRing->N+1)*sizeof(int));
      critPairTemp->mult2   = (int*) omalloc((currRing->N+1)*sizeof(int));
    }
    critPairDeg = 0;
    gCurrIter = gCurrIter->next;
  }
  // same critical pair processing for the last element in gCurr
  // This is outside of the loop to keep memory low, since we know that after
  // this element no new memory for a critical pair must be allocated.
  pGetExpV(gCurrIter->p, expVecTemp); 
  // computation of the lcm and the corresponding multipliers for the critical
  // pair generated by the new element and elements of the previous iteration
  // steps, i.e. elements already in redGB
  for(j=1; j<=currRing->N; j++)
  {
    temp  = expVecTemp[j] - expVecNewElement[j];
    if(temp<0)
    {
      critPairTemp->mult1[j]    =   -temp;  
      critPairTemp->mult2[j]    =   0; 
      critPairTemp->mLabel1[j]  =   gCurr.label[j] - temp;
      critPairTemp->mLabel2[j]  =   gCurrIter->label[j];
      critPairDeg               +=  (gCurr.label[j] - temp);
    }
    else
    {
      critPairTemp->mult1[j]    =   0;  
      critPairTemp->mult2[j]    =   temp;  
      critPairTemp->mLabel1[j]  =   gCurr.label[j];
      critPairTemp->mLabel2[j]  =   gCurrIter->label[j] + temp;
      critPairDeg               +=  gCurr.label[j];
    }
  }
  critPairTemp->smLabel1 = getShortExpVecFromArray(critPairTemp->mLabel1);
  
  // testing the F5 Criterion
  if( !criterion1(critPairTemp->mLabel1, critPairTemp->smLabel1, f5Rules) 
      && !criterion1(critPairTemp->mLabel2, critPairTemp->smLabel2, f5Rules) 
      && !criterion2(critPairTemp->mLabel1, critPairTemp->smLabel1, rewRules)   
      && !criterion2(critPairTemp->mLabel2, critPairTemp->smLabel2, rewRules)
    ) 
  {
    // completing the construction of the new critical pair and inserting it
    // to the list of critical pairs 
    critPairTemp->p2  = gCurrIter->p;
    // now we really need the memory for the exp label
    critPairTemp->mLabelExp = (unsigned long*) omalloc(VARS*sizeof(unsigned long));
    getExpFromIntArray( critPairTemp->mLabel1, critPairTemp->mLabelExp, numVariables,
                        shift, negBitmaskShifted, offsets);
    getExpFromIntArray( critPairTemp->mLabel2, checkExp, numVariables,
                        shift, negBitmaskShifted, offsets);
    
    // compare which label is greater and possibly switch the 1st and 2nd 
    // generator in critPairTemp
    expCmp(critPairTemp->mLabelExp, checkExp);
    
    insertCritPair(critPairTemp, critPairDeg, critPairsBounds);
  }
  omfree(checkExp);
  omfree(expVecTemp);
  omfree(expVecNewElement);
}



void insertCritPair(Cpair* cp, long deg, CpairDegBound* bound)
{
  if(!bound) // empty list?
  {
   CpairDegBound boundNew = {NULL, deg, cp, 1};
  }
  else
  {
    while(bound->next && (bound->next->deg < deg))
    {
      bound = bound->next;
    }
    if(bound->next->deg == deg)
    {
      cp->next        = bound->next->cp;
      bound->next->cp = cp;
      bound->next->length++;
    }
    else
    {
      CpairDegBound boundNew  = {bound->next, deg, cp, 1};
      bound->next             = &boundNew;
    }
  }
}



inline bool criterion1(const int* mLabel1, const unsigned long smLabel1, const F5Rules& f5Rules)
{
  int i = 0;
  int j = currRing->N;
  for( ; i < f5Rules.size; i++)
  {
    if(!(smLabel1 & f5Rules.slabel[i]))
    {
      while(j)
      {
        if(mLabel1[j] > f5Rules.label[i][j])
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



inline bool criterion2(const int* mLabel1, const unsigned long smLabel1, const RewRules& rewRules)
{
  int j = currRing->N;
  const RewRules* temp = &rewRules;
  while(temp)
  {
    if(!(smLabel1 & temp->slabel))
    {
      while(j)
      {
        if(mLabel1[j] > temp->label[j])
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



inline void getExpFromIntArray( const int* exp, unsigned long* r, 
                                int numVariables, int* shift, int* negBitmaskShifted, 
                                int* offsets)
{
  register int i = numVariables;
  for( ; i; i--)
  {
    register int shiftL   =   shift[i];
    long ee               =   exp[i] << shiftL;
    register int offsetL  =   offsets[i];
    r[offsetL]            &=  negBitmaskShifted[i];
    r[offsetL]            |=  ee;
  }
}



/// my own GetBitFields
/// @sa GetBitFields
inline unsigned long GetBitFieldsF5e(int e,
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



inline int expCmp(const unsigned long* a, const unsigned long* b)
{
    p_MemCmp_LengthGeneral_OrdGeneral(a, b, currRing->CmpL_Size, currRing->ordsgn,
                                      return 0, return 1, return -1);
}
#endif
// HAVE_F5C
