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
#include "options.h"
#include "structs.h"
#include "omalloc.h"
#include "polys.h"
#include "timer.h"
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

#ifdef PDEBUG
#undef PDEBUG
#define PDEBUG 1 
#endif
#define F5EDEBUG  1
#define setMaxIdeal 64
#define NUMVARS currRing->ExpL_Size
int create_count_f5 = 0; // for KDEBUG option in reduceByRedGBCritPair

/// NOTE that the input must be homogeneous to guarantee termination and
/// correctness. Thus these properties are assumed in the following.
ideal f5cMain(ideal F, ideal Q) 
{
  if(idIs0(F)) 
  {
    return idInit(1, F->rank);
  }
  // interreduction of the input ideal F
  ideal FRed = kInterRed(F, NULL);
  idDelete( &F );
  F = FRed;

#if F5EDEBUG
  int j = 0;
  int k = 0;
  int* expVec   = new int[(currRing->N)+1];
  for( ; k<IDELEMS(F); k++)
  {
    Print("ORDER: %ld\n",F->m[k]->exp[currRing->pOrdIndex]);
    Print("SIZE OF INTERNAL EXPONENT VECTORS: %d\n",currRing->ExpL_Size);
    pGetExpV(F->m[k],expVec);
    Print("EXP VEC: ");
    for( ; j<currRing->N+1; j++)
    {
      Print("%d  ",expVec[j]);
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
  unsigned long* negBitmaskShifted  = (unsigned long*) omalloc((currRing->N+1)*sizeof(unsigned long));
  int* offsets            = (int*) omalloc((currRing->N+1)*sizeof(int));
  const unsigned long _bitmasks[4] = {-1, 0x7fff, 0x7f, 0x3};
  for( ; i<currRing->N+1; i++)
  {
    /*
     shift[i]                = (currRing->VarOffset[i] >> 24) & 0x3f;
    negBitmaskShifted[i]    = ~((currRing->bitmask & 
                                _bitmasks[(currRing->VarOffset[i] >> 30)]) 
                                << shift[i]);
    offsets[i]              = (currRing->VarOffset[i] & 0xffffff);
    */
    shift[i]                = currRing->VarOffset[i] >> 24;
    negBitmaskShifted[i]    = ~(currRing->bitmask << shift[i]);
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
#if F5EDEBUG
    for( k=0; k<IDELEMS(r); k++ )
    {
      pTest( r->m[k] );
      Print("TESTS: %p ",r->m[k]);
      pWrite(r->m[k]);
    }
#endif
    Print("HERE1\n");
    ideal rTemp = kInterRed(r);
    idDelete( &r );
    r = rTemp;
    Print("HERE2\n");
  }
  
  omfree(shift);
  omfree(negBitmaskShifted);
  omfree(offsets);
  
  return r;
}



ideal f5cIter ( poly p, ideal redGB, int numVariables, int* shift, 
                unsigned long* negBitmaskShifted, int* offsets
              )
{
#if F5EDEBUG
  Print("F5CITER-BEGIN\n");
  Print("ORDER %ld -- %ld\n",p_GetOrder(p,currRing), p->exp[currRing->pOrdIndex]);
#endif  
  // create the reduction structure "strat" which is needed for all 
  // reductions with redGB in this iteration step
  kStrategy strat = new skStrategy;
  strat->syzComp  = 0;
  strat->ak       = idRankFreeModule(redGB);
  prepRedGBReduction(strat, redGB);

  int i;
  // create array of leading monomials of previously computed elements in redGB
  F5Rules* f5Rules        = (F5Rules*) omalloc(sizeof(struct F5Rules));
  // malloc memory for slabel
  f5Rules->label  = (int**) omalloc(IDELEMS(redGB)*sizeof(int*));
  f5Rules->slabel = (unsigned long*) omalloc((currRing->N+1)*
                    sizeof(unsigned long)); 

  for(i=0; i<IDELEMS(redGB); i++) 
  {
    f5Rules->label[i]  =  (int*) omalloc((currRing->N+1)*sizeof(int));
    pGetExpV(redGB->m[i], f5Rules->label[i]);
    pGetExpV(redGB->m[i], f5Rules->label[i]);
    f5Rules->slabel[i] =  pGetShortExpVector(redGB->m[i]); // bit complement ~
  } 

#if F5EDEBUG
  int j = 0;
  int k = 0;
  Print("SIZE OF redGB: %d\n",IDELEMS(redGB));
  for( ; k<IDELEMS(redGB); k++)
  {
    j = 0;
    Print("Poly: ");
    pWrite(pHead(redGB->m[k]));
    Print("%d. EXP VEC: ", k);
    Print("%p->%d\n", f5Rules->label[k], f5Rules->label[k][0]);
    for( ; j<currRing->N+1; j++)
    {
      Print("%d ",f5Rules->label[k][j]);
    }
    Print("\n");
  }
#endif

  f5Rules->size = i++;
  // initialize a first (dummy) rewrite rule for the initial polynomial of this
  // iteration step
  int* firstRuleLabel = (int*) omalloc( (currRing->N+1)*sizeof(int) );
  firstRuleLabel[0]   = 0;
  for( i=1;i<(currRing->N+1);i++ ) 
  {
    firstRuleLabel[i] = 0;
  }
  RewRules firstRule  = { NULL, firstRuleLabel, 0 };
  // reduce and initialize the list of Lpolys with the current ideal generator p
  p = (redGB, currQuotient, p);  
  Lpoly* gCurr      = (Lpoly*) omalloc( sizeof(Lpoly) );
  gCurr->next       = NULL;
  gCurr->sExp       = pGetShortExpVector(p);
  gCurr->p          = p;
  gCurr->rewRule    = &firstRule;
  gCurr->redundant  = false;
  
  // initializing the list of critical pairs for this iteration step 
  CpairDegBound* cpBounds = NULL;
  criticalPairInit( gCurr, redGB, *f5Rules, &cpBounds, numVariables, shift,
                    negBitmaskShifted, offsets
                  ); 
  if( cpBounds )
  {
    computeSpols( strat, cpBounds, redGB, gCurr, f5Rules, numVariables, shift, 
                  negBitmaskShifted, offsets
                );
  }
  // delete the reduction strategy strat since the current iteration step is
  // completed right now
  clearStrat( strat, redGB );
  omfree( firstRuleLabel );
  // next all new elements are added to redGB & redGB is being reduced
  Lpoly* temp;
  while( gCurr )
  {
    if( p_GetOrder( gCurr->p, currRing ) == pWTotaldegree( gCurr->p, currRing ) )
    {
      Print(" ALLES OK\n");
    }
    else 
    {
      Print("BEI POLY "); gCurr->p; Print(" stimmt etwas nicht!\n");
    }
    idInsertPoly( redGB, gCurr->p );
    temp = gCurr;
    gCurr = gCurr->next;
    omfree(temp);
  }
  idSkipZeroes( redGB );
#if F5EDEBUG
  Print("F5CITER-END\n");
#endif  
  return redGB;
}



void criticalPairInit ( Lpoly* gCurr, const ideal redGB, 
                        const F5Rules& f5Rules,  
                        CpairDegBound** cpBounds, int numVariables, int* shift, 
                        unsigned long* negBitmaskShifted, int* offsets
                      )
{
#if F5EDEBUG
  Print("CRITPAIRINIT-BEGINNING\n");
#endif
  int i, j;
  int* expVecNewElement = (int*) omalloc((currRing->N+1)*sizeof(int));
  int* expVecTemp       = (int*) omalloc((currRing->N+1)*sizeof(int));
  pGetExpV(gCurr->p, expVecNewElement); 
  // this must be changed for parallelizing the generation process of critical
  // pairs
  Cpair* cpTemp;
  Cpair* cp = (Cpair*) omalloc( sizeof(Cpair) );
  cpTemp    = cp;
  cpTemp->next      = NULL;
  cpTemp->mLabelExp = NULL;
  cpTemp->mLabel1   = NULL;
  cpTemp->smLabel1  = 0;
  cpTemp->mult1     = NULL;
  cpTemp->p1        = gCurr->p;
  cpTemp->rewRule1  = gCurr->rewRule;
  cpTemp->mLabel2   = NULL;
  cpTemp->smLabel2  = 0;
  cpTemp->mult2     = NULL;
  cpTemp->p2        = NULL;

  // we only need to alloc memory for the 1st label as for the initial 
  // critical pairs all 2nd generators have label NULL in F5e
  cpTemp->mLabel1   = (int*) omalloc((currRing->N+1)*sizeof(int));
  cpTemp->mult1     = (int*) omalloc((currRing->N+1)*sizeof(int));
  cpTemp->mult2     = (int*) omalloc((currRing->N+1)*sizeof(int));
  int temp;
  long critPairDeg = pDeg(gCurr->p, currRing);
  for(i=0; i<IDELEMS(redGB)-1; i++)
  {
    pGetExpV(redGB->m[i], expVecTemp); 
    Print("EXPVECTEMP[0]: %d\n",expVecTemp[0]);
    // computation of the lcm and the corresponding multipliers for the critical
    // pair generated by the new element and elements of the previous iteration
    // steps, i.e. elements already in redGB
    cpTemp->mLabel1[0]  = cpTemp->mult1[0]  = 0; 
    cpTemp->mult2[0]    = 0; 
    for(j=1; j<=currRing->N; j++)
    {
      temp  = expVecNewElement[j] - expVecTemp[j];
      // note that the label of the first element in gCurr is 0
      // thus gCurr.label is no longer mentioned in the following
      // computations
      if(temp<0)
      {
        cpTemp->mult1[j]    =   -temp;  
        cpTemp->mult2[j]    =   0; 
        cpTemp->mLabel1[j]  =   - temp;
        critPairDeg         +=  (- temp); 
      }
      else
      {
        cpTemp->mult1[j]    =   0;  
        cpTemp->mult2[j]    =   temp;  
        cpTemp->mLabel1[j]  =   0;
      }
    }
    cpTemp->smLabel1 = ~getShortExpVecFromArray(cpTemp->mLabel1);
    
    // testing the F5 Criterion
    if(!criterion1(cpTemp->mLabel1, cpTemp->smLabel1, &f5Rules)) 
    {
      // completing the construction of the new critical pair and inserting it
      // to the list of critical pairs 
      cpTemp->p2        = redGB->m[i];
      // now we really need the memory for the exp label
      cpTemp->mLabelExp = (unsigned long*) omalloc0(NUMVARS*
                                sizeof(unsigned long));
      Print("CRITPAIR EXPTEMP 0: %ld\n",cpTemp->mLabelExp[0]);
      getExpFromIntArray( cpTemp->mLabel1, cpTemp->mLabelExp, 
                          numVariables, shift, negBitmaskShifted, offsets );
      Print("CRITPAIR EXPTEMP 0: %ld\n",cpTemp->mLabelExp[0]);
      insertCritPair(cpTemp, critPairDeg, cpBounds);
      Cpair* cp = (Cpair*) omalloc( sizeof(Cpair) );
      cpTemp            = cp;
      cpTemp->next      = NULL;
      cpTemp->mLabelExp = NULL;
      cpTemp->mLabel1   = NULL;
      cpTemp->smLabel1  = 0;
      cpTemp->mult1     = NULL;
      cpTemp->p1        = gCurr->p;
      cpTemp->rewRule1  = NULL;
      cpTemp->mLabel2   = NULL;
      cpTemp->smLabel2  = 0;
      cpTemp->mult2     = NULL;
      cpTemp->p2        = NULL;

      cpTemp->mLabel1   = (int*) omalloc((currRing->N+1)*sizeof(int));
      cpTemp->mult1     = (int*) omalloc((currRing->N+1)*sizeof(int));
      cpTemp->mult2     = (int*) omalloc((currRing->N+1)*sizeof(int));
    }
    critPairDeg = pDeg(gCurr->p, currRing);
  }
  // same critical pair processing for the last element in redGB
  // This is outside of the loop to keep memory low, since we know that after
  // this element no new memory for a critical pair must be allocated.
  pGetExpV(redGB->m[IDELEMS(redGB)-1], expVecTemp); 
  // computation of the lcm and the corresponding multipliers for the critical
  // pair generated by the new element and elements of the previous iteration
  // steps, i.e. elements already in redGB
  cpTemp->mLabel1[0]  = cpTemp->mult1[0]  = pGetComp(cpTemp->p1); 
  cpTemp->mult2[0]    = pGetComp(redGB->m[IDELEMS(redGB)-1]); 
  for(j=1; j<=currRing->N; j++)
  {
    temp  = expVecNewElement[j] - expVecTemp[j];
    // note that the label of the first element in gCurr is 0
    // thus gCurr.label is no longer mentioned in the following
    // computations
    if(temp<0)
    {
      cpTemp->mult1[j]    =   -temp;  
      cpTemp->mult2[j]    =   0; 
      cpTemp->mLabel1[j]  =   -temp;
      critPairDeg         +=  (- temp);
    }
    else
    {
      cpTemp->mult1[j]    =   0;  
      cpTemp->mult2[j]    =   temp;  
      cpTemp->mLabel1[j]  =   0;
    }
  }
  cpTemp->smLabel1 = ~getShortExpVecFromArray(cpTemp->mLabel1);
  // testing the F5 Criterion
  if(!criterion1(cpTemp->mLabel1, cpTemp->smLabel1, &f5Rules)) 
  {
    // completing the construction of the new critical pair and inserting it
    // to the list of critical pairs 
    cpTemp->p2        = redGB->m[IDELEMS(redGB)-1];
    // now we really need the memory for the exp label
    cpTemp->mLabelExp = (unsigned long*) omalloc0(NUMVARS*
                              sizeof(unsigned long));
    getExpFromIntArray( cpTemp->mLabel1, cpTemp->mLabelExp, 
                        numVariables, shift, negBitmaskShifted, offsets
                      );
    insertCritPair( cpTemp, critPairDeg, cpBounds );
  }
  omfree(expVecTemp);
  omfree(expVecNewElement);
#if F5EDEBUG
  Print("CRITPAIRINIT-BEGINNING\n");
#endif
}



void criticalPairPrev ( Lpoly* gCurr, const ideal redGB, 
                        const F5Rules& f5Rules, CpairDegBound** cpBounds, 
                        int numVariables, int* shift, unsigned long* negBitmaskShifted, 
                        int* offsets
                      )
{
#if F5EDEBUG
  Print("CRITPAIRPREV-BEGINNING\n");
#endif
  int i, j;
  int* expVecNewElement = (int*) omalloc((currRing->N+1)*sizeof(int));
  int* expVecTemp       = (int*) omalloc((currRing->N+1)*sizeof(int));
  pGetExpV(gCurr->p, expVecNewElement); 
  // this must be changed for parallelizing the generation process of critical
  // pairs
  Cpair* cpTemp;
  Cpair* cp         = (Cpair*) omalloc( sizeof(Cpair) );
  cpTemp            = cp;
  cpTemp->next      = NULL;
  cpTemp->mLabelExp = NULL;
  cpTemp->mLabel1   = NULL;
  cpTemp->smLabel1  = 0;
  cpTemp->mult1     = NULL;
  cpTemp->p1        = gCurr->p;
  cpTemp->rewRule1  = gCurr->rewRule;
  cpTemp->mLabel2   = NULL;
  cpTemp->smLabel2  = 0;
  cpTemp->mult2     = NULL;
  cpTemp->p2        = NULL;

  // we only need to alloc memory for the 1st label as for the initial 
  // critical pairs all 2nd generators have label NULL in F5e
  cpTemp->mLabel1   = (int*) omalloc((currRing->N+1)*sizeof(int));
  cpTemp->mult1     = (int*) omalloc((currRing->N+1)*sizeof(int));
  cpTemp->mult2     = (int*) omalloc((currRing->N+1)*sizeof(int));
  int temp;
  long critPairDeg = pDeg(gCurr->p, currRing);
  for(i=0; i<IDELEMS(redGB)-1; i++)
  {
    pGetExpV(redGB->m[i], expVecTemp); 
    // computation of the lcm and the corresponding multipliers for the critical
    // pair generated by the new element and elements of the previous iteration
    // steps, i.e. elements already in redGB
    cpTemp->mLabel1[0]  = cpTemp->mult1[0]  = pGetExp(cpTemp->p1, 0); 
    cpTemp->mult2[0]    = pGetExp(redGB->m[i], 0); 
    for(j=1; j<=currRing->N; j++)
    {
      temp  = expVecNewElement[j] - expVecTemp[j];
      if(temp<0)
      {
        cpTemp->mult1[j]    =   -temp;  
        cpTemp->mult2[j]    =   0; 
        cpTemp->mLabel1[j]  =   cpTemp->rewRule1->label[j] - temp;
        critPairDeg         +=  (cpTemp->rewRule1->label[j] - temp); 
      }
      else
      {
        cpTemp->mult1[j]    =   0;  
        cpTemp->mult2[j]    =   temp;  
        cpTemp->mLabel1[j]  =   cpTemp->rewRule1->label[j];
      }
    }
    cpTemp->smLabel1 = ~getShortExpVecFromArray(cpTemp->mLabel1);
    
    // testing the F5 Criterion
    if( !criterion1(cpTemp->mLabel1, cpTemp->smLabel1, &f5Rules) )
    {
      // completing the construction of the new critical pair and inserting it
      // to the list of critical pairs 
      cpTemp->p2        = redGB->m[i];
      // now we really need the memory for the exp label
      cpTemp->mLabelExp = (unsigned long*) omalloc0(NUMVARS*
                                sizeof(unsigned long));
      getExpFromIntArray( cpTemp->mLabel1, cpTemp->mLabelExp, 
                          numVariables, shift, negBitmaskShifted, offsets );
      insertCritPair(cpTemp, critPairDeg, cpBounds);
      Cpair* cp         = (Cpair*) omalloc( sizeof(Cpair) );
      cpTemp            = cp;
      cpTemp->next      = NULL;
      cpTemp->mLabelExp = NULL;
      cpTemp->mLabel1   = NULL;
      cpTemp->smLabel1  = 0;
      cpTemp->mult1     = NULL;
      cpTemp->p1        = gCurr->p;
      cpTemp->rewRule1  = gCurr->rewRule;
      cpTemp->mLabel2   = NULL;
      cpTemp->smLabel2  = 0;
      cpTemp->mult2     = NULL;
      cpTemp->p2        = NULL;

      cpTemp->mLabel1   = (int*) omalloc((currRing->N+1)*sizeof(int));
      cpTemp->mult1     = (int*) omalloc((currRing->N+1)*sizeof(int));
      cpTemp->mult2     = (int*) omalloc((currRing->N+1)*sizeof(int));
    }
    critPairDeg = pDeg(gCurr->p, currRing);
  }
  // same critical pair processing for the last element in redGB
  // This is outside of the loop to keep memory low, since we know that after
  // this element no new memory for a critical pair must be allocated.
  pGetExpV(redGB->m[IDELEMS(redGB)-1], expVecTemp); 
  // computation of the lcm and the corresponding multipliers for the critical
  // pair generated by the new element and elements of the previous iteration
  // steps, i.e. elements already in redGB
  cpTemp->mLabel1[0]  = cpTemp->mult1[0]  = pGetExp(cpTemp->p1, 0); 
  cpTemp->mult2[0]    = pGetExp(redGB->m[IDELEMS(redGB)-1], 0); 
  for(j=1; j<=currRing->N; j++)
  {
    temp  = expVecNewElement[j] - expVecTemp[j];
    if(temp<0)
    {
      cpTemp->mult1[j]    =   -temp;  
      cpTemp->mult2[j]    =   0; 
      cpTemp->mLabel1[j]  =   cpTemp->rewRule1->label[j] - temp;
      critPairDeg         +=  (cpTemp->rewRule1->label[j] - temp);
    }
    else
    {
      cpTemp->mult1[j]    =   0;  
      cpTemp->mult2[j]    =   temp;  
      cpTemp->mLabel1[j]  =   cpTemp->rewRule1->label[j];
    }
  }
  cpTemp->smLabel1 = ~getShortExpVecFromArray(cpTemp->mLabel1);
  
  // testing the F5 Criterion
  if( !criterion1(cpTemp->mLabel1, cpTemp->smLabel1, &f5Rules) ) 
  {
    // completing the construction of the new critical pair and inserting it
    // to the list of critical pairs 
    cpTemp->p2        = redGB->m[IDELEMS(redGB)-1];
    // now we really need the memory for the exp label
    cpTemp->mLabelExp = (unsigned long*) omalloc(NUMVARS*
                              sizeof(unsigned long));
    getExpFromIntArray( cpTemp->mLabel1, cpTemp->mLabelExp, 
                        numVariables, shift, negBitmaskShifted, offsets
                      );
    insertCritPair(cpTemp, critPairDeg, cpBounds);
  }
  omfree(expVecTemp);
  omfree(expVecNewElement);
#if F5EDEBUG
  Print("CRITPAIRPREV-END\n");
#endif
}



void criticalPairCurr ( Lpoly* gCurr, const F5Rules& f5Rules, 
                        CpairDegBound** cpBounds, int numVariables, 
                        int* shift, unsigned long* negBitmaskShifted, int* offsets
                      )
{
#if F5EDEBUG
  Print("CRITPAIRCURR-BEGINNING\n");
#endif
  int i, j;
  unsigned long* mLabelExp;
  int* expVecNewElement = (int*) omalloc((currRing->N+1)*sizeof(int));
  int* expVecTemp       = (int*) omalloc((currRing->N+1)*sizeof(int));
  pGetExpV(gCurr->p, expVecNewElement); 
  Lpoly* gCurrIter  = gCurr->next;
  // this must be changed for parallelizing the generation process of critical
  // pairs
  Cpair* cpTemp;
  Cpair* cp         = (Cpair*) omalloc( sizeof(Cpair) );
  cpTemp            = cp;
  cpTemp->next      = NULL;
  cpTemp->mLabelExp = NULL;
  cpTemp->mLabel1   = NULL;
  cpTemp->smLabel1  = 0;
  cpTemp->mult1     = NULL;
  cpTemp->p1        = gCurr->p;
  cpTemp->rewRule1  = gCurr->rewRule;
  cpTemp->mLabel2   = NULL;
  cpTemp->smLabel2  = 0;
  cpTemp->mult2     = NULL;
  cpTemp->p2        = gCurrIter->p;
  cpTemp->rewRule2  = gCurrIter->rewRule;

  // we need to alloc memory for the 1st & the 2nd label here
  // both elements are generated during the current iteration step
  cpTemp->mLabel1   = (int*) omalloc((currRing->N+1)*sizeof(int));
  cpTemp->mLabel2   = (int*) omalloc((currRing->N+1)*sizeof(int));
  cpTemp->mult1     = (int*) omalloc((currRing->N+1)*sizeof(int));
  cpTemp->mult2     = (int*) omalloc((currRing->N+1)*sizeof(int));
  // alloc memory for a temporary (non-integer/SINGULAR internal) exponent vector
  // for fast comparisons at the end which label is greater, those of the 1st or
  // those of the 2nd generator
  // Note: As we do not need the smaller exponent vector we do NOT store both in
  // the critical pair structure, but only the greater one. Thus the following
  // memory is freed before the end of criticalPairCurr()
  unsigned long* checkExp = (unsigned long*) omalloc0(NUMVARS*sizeof(unsigned long));
  int temp;
  long critPairDeg = pDeg(gCurr->p, currRing);
  while(gCurrIter->next)
  {
    pGetExpV(gCurrIter->p, expVecTemp); 
    // computation of the lcm and the corresponding multipliers for the critical
    // pair generated by the new element and elements of the previous iteration
    // steps, i.e. elements already in redGB
    cpTemp->mLabel1[0]  = cpTemp->mult1[0]  = pGetExp(cpTemp->p1, 0); 
    cpTemp->mLabel2[0]  = cpTemp->mult2[0]  = pGetExp(cpTemp->p2, 0); 
    for(j=1; j<currRing->N+1; j++)
    {
      temp  = expVecNewElement[j] - expVecTemp[j];
      if(temp<0)
      {
        cpTemp->mult1[j]    =   -temp;  
        cpTemp->mult2[j]    =   0; 
        cpTemp->mLabel1[j]  =   cpTemp->rewRule1->label[j] - temp;
        cpTemp->mLabel2[j]  =   cpTemp->rewRule2->label[j];
        critPairDeg         +=  cpTemp->rewRule2->label[j]; 
      }
      else
      {
        cpTemp->mult1[j]    =   0;  
        cpTemp->mult2[j]    =   temp;  
        cpTemp->mLabel1[j]  =   cpTemp->rewRule1->label[j];
        cpTemp->mLabel2[j]  =   cpTemp->rewRule2->label[j] + temp;
      }
    }
    cpTemp->smLabel1 = ~getShortExpVecFromArray(cpTemp->mLabel1);
    cpTemp->smLabel2 = ~getShortExpVecFromArray(cpTemp->mLabel2);
    
    // testing the F5 Criterion
    if( !criterion1(cpTemp->mLabel1, cpTemp->smLabel1, &f5Rules) 
        && !criterion1(cpTemp->mLabel2, cpTemp->smLabel2, &f5Rules) 
        && !criterion2(cpTemp->mLabel2, cpTemp->smLabel2, cpTemp->rewRule2)
      ) 
    {
      // completing the construction of the new critical pair and inserting it
      // to the list of critical pairs 
      // now we really need the memory for the exp label
      cpTemp->mLabelExp = (unsigned long*) omalloc0(NUMVARS*
                                sizeof(unsigned long));
      getExpFromIntArray( cpTemp->mLabel1, cpTemp->mLabelExp, 
                          numVariables, shift, negBitmaskShifted, offsets
                        );
      getExpFromIntArray( cpTemp->mLabel2, checkExp, numVariables,
                          shift, negBitmaskShifted, offsets
                        );
      // compare which label is greater and possibly switch the 1st and 2nd 
      // generator in cpTemp
      // exchange generator 1 and 2 in cpTemp
      if( expCmp(cpTemp->mLabelExp, checkExp) == 1 )
      {
        poly pTempHolder                = cpTemp->p1;
        int* mLabelTempHolder           = cpTemp->mLabel1;
        int* multTempHolder             = cpTemp->mult1;
        unsigned long smLabelTempHolder = cpTemp->smLabel1;  
        RewRules* rewRuleTempHolder     = cpTemp->rewRule1;

        cpTemp->p1                      = cpTemp->p2;
        cpTemp->p2                      = pTempHolder;
        cpTemp->mLabel1                 = cpTemp->mLabel2;
        cpTemp->mLabel2                 = mLabelTempHolder;
        cpTemp->mult1                   = cpTemp->mult2;
        cpTemp->mult2                   = multTempHolder;
        cpTemp->smLabel1                = cpTemp->smLabel2;
        cpTemp->smLabel2                = smLabelTempHolder;
        cpTemp->rewRule1                = cpTemp->rewRule2;
        cpTemp->rewRule2                = rewRuleTempHolder;
      }
      
      insertCritPair(cpTemp, critPairDeg, cpBounds);
      
      Cpair* cp         = (Cpair*) omalloc( sizeof(Cpair) );
      cpTemp            = cp;
      cpTemp->next      = NULL;
      cpTemp->mLabelExp = NULL;
      cpTemp->mLabel1   = NULL;
      cpTemp->smLabel1  = 0;
      cpTemp->mult1     = NULL;
      cpTemp->p1        = gCurr->p;
      cpTemp->rewRule1  = gCurr->rewRule;
      cpTemp->mLabel2   = NULL;
      cpTemp->smLabel2  = 0;
      cpTemp->mult2     = NULL;
      cpTemp->p2        = gCurrIter->next->p;
      cpTemp->rewRule2  = gCurrIter->next->rewRule;
      cpTemp->mLabel1   = (int*) omalloc((currRing->N+1)*sizeof(int));
      cpTemp->mult1     = (int*) omalloc((currRing->N+1)*sizeof(int));
      cpTemp->mult2     = (int*) omalloc((currRing->N+1)*sizeof(int));
    }
    critPairDeg = pDeg(gCurr->p, currRing);
    gCurrIter = gCurrIter->next;
  }
  // same critical pair processing for the last element in gCurr
  // This is outside of the loop to keep memory low, since we know that after
  // this element no new memory for a critical pair must be allocated.
  pGetExpV(gCurrIter->p, expVecTemp); 
  // computation of the lcm and the corresponding multipliers for the critical
  // pair generated by the new element and elements of the previous iteration
  // steps, i.e. elements already in redGB
  cpTemp->mLabel1[0]  = cpTemp->mult1[0]  = pGetExp(cpTemp->p1, 0); 
  cpTemp->mLabel2[0]  = cpTemp->mult2[0]  = pGetExp(gCurrIter->p, 0); 
  for(j=1; j<=currRing->N; j++)
  {
    temp  = expVecNewElement[j] - expVecTemp[j];
    if(temp<0)
    {
      cpTemp->mult1[j]    =   -temp;  
      cpTemp->mult2[j]    =   0; 
      cpTemp->mLabel1[j]  =   cpTemp->rewRule1->label[j] - temp;
      cpTemp->mLabel2[j]  =   cpTemp->rewRule2->label[j];
      critPairDeg         +=  cpTemp->rewRule2->label[j];
    }
    else
    {
      cpTemp->mult1[j]    =   0;  
      cpTemp->mult2[j]    =   temp;  
      cpTemp->mLabel1[j]  =   cpTemp->rewRule1->label[j];
      cpTemp->mLabel2[j]  =   cpTemp->rewRule2->label[j] + temp;
    }
  }
  cpTemp->smLabel1 = ~getShortExpVecFromArray(cpTemp->mLabel1);
  cpTemp->smLabel2 = ~getShortExpVecFromArray(cpTemp->mLabel2);
  
  // testing the F5 Criterion
  if( !criterion1(cpTemp->mLabel1, cpTemp->smLabel1, &f5Rules) 
      && !criterion1(cpTemp->mLabel2, cpTemp->smLabel2, &f5Rules) 
      && !criterion2(cpTemp->mLabel2, cpTemp->smLabel2, cpTemp->rewRule2)
    ) 
  {
    // completing the construction of the new critical pair and inserting it
    // to the list of critical pairs 
    // now we really need the memory for the exp label
    cpTemp->mLabelExp = (unsigned long*) omalloc0(NUMVARS*
                              sizeof(unsigned long));
    getExpFromIntArray( cpTemp->mLabel1, cpTemp->mLabelExp, 
                        numVariables, shift, negBitmaskShifted, offsets
                      );
    getExpFromIntArray( cpTemp->mLabel2, checkExp, numVariables,
                        shift, negBitmaskShifted, offsets
                      );
    // compare which label is greater and possibly switch the 1st and 2nd 
    // generator in cpTemp
    // exchange generator 1 and 2 in cpTemp
    if( expCmp(cpTemp->mLabelExp, checkExp) == 1 )
    {
      poly pTempHolder                = cpTemp->p1;
      int* mLabelTempHolder           = cpTemp->mLabel1;
      int* multTempHolder             = cpTemp->mult1;
      unsigned long smLabelTempHolder = cpTemp->smLabel1;  
      RewRules* rewRuleTempHolder     = cpTemp->rewRule1;

      cpTemp->p1                      = cpTemp->p2;
      cpTemp->p2                      = pTempHolder;
      cpTemp->mLabel1                 = cpTemp->mLabel2;
      cpTemp->mLabel2                 = mLabelTempHolder;
      cpTemp->mult1                   = cpTemp->mult2;
      cpTemp->mult2                   = multTempHolder;
      cpTemp->smLabel1                = cpTemp->smLabel2;
      cpTemp->smLabel2                = smLabelTempHolder;
      cpTemp->rewRule1                = cpTemp->rewRule2;
      cpTemp->rewRule2                = rewRuleTempHolder;
    }
    
    insertCritPair(cpTemp, critPairDeg, cpBounds);
  } 

  omfree(checkExp);
  omfree(expVecTemp);
  omfree(expVecNewElement);
#if F5EDEBUG
  Print("CRITPAIRCURR-END\n");
#endif
}



void insertCritPair( Cpair* cp, long deg, CpairDegBound** bound )
{
#if F5EDEBUG
  Print("INSERTCRITPAIR-BEGINNING deg bound %p\n",*bound);
  Print("ADDRESS NEW CRITPAIR: %p -- degree %ld\n",cp, deg);
  pWrite(cp->p1);
  pWrite(cp->p2);
  if( (*bound) ) 
  {
    Print("ADDRESS BOUND CRITPAIR: %p -- deg %ld -- length %d\n",(*bound)->cp,(*bound)->deg, (*bound)->length);
    pWrite( (*bound)->cp->p1 );
  }
#endif
  if( !(*bound) ) // empty list?
  {
    CpairDegBound* boundNew = (CpairDegBound*) omalloc(sizeof(CpairDegBound));
    boundNew->next          = NULL;
    boundNew->deg           = deg;
    boundNew->cp            = cp;
    boundNew->length        = 1;
    *bound                  = boundNew;
  }
  else
  {
    if((*bound)->deg < deg) 
    {
      CpairDegBound** temp = bound;
      while((*temp)->next && ((*temp)->next->deg < deg))
      {
        *temp = (*temp)->next;
      }
      if( (*temp)->next && (*temp)->next->deg == deg )
      {
        cp->next          = (*temp)->next->cp;
        (*temp)->next->cp = cp;
        (*temp)->next->length++;
      }
      else
      {
        CpairDegBound* boundNew = (CpairDegBound*) omalloc(sizeof(CpairDegBound));
        boundNew->next          = (*temp)->next;
        boundNew->deg           = deg;
        boundNew->cp            = cp;
        boundNew->length        = 1;
        (*temp)->next           = boundNew;
        Print("HERE %p\n",*temp);
      }
    }
    else
    {
      if((*bound)->deg == deg) 
      {
        cp->next     = (*bound)->cp;
        (*bound)->cp = cp;
        (*bound)->length++;
      }
      else
        {
        CpairDegBound* boundNew = (CpairDegBound*) omalloc(sizeof(CpairDegBound));
        boundNew->next          = *bound;
        boundNew->deg           = deg;
        boundNew->cp            = cp;
        boundNew->length        = 1;
        *bound                  = boundNew;
      }
    }
  }
#if F5EDEBUG
  pWrite( (*bound)->cp->p2 );
  Print("INSERTCRITPAIR-END deg bound %p\n",*bound);
#endif
}



inline BOOLEAN criterion1 ( const int* mLabel, const unsigned long smLabel, 
                            const F5Rules* f5Rules
                          )
{
  int i = 0;
  int j = currRing->N;
#if F5EDEBUG
    Print("Tested Element: ");
    while( j )
    {
      Print("%d ",mLabel[(currRing->N)-j]);
      j--;
    }
    j = currRing->N;
    Print("\n %ld\n",smLabel);
    
#endif
  nextElement:
  for( ; i < f5Rules->size; i++)
  {
#if F5EDEBUG
    Print("F5 Rule: ");
    while( j )
    {
      Print("%d ",f5Rules->label[i][(currRing->N)-j]);
      j--;
    }
    j = currRing->N;
    Print("\n %ld\n",f5Rules->slabel[i]);
#endif
    if(!(smLabel & f5Rules->slabel[i]))
    {
      while(j)
      {
        if(mLabel[j] < f5Rules->label[i][j])
        {
          j = currRing->N;
          i++;
          goto nextElement;
        }
        j--;
      }
#if F5EDEBUG
        Print("CRITERION1-END-DETECTED \n");
#endif
      return true;
    }
      Print("HERE\n");

  }
#if F5EDEBUG
  Print("CRITERION1-END \n");
#endif
  return false;
}



inline BOOLEAN criterion2 ( const int* mLabel, const unsigned long smLabel, 
                            RewRules* rewRules
                          )
{
#if F5EDEBUG
    Print("CRITERION2-BEGINNING %p\n", rewRules);
#endif
  int j = currRing->N;
  if( rewRules->next )
  {
    RewRules* temp = rewRules->next;
    Print("%p\n", temp);
#if F5EDEBUG
    Print("Tested Element: ");
    while( j )
    {
      Print("%d ",mLabel[(currRing->N)-j]);
      j--;
    }
    j = currRing->N;
    Print("\n");
#endif
    nextElement:
    while( NULL != temp )
    {
#if F5EDEBUG
    Print("Rew Rule: %p\n",temp->label);
    while( j )
    {
      Print("%d ",temp->label[(currRing->N)-j]);
      j--;
    }
    j = currRing->N;
    Print("\n");
#endif
      if(!(smLabel & temp->slabel))
      {
        while(j)
        {
          if(mLabel[j] < temp->label[j])
          {
            j     = currRing->N;
            temp  = temp->next;
            goto nextElement;
          }
          j--;
        }
#if F5EDEBUG
        Print("CRITERION2-END \n");
#endif
          return true;
      }
      Print("HERE\n");
      temp  = temp->next;
    }
  }
#if F5EDEBUG
  Print("CRITERION2-END \n");
#endif
  return false;
}



void computeSpols ( kStrategy strat, CpairDegBound* cp, ideal redGB, Lpoly* gCurr, 
                    const F5Rules* f5Rules, int numVariables, 
                    int* shift, unsigned long* negBitmaskShifted, int* offsets
                  )
{
#if F5EDEBUG
  Print("COMPUTESPOLS-BEGINNING\n");
#endif
  Cpair* temp             = NULL;
  Cpair* tempDel          = NULL;
  RewRules* rewRulesLast  = NULL; 
  Lpoly* higherLabel      = NULL;
  Lpoly*    gCurrLast     = gCurr;
  BOOLEAN redundant       = false;
  // start the rewriter rules list with a NULL element for the recent,
  // i.e. initial element in \c gCurr
  rewRulesLast        = gCurr->rewRule;
  // this will go on for the complete current iteration step!
  // => after computeSpols() terminates this iteration step is done!
  int* multTemp = (int*) omalloc( (currRing->N+1)*sizeof(int) );
  poly sp;
  // compute and reduce new elements as long as we have critical pairs 
  while( cp )
  {
#if F5EDEBUG
    Print("START OF NEW DEG ROUND: CP %ld -- %p\n",cp->deg,cp);
#endif
    temp  = sort(cp->cp, cp->length); 
    CpairDegBound* cpDel  = cp;
    cp                    = cp->next;
    omfree( cpDel );
    // The first element cannot be detected by Criterion 2 as there are no new
    // rules added to \c rewRules until now.
    Print("Last Element in Rewrules? %p points to %p\n", rewRulesLast,rewRulesLast->next);
    RewRules* newRule   = (RewRules*) omalloc( sizeof(RewRules) );
    newRule->next       = NULL;
    newRule->label      = temp->mLabel1;
    newRule->slabel     = ~temp->smLabel1;
    rewRulesLast->next  = newRule;
    rewRulesLast        = newRule; 
#if F5EDEBUG
    Print("Last Element in Rewrules? %p points to %p\n", rewRulesLast,rewRulesLast->next);
#endif

    // from this point on, rewRulesLast != NULL, thus we do not need to test this
    // again in the following iteration over the list of critical pairs
    
#if F5EDEBUG
    Print("CRITICAL PAIR BEFORE S-SPOLY COMPUTATION:\n");
    Print("GEN1: ");
    pWrite(temp->p1);
    Print("GEN2: ");
    pWrite(temp->p2);
#endif

    // compute s-polynomial and reduce it w.r.t. redGB
    sp  = reduceByRedGBCritPair ( temp, strat, numVariables, shift, 
                                  negBitmaskShifted, offsets 
                                );
    pNorm( sp ); 
#if F5EDEBUG
    Print("BEFORE:  ");
    pWrite( sp );
    pTest(sp);
#endif
    sp = currReduction( sp, &temp, rewRulesLast, gCurr, f5Rules, multTemp, 
                        numVariables, shift, negBitmaskShifted, offsets, 
                        &redundant
                      );
#if F5EDEBUG
    Print("AFTER:  ");
    pWrite(pHead(sp));
    pTest(sp);
#endif
    tempDel  = temp;
    temp     = temp->next;
    omfree(tempDel);
    
    // otherwise sp is reduced to zero and we do not need to add it to gCurr
    // Note that even in this case the corresponding rule is already added to
    // rewRules list!
    if( sp )
    {
      pNorm( sp ); 
      Print("ORDER %ld -- %ld\n",p_GetOrder(sp,currRing), sp->exp[currRing->pOrdIndex]);
      // add sp together with rewRulesLast to gCurr!!!
      Lpoly* newElement     = (Lpoly*) omalloc( sizeof(Lpoly) );
      newElement->next      = NULL;
      newElement->p         = sp; 
      newElement->sExp      = pGetShortExpVector(sp); 
      newElement->rewRule   = rewRulesLast; 
      newElement->redundant = redundant;
      // update pointer to last element in gCurr list
      gCurrLast->next       = newElement;
      gCurrLast             = newElement;
      Print("NEW ELEMENT ADDED TO GCURR!\n");
      pWrite( newElement->p );
      Print("SHORT EXP VECTOR: %ld\n", newElement->sExp);
      criticalPairPrev( gCurrLast, redGB, *f5Rules, &cp, numVariables, 
                        shift, negBitmaskShifted, offsets 
                      );
        criticalPairCurr( gCurrLast, *f5Rules, &cp, numVariables, 
                          shift, negBitmaskShifted, offsets 
                        );
    }
    //------------------------------------------------
    // TODO: CURRENT ITERATION REDUCTION
    //------------------------------------------------
    Print("THIS STEP %p\n",temp);
    while( temp!=NULL )
    {
      if(!criterion2(temp->mLabel1, temp->smLabel1, temp->rewRule1))
      {
        Print("Last Element in Rewrules? %p points to %p\n", rewRulesLast,rewRulesLast->next);
        RewRules* newRule   = (RewRules*) omalloc( sizeof(RewRules) );
        newRule->next       = NULL;
        newRule->label      = temp->mLabel1;
        newRule->slabel     = ~temp->smLabel1;
        rewRulesLast->next  = newRule;
        rewRulesLast        = newRule; 
      }
      
#if F5EDEBUG
      Print("CRITICAL PAIR BEFORE S-SPOLY COMPUTATION:\n");
      Print("GEN1: ");
      pWrite(temp->p1);
      Print("GEN2: ");
      pWrite(temp->p2);
#endif

      // compute s-polynomial and reduce it w.r.t. redGB
      sp  = reduceByRedGBCritPair ( temp, strat, numVariables, shift,   
                                    negBitmaskShifted, offsets 
                                  );
      pNorm( sp ); 
      
      Print("BEFORE:  ");
      pWrite(sp);
      pTest(sp);
      sp = currReduction( sp, &temp, rewRulesLast, gCurr, f5Rules, multTemp, 
                          numVariables, shift, negBitmaskShifted, offsets, 
                          &redundant
                        );
      Print("AFTER:  ");
      pTest(sp);


      tempDel  = temp;
      temp     = temp->next;
      omfree(tempDel);
      
      // otherwise sp is reduced to zero and we do not need to add it to gCurr
      // Note that even in this case the corresponding rule is already added to
      // rewRules list!
      if( sp )
      {
        Print("ORDER %ld -- %ld\n",p_GetOrder(sp,currRing), sp->exp[currRing->pOrdIndex]);
        pNorm( sp ); 
        // add sp together with rewRulesLast to gCurr!!!
        Lpoly* newElement     = (Lpoly*) omalloc( sizeof(Lpoly) );
        newElement->next      = NULL;
        newElement->p         = sp; 
        newElement->sExp      = pGetShortExpVector(sp); 
        newElement->rewRule   = rewRulesLast; 
        newElement->redundant = redundant;
        // update pointer to last element in gCurr list
        gCurrLast->next       = newElement;
        gCurrLast             = newElement;
        Print("NEW ELEMENT ADDED TO GCURR!\n");
        pWrite( newElement->p );
        Print("SHORT EXP VECTOR: %ld\n", newElement->sExp);
        criticalPairPrev( gCurrLast, redGB, *f5Rules, &cp, numVariables, 
                          shift, negBitmaskShifted, offsets 
                        );
        criticalPairCurr( gCurrLast, *f5Rules, &cp, numVariables, 
                          shift, negBitmaskShifted, offsets 
                        );
        }
    }
  }
  omfree( multTemp );

#if F5EDEBUG
  Print("COMPUTESPOLS-END\n");
#endif
}



inline void kBucketCopyToPoly(kBucket_pt bucket, poly *p, int *length)
{
  int i = kBucketCanonicalize(bucket);
  if (i > 0)
  {
  #ifdef USE_COEF_BUCKETS
    MULTIPLY_BUCKET(bucket,i);
    //bucket->coef[i]=NULL;
  #endif
    *p = pCopy(bucket->buckets[i]);
    *length = bucket->buckets_length[i];
  }
  else
  {
    *p = NULL;
    *length = 0;
  }
}



poly currReduction  ( poly sp, Cpair** cp, RewRules* rewRulesLast, Lpoly* gCurr, 
                      const F5Rules* f5Rules, int* multTemp, int numVariables, 
                      int* shift, unsigned long* negBitmaskShifted, int* offsets, 
                      BOOLEAN* redundant
                    )

{
#if F5EDEBUG
    Print("CURRREDUCTION-BEGINNING \n");
#endif
  BOOLEAN isMult  = false;
  int i;
  unsigned long multShortExp;
  static int tempLength           = 0;
  unsigned short int canonicalize = 0; 
  Lpoly* temp                     = gCurr;
  kBucket* bucket                 = kBucketCreate();
  unsigned long bucketExp;
  kBucketInit( bucket, sp, pLength(sp) );
  
  //----------------------------------------
  // reduction of the leading monomial of sp
  //----------------------------------------
  // Note that we need to make this top reduction explicit to be able to decide
  // if the returned polynomial is redundant or not!
  // search for reducers in the list gCurr
  *redundant  = false;
  while ( temp )
  {
    startagainTop:
    bucketExp = ~( pGetShortExpVector(kBucketGetLm(bucket)) );
    if( isDivisibleGetMult( temp->p, temp->sExp, kBucketGetLm( bucket ), 
                            bucketExp, &multTemp, &isMult
                          ) 
      )
    {
      *redundant = true;
      // if isMult => lm(sp) > lm(temp->p) => we need to multiply temp->p by 
      // multTemp and check this multiple by both criteria
      Print("ISMULT %d\n",isMult);
      if( isMult )
      {
        // compute the multiple of the rule of temp & multTemp
        for( i=1;i<(currRing->N)+1; i++ )
        {
          multTemp[i] +=  temp->rewRule->label[i];
        }
        multShortExp  = getShortExpVecFromArray( multTemp );
         
        // test the multiplied label by both criteria 
        if( !criterion1( multTemp, multShortExp, f5Rules ) && 
            !criterion2( multTemp, multShortExp, temp->rewRule )
          )
        { 
          static unsigned long* multTempExp = (unsigned long*) 
                          omalloc0( NUMVARS*sizeof(unsigned long) );
          getExpFromIntArray( multTemp, multTempExp, numVariables,
                              shift, negBitmaskShifted, offsets
                            );   
          // if a higher label reduction takes place we need to create
          // a new Lpoly with the higher label and store it in a different 
          // linked list for later reductions

          if( expCmp( multTempExp, (*cp)->mLabelExp ) == 1 )
          {            
#if F5EDEBUG
    Print("HIGHER LABEL REDUCTION \n");
#endif
            poly newPoly  = pInit();
            poly oldPoly  = pInit();
            int length;
            pWrite(kBucketGetLm(bucket));
            kBucketCopyToPoly( bucket, &newPoly, &length );
            Print("NEW POLYNOMIAL FROM BUCKET: ");
            pWrite(newPoly);
            oldPoly = pCopy( newPoly );
            // add new rule to RewRules
            RewRules* newRule = (RewRules*) omalloc( sizeof(RewRules) );
            newRule->label    = (int*) omalloc( (currRing->N+1)*
                                                sizeof(int) 
                                              );
            newRule->next       = NULL;
            newRule->label      = multTemp;
            newRule->slabel     = multShortExp;
            rewRulesLast->next  = newRule;
            rewRulesLast        = newRule; 
            Print("HERE?\n");
            
            // generate a new critical for further reduction steps
            // note: this will be a "trivial" critical pair, as the 2nd
            // generator will be 1
            Cpair* newPair      = (Cpair*) omalloc( sizeof(Cpair) );
            newPair->mLabelExp  = (unsigned long*) omalloc0( NUMVARS*
                                    sizeof(unsigned long) );
            newPair->mLabel1  = (int*) omalloc( (currRing->N+1)*sizeof(int) );
            newPair->mult1    = (int*) omalloc( (currRing->N+1)*sizeof(int) );
            newPair->mult2    = (int*) omalloc( (currRing->N+1)*sizeof(int) );
            // multiplier for new polynomial
            static poly multiplier = pOne();
            int j = 0;
            for( j=0;j<NUMVARS;j++ )
            {
              newPair->mLabelExp[j] = multTempExp[j];
              multiplier->exp[j]    = multTempExp[j];
            }
            for( j=0;j<currRing->N+1;j++ )
            {
              newPair->mLabel1[j] = multTemp[j];
              newPair->mult1[j]   = 0;
              newPair->mult2[j]   = 0;
            }
            newPair->smLabel1   = multShortExp;
            newPair->rewRule1   = temp->rewRule;
            newPair->mLabel2    = NULL;
            newPair->smLabel2   = 0;
            newPair->mult2      = NULL;
            newPair->p2         = pOne();
            // this is ok since p2 is never tested by the 2nd criterion
            newPair->rewRule2   = NULL;
            
            // initialize the new bucket
            kBucketInit( bucket, newPoly, 0 );
            //multiplier->exp       = multTempExp;
            //getExpFromIntArray( multTemp, multiplier->exp, numVariables, shift, 
            //                    negBitmaskShifted, offsets
            //                  );

            // throw away the leading monomials of reducer and bucket
            p_SetCoeff( multiplier, pGetCoeff(kBucketGetLm(bucket)), currRing );
            tempLength = pLength( temp->p->next );
            kBucketExtractLm(bucket);
            kBucket_Minus_m_Mult_p( bucket, multiplier, temp->p->next, 
                                    &tempLength 
                                  ); 
            newPair->p1 =  kBucketExtractLm( bucket );
            newPair->p1 =  p_Merge_q ( newPair->p1, kBucketExtractLm(bucket), 
                                        currRing 
                                      );
            // insertion sort of newPair to the list of critical pairs waiting
            // to be reduced, sorted by increasing labels
            Cpair* temp = (*cp)->next;
                Print("ADDRESS: %p\n",temp);
            if( temp )
            { 
              if( (expCmp(newPair->mLabelExp, temp->mLabelExp) == -1) )
              {
                (*cp)->next = newPair;
                newPair->next = temp;
              }
              else
              {
                while ( temp->next && (expCmp(newPair->mLabelExp, temp->next->mLabelExp) == 1) )
                {
                  temp  = temp->next;
                }
                newPair->next = temp->next;
                temp->next    = newPair;
              }
            }
            else
            {
              newPair->next = NULL;
              (*cp)->next   = newPair;
            }  
            // get back on track for the old poly which has to be checked for 
            // reductionbsy by the following element in gCurr
            pWrite(newPoly);
            Print("Poly copying: ");
            pWrite(newPoly);
            pWrite(oldPoly);
            kBucketInit( bucket, oldPoly, 0 );
            pDelete( &oldPoly );
            isMult      = false;
            *redundant  = true;
            temp    = temp->next;
            goto startagainTop;
          }
          // else we can go on and reduce sp
          static poly multiplier = pOne();
          getExpFromIntArray( multTemp, multiplier->exp, numVariables, shift, 
                              negBitmaskShifted, offsets
                            );
          // throw away the leading monomials of reducer and bucket
          pSetm( multiplier );
          p_SetCoeff( multiplier, pGetCoeff(kBucketGetLm(bucket)), currRing );
          tempLength = pLength( temp->p->next );
          kBucketExtractLm(bucket);
          kBucket_Minus_m_Mult_p( bucket, multiplier, temp->p->next, 
                                  &tempLength 
                                ); 
          if( canonicalize++ % 40 )
          {
            kBucketCanonicalize( bucket );
            canonicalize = 0;
          }
          isMult      = false;
          *redundant  = false;
          temp        = gCurr;
          goto startagainTop;
        }
      }
      // isMult = 0 => multTemp = 1 => we do not need to test temp->p by any
      // criterion again => go on with reduction steps
      else
      {
        pWrite(kBucketGetLm(bucket));
        number coeff  = pGetCoeff(kBucketGetLm(bucket));
        poly tempNeg  = pInit();
        // throw away the leading monomials of reducer and bucket
        tempNeg       = pCopy( temp->p );
        tempLength    = pLength( tempNeg->next );
        pWrite(kBucketGetLm(bucket));
        p_Mult_nn( tempNeg, coeff, currRing );
        kBucketExtractLm(bucket);
        kBucket_Add_q( bucket, pNeg(tempNeg->next), &tempLength ); 
        if( canonicalize++ % 40 )
        {
          kBucketCanonicalize( bucket );
          canonicalize = 0;
        }

        *redundant  = false;
        temp        = gCurr;
        goto startagainTop;
      } 
    }
    temp  = temp->next;
  }
  // we know that sp = 0 at this point!
  pWrite(kBucketGetLm(bucket));
  sp  = kBucketExtractLm( bucket );
#if F5EDEBUG
  Print("END OF TOP REDUCTION:  ");
#endif
  pTest( sp );
  pWrite( sp ); 
  //-------------------------------------------
  // now the reduction of the tail of sp starts
  //-------------------------------------------
  // reduce sp completely (Faugere does only top reductions!)
  while ( kBucketGetLm( bucket ) )
  {
    // search for reducers in the list gCurr
    temp = gCurr;
    while ( temp )
    {
      startagainTail:
      bucketExp = ~( pGetShortExpVector(kBucketGetLm(bucket)) );
      if( isDivisibleGetMult( kBucketGetLm( bucket ), bucketExp, temp->p, 
                              temp->sExp, &multTemp, &isMult
                            ) 
        )
      {
        // if isMult => lm(sp) > lm(temp->p) => we need to multiply temp->p by 
        // multTemp and check this multiple by both criteria
        if( isMult )
        {
          // compute the multiple of the rule of temp & multTemp
          for( i=1; i<(currRing->N)+1; i++ )
          {
            multTemp[i] +=  temp->rewRule->label[i];
          }
          
          multShortExp  = getShortExpVecFromArray( multTemp );
          
          // test the multiplied label by both criteria 
          if( !criterion1( multTemp, multShortExp, f5Rules ) && 
              !criterion2( multTemp, multShortExp, temp->rewRule )
            )
          {  
            static unsigned long* multTempExp = (unsigned long*) 
                            omalloc0( NUMVARS*sizeof(unsigned long) );
            getExpFromIntArray( multTemp, multTempExp, numVariables,
                                shift, negBitmaskShifted, offsets
                              );   
            // if a higher label reduction should be done we do NOT reduce at all
            // we want to be fast in the tail reduction part
            if( expCmp( multTempExp, (*cp)->mLabelExp ) == 1 )
            {            
              isMult      = false;
              *redundant  = true;
              temp        = temp->next;
              goto startagainTail;
            }
            poly multiplier = pOne();
            getExpFromIntArray( multTemp, multiplier->exp, numVariables, shift, 
                                negBitmaskShifted, offsets
                              );
            // throw away the leading monomials of reducer and bucket
            pSetm( multiplier );
            p_SetCoeff( multiplier, pGetCoeff(kBucketGetLm(bucket)), currRing );
            tempLength = pLength( temp->p->next );

            kBucketExtractLm(bucket);
            kBucket_Minus_m_Mult_p( bucket, multiplier, temp->p->next, 
                                    &tempLength 
                                  ); 
            if( canonicalize++ % 40 )
            {
              kBucketCanonicalize( bucket );
              canonicalize = 0;
            }
            isMult  = false;
            temp    = gCurr;
            goto startagainTail;
          }
        }
        // isMult = 0 => multTemp = 1 => we do not need to test temp->p by any
        // criterion again => go on with reduction steps
        else
        {
          number coeff  = pGetCoeff(kBucketGetLm(bucket));
          poly tempNeg  = pInit();
          // throw away the leading monomials of reducer and bucket
          tempNeg       = pCopy( temp->p );
          tempLength    = pLength( tempNeg->next );
          kBucketExtractLm(bucket);
          kBucket_Add_q( bucket, pNeg(tempNeg->next), &tempLength ); 
          if( canonicalize++ % 40 )
          {
            kBucketCanonicalize( bucket );
            canonicalize = 0;
          }
          temp  = gCurr;
          goto startagainTail;
        } 
      }
      temp  = temp->next;
    }
    // here we know that 
    sp =  p_Merge_q( sp, kBucketExtractLm(bucket), currRing );
  }
#if F5EDEBUG
    Print("CURRREDUCTION-END \n");
#endif
  kBucketDeleteAndDestroy( &bucket );
  return sp;
}



Cpair* sort(Cpair* cp, unsigned int length)
{
  // using merge sort 
  // Link: http://en.wikipedia.org/wiki/Merge_sort
  if(length == 1) 
  {
    return cp; 
  }
  else
  {
    int length1 = length / 2;
    int length2 = length - length1;
    // pointer to the start of the 2nd linked list for the next
    // iteration step of the merge sort
    Cpair* temp = cp;
    for(length=1; length < length1; length++)
    {
      temp = temp->next;
    }
    Cpair* cp2  = temp->next;
    temp->next  = NULL; 
    cp  = sort(cp, length1);
    cp2 = sort(cp2, length2);
    return merge(cp, cp2);
  }
}



Cpair* merge(Cpair* cp, Cpair* cp2)
{
  // initialize new, sorted list of critical pairs
  Cpair* cpNew = NULL;
  if( expCmp(cp->mLabelExp, cp2->mLabelExp) == -1 )
  {
    cpNew = cp;
    cp    = cp->next;
  }
  else
  { 
    cpNew = cp2;
    cp2   = cp2->next;
  }
  Cpair* temp = cpNew;
  while(cp!=NULL && cp2!=NULL)
  {
    if( expCmp(cp->mLabelExp, cp2->mLabelExp) == -1 )
    {
      temp->next  = cp;
      temp        = cp;
      cp          = cp->next;
    }
    else
    {
      temp->next  = cp2;
      temp        = cp2;
      cp2         = cp2->next;
    }
  }
  if(cp!=NULL)
  {
    temp->next  = cp;
  }
  else 
  {
    temp->next  = cp2;
  }

  return cpNew;
}



inline poly multInit( const int* exp, int numVariables, int* shift, 
                      unsigned long* negBitmaskShifted, int* offsets 
                    )
{
  poly np;
  omTypeAllocBin( poly, np, currRing->PolyBin );
  Print("POLY ADDRESS %p\n",np);
  p_SetRingOfLm( np, currRing );
  unsigned long* expTemp  =   (unsigned long*) omalloc0(NUMVARS*
                              sizeof(unsigned long));
  getExpFromIntArray( exp, expTemp, numVariables, shift, negBitmaskShifted, 
                      offsets 
                    );
  static number n  = nInit(1);
  Print("EXPONENT VECTOR INTERNAL: %ld %ld %ld %ld\n", expTemp[0], expTemp[1], expTemp[2], expTemp[3]);
  p_MemCopy_LengthGeneral( np->exp, expTemp, NUMVARS );
  pNext(np) = NULL;
  pSetCoeff0(np, n);
  p_Setm( np, currRing );
  return np;
}



poly createSpoly( Cpair* cp, int numVariables, int* shift, unsigned long* negBitmaskShifted,
                  int* offsets, poly spNoether, int use_buckets, ring tailRing, 
                  TObject** R
                )
{
#if F5EDEBUG 
  Print("CREATESPOLY - BEGINNING\n");
#endif
  LObject Pair( currRing );
  Pair.p1  = cp->p1;
  Print("P1: ");
  pWrite(cp->p1);
  Pair.p2  = cp->p2;
  Print("P2: ");
  pWrite(cp->p2);
  poly m1 = multInit( cp->mult1, numVariables, shift, 
                      negBitmaskShifted, offsets 
                    );
  Print("M1: %p ",m1);
  pWrite(m1);
  poly m2 = multInit( cp->mult2, numVariables, shift, 
                      negBitmaskShifted, offsets 
                    );
  Print("M2: %p ",m2);
  pWrite(m2);
#ifdef KDEBUG
  create_count_f5++;
#endif
  kTest_L( &Pair );
  poly p1 = Pair.p1;
  poly p2 = Pair.p2;


  poly last;
  Pair.tailRing = tailRing;

  assume(p1 != NULL);
  assume(p2 != NULL);
  assume(tailRing != NULL);

  poly a1 = pNext(p1), a2 = pNext(p2);
  number lc1 = pGetCoeff(p1), lc2 = pGetCoeff(p2);
  int co=0, ct = 3; // as lc1 = lc2 = 1 => 3=ksCheckCoeff(&lc1, &lc2); !!!

  int l1=0, l2=0;

  if (p_GetComp(p1, currRing)!=p_GetComp(p2, currRing))
  {
    if (p_GetComp(p1, currRing)==0)
    {
      co=1;
      p_SetCompP(p1,p_GetComp(p2, currRing), currRing, tailRing);
    }
    else
    {
      co=2;
      p_SetCompP(p2, p_GetComp(p1, currRing), currRing, tailRing);
    }
  }

  if (m1 == NULL)
    k_GetLeadTerms(p1, p2, currRing, m1, m2, tailRing);

  pSetCoeff0(m1, lc2);
  pSetCoeff0(m2, lc1);  // and now, m1 * LT(p1) == m2 * LT(p2)

  if (R != NULL)
  {
    if (Pair.i_r1 == -1)
    {
      l1 = pLength(p1) - 1;
    }
    else
    {
      l1 = (R[Pair.i_r1])->GetpLength() - 1;
    }
    if (Pair.i_r2 == -1)
    {
      l2 = pLength(p2) - 1;
    }
    else
    {
      l2 = (R[Pair.i_r2])->GetpLength() - 1;
    }
  }

  // get m2 * a2
  if (spNoether != NULL)
  {
    l2 = -1;
    a2 = tailRing->p_Procs->pp_Mult_mm_Noether( a2, m2, spNoether, l2, 
                                                tailRing,last
                                              );
    assume(l2 == pLength(a2));
  }
  else
    a2 = tailRing->p_Procs->pp_Mult_mm(a2, m2, tailRing,last);
#ifdef HAVE_RINGS
  if (!(rField_is_Domain(currRing))) l2 = pLength(a2);
#endif

  Pair.SetLmTail(m2, a2, l2, use_buckets, tailRing, last);

  // get m2*a2 - m1*a1
  Pair.Tail_Minus_mm_Mult_qq(m1, a1, l1, spNoether);

  // Clean-up time
  Pair.LmDeleteAndIter();
  p_LmDelete(m1, tailRing);

  if (co != 0)
  {
    if (co==1)
    {
      p_SetCompP(p1,0, currRing, tailRing);
    }
    else
    {
      p_SetCompP(p2,0, currRing, tailRing);
    }
  }

  pTest(Pair.GetLmCurrRing());
#if F5EDEBUG 
  Print("CREATESPOLY - BEGINNING\n");
#endif
  return Pair.GetLmCurrRing();
}




///////////////////////////////////////////////////////////////////////////
// INTERREDUCTION STUFF: HANDLED A BIT DIFFERENT FROM SINGULAR KERNEL    //
///////////////////////////////////////////////////////////////////////////

// from kstd1.cc, strat->enterS points to one of these functions
void enterSMoraNF (LObject p, int atS,kStrategy strat, int atR = -1);


//-----------------------------------------------------------------------------
// BEGIN static stuff from kstd1.cc 
// This is needed for the computation of strat, but as it is static in kstd1.cc
// we need to copy it!
//-----------------------------------------------------------------------------

static int doRed (LObject* h, TObject* with,BOOLEAN intoT,kStrategy strat)
{
  poly hp;
  int ret;
#if KDEBUG > 0
  kTest_L(h);
  kTest_T(with);
#endif
  // Hmmm ... why do we do this -- polys from T should already be normalized
  if (!TEST_OPT_INTSTRATEGY)  
    with->pNorm();
#ifdef KDEBUG
  if (TEST_OPT_DEBUG)
  {
    PrintS("reduce ");h->wrp();PrintS(" with ");with->wrp();PrintLn();
  }
#endif
  if (intoT)
  {
    // need to do it exacly like this: otherwise
    // we might get errors
    LObject L= *h;
    L.Copy();
    h->GetP();
    h->SetLength(strat->length_pLength);
    ret = ksReducePoly(&L, with, strat->kNoetherTail(), NULL, strat);
    if (ret)
    {
      if (ret < 0) return ret;
      if (h->tailRing != strat->tailRing)
        h->ShallowCopyDelete(strat->tailRing,
                             pGetShallowCopyDeleteProc(h->tailRing,
                                                       strat->tailRing));
    }
    enterT(*h,strat);
    *h = L;
  }
  else
    ret = ksReducePoly(h, with, strat->kNoetherTail(), NULL, strat);
#ifdef KDEBUG
  if (TEST_OPT_DEBUG)
  {
    PrintS("to ");h->wrp();PrintLn();
  }
#endif
  return ret;
}



/*2
* reduces h with elements from T choosing first possible
* element in T with respect to the given ecart
* used for computing normal forms outside kStd
*/
static poly redMoraNF (poly h,kStrategy strat, int flag)
{
  LObject H;
  H.p = h;
  int j = 0;
  int z = 10;
  int o = H.SetpFDeg();
  H.ecart = pLDeg(H.p,&H.length,currRing)-o;
  if ((flag & 2) == 0) cancelunit(&H,TRUE);
  H.sev = pGetShortExpVector(H.p);
  unsigned long not_sev = ~ H.sev;
  loop
  {
    if (j > strat->tl)
    {
      return H.p;
    }
    if (TEST_V_DEG_STOP)
    {
      if (kModDeg(H.p)>Kstd1_deg) pLmDelete(&H.p);
      if (H.p==NULL) return NULL;
    }
    if  (p_LmShortDivisibleBy ( strat->T[j].GetLmTailRing(), strat->sevT[j], 
                                H.GetLmTailRing(), not_sev, strat->tailRing
                              )
        )
    {
      //if (strat->interpt) test_int_std(strat->kIdeal);
      /*- remember the found T-poly -*/
      poly pi = strat->T[j].p;
      int ei = strat->T[j].ecart;
      int li = strat->T[j].length;
      int ii = j;
      /*
      * the polynomial to reduce with (up to the moment) is;
      * pi with ecart ei and length li
      */
      loop
      {
        /*- look for a better one with respect to ecart -*/
        /*- stop, if the ecart is small enough (<=ecart(H)) -*/
        j++;
        if (j > strat->tl) break;
        if (ei <= H.ecart) break;
        if (((strat->T[j].ecart < ei)
          || ((strat->T[j].ecart == ei)
        && (strat->T[j].length < li)))
        && pLmShortDivisibleBy(strat->T[j].p,strat->sevT[j], H.p, not_sev))
        {
          /*
          * the polynomial to reduce with is now;
          */
          pi = strat->T[j].p;
          ei = strat->T[j].ecart;
          li = strat->T[j].length;
          ii = j;
        }
      }
      /*
      * end of search: have to reduce with pi
      */
      z++;
      if (z>10)
      {
        pNormalize(H.p);
        z=0;
      }
      if ((ei > H.ecart) && (!strat->kHEdgeFound))
      {
        /*
        * It is not possible to reduce h with smaller ecart;
        * we have to reduce with bad ecart: H has to enter in T
        */
        doRed(&H,&(strat->T[ii]),TRUE,strat);
        if (H.p == NULL)
          return NULL;
      }
      else
      {
        /*
        * we reduce with good ecart, h need not to be put to T
        */
        doRed(&H,&(strat->T[ii]),FALSE,strat);
        if (H.p == NULL)
          return NULL;
      }
      /*- try to reduce the s-polynomial -*/
      o = H.SetpFDeg();
      if ((flag &2 ) == 0) cancelunit(&H,TRUE);
      H.ecart = pLDeg(H.p,&(H.length),currRing)-o;
      j = 0;
      H.sev = pGetShortExpVector(H.p);
      not_sev = ~ H.sev;
    }
    else
    {
      j++;
    }
    Print("POLY IN REDUCTION:  ");
    if( p_GetOrder( H.p, currRing ) == pWTotaldegree( H.p, currRing ) )
    {
      Print(" ALLES OK\n");
    }
    else 
    {
      Print("BEI POLY %p",H.p); Print(" stimmt etwas nicht!\n");
    }
    pWrite( H.p );
    
  }
}

//------------------------------------------------------------------------
// END static stuff from kstd1.cc 
//------------------------------------------------------------------------

void prepRedGBReduction(kStrategy strat, ideal F, ideal Q, int lazyReduce)
{
  int i;
  LObject   h;

  strat->kHEdgeFound = ppNoether != NULL;
  strat->kNoether=pCopy(ppNoether);
  test|=Sy_bit(OPT_REDTAIL);
  if (TEST_OPT_STAIRCASEBOUND
  && (0<Kstd1_deg)
  && ((!strat->kHEdgeFound)
    ||(TEST_OPT_DEGBOUND && (pWTotaldegree(strat->kNoether)<Kstd1_deg))))
  {
    pDelete(&strat->kNoether);
    strat->kNoether=pOne();
    pSetExp(strat->kNoether,1, Kstd1_deg+1);
    pSetm(strat->kNoether);
    strat->kHEdgeFound=TRUE;
  }
  initBuchMoraCrit(strat);
  initBuchMoraPos(strat);
  initMora(F,strat);
  strat->enterS = enterSMoraNF;
  /*- set T -*/
  strat->tl = -1;
  strat->tmax = setmaxT;
  strat->T = initT();
  strat->R = initR();
  strat->sevT = initsevT();
  /*- set S -*/
  strat->sl = -1;
  /*- init local data struct.-------------------------- -*/
  /*Shdl=*/initS(F,Q,strat);
  if ((strat->ak!=0)
  && (strat->kHEdgeFound))
  {
    if (strat->ak!=1)
    {
      pSetComp(strat->kNoether,1);
      pSetmComp(strat->kNoether);
      poly p=pHead(strat->kNoether);
      pSetComp(p,strat->ak);
      pSetmComp(p);
      p=pAdd(strat->kNoether,p);
      strat->kNoether=pNext(p);
      p_LmFree(p,currRing);
    }
  }
  if (TEST_OPT_INTSTRATEGY && ((lazyReduce & KSTD_NF_LAZY)==0))
  {
    for (i=strat->sl; i>=0; i--)
      pNorm(strat->S[i]);
  }
  
  assume(!(idIs0(F)&&(Q==NULL)));

// lazy_reduce flags: can be combined by |
//#define KSTD_NF_LAZY   1
  // do only a reduction of the leading term
//#define KSTD_NF_ECART  2
  // only local: recude even with bad ecart
  //poly   p;

  //if ((idIs0(F))&&(Q==NULL))
  //  return pCopy(q); /*F=0*/
  //strat->ak = si_max(idRankFreeModule(F),pMaxComp(q));
  /*- creating temp data structures------------------- -*/
  strat->kHEdgeFound = ppNoether != NULL;
  strat->kNoether    = pCopy(ppNoether);
  test|=Sy_bit(OPT_REDTAIL);
  test&=~Sy_bit(OPT_INTSTRATEGY);
  if (TEST_OPT_STAIRCASEBOUND
  && (! TEST_V_DEG_STOP)
  && (0<Kstd1_deg)
  && ((!strat->kHEdgeFound)
    ||(TEST_OPT_DEGBOUND && (pWTotaldegree(strat->kNoether)<Kstd1_deg))))
  {
    pDelete(&strat->kNoether);
    strat->kNoether=pOne();
    pSetExp(strat->kNoether,1, Kstd1_deg+1);
    pSetm(strat->kNoether);
    strat->kHEdgeFound=TRUE;
  }
  initBuchMoraCrit(strat);
  initBuchMoraPos(strat);
  initMora(F,strat);
  strat->enterS = enterSMoraNF;
  /*- set T -*/
  strat->tl = -1;
  strat->tmax = setmaxT;
  strat->T = initT();
  strat->R = initR();
  strat->sevT = initsevT();
  /*- set S -*/
  strat->sl = -1;
  /*- init local data struct.-------------------------- -*/
  /*Shdl=*/initS(F,Q,strat);
  if ((strat->ak!=0)
  && (strat->kHEdgeFound))
  {
    if (strat->ak!=1)
    {
      pSetComp(strat->kNoether,1);
      pSetmComp(strat->kNoether);
      poly p=pHead(strat->kNoether);
      pSetComp(p,strat->ak);
      pSetmComp(p);
      p=pAdd(strat->kNoether,p);
      strat->kNoether=pNext(p);
      p_LmFree(p,currRing);
    }
  }
  if ((lazyReduce & KSTD_NF_LAZY)==0)
  {
    for (i=strat->sl; i>=0; i--)
      pNorm(strat->S[i]);
  }
  /*- puts the elements of S also to T -*/
  for (i=0; i<=strat->sl; i++)
  {
    h.p = strat->S[i];
    h.ecart = strat->ecartS[i];
    if (strat->sevS[i] == 0) strat->sevS[i] = pGetShortExpVector(h.p);
    else assume(strat->sevS[i] == pGetShortExpVector(h.p));
    h.length = pLength(h.p);
    h.sev = strat->sevS[i];
    h.SetpFDeg();
    enterT(h,strat);
  }
}



poly reduceByRedGBCritPair  ( Cpair* cp, kStrategy strat, int numVariables, 
                              int* shift, unsigned long* negBitmaskShifted, 
                              int* offsets, int lazyReduce
                            )
{
  poly  p;
  int   i;
  int   j;
  int   o;
  BITSET save_test=test;
  // create the s-polynomial corresponding to the critical pair cp
  poly q = createSpoly( cp, numVariables, shift, negBitmaskShifted, offsets );
  /*- compute------------------------------------------- -*/
  p = pCopy(q);
  deleteHC(&p,&o,&j,strat);
  if (TEST_OPT_PROT) 
  { 
    PrintS("r"); 
    mflush(); 
  }
  if (p!=NULL) p = redMoraNF(p,strat, lazyReduce & KSTD_NF_ECART);
  if ((p!=NULL)&&((lazyReduce & KSTD_NF_LAZY)==0))
  {
    if (TEST_OPT_PROT) 
    { 
      PrintS("t"); mflush(); 
    }
    Print("CURRING TYP: %p\n",currRing->typ);
    p = redtail(p,strat->sl,strat);
  }
  test=save_test;
  if (TEST_OPT_PROT) PrintLn();
  return p;
}



// NEEDED AT ALL?
poly reduceByRedGBPoly( poly q, kStrategy strat, int lazyReduce )
{
  poly  p;
  int   i;
  int   j;
  int   o;
  BITSET save_test=test;
  ////////////////////////////////////////////////////////
  // TODO: critical pair -> s-polynomial
  //       q should be the s-polynomial!!!!
  ////////////////////////////////////////////////////////
  
  /*- compute------------------------------------------- -*/
  p = pCopy(q);
  deleteHC(&p,&o,&j,strat);
  if (TEST_OPT_PROT) 
  { 
    PrintS("r"); 
    mflush(); 
  }
  if (p!=NULL) p = redMoraNF(p,strat, lazyReduce & KSTD_NF_ECART);
  if ((p!=NULL)&&((lazyReduce & KSTD_NF_LAZY)==0))
  {
    if (TEST_OPT_PROT) 
    { 
      PrintS("t"); 
      mflush(); 
    }
    p = redtail(p,strat->sl,strat);
  }
  test=save_test;
  if (TEST_OPT_PROT) PrintLn();
  return p;
}



void clearStrat(kStrategy strat, ideal F, ideal Q)
{
  int i;
  cleanT(strat);
  omFreeSize((ADDRESS)strat->T,strat->tmax*sizeof(TObject));
  omFreeSize((ADDRESS)strat->ecartS,IDELEMS(strat->Shdl)*sizeof(int));
  omFreeSize((ADDRESS)strat->sevS,IDELEMS(strat->Shdl)*sizeof(unsigned long));
  omFreeSize((ADDRESS)strat->NotUsedAxis,(pVariables+1)*sizeof(BOOLEAN));
  omfree(strat->sevT);
  omfree(strat->S_2_R);
  omfree(strat->R);

  if ((Q!=NULL)&&(strat->fromQ!=NULL))
  {
    i=((IDELEMS(Q)+IDELEMS(F)+15)/16)*16;
    omFreeSize((ADDRESS)strat->fromQ,i*sizeof(int));
    strat->fromQ=NULL;
  }
  pDelete(&strat->kHEdge);
  pDelete(&strat->kNoether);
  if ((TEST_OPT_WEIGHTM)&&(F!=NULL))
  {
    pRestoreDegProcs(pFDegOld, pLDegOld);
    if (ecartWeights)
    {
      omFreeSize((ADDRESS *)&ecartWeights,(pVariables+1)*sizeof(short));
      ecartWeights=NULL;
    }
  }
  idDelete(&strat->Shdl);

}




///////////////////////////////////////////////////////////////////////////
// MEMORY & INTERNAL EXPONENT VECTOR STUFF: HANDLED A BIT DIFFERENT FROM //
// SINGULAR KERNEL                                                       //
///////////////////////////////////////////////////////////////////////////

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
                                int numVariables, int* shift, unsigned long* 
                                negBitmaskShifted, int* offsets
                              )
{
  register int i = numVariables;
  for( ; i; i--)
  {
    register int shiftL   =   shift[i];
    Print("%d. EXPONENT CREATION %d\n",i,exp[i]);
    unsigned long ee      =   exp[i];
    ee                    =   ee << shiftL;
    register int offsetL  =   offsets[i];
    r[offsetL]            &=  negBitmaskShifted[i];
    r[offsetL]            |=  ee;
  }
  r[currRing->pCompIndex] = exp[0];
  Print("COMPONENT CREATION: %d\n", exp[0]);
  Print("EXPONENT VECTOR INTERNAL AT CREATION: %ld %ld %ld %ld\n", r[0], r[1], r[2], r[3]);
}



/// my own GetBitFields
/// @sa GetBitFields
inline unsigned long GetBitFieldsF5e( int e, unsigned int s, 
                                      unsigned int n
                                    )
{
#define Sy_bit_L(x)     (((unsigned long)1L)<<(x))
  unsigned int i = 0;
  unsigned long  ev = 0L;
  assume(n > 0 && s < BIT_SIZEOF_LONG);
  do
  {
    assume(s+i < BIT_SIZEOF_LONG);
    if ((long) e > (long) i) ev |= Sy_bit_L(s+i);
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


static inline BOOLEAN isDivisibleGetMult  ( poly a, unsigned long sev_a, poly b, 
                                            unsigned long not_sev_b, int** mult,
                                            BOOLEAN* isMult
                                          )
{
#if F5EDEBUG
    Print("ISDIVISIBLE-BEGINNING \n");
#endif
  pWrite(a);
  pWrite(b);
  p_LmCheckPolyRing1(a, currRing);
  p_LmCheckPolyRing1(b, currRing);
  if (sev_a & not_sev_b)
  {
    pAssume1(_p_LmDivisibleByNoComp(a, currRing, b, currRing) == FALSE);
    *isMult = false;
#if F5EDEBUG
    Print("ISDIVISIBLE-END1 \n");
#endif
    return FALSE;
  }
  if (p_GetComp(a, currRing) == 0 || p_GetComp(a,currRing) == p_GetComp(b,currRing))
  {
    int i=currRing->N;
    pAssume1(currRing->N == currRing->N);
    *mult[0]  = p_GetComp(a,currRing);
    do
    {
      Print("%d ---- %d\n",p_GetExp(a,i,currRing), p_GetExp(b,i,currRing) );
      if (p_GetExp(a,i,currRing) < p_GetExp(b,i,currRing))
      {
        *isMult = false;
#if F5EDEBUG
    Print("ISDIVISIBLE-END2 \n");
#endif
        return FALSE;
      }
      (*mult)[i] = (p_GetExp(a,i,currRing) - p_GetExp(b,i,currRing)); 
      if( ((*mult)[i])>0 )
      {
        *isMult = true;
      }
      i--;
    }
    while (i);
    (*mult)[0]  = 0;
#ifdef HAVE_RINGS
#if F5EDEBUG
    Print("ISDIVISIBLE-END3 \n");
#endif
    return nDivBy(p_GetCoeff(b, r), p_GetCoeff(a, r));
#else
#if F5EDEBUG
    Print("ISDIVISIBLE-END4 \n");
#endif
    return TRUE;
#endif
  }
#if F5EDEBUG
    Print("ISDIVISIBLE-END5 \n");
#endif
  return FALSE;
}
#endif
// HAVE_F5C
