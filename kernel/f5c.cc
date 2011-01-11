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

#ifdef NDEBUG
#undef NDEBUG
#define NDEBUG 0
#endif
#ifdef PDEBUG
#undef PDEBUG
#define PDEBUG 0 
#endif
#define F5ETAILREDUCTION  0 
#define F5EDEBUG00        1
#define F5EDEBUG0         0 
#define F5EDEBUG1         0 
#define F5EDEBUG2         0 
#define F5EDEBUG3         0 
#define setMaxIdeal       64
#define NUMVARS           currRing->ExpL_Size
int create_count_f5 = 0; // for KDEBUG option in reduceByRedGBCritPair
// size for strat & rewRules in the corresponding iteration steps
// this is needed for the lengths of the rules arrays in the following
unsigned long rewRulesSize        = 0;
unsigned long f5RulesSize         = 0;
unsigned long stratSize           = 0;
unsigned long superTopReductions  = 0;
unsigned long zeroReductions      = 0;
unsigned long number1Reductions   = 0;
unsigned long numberReductions    = 0;
 
/// NOTE that the input must be homogeneous to guarantee termination and
/// correctness. Thus these properties are assumed in the following.
ideal f5cMain(ideal F, ideal Q) 
{
  if(idIs0(F)) 
  {
    return idInit(1, F->rank);
  }
  // interreduction of the input ideal F
  ideal FRed      = idCopy( F );
  //ideal FRedTemp  = FRed;
  //idDelete( &FRed );
  //FRed            = FRedTemp;

#if F5EDEBUG3
  int j = 0;
  int k = 0;
  int* expVec   = new int[(currRing->N)+1];
  for( ; k<IDELEMS(FRed); k++)
  {
    Print("ORDER: %ld\n",FRed->m[k]->exp[currRing->pOrdIndex]);
    Print("SIZE OF INTERNAL EXPONENT VECTORS: %d\n",currRing->ExpL_Size);
    pGetExpV(FRed->m[k],expVec);
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
  int numVariables                  = currRing->N;
  /// reading/writing/comparison
  int* shift                        = (int*) omAlloc((currRing->N+1)*sizeof(int));
  unsigned long* negBitmaskShifted  = (unsigned long*) omAlloc((currRing->N+1)*
                                      sizeof(unsigned long));
  int* offsets                      = (int*) omAlloc((currRing->N+1)*sizeof(int));
  const unsigned long _bitmasks[4]  = {-1, 0x7fff, 0x7f, 0x3};
  for( ; i<currRing->N+1; i++)
  {
    shift[i]                = currRing->VarOffset[i] >> 24;
    negBitmaskShifted[i]    = ~(currRing->bitmask << shift[i]);
    offsets[i]              = (currRing->VarOffset[i] & 0xffffff);
  }
  
  ideal r = idInit(1, FRed->rank);
  // save the first element in ideal r, initialization of iteration process
  r->m[0] = FRed->m[0];
  // counter over the remaining generators of the input ideal F
  for(i=1; i<IDELEMS(FRed); i++) 
  {
    // computation of r: a groebner basis of <F[0],...,F[gen]> = <r,F[gen]>
    r = f5cIter(FRed->m[i], r, numVariables, shift, negBitmaskShifted, offsets);
    // the following interreduction is the essential idea of F5e.
    // NOTE that we do not need the old rules from previous iteration steps
    // => we only interreduce the polynomials and forget about their labels
    ideal rTemp = kInterRed(r);
    idDelete( &r );
    r = rTemp;
#if F5EDEBUG2
    for( int k=0; k<IDELEMS(r); k++ )
    {
      pTest( r->m[k] );
      Print("TESTS after interred: %p ",r->m[k]);
      pWrite(r->m[k]);
    }
#endif
  }
  omFree(shift);
  omFree(negBitmaskShifted);
  omFree(offsets);
#if F5EDEBUG00
  Print("-------------------------------------------\n");
  Print("# Super Top Reductions:  %ld\n", superTopReductions);
  Print("# Zero Reductions:       %ld\n", zeroReductions);
  Print("# Reductions:            %ld\n", number1Reductions);
  Print("# Reduction steps:       %ld\n", numberReductions);
  Print("-------------------------------------------\n");
#endif
  create_count_f5     = 0;
  stratSize           = 0;
  f5RulesSize         = 0;
  rewRulesSize        = 0;
  superTopReductions  = 0;
  zeroReductions      = 0;
  numberReductions    = 0;
  number1Reductions   = 0;
  return r;
}



ideal f5cIter ( 
                poly p, ideal redGB, int numVariables, int* shift, 
                unsigned long* negBitmaskShifted, int* offsets
              )
{
#if F5EDEBUG1
  Print("F5CITER-BEGIN\n");
  Print("NEXT ITERATION ELEMENT: ");
  pWrite( p );
  Print("REDGB ELEMENT: ");
  pWrite( redGB->m[0] );
#endif
#if F5EDEBUG3
  Print("ORDER %ld -- %ld\n",p_GetOrder(p,currRing), p->exp[currRing->pOrdIndex]);
  int j = 0;
  int k = 0;
  Print("SIZE OF redGB: %d\n",IDELEMS(redGB));
  for( ; k<IDELEMS(redGB); k++)
  {
    j = 0;
    Print("Poly: %p -- ",redGB->m[k]);
    pTest( redGB->m[k] );
    pWrite(pHead(redGB->m[k]));
    Print("%d. EXP VEC: ", k);
    Print("\n");
  }
#endif  
  // create the reduction structure "strat" which is needed for all 
  // reductions with redGB in this iteration step
  kStrategy strat   = new skStrategy;
  BOOLEAN b         = pLexOrder;
  BOOLEAN toReset   = FALSE;
  BOOLEAN delete_w  = TRUE;
  if (rField_has_simple_inverse())
  {  
    strat->LazyPass = 20;
  }
  else
  {
    strat->LazyPass = 2;
  }
  strat->LazyDegree   = 1;
  strat->enterOnePair = enterOnePairNormal;
  strat->chainCrit    = chainCritNormal;
  strat->syzComp      = 0;
  strat->ak           = idRankFreeModule(redGB);
  prepRedGBReduction(strat, redGB);
#if F5EDEBUG3
  Print("F5CITER-AFTER PREPREDUCTION\n");
  Print("ORDER %ld -- %ld\n",p_GetOrder(p,currRing), p->exp[currRing->pOrdIndex]);
  Print("SIZE OF redGB: %d\n",IDELEMS(redGB));
  for(k=0 ; k<IDELEMS(redGB); k++)
  {
    j = 0;
    Print("Poly: %p -- ",redGB->m[k]);
    pTest( redGB->m[k] );
    pWrite(pHead(redGB->m[k]));
    Print("%d. EXP VEC: ", k);
    Print("\n");
  }
#endif  
  int i;
  // store #elements in redGB for freeing the memory of F5Rules in the end of this
  // iteration step
  unsigned long oldLength;
  f5RulesSize         = 2*(strat->sl+1);
  // create array of leading monomials of previously computed elements in redGB
  F5Rules* f5Rules    = (F5Rules*) omAlloc(sizeof(struct F5Rules));
  RewRules* rewRules  = (RewRules*) omAlloc(sizeof(struct RewRules));
  // malloc memory for all rules
  f5Rules->coeff      = (number*) omAlloc(f5RulesSize*
                        sizeof(number)); 
  f5Rules->label      = (int**) omAlloc(f5RulesSize*sizeof(int*));
  f5Rules->slabel     = (unsigned long*) omAlloc(f5RulesSize*
                        sizeof(unsigned long)); 
  
  // set global variables for the sizes of F5 & Rewritten Rules available
  rewRulesSize  = f5RulesSize = 2*(strat->sl+1);
  stratSize     = strat->sl+1;

  // malloc two times the size of the previous Groebner basis
  // Note that we possibly need more memory in this iteration step!
  rewRules->coeff   = (number*) omAlloc((rewRulesSize)*
                      sizeof(number)); 
  rewRules->label   = (int**) omAlloc((rewRulesSize)*sizeof(int*));
  rewRules->slabel  = (unsigned long*) omAlloc((rewRulesSize)*
                      sizeof(unsigned long)); 
  // Initialize a first (dummy) rewrite rule for the initial polynomial of this
  // iteration step:
  // (a) Note that we are allocating & setting all entries to zero for this first 
  //     rewrite rule.
  // (b) Note also that the size of strat is >=1.
  rewRules->coeff[0]  = n_Init( 1, currRing );
  rewRules->label[0]  = (int*) omAlloc0( (currRing->N+1)*sizeof(int) );
  rewRules->slabel[0] = 0;
  for(i=1; i<rewRulesSize; i++) 
  {
    rewRules->label[i]  =  (int*) omAlloc( (currRing->N+1)*sizeof(int) );
  } 
  pTest( redGB->m[0] );
  // use the strategy strat to get the F5 Rules:
  // When preparing strat we have already computed & stored the short exonent
  // vectors there => do not recompute them again 
  for(i=0; i<stratSize; i++) 
  {
    f5Rules->coeff[i]   = n_Init( 1, currRing );
    f5Rules->label[i]   =  (int*) omAlloc( (currRing->N+1)*sizeof(int) );
    pGetExpV( strat->S[i], f5Rules->label[i] );
    f5Rules->slabel[i]  = strat->sevS[i];
  } 
  // alloc memory for the rest of the labels
  for( ; i<f5RulesSize; i++) 
  {
    f5Rules->label[i]   = (int*) omAlloc( (currRing->N+1)*sizeof(int) );
  } 

  rewRules->size  = 1;
  f5Rules->size   = stratSize;
  // reduce and initialize the list of Lpolys with the current ideal generator p
#if F5EDEBUG2
  Print("Before reduction\n");
  pWrite( p );
  pTest( p );
#endif
  p = kNF( redGB, NULL, p );
  //p = reduceByRedGBPoly( p, strat );
#if F5EDEBUG2
  Print("After reduction: ");
  pTest( p );
  pWrite( p );
#endif
  if( p )
  {
    //pNorm( p );  
    Lpoly* gCurr      = (Lpoly*) omAlloc( sizeof(Lpoly) );
    gCurr->next       = NULL;
    gCurr->sExp       = pGetShortExpVector(p);
    gCurr->p          = p;
    gCurr->rewRule    = 0;
    gCurr->redundant  = FALSE;
     
    Lpoly* gCurrFirst = gCurr;
    // initializing the list of critical pairs for this iteration step 
    CpairDegBound* cpBounds = NULL;
    criticalPairInit( 
                      gCurr, strat, *f5Rules, *rewRules, &cpBounds, numVariables, 
                      shift, negBitmaskShifted, offsets
                    ); 
    if( cpBounds )
    {
      computeSpols( 
                    strat, cpBounds, redGB, &gCurr, &f5Rules, &rewRules, 
                    numVariables, shift, negBitmaskShifted, offsets
                  );
    }
    // next all new elements are added to redGB & redGB is being reduced
    Lpoly* temp;
#if F5EDEBUG2
    int counter = 1;
#endif
    while( gCurrFirst )
    {
#if F5EDEBUG3
      if( p_GetOrder( gCurrFirst->p, currRing ) == pWTotaldegree( gCurrFirst->p, currRing ) )
      {
        Print(" ALLES OK\n");
      }
      else 
      {
        Print("BEI POLY "); gCurrFirst->p; //Print(" stimmt etwas nicht!\n");
      }
#endif
#if F5EDEBUG2
      Print("%d INSERT TO REDGB: ",counter);
      pWrite(gCurrFirst->p);
#endif
      idInsertPoly( redGB, gCurrFirst->p );
      temp        = gCurrFirst;
      gCurrFirst  = gCurrFirst->next;
      omFree(temp);
#if F5EDEBUG2
      counter++;
#endif
    }
    idSkipZeroes( redGB );
  }
#if F5EDEBUG1
  Print("F5CITER-END\n");
#endif  
  // free memory
  // Delete the F5 Rules, the Rewritten Rules, and the reduction strategy 
  // strat, since the current iteration step is completed right now.
  oldLength = strat->sl;
  for( i=0; i<=oldLength; i++ )
  {
    omFreeSize( f5Rules->label[i], (currRing->N+1)*sizeof(int) );
  }
  omFreeSize( f5Rules->label, f5RulesSize*sizeof(int*) );
  omFreeSize( f5Rules->slabel, f5RulesSize*sizeof(unsigned long) );
  omFreeSize( f5Rules->coeff, f5RulesSize*sizeof(number) );
  
  omFreeSize( f5Rules, sizeof(F5Rules) );
  
  for( i=0; i<rewRulesSize; i++ )
  {
    omFreeSize( rewRules->label[i], (currRing->N+1)*sizeof(int) );
  }
  omFreeSize( rewRules->slabel, rewRulesSize*sizeof(unsigned long) );
  omFreeSize( rewRules->label, rewRulesSize*sizeof(int*) );
  omFreeSize( rewRules->coeff, rewRulesSize*sizeof(number) );
  
  omFreeSize( rewRules, sizeof(RewRules) );
  clearStrat( strat, redGB );
  
  return redGB;
}



void criticalPairInit ( 
  Lpoly* gCurr, const kStrategy strat, 
  const F5Rules& f5Rules, const RewRules& rewRules,
  CpairDegBound** cpBounds, int numVariables, int* shift, 
  unsigned long* negBitmaskShifted, int* offsets
                      )
{
#if F5EDEBUG1
  Print("CRITPAIRINIT-BEGINNING\n");
#endif
  int i, j;
  int* expVecNewElement = (int*) omAlloc((currRing->N+1)*sizeof(int));
  pGetExpV(gCurr->p, expVecNewElement); 
  // this must be changed for parallelizing the generation process of critical
  // pairs
  Cpair* cpTemp;
  Cpair* cp = (Cpair*) omAlloc( sizeof(Cpair) );
  cpTemp    = cp;
  cpTemp->next      = NULL;
  cpTemp->mLabelExp = NULL;
  cpTemp->mLabel1   = NULL;
  cpTemp->smLabel1  = 0;
  cpTemp->mult1     = NULL;
  cpTemp->p1        = gCurr->p;
  cpTemp->rewRule1  = gCurr->rewRule;
  //Print("TEST REWRULE1 %p\n",cpTemp->rewRule1);
  cpTemp->mLabel2   = NULL;
  cpTemp->smLabel2  = 0;
  cpTemp->mult2     = NULL;
  cpTemp->p2        = NULL;

  // we only need to alloc memory for the 1st label as for the initial 
  // critical pairs all 2nd generators have label NULL in F5e
  cpTemp->mLabel1   = (int*) omAlloc((currRing->N+1)*sizeof(int));
  cpTemp->mult1     = (int*) omAlloc((currRing->N+1)*sizeof(int));
  cpTemp->mult2     = (int*) omAlloc((currRing->N+1)*sizeof(int));
  int temp;
  long critPairDeg; // degree of the label of the pair in the following
  for(i=0; i<strat->sl; i++)
  {
    // computation of the lcm and the corresponding multipliers for the critical
    // pair generated by the new element and elements of the previous iteration
    // steps, i.e. elements already in redGB
    cpTemp->mLabel1[0]  = cpTemp->mult1[0]  = 0; 
    cpTemp->mult2[0]    = 0; 
    critPairDeg         = 0;
    for(j=1; j<=currRing->N; j++)
    {
      temp  = expVecNewElement[j] - f5Rules.label[i][j];
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

    // this is the ggv criterion!
    if( !criterion1(cpTemp->mLabel1, cpTemp->smLabel1, &f5Rules) ) 
    {
      // completing the construction of the new critical pair and inserting it
      // to the list of critical pairs 
      cpTemp->p2        = strat->S[i];
      cpTemp->coeff2    = n_Div( pGetCoeff(cpTemp->p1), pGetCoeff(cpTemp->p2), currRing );
#if F5EDEBUG1
      Print("2nd gen: ");
      pWrite( pHead(cpTemp->p2) );
#endif
      // now we really need the memory for the exp label
      //cpTemp->mLabelExp = (unsigned long*) omAlloc0(NUMVARS*
      //                          sizeof(unsigned long));
      cpTemp->mLabelExp   = pOne();
      getExpFromIntArray( cpTemp->mLabel1, cpTemp->mLabelExp, 
                          numVariables, shift, negBitmaskShifted, offsets );
      insertCritPair(cpTemp, critPairDeg, cpBounds);
      Cpair* cp         = (Cpair*) omAlloc( sizeof(Cpair) );
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

      cpTemp->mLabel1   = (int*) omAlloc((currRing->N+1)*sizeof(int));
      cpTemp->mult1     = (int*) omAlloc((currRing->N+1)*sizeof(int));
      cpTemp->mult2     = (int*) omAlloc((currRing->N+1)*sizeof(int));
    }
  }
  // same critical pair processing for the last element in redGB
  // This is outside of the loop to keep memory low, since we know that after
  // this element no new memory for a critical pair must be allocated.
  // computation of the lcm and the corresponding multipliers for the critical
  // pair generated by the new element and elements of the previous iteration
  // steps, i.e. elements already in redGB
  cpTemp->mLabel1[0]  = cpTemp->mult1[0]  = pGetComp(cpTemp->p1); 
  cpTemp->mult2[0]    = pGetComp(strat->S[strat->sl]); 
  critPairDeg         = 0;
  for(j=1; j<=currRing->N; j++)
  {
    temp  = expVecNewElement[j] - f5Rules.label[strat->sl][j];
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
  
  // this is the ggv criterion
  if( !criterion1(cpTemp->mLabel1, cpTemp->smLabel1, &f5Rules) ) 
  {
    // completing the construction of the new critical pair and inserting it
    // to the list of critical pairs 
    cpTemp->p2        = strat->S[strat->sl];
    cpTemp->coeff2    = n_Div( pGetCoeff(cpTemp->p1), pGetCoeff(cpTemp->p2), currRing );
#if F5EDEBUG1
    Print("2nd gen: ");
    pWrite( pHead(cpTemp->p2) );
#endif
    // now we really need the memory for the exp label
    //cpTemp->mLabelExp = (unsigned long*) omAlloc0(NUMVARS*
    //                          sizeof(unsigned long));
    cpTemp->mLabelExp   = pOne();
    getExpFromIntArray( cpTemp->mLabel1, cpTemp->mLabelExp, 
                        numVariables, shift, negBitmaskShifted, offsets
                      );
    insertCritPair( cpTemp, critPairDeg, cpBounds );
  }
  else 
  {
    // we can delete the memory reserved for cpTemp
    omFree( cpTemp->mult1 );
    omFree( cpTemp->mult2 );
    omFree( cpTemp->mLabel1 );
    omFree( cpTemp );
  }
  omFree(expVecNewElement);
#if F5EDEBUG1
  Print("CRITPAIRINIT-END\n");
#endif
}



void criticalPairPrev ( 
  Lpoly* gCurrNew, Lpoly* gCurr, const kStrategy strat, const F5Rules& f5Rules, 
  const RewRules& rewRules, CpairDegBound** cpBounds, 
  int numVariables, int* shift, unsigned long* negBitmaskShifted, 
  int* offsets
                      )
{
#if F5EDEBUG1
  Print("CRITPAIRPREV-BEGINNING\n");
#endif
  int i, j;
  int* expVecNewElement = (int*) omAlloc((currRing->N+1)*sizeof(int));
  pGetExpV(gCurrNew->p, expVecNewElement); 
  // this must be changed for parallelizing the generation process of critical
  // pairs
  Cpair* cpTemp;
  Cpair* cp         = (Cpair*) omAlloc( sizeof(Cpair) );
  cpTemp            = cp;
  cpTemp->next      = NULL;
  cpTemp->mLabelExp = NULL;
  cpTemp->mLabel1   = NULL;
  cpTemp->smLabel1  = 0;
  cpTemp->mult1     = NULL;
  cpTemp->p1        = gCurrNew->p;
  cpTemp->rewRule1  = gCurrNew->rewRule;
  cpTemp->mLabel2   = NULL;
  cpTemp->smLabel2  = 0;
  cpTemp->mult2     = NULL;
  cpTemp->p2        = NULL;

  // we only need to alloc memory for the 1st label as for the initial 
  // critical pairs all 2nd generators have label NULL in F5e
  cpTemp->mLabel1   = (int*) omAlloc((currRing->N+1)*sizeof(int));
  cpTemp->mult1     = (int*) omAlloc((currRing->N+1)*sizeof(int));
  cpTemp->mult2     = (int*) omAlloc((currRing->N+1)*sizeof(int));
  int temp;
  long critPairDeg; // degree of the label of the critical pair in the following
  for(i=0; i<strat->sl; i++)
  {
    // computation of the lcm and the corresponding multipliers for the critical
    // pair generated by the new element and elements of the previous iteration
    // steps, i.e. elements already in redGB
    cpTemp->mLabel1[0]  = cpTemp->mult1[0]  = pGetExp(cpTemp->p1, 0); 
    cpTemp->mult2[0]    = pGetExp(strat->S[i], 0); 
    critPairDeg         = 0;
    for(j=1; j<=currRing->N; j++)
    {
      temp  = expVecNewElement[j] - f5Rules.label[i][j];
      if(temp<0)
      {
        cpTemp->mult1[j]    =   -temp;  
        cpTemp->mult2[j]    =   0; 
        cpTemp->mLabel1[j]  =   rewRules.label[cpTemp->rewRule1][j] - temp;
        critPairDeg         +=  rewRules.label[cpTemp->rewRule1][j] - temp; 
      }
      else
      {
        cpTemp->mult1[j]    =   0;  
        cpTemp->mult2[j]    =   temp;  
        cpTemp->mLabel1[j]  =   rewRules.label[cpTemp->rewRule1][j];
        critPairDeg         +=  rewRules.label[cpTemp->rewRule1][j]; 
      }
    }
    cpTemp->smLabel1 = ~getShortExpVecFromArray(cpTemp->mLabel1);
    
#if F5EDEBUG1
    Print("2nd generator of pair: ");
    pWrite( pHead(strat->S[i]) );
#endif
    
    // this is the ggv criterion!
    if( !criterion1(cpTemp->mLabel1, cpTemp->smLabel1, &f5Rules) )
    {
      // completing the construction of the new critical pair and inserting it
      // to the list of critical pairs 
      cpTemp->p2        = strat->S[i];
      cpTemp->coeff2    = n_Div( pGetCoeff(cpTemp->p1), pGetCoeff(cpTemp->p2), currRing );
      // now we really need the memory for the exp label
      //cpTemp->mLabelExp = (unsigned long*) omAlloc0(NUMVARS*
      //                          sizeof(unsigned long));
      cpTemp->mLabelExp   = pOne();
      getExpFromIntArray( cpTemp->mLabel1, cpTemp->mLabelExp, 
                          numVariables, shift, negBitmaskShifted, offsets );
      insertCritPair(cpTemp, critPairDeg, cpBounds);
      Cpair* cp         = (Cpair*) omAlloc( sizeof(Cpair) );
      cpTemp            = cp;
      cpTemp->next      = NULL;
      cpTemp->mLabelExp = NULL;
      cpTemp->mLabel1   = NULL;
      cpTemp->smLabel1  = 0;
      cpTemp->mult1     = NULL;
      cpTemp->p1        = gCurrNew->p;
      cpTemp->rewRule1  = gCurrNew->rewRule;
      cpTemp->mLabel2   = NULL;
      cpTemp->smLabel2  = 0;
      cpTemp->mult2     = NULL;
      cpTemp->p2        = NULL;

      cpTemp->mLabel1   = (int*) omAlloc((currRing->N+1)*sizeof(int));
      cpTemp->mult1     = (int*) omAlloc((currRing->N+1)*sizeof(int));
      cpTemp->mult2     = (int*) omAlloc((currRing->N+1)*sizeof(int));
    }
  }
  // same critical pair processing for the last element in redGB
  // This is outside of the loop to keep memory low, since we know that after
  // this element no new memory for a critical pair must be allocated.
  // computation of the lcm and the corresponding multipliers for the critical
  // pair generated by the new element and elements of the previous iteration
  // steps, i.e. elements already in redGB
  cpTemp->mLabel1[0]  = cpTemp->mult1[0]  = pGetExp(cpTemp->p1, 0); 
  cpTemp->mult2[0]    = pGetExp(strat->S[strat->sl], 0); 
  critPairDeg         = 0;
  for(j=1; j<=currRing->N; j++)
  {
    temp  = expVecNewElement[j] - f5Rules.label[strat->sl][j];
    if( temp<0 )
    {
      cpTemp->mult1[j]    =   -temp;  
      cpTemp->mult2[j]    =   0; 
      cpTemp->mLabel1[j]  =   rewRules.label[cpTemp->rewRule1][j] - temp;
      critPairDeg         +=  rewRules.label[cpTemp->rewRule1][j] - temp; 
    }
    else
    {
      cpTemp->mult1[j]    =   0;  
      cpTemp->mult2[j]    =   temp;  
      cpTemp->mLabel1[j]  =   rewRules.label[cpTemp->rewRule1][j];
      critPairDeg         +=  rewRules.label[cpTemp->rewRule1][j]; 
    }
  }
  cpTemp->smLabel1 = ~getShortExpVecFromArray(cpTemp->mLabel1);
  
#if F5EDEBUG1
    Print("2nd generator of pair: ");
    pWrite( pHead(strat->S[strat->sl]) );
#endif
  // testing the F5 Criterion
  
  // this is the ggv criterion!
  if( !criterion1(cpTemp->mLabel1, cpTemp->smLabel1, &f5Rules) )
  {
    // completing the construction of the new critical pair and inserting it
    // to the list of critical pairs 
    cpTemp->p2        = strat->S[strat->sl];
    cpTemp->coeff2    = n_Div( pGetCoeff(cpTemp->p1), pGetCoeff(cpTemp->p2), currRing );
    // now we really need the memory for the exp label
    //cpTemp->mLabelExp = (unsigned long*) omAlloc0(NUMVARS*
    //                          sizeof(unsigned long));
    cpTemp->mLabelExp   = pOne();
    getExpFromIntArray( cpTemp->mLabel1, cpTemp->mLabelExp, 
                        numVariables, shift, negBitmaskShifted, offsets
                      );
    insertCritPair(cpTemp, critPairDeg, cpBounds);
  }
  else 
  {
    // we can delete the memory reserved for cpTemp
    omFree( cpTemp->mult1 );
    omFree( cpTemp->mult2 );
    omFree( cpTemp->mLabel1 );
    omFree( cpTemp );
  }
  omFree(expVecNewElement);
#if F5EDEBUG1
  Print("CRITPAIRPREV-END\n");
#endif
}



void criticalPairCurr ( 
  Lpoly* gCurrNew, Lpoly* gCurr, const kStrategy strat, const F5Rules& f5Rules, 
  const RewRules& rewRules, CpairDegBound** cpBounds, int numVariables, 
  int* shift, unsigned long* negBitmaskShifted, int* offsets
                      )
{
#if F5EDEBUG1
  Print("CRITPAIRCURR-BEGINNING\n");
#endif
  int i, j;
  poly mLabelExp;
  // all pairs should be computed if possible as ggv does not do
  // higher label reductions, but computes the pairs again afterwards
  bool pairNeeded       = TRUE;
  int* expVecNewElement = (int*) omAlloc((currRing->N+1)*sizeof(int));
  int* expVecTemp       = (int*) omAlloc((currRing->N+1)*sizeof(int));
  pGetExpV(gCurrNew->p, expVecNewElement); 
  Lpoly* gCurrIter  = gCurr;
  // this must be changed for parallelizing the generation process of critical
  // pairs
  Cpair* cpTemp;
  Cpair* cp         = (Cpair*) omAlloc( sizeof(Cpair) );
  cpTemp            = cp;
  cpTemp->next      = NULL;
  cpTemp->mLabelExp = NULL;
  cpTemp->mLabel1   = NULL;
  cpTemp->smLabel1  = 0;
  cpTemp->mult1     = NULL;
  cpTemp->p1        = gCurrNew->p;
  cpTemp->rewRule1  = gCurrNew->rewRule;
  cpTemp->mLabel2   = NULL;
  cpTemp->smLabel2  = 0;
  cpTemp->mult2     = NULL;

  // we need to alloc memory for the 1st & the 2nd label here
  // both elements are generated during the current iteration step
  cpTemp->mLabel1   = (int*) omAlloc((currRing->N+1)*sizeof(int));
  cpTemp->mLabel2   = (int*) omAlloc((currRing->N+1)*sizeof(int));
  cpTemp->mult1     = (int*) omAlloc((currRing->N+1)*sizeof(int));
  cpTemp->mult2     = (int*) omAlloc((currRing->N+1)*sizeof(int));
  // alloc memory for a temporary (non-integer/SINGULAR internal) exponent vector
  // for fast comparisons at the end which label is greater, those of the 1st or
  // those of the 2nd generator
  // Note: As we do not need the smaller exponent vector we do NOT store both in
  // the critical pair structure, but only the greater one. Thus the following
  // memory is freed before the end of criticalPairCurr()
  poly checkExp = pOne();
  int temp;
  long critPairDeg; // degree of the label of the pair in the following
  while(gCurrIter->next != gCurrNew)
  {
    cpTemp->p2        = gCurrIter->p;
    cpTemp->coeff2    = n_Div( pGetCoeff(cpTemp->p1), pGetCoeff(cpTemp->p2), currRing );
#if F5EDEBUG1
    Print("2nd generator of pair: ");
    pWrite( pHead(cpTemp->p2) );
#endif
    cpTemp->rewRule2  = gCurrIter->rewRule;
    pGetExpV(gCurrIter->p, expVecTemp); 
    // computation of the lcm and the corresponding multipliers for the critical
    // pair generated by the new element and elements of the previous iteration
    // steps, i.e. elements already in redGB
    cpTemp->mLabel1[0]  = cpTemp->mult1[0]  = pGetExp(cpTemp->p1, 0); 
    cpTemp->mLabel2[0]  = cpTemp->mult2[0]  = pGetExp(cpTemp->p2, 0); 
    critPairDeg         = 0;
    for(j=1; j<currRing->N+1; j++)
    {
      temp  = expVecNewElement[j] - expVecTemp[j];
      if(temp<0)
      {
        cpTemp->mult1[j]    =   -temp;  
        cpTemp->mult2[j]    =   0; 
        cpTemp->mLabel1[j]  =   rewRules.label[cpTemp->rewRule1][j] - temp;
        cpTemp->mLabel2[j]  =   rewRules.label[cpTemp->rewRule2][j];
        critPairDeg         +=  rewRules.label[cpTemp->rewRule1][j] - temp; 
      }
      else
      {
        cpTemp->mult1[j]    =   0;  
        cpTemp->mult2[j]    =   temp;  
        cpTemp->mLabel1[j]  =   rewRules.label[cpTemp->rewRule1][j];
        cpTemp->mLabel2[j]  =   rewRules.label[cpTemp->rewRule2][j] + temp;
        critPairDeg         +=  rewRules.label[cpTemp->rewRule1][j]; 
      }
    }
    // compute only if there is a "real" multiple of p1 needed
    // otherwise we can go on with the next element, since the 
    // 2nd generator is a past reducer of p1 which was not allowed
    // to reduce!
    if( pairNeeded )
    {
      cpTemp->smLabel1 = ~getShortExpVecFromArray(cpTemp->mLabel1);
      cpTemp->smLabel2 = ~getShortExpVecFromArray(cpTemp->mLabel2);
      
      // testing the F5 & Rewritten Criterion
      
      // check for equality on labels including the coefficients!!!
      //cpTemp->mLabelExp = (unsigned long*) omAlloc0(NUMVARS*
      //                          sizeof(unsigned long));
      cpTemp->mLabelExp   = pOne();
      getExpFromIntArray( cpTemp->mLabel1, cpTemp->mLabelExp, 
                          numVariables, shift, negBitmaskShifted, offsets
                        );
      getExpFromIntArray( cpTemp->mLabel2, checkExp, numVariables,
                          shift, negBitmaskShifted, offsets
                        );
      int labelEqual = pLmCmp( cpTemp->mLabelExp, checkExp );
      if( ! ( labelEqual == 0 && 
              n_Equal ( pGetCoeff(cpTemp->p1), 
                        pGetCoeff(cpTemp->p2), 
                        currRing ) 
            )   
        )
      {

        // this is the ggv criterion!
        if(  
           !criterion1(cpTemp->mLabel1, cpTemp->smLabel1, &f5Rules) 
           && !criterion1(cpTemp->mLabel2, cpTemp->smLabel2, &f5Rules) 
          ) 
        {
          // completing the construction of the new critical pair and inserting it
          // to the list of critical pairs 
          // now we really need the memory for the exp label
          // compare which label is greater and possibly switch the 1st and 2nd 
          // generator in cpTemp
          // exchange generator 1 and 2 in cpTemp
          if( pLmCmp(cpTemp->mLabelExp, checkExp) == -1 )
          {
            poly pTempHolder                = cpTemp->p1;
            int* mLabelTempHolder           = cpTemp->mLabel1;
            int* multTempHolder             = cpTemp->mult1;
            unsigned long smLabelTempHolder = cpTemp->smLabel1;  
            unsigned long rewRuleTempHolder = cpTemp->rewRule1;
            poly expTempHolder              = cpTemp->mLabelExp;

            cpTemp->coeff2                  = n_Invers( cpTemp->coeff2, currRing);
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
            cpTemp->mLabelExp               = checkExp;
            checkExp                        = expTempHolder;
          }

          insertCritPair(cpTemp, critPairDeg, cpBounds);

          Cpair* cp         = (Cpair*) omAlloc( sizeof(Cpair) );
          cpTemp            = cp;
          cpTemp->next      = NULL;
          cpTemp->mLabelExp = NULL;
          cpTemp->mLabel1   = NULL;
          cpTemp->smLabel1  = 0;
          cpTemp->mult1     = NULL;
          cpTemp->p1        = gCurrNew->p;
          cpTemp->rewRule1  = gCurrNew->rewRule;
          cpTemp->mLabel2   = NULL;
          cpTemp->smLabel2  = 0;
          cpTemp->mult2     = NULL;
          cpTemp->rewRule2  = (gCurrIter->next)->rewRule;
          cpTemp->mLabel1   = (int*) omAlloc((currRing->N+1)*sizeof(int));
          cpTemp->mLabel2   = (int*) omAlloc((currRing->N+1)*sizeof(int));
          cpTemp->mult1     = (int*) omAlloc((currRing->N+1)*sizeof(int));
          cpTemp->mult2     = (int*) omAlloc((currRing->N+1)*sizeof(int));
        }
      }
    }
    gCurrIter   = gCurrIter->next;
  }
  // same critical pair processing for the last element in gCurr
  // This is outside of the loop to keep memory low, since we know that after
  // this element no new memory for a critical pair must be allocated.
  cpTemp->p2  = gCurrIter->p;
  cpTemp->coeff2    = n_Div( pGetCoeff(cpTemp->p1), pGetCoeff(cpTemp->p2), currRing );
#if F5EDEBUG1
  Print("2nd generator of pair: ");
  pWrite( pHead(cpTemp->p2) );
#endif
  pGetExpV(gCurrIter->p, expVecTemp); 
  // computation of the lcm and the corresponding multipliers for the critical
  // pair generated by the new element and elements of the previous iteration
  // steps, i.e. elements already in redGB
  cpTemp->mLabel1[0]  = cpTemp->mult1[0]  = pGetExp(cpTemp->p1, 0); 
  cpTemp->rewRule2    = gCurrIter->rewRule;
  cpTemp->mLabel2[0]  = cpTemp->mult2[0]  = pGetExp(gCurrIter->p, 0); 
  critPairDeg         = 0;
  for(j=1; j<=currRing->N; j++)
  {
    temp  = expVecNewElement[j] - expVecTemp[j];
    if(temp<0)
    {
      cpTemp->mult1[j]    =   -temp;  
      cpTemp->mult2[j]    =   0; 
      cpTemp->mLabel1[j]  =   rewRules.label[cpTemp->rewRule1][j] - temp;
      cpTemp->mLabel2[j]  =   rewRules.label[cpTemp->rewRule2][j];
      critPairDeg         +=  rewRules.label[cpTemp->rewRule1][j] - temp; 
    }
    else
    {
      cpTemp->mult1[j]    =   0;  
      cpTemp->mult2[j]    =   temp;  
      cpTemp->mLabel1[j]  =   rewRules.label[cpTemp->rewRule1][j];
      cpTemp->mLabel2[j]  =   rewRules.label[cpTemp->rewRule2][j] + temp;
      critPairDeg         +=  rewRules.label[cpTemp->rewRule1][j]; 
    }
  }
  if( pairNeeded )
  {
    cpTemp->smLabel1 = ~getShortExpVecFromArray(cpTemp->mLabel1);
    cpTemp->smLabel2 = ~getShortExpVecFromArray(cpTemp->mLabel2);
    
  
    // this is the ggv criterion!
    if(  
        !criterion1(cpTemp->mLabel1, cpTemp->smLabel1, &f5Rules) 
        && !criterion1(cpTemp->mLabel2, cpTemp->smLabel2, &f5Rules) 
      ) 
    {
      // completing the construction of the new critical pair and inserting it
      // to the list of critical pairs 
      // now we really need the memory for the exp label
      //cpTemp->mLabelExp = (unsigned long*) omAlloc0(NUMVARS*
      //                          sizeof(unsigned long));
      cpTemp->mLabelExp = pOne();
      getExpFromIntArray( cpTemp->mLabel1, cpTemp->mLabelExp, 
                          numVariables, shift, negBitmaskShifted, offsets
                        );
      getExpFromIntArray( cpTemp->mLabel2, checkExp, numVariables,
                          shift, negBitmaskShifted, offsets
                        );
      int labelEqual = pLmCmp( cpTemp->mLabelExp, checkExp );
      if( ! ( labelEqual == 0 && 
              n_Equal ( pGetCoeff(cpTemp->p1), 
                        pGetCoeff(cpTemp->p2), 
                        currRing ) 
            )   
        )
      {
        // compare which label is greater and possibly switch the 1st and 2nd 
        // generator in cpTemp
        // exchange generator 1 and 2 in cpTemp
        if( pLmCmp(cpTemp->mLabelExp, checkExp) == -1 )
        {
          poly pTempHolder                = cpTemp->p1;
          int* mLabelTempHolder           = cpTemp->mLabel1;
          int* multTempHolder             = cpTemp->mult1;
          unsigned long smLabelTempHolder = cpTemp->smLabel1;  
          unsigned long rewRuleTempHolder = cpTemp->rewRule1;
          poly expTempHolder              = cpTemp->mLabelExp;

          cpTemp->coeff2                  = n_Invers( cpTemp->coeff2, currRing);
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
          cpTemp->mLabelExp               = checkExp;
          checkExp                        = expTempHolder;
        }
      
        insertCritPair(cpTemp, critPairDeg, cpBounds);
      }
    } 
    else 
    {
      // we can delete the memory reserved for cpTemp
      omFree( cpTemp->mult1 );
      omFree( cpTemp->mult2 );
      omFree( cpTemp->mLabel1 );
      omFree( cpTemp->mLabel2 );
      omFree( cpTemp );
    }
  }
  omFree(checkExp);
  omFree(expVecTemp);
  omFree(expVecNewElement);
#if F5EDEBUG1
  Print("CRITPAIRCURR-END\n");
#endif
}



void insertCritPair( Cpair* cp, long deg, CpairDegBound** bound )
{
  // pointer for deleting critical pairs of the same signature:
  // ggv says: one pair per signature!
  // NOTE that this is not possible in F5 due to the Rewritten Criterion!
  Cpair* tempForDel       = NULL;
#if F5EDEBUG1
  Print("INSERTCRITPAIR-BEGINNING deg bound %p\n",*bound);
#endif
#if F5EDEBUG1
  Print("ADDRESS NEW CRITPAIR: %p -- degree %ld\n",cp, deg);
  pWrite(cp->p1);
  pWrite(cp->p2);
  Print("LABEL NEW PAIR: ");
  pWrite( cp->mLabelExp );
  int j = currRing->N;
    while( j )
    {
      Print("%d ",cp->mLabel1[(currRing->N)-j]);
      j--;
    }
    j = currRing->N;
    Print("\n"); 
#endif
#if F5EDEBUG2
  if( (*bound) ) 
  {
    Print("ADDRESS BOUND CRITPAIR: %p -- deg %ld -- length %d\n",(*bound)->cp,(*bound)->deg, (*bound)->length);
    pWrite( (*bound)->cp->p1 );
  }
#endif
  if( !(*bound) ) // empty list?
  {
    CpairDegBound* boundNew = (CpairDegBound*) omAlloc(sizeof(CpairDegBound));
    boundNew->next          = NULL;
    boundNew->deg           = deg;
    boundNew->cp            = cp;
    boundNew->length        = 1;
    *bound                  = boundNew;
  }
  else
  {
    tempForDel    = (*bound)->cp;
// first element in list has higher label
    if( pLmCmp(cp->mLabelExp, tempForDel->mLabelExp) == -1 )
    {
      cp->next      = (*bound)->cp;
      (*bound)->cp  = cp;
      (*bound)->length++;
    }
    else
    {
      // first element in list has equal label
      if( pLmCmp(cp->mLabelExp, tempForDel->mLabelExp) == 0 )
      {
        // need to check which generating element was generated later
        if( cp->rewRule1 > tempForDel->rewRule1 )
        {
          Cpair* tempDel  = tempForDel;
          cp->next        = tempForDel->next;
          (*bound)->cp    = cp;
          
          omFreeSize( tempDel->mLabel1, ((currRing->N)+1)*sizeof(int) );
          omFreeSize( tempDel->mult1, ((currRing->N)+1)*sizeof(int) );
          omFreeSize( tempDel->mult2, ((currRing->N)+1)*sizeof(int) );
          omFreeSize( tempDel, sizeof(Cpair) );
        }
        else
        {
          // throw away the new critical pair
          // Note that this situation can only happen when a higher label reduction
          // has led to cp and the 2nd generator becomes the new 1st generator!!!
          omFreeSize( cp->mLabel1, ((currRing->N)+1)*sizeof(int) );
          omFreeSize( cp->mult1, ((currRing->N)+1)*sizeof(int) );
          omFreeSize( cp->mult2, ((currRing->N)+1)*sizeof(int) );
          omFreeSize( cp, sizeof(Cpair) );
        }
      }
      else
      {
        // first element in list has smaller label
        while( NULL!=tempForDel->next && pLmCmp(cp->mLabelExp, (tempForDel->next)->mLabelExp) == 1 )
        {
          tempForDel  = tempForDel->next;
        }
        if( !tempForDel->next )
        {
          cp->next          = NULL;
          tempForDel->next  = cp;
        }
        else
        {
          if( pLmCmp(cp->mLabelExp, (tempForDel->next)->mLabelExp) == 0 )
          {
            // need to check which generating element was generated later
            if( cp->rewRule1 > (tempForDel->next)->rewRule1 )
            {
              Cpair* tempDel  = tempForDel->next;
              cp->next =  (tempForDel->next)->next;
              tempForDel->next  = cp;
              omFreeSize( tempDel->mLabel1, ((currRing->N)+1)*sizeof(int) );
              omFreeSize( tempDel->mult1, ((currRing->N)+1)*sizeof(int) );
              omFreeSize( tempDel->mult2, ((currRing->N)+1)*sizeof(int) );
              omFreeSize( tempDel, sizeof(Cpair) );
            }
            else
            {
              // throw away the new critical pair
              // Note that this situation can only happen when a higher label reduction
              // has led to cp and the 2nd generator becomes the new 1st generator!!!
              omFreeSize( cp->mLabel1, ((currRing->N)+1)*sizeof(int) );
              omFreeSize( cp->mult1, ((currRing->N)+1)*sizeof(int) );
              omFreeSize( cp->mult2, ((currRing->N)+1)*sizeof(int) );
              omFreeSize( cp, sizeof(Cpair) );
            }
          }
          else
          {
            if( pLmCmp(cp->mLabelExp, (tempForDel->next)->mLabelExp) == -1 )
            {
              cp->next          = tempForDel->next;
              tempForDel->next  = cp;
            }
          }
        } 
      }
    }
  }
#if F5EDEBUG2
  CpairDegBound* test = *bound;
  Print("-------------------------------------\n");
  while( test )
  {
    Print("DEGREE %d\n",test->deg);
    Cpair* testcp = test->cp;
    while( testcp )
    {
      poly cpSig = pOne();
      for(int lalo=1; lalo<=currRing->N; lalo++)
      {
        pSetExp( cpSig, lalo, testcp->mLabel1[lalo] );
      }
      Print("Pairs: %p\n",testcp);
      pWrite(pHead(testcp->p1));
      pWrite(pHead(testcp->p2));
      Print("Signature: ");
      pWrite( cpSig );
      pDelete( &cpSig );
      testcp = testcp->next;
    }
    test  = test->next;
  }
  Print("-------------------------------------\n");
  Print("INSERTCRITPAIR-END deg bound %p\n",*bound);
#endif
}



inline BOOLEAN criterion1 ( const int* mLabel, const unsigned long smLabel, 
                            const F5Rules* f5Rules
                          )
{
  int i = 0;
  int j = currRing->N;
#if F5EDEBUG1
    Print("CRITERION1-BEGINNING\nTested Element: ");
#endif
#if F5EDEBUG1
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
#if F5EDEBUG2
    Print("F5 Rule: ");
    while( j )
    {
      Print("%d ",f5Rules->label[i][(currRing->N)-j]);
      j--;
    }
    j = currRing->N;
    Print("\n %ld\n", f5Rules->slabel[i]);
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
#if F5EDEBUG1
        Print("CRITERION1-END-DETECTED \n");
#endif
      return TRUE;
    }
  }
#if F5EDEBUG1
  Print("CRITERION1-END \n");
#endif
  return FALSE;
}



inline BOOLEAN newCriterion1 ( const int* mLabel, const unsigned long smLabel, 
                            const F5Rules* f5Rules, const unsigned long stratSize
                          )
{
  int i = 0;
  int j = currRing->N;
#if F5EDEBUG1
  Print("CRITERION1-BEGINNING\nTested Element: ");
#endif
#if F5EDEBUG1
  while( j )
    {
      Print("%d ",mLabel[(currRing->N)-j]);
      j--;
    }
  j = currRing->N;
  Print("\n %ld\n",smLabel);

#endif
  if( f5Rules->size <= stratSize )
    {
      return FALSE;
    }
  else
    {
      i = stratSize;
nextElement:

      for( ; i < f5Rules->size; i++)
        {
#if F5EDEBUG2
          Print("F5 Rule: ");
          while( j )
            {
              Print("%d ",f5Rules->label[i][(currRing->N)-j]);
              j--;
            }
          j = currRing->N;
          Print("\n %ld\n", f5Rules->slabel[i]);
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
#if F5EDEBUG1
              Print("CRITERION1-END-DETECTED \n");
#endif
              return TRUE;
            }
        }
#if F5EDEBUG1
      Print("CRITERION1-END \n");
#endif
      return FALSE;
    }
}



inline BOOLEAN criterion2 ( 
                            const int* mLabel, const unsigned long smLabel, 
                            const RewRules* rewRules, const unsigned long rewRulePos
                          )
{
  unsigned long i   = rewRulePos + 1;
  unsigned long end = rewRules->size;
  int j             = currRing->N;
#if F5EDEBUG1
    Print("CRITERION2-BEGINNING\nTested Element: ");
#endif
#if F5EDEBUG1
    while( j )
    {
      Print("%d ",mLabel[(currRing->N)-j]);
      j--;
    }
    poly pTestRule = pOne();   
    for( int ctr=0; ctr<=currRing->N; ctr++ )
    {
      pSetExp( pTestRule, ctr, mLabel[ctr] );
    }
    j = currRing->N;
    Print("\n %ld\n",smLabel);
    pWrite( pTestRule );
    pDelete( &pTestRule ); 
#endif
  nextElement:
  for( ; i < end; i++)
  {
#if F5EDEBUG1
    Print("Rewrite Rule: ");
    while( j )
    {
      Print("%d ",rewRules->label[i][(currRing->N)-j]);
      j--;
    }
    j = currRing->N;
    Print("\n %ld\n",rewRules->slabel[i]);
#endif
    if(!(smLabel & rewRules->slabel[i]))
    {
      while(j)
      {
        if(mLabel[j] < rewRules->label[i][j])
        {
          j = currRing->N;
          i++;
          goto nextElement;
        }
        j--;
      }
#if F5EDEBUG1
    Print("Rewrite Rule: ");
    j = currRing->N;
    while( j )
    {
      Print("%d ",rewRules->label[i][(currRing->N)-j]);
      j--;
    }
    j = currRing->N;
    Print("\n %ld\n",rewRules->slabel[i]);
        Print("CRITERION2-END-DETECTED \n");
#endif
      return TRUE;
    }
  }
#if F5EDEBUG1
  Print("CRITERION2-END \n");
#endif
  return FALSE;
}



void computeSpols ( 
                    kStrategy strat, CpairDegBound* cp, ideal redGB, Lpoly** gCurr, 
                    F5Rules** f5Rules, RewRules** rewRules, int numVariables, 
                    int* shift, unsigned long* negBitmaskShifted, int* offsets
                  )
{
#if F5EDEBUG1
  Print("COMPUTESPOLS-BEGINNING\n");
#endif
  // check whether a new deg step starts or not
  // needed to keep the synchronization of RewRules list and Spoly list alive
  BOOLEAN start               = TRUE; 
  BOOLEAN newStep             = TRUE; 
  Cpair* temp                 = NULL;
  Cpair* tempDel              = NULL;
  Lpoly** gCurrLast           = (Lpoly**) omAlloc( sizeof(Lpoly*) );
  *gCurrLast                  = *gCurr;
  // rewRulesCurr stores the index of the first rule of the current degree step
  // Note that if there are higher label reductions taking place in currReduction() 
  // one has access to the last actual rewrite rule via rewRules->size.
  unsigned long rewRulesCurr;
  Spoly* spolysLast           = NULL;
  Spoly* spolysFirst          = NULL;
  // start the rewriter rules list with a NULL element for the recent,
  // i.e. initial element in \c gCurr
  //rewRulesLast                = (*gCurr)->rewRule;
  // this will go on for the complete current iteration step!
  // => after computeSpols() terminates this iteration step is done!
  int* multTemp               = (int*) omAlloc0( (currRing->N+1)*sizeof(int) );
  int* multLabelTemp          = (int*) omAlloc0( (currRing->N+1)*sizeof(int) );
  poly sp;
#if F5EDEBUG2
    Print("START OF NEW DEG ROUND: CP %ld | %p -- %p: # %d\n",cp->deg,cp->cp,cp,cp->length);
    Print("NEW CPDEG? %p\n",cp->next);
#endif
    //temp  = sort(cp->cp, cp->length); 
    temp                  = cp->cp;
    //CpairDegBound* cpDel  = cp;
    //cp->cp                = (cp->cp)->next;
    //omFree( cpDel );

    // compute all s-polynomials of this degree step and reduce them
    // w.r.t. redGB as preparation for the current reduction steps 
    while( NULL != temp )
    {
      //Print("Last Element in Rewrules? %p points to %p\n", rewRulesLast, rewRulesLast->next);
#if F5EDEBUG2
      Print("COMPUTING PAIR: %p -- NEXT PAIR %p\n",temp, temp->next);
      pWrite( pHead(temp->p1) );
      pWrite( pHead(temp->p2) );
#endif
      // if the pair is not rewritable add the corresponding rule and 
      // and compute the corresponding s-polynomial (and pre-reduce it
      // w.r.t. redGB

      // no criteria tests in the basic algorithm!
      if( !newCriterion1(temp->mLabel1, temp->smLabel1, *f5Rules, stratSize) ) 
      {
      /*
      if( 
          !criterion2(temp->mLabel1, temp->smLabel1, (*rewRules), temp->rewRule1) &&
          (!temp->mLabel2 || !criterion2(temp->mLabel2, temp->smLabel2, (*rewRules), temp->rewRule2)) 
        )
      {
      */
        if( (*rewRules)->size < rewRulesSize )
        {
#if F5EDEBUG2
          Print("POSITION: %ld/%ld\n",(*rewRules)->size,rewRulesSize);
#endif
          // copy data from critical pair rule to rewRule
          register unsigned long _length  = currRing->N+1;
          register unsigned long _i       = 0;
          register int* _d                = (*rewRules)->label[(*rewRules)->size];
          register int* _s                = temp->mLabel1;
          while( _i<_length )
          {
            _d[_i]  = _s[_i];
            _i++;
          }
          (*rewRules)->slabel[(*rewRules)->size]  = ~temp->smLabel1;
          (*rewRules)->coeff[(*rewRules)->size]   = (*rewRules)->coeff[temp->rewRule1];
          (*rewRules)->size++;
        }
        else
        {
#if F5EDEBUG2
          Print("ALLOC MORE MEMORY -- %p\n", (*rewRules)->label[0]);
#endif
          unsigned int old                = rewRulesSize;
          rewRulesSize                    = 3*rewRulesSize;
          RewRules* newRules              = (RewRules*) omAlloc( sizeof(RewRules) );
          newRules->coeff                 = (number*) omAlloc( rewRulesSize*sizeof(number) );
          newRules->label                 = (int**) omAlloc( rewRulesSize*sizeof(int*) );
          newRules->slabel                = (unsigned long*)omAlloc( rewRulesSize*sizeof(unsigned long) );
          newRules->size                  = (*rewRules)->size;
          register unsigned long _length  = currRing->N+1;
          register unsigned long ctr      = 0;
          for( ; ctr<old; ctr++ )
          {
            newRules->coeff[ctr]      = (*rewRules)->coeff[ctr];
            newRules->label[ctr]      = (int*) omAlloc( (currRing->N+1)*sizeof(int) );
            register unsigned long _i = 0;
            register int* _d          = newRules->label[ctr];
            register int* _s          = (*rewRules)->label[ctr];
            while( _i<_length )
            {
              _d[_i]  = _s[_i]; 
              _i++;
            }
            omFreeSize( (*rewRules)->label[ctr], (currRing->N+1)*sizeof(int) );
            newRules->slabel[ctr] = (*rewRules)->slabel[ctr];
          }
          omFreeSize( (*rewRules)->slabel, old*sizeof(unsigned long) );
          for( ; ctr<rewRulesSize; ctr++ )
          {
            newRules->label[ctr] =  (int*) omAlloc( (currRing->N+1)*sizeof(int) );
          }
          omFreeSize( (*rewRules), sizeof(RewRules) );
          (*rewRules)  = newRules;
#if F5EDEBUG2
          Print("MEMORY ALLOCATED -- %p\n", (*rewRules)->label[0]);
#endif
          // now we can go on adding the new rule to rewRules
  
          // copy data from critical pair rule to rewRule
          register unsigned long _i = 0;
          register int* _d          = (*rewRules)->label[(*rewRules)->size];
          register int* _s          = temp->mLabel1;
          while( _i<_length )
          {
            _d[_i]  = _s[_i];
            _i++;
          }
          (*rewRules)->slabel[(*rewRules)->size]  = ~temp->smLabel1;
          (*rewRules)->coeff[(*rewRules)->size]   = (*rewRules)->coeff[temp->rewRule1];
          (*rewRules)->size++;

        } 
#if F5EDEBUG1
        Print("RULE #%d: ",(*rewRules)->size);
        for( int _l=0; _l<currRing->N+1; _l++ )
        {
          Print("%d  ",(*rewRules)->label[(*rewRules)->size-1][_l]);
        }
        Print("\n-------------------------------------\n");
#endif
        // from this point on, rewRulesLast != NULL, thus we do not need to test this
        // again in the following iteration over the list of critical pairs
        
#if F5EDEBUG1
        Print("CRITICAL PAIR BEFORE S-SPOLY COMPUTATION:\n");
        Print("%p\n",temp);
        Print("GEN1: %p\n",temp->p1);
        pWrite(pHead(temp->p1));
        pTest(temp->p1);
        Print("GEN2: %p\n",temp->p2);
        pWrite(pHead(temp->p2));
        pTest(temp->p2);
        int ctr = 0;
        poly pTestRule  = pOne();
        for( ctr=0; ctr<=currRing->N; ctr++ )
        {
          Print("%d ",temp->mLabel1[ctr]);
          pSetExp( pTestRule, ctr, temp->mLabel1[ctr] );
          
        }
        Print("\n");
        pWrite( pTestRule );
        pDelete( &pTestRule );
#endif
        // save current position of rewrite rules in array to synchronize them at the end of
        // currReduction() with the corresponding labeled polynomial
        rewRulesCurr  = (*rewRules)->size-1;

        // check if the critical pair is a trivial one, i.e. a pair generated 
        // during a higher label reduction 
        // => p1 is already the s-polynomial reduced w.r.t. redGB and we do not 
        // need to reduce and/or compute anything
        if( temp->p2 )
        { 
          // compute s-polynomial and reduce it w.r.t. redGB
          sp  = reduceByRedGBCritPair ( 
                                        temp, strat, numVariables, shift, 
                                        negBitmaskShifted, offsets 
                                      );
        }
        else
        {
          sp = temp->p1;
        }
#if F5EDEBUG2
        Print("AFTER REDUCTION W.R.T. REDGB -- %p\n", sp);
        pWrite( sp );
        pTest(sp);
#endif
        number1Reductions++;
        if( sp )
        {
          // all rules and s-polynomials of this degree step are computed and 
          // prepared for further reductions in currReduction()
          currReduction ( 
              strat, sp, temp->mLabelExp, rewRules, rewRulesCurr, 
              redGB, &cp, *gCurr, gCurrLast, f5Rules, multTemp, multLabelTemp, 
              numVariables, shift, negBitmaskShifted, offsets
              );
        }
        else // sp == 0
        {
          pDelete( &sp );
        }
      }
      else
      {
        //  free memory of mLabel1 which would have been the corresponding
        //  rewrite rule, but which was detected by one of F5's criteria
        omFree( temp->mLabel1 );
      }
      // free memory
      tempDel  = temp;
      cp->cp  = (cp->cp)->next;
      temp = (cp->cp);
      //if( cp->cp )
      //{
      //  temp     = cp->cp;
      //}
      // note that this has no influence on the address of temp->label!
      // its memory was allocated at a different place and we still need these:
      // those are just the rewrite rules for the newly computed elements!
      omFree( tempDel->mult1 );
      omFree( tempDel->mult2 );
      // (a) mLabel1 is the corresponding rewrite rule! If the rewrite rule was detected
      //     by F5's criteria than mLabel1 is deleted in the above else branch!
      // (b) mlabel2 is possibly NULL if the 2nd generator is from a 
      //     previous iteration step, i.e. already in redGB
      if( tempDel->mLabel2 )
      {
        omFree( tempDel->mLabel2 );
      }
      omFree( tempDel );
    }
    // elements are added to linked list gCurr => start next degree step
    spolysFirst = spolysLast  = NULL;
    newStep     = TRUE; 
#if F5EDEBUG2
    Print("DEGREE STEP DONE:\n------\n");
    Lpoly* gCurrTemp = *gCurr;
    while( gCurrTemp )
    {
      pWrite( pHead(gCurrTemp->p) );
      gCurrTemp = gCurrTemp->next;
    }
    Print("-------\n");
#endif
  // get back the new list of elements in gCurr, i.e. the list of elements
  // computed in this iteration step
#if F5EDEBUG1
  Print("ITERATION STEP DONE: \n");
  Lpoly* gCurrTemp2 = *gCurr;
  while( gCurrTemp2 )
  {
    pWrite( pHead(gCurrTemp2->p) );
    gCurrTemp2 = gCurrTemp2->next;
  }
  Print("COMPUTESPOLS-END\n");
    Print("HERE1 -- %p -- %p\n", (*rewRules), (*rewRules)->label[0]);
#endif
  // free memory
  omFree( multTemp );
  omFree( multLabelTemp );
  // the following is false as we use arrays for rewRules right now which will be 
  // deleted in f5cIter(), similar to f5Rules
  /*
  RewRules* tempRule;
  while( rewRulesFirst )
  {
    tempRule      = rewRulesFirst;
    rewRulesFirst = rewRulesFirst->next;
    omFree( tempRule->label );
    omFree( tempRule );
  }
  */
}

/////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////
// here should computeSpols stop
/////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////



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



void currReduction  ( 
                      kStrategy strat, poly sp, poly spLabelExp,
                      RewRules** rewRulesP, unsigned long rewRulesCurr,
                      ideal redGB, CpairDegBound** cp, Lpoly* gCurrFirst, 
                      Lpoly** gCurrLast,
                      F5Rules** f5RulesP, int* multTemp, 
                      int* multLabelTemp, int numVariables, int* shift, 
                      unsigned long* negBitmaskShifted, int* offsets
                    )

{
#if F5EDEBUG1
    Print("CURRREDUCTION-BEGINNING: GCURR %p -- %p\n",gCurrFirst, (gCurrFirst)->next);
#endif
  RewRules* rewRules  = *rewRulesP;
  F5Rules* f5Rules    = *f5RulesP;
  BOOLEAN isMult      = FALSE;
  BOOLEAN superTop    = FALSE;
  // check needed to ensure termination of F5 (see F5+)
  // this will be added to all new labeled polynomials to check
  // when to terminate the algorithm
  BOOLEAN redundant = FALSE;
  int i;
  unsigned long multLabelShortExp;
  static int tempLength           = 0;
  number multCoeff1, multCoeff2;
  unsigned short int canonicalize = 0; 
  Lpoly* temp;
  unsigned long bucketExp;
#if F5EDEBUG2
  Print("LIST OF SPOLYS TO BE REDUCED: \n---------------\n");
    Print("%p -- ",sp);
    pWrite( pHead(sp) );
    Print("RULE #%d of %ld -- ",rewRulesCurr, rewRules->size);
    for( int _l=0; _l<currRing->N+1; _l++ )
    {
      Print("%d  ",rewRules->label[rewRulesCurr][_l]);
    }
    Print("\n-------------------------------------\n");
  Print("---------------\n");
#endif
  // iterate over all elements in the s-polynomial list
  startComplete:
#if F5EDEBUG1
    Print("SPTEMP TO BE REDUCED: %p : %p -- ", sp, sp );
    pWrite( pHead(sp) );
    Print("RULE #%d of %ld -- ",rewRulesCurr, rewRules->size);
    for( int _l=0; _l<currRing->N+1; _l++ )
    {
      Print("%d  ",rewRules->label[rewRulesCurr][_l]);
    }
    Print("\n-------------------------------------\n");
#endif
    kBucket* bucket                 = kBucketCreate();
    kBucketInit( bucket, sp, pLength(sp) );
    temp  = gCurrFirst;
    //----------------------------------------
    // reduction of the leading monomial of sp
    //----------------------------------------
    // Note that we need to make this top reduction explicit to be able to decide
    // if the returned polynomial is redundant or not!
    // search for reducers in the list gCurr
    redundant  = FALSE;
    while ( temp )
    {
      startagainTop:
      bucketExp = ~( pGetShortExpVector(kBucketGetLm(bucket)) );
#if F5EDEBUG2
      Print("TO BE REDUCED: ");
      pWrite( kBucketGetLm(bucket) );
      Print("POSSIBLE REDUCER %p ",temp->p);
      pTest( temp->p );
      pWrite(pHead(temp->p));
#endif
      // loop over elements of lower index, i.e. elements in strat
      for( int ctr=0; ctr<IDELEMS(redGB); ctr++ )
      {
        if( isDivisibleGetMult( redGB->m[ctr], f5Rules->slabel[ctr], kBucketGetLm( bucket ), 
              bucketExp, &multTemp, &isMult
              ) 
          )
        {
          multCoeff1          = pGetCoeff( kBucketGetLm(bucket) );
          multCoeff2          = pGetCoeff( redGB->m[ctr] );
          multCoeff2          = n_Div( multCoeff1, multCoeff2, currRing );

          static poly multiplier = pOne();
          static poly multReducer;
          getExpFromIntArray( multTemp, multiplier, numVariables, shift, 
              negBitmaskShifted, offsets
              );
          // throw away the leading monomials of reducer and bucket
          p_SetCoeff( multiplier, multCoeff2, currRing );
          pSetm( multiplier );
          //p_SetCoeff( multiplier, pGetCoeff(kBucketGetLm(bucket)), currRing );
          kBucketExtractLm(bucket);
          // build the multiplied reducer (note that we do not need the leading
          // term at all!
#if F5EDEBUG2
          Print("MULT: %p\n", multiplier );
          pWrite( multiplier );
#endif
          multReducer = pp_Mult_mm( redGB->m[ctr]->next, multiplier, currRing );
#if F5EDEBUG2
          Print("MULTRED BEFORE: \n" );
          pWrite( pHead(multReducer) );
#endif
#if F5EDEBUG2
          Print("MULTRED AFTER: \n" );
          pWrite( pHead(multReducer) );
#endif
          //  length must be computed after the reduction with 
          //  redGB!
          tempLength = pLength( multReducer );
          // reduce polynomial
          kBucket_Add_q( bucket, pNeg(multReducer), &tempLength ); 
          numberReductions++;
#if F5EDEBUG2
          Print("AFTER REDUCTION STEP: ");
          pWrite( kBucketGetLm(bucket) );
#endif
          if( canonicalize++ % 40 )
          {
            kBucketCanonicalize( bucket );
            canonicalize = 0;
          }
          superTop  = FALSE;
          isMult    = FALSE;
          redundant = FALSE;
          if( kBucketGetLm( bucket ) )
          {
            temp  = gCurrFirst;
          }
          else
          {
            sp = NULL;
            goto kBucketLmZero;
          }
          goto startagainTop;

        }
      }
        if( isDivisibleGetMult( temp->p, temp->sExp, kBucketGetLm( bucket ), 
              bucketExp, &multTemp, &isMult
              ) 
          )
        {
          redundant = TRUE;
          // if isMult => lm(sp) > lm(temp->p) => we need to multiply temp->p by 
          // multTemp and check this multiple by both criteria
#if F5EDEBUG1
          Print("ISMULT %d\n",isMult);
#endif
          if( isMult )
          {
            // compute the multiple of the rule of temp & multTemp
            for( i=1;i<(currRing->N)+1; i++ )
            {
              multLabelTemp[i]  = multTemp[i] + rewRules->label[temp->rewRule][i];
            }
            multLabelTemp[0]    = rewRules->label[temp->rewRule][0];
            multLabelShortExp   = ~getShortExpVecFromArray( multLabelTemp );
            multCoeff1          = pGetCoeff( kBucketGetLm(bucket) );
            multCoeff2          = pGetCoeff( temp->p );
            multCoeff2          = n_Div( multCoeff1, multCoeff2, currRing );
            // test the multiplied label by both criteria 

            // no criteria tests for the basic algorithm
            /*
               if( !criterion1( multLabelTemp, multLabelShortExp, f5Rules, strat ) && 
               !criterion2( multLabelTemp, multLabelShortExp, rewRules, temp->rewRule )
               )
               { 
             */
            static unsigned long* multTempExp = (unsigned long*) 
              omAlloc0( NUMVARS*sizeof(unsigned long) );
            poly multLabelTempExp = pOne();
            getExpFromIntArray( multLabelTemp, multLabelTempExp, numVariables,
                shift, negBitmaskShifted, offsets
                );   
            // if a higher label reduction takes place we need to create
            // a new Lpoly with the higher label and store it in a different 
            // linked list for later reductions

            // in the basic algorithm we do not execute higher label reductions at all!
            if( pLmCmp( multLabelTempExp, spLabelExp ) == 1 )
            {            
              /*
#if F5EDEBUG1
Print("HIGHER LABEL REDUCTION \n");
#endif
poly newPoly  = pInit();
int length;
int cano            = kBucketCanonicalize( bucket );
kBucket* newBucket  = kBucketCreate();
kBucketInit ( newBucket, pCopy(bucket->buckets[cano]), 
bucket->buckets_length[cano] 
);
static poly multiplier = pOne();
getExpFromIntArray( multTemp, multiplier->exp, numVariables, shift, 
negBitmaskShifted, offsets
);
              // throw away the leading monomials of reducer and bucket
              pSetm( multiplier );
              p_SetCoeff( multiplier, pGetCoeff(kBucketGetLm(newBucket)), currRing );
              tempLength = pLength( temp->p->next );
              kBucketExtractLm(newBucket);
#if F5EDEBUG2
Print("MULTIPLIER: ");
pWrite(multiplier);
Print("REDUCER: ");
pWrite( pHead(temp->p) );
#endif
kBucket_Minus_m_Mult_p( newBucket, multiplier, temp->p->next, 
&tempLength 
); 
              // get monomials out of bucket and save the poly as first generator 
              // of a new critical pair
              int length2 = 0;
              // write bucket to poly & destroy bucket
              kBucketClear( newBucket, &newPoly, &length2 );
              kBucketDeleteAndDestroy( &newBucket );

              newPoly = reduceByRedGBPoly( newPoly, strat );

              // add the new rule even when newPoly is zero!
              // Note that we possibly need more memory in this iteration step!
#if F5EDEBUG2
Print("SIZES BEFORE: %ld < %ld ?\n",rewRules->size, rewRulesSize);
Print("ADDRESS: %p\n", rewRules->label[0]);
#endif
              // get the corresponding offsets for the insertion of the element in the two lists:
              Spoly* tempSpoly            = spTemp;
              if( rewRules->size<rewRulesSize )
              {
              // add element at the end 
              if( expCmp( multLabelTempExp, spolysLast->labelExp ) == 1 )
              {
              // copy data from critical pair rule to rewRule
              register unsigned long _length  = currRing->N+1;
              register unsigned long _i       = 0;
              register int* _d                = rewRules->label[rewRules->size];
              register int* _s                = multLabelTemp;
              while( _i<_length )
              {
              _d[_i]  = _s[_i];
              _i++;
              }
              rewRules->slabel[rewRules->size]  = ~multLabelShortExp;
              rewRules->size++;
              tempSpoly = spolysLast;
              }
              // search list for the place where to insert this element
              // note that we know that it is smaller than the last element w.r.t. labels
              else
              { 
              unsigned long insertOffset  = 0;
              while( tempSpoly->next && expCmp(multLabelTempExp, tempSpoly->next->labelExp) == 1 )
              {
                insertOffset++;
                tempSpoly = tempSpoly->next;
              }
              // insert rule after position rewRulesCurr+offset
              // insert poly after tempSpoly
              register unsigned long _length  = currRing->N+1;
              register unsigned long _ctr     = rewRules->size-1;
              for( ; _ctr>rewRulesCurr+insertOffset; _ctr-- )
              { 
                register unsigned long _i       = 0;
                register int* _d                = rewRules->label[_ctr+1];
                register int* _s                = rewRules->label[_ctr];
                _i = 0;
                while( _i<_length )
                {
                  _d[_i]  = _s[_i];
                  _i++;
                }
                rewRules->slabel[_ctr+1] = rewRules->slabel[_ctr];
              }
              register unsigned long _i       = 0;
              register int* _d                = rewRules->label[rewRulesCurr+insertOffset+1];
              register int* _s                = multLabelTemp;
              while( _i<_length )
              {
                _d[_i]  = _s[_i];
                _i++;
              }
              rewRules->slabel[rewRulesCurr+insertOffset+1]  = ~multLabelShortExp;
              rewRules->size++;
            }
            }
              else
              {
#if F5EDEBUG1
                Print("ALLOC MORE MEMORYi -- %p\n", rewRules->label[0]);
#endif
                unsigned int old                = rewRulesSize;
                rewRulesSize                    = 3*rewRulesSize;
                RewRules* newRules              = (RewRules*) omAlloc( sizeof(RewRules) );
                newRules->label                 = (int**) omAlloc( rewRulesSize*sizeof(int*) );
                newRules->slabel                = (unsigned long*)omAlloc( rewRulesSize*sizeof(unsigned long) );
                newRules->size                  = rewRules->size;

                // add element at the end 
                if( expCmp( multLabelTempExp, spolysLast->labelExp ) == 1 )
                {
                  register unsigned long _length  = currRing->N+1;
                  register unsigned long _ctr      = 0;
                  for( ; _ctr<old; _ctr++ )
                  {
                    newRules->label[_ctr]     =  (int*) omAlloc( (currRing->N+1)*sizeof(int) );
                    register unsigned long _i = 0;
                    register int* _d          = newRules->label[_ctr];
                    register int* _s          = rewRules->label[_ctr];
                    while( _i<_length )
                    {
                      _d[_i]  = _s[_i];
                      _i++;
                    }
                    omFreeSize( rewRules->label[_ctr], (currRing->N+1)*sizeof(int) );
                    newRules->slabel[_ctr] = rewRules->slabel[_ctr];
                  }
                  omFreeSize( rewRules->slabel, old*sizeof(unsigned long) );
                  for( ; _ctr<rewRulesSize; _ctr++ )
                  {
                    newRules->label[_ctr] =  (int*) omAlloc( (currRing->N+1)*sizeof(int) );
                  }
                  omFreeSize( rewRules, sizeof(RewRules) );
                  *rewRulesP  = rewRules  = newRules;
                  tempSpoly   = spolysLast;
                  // now we can go on adding the new rule to rewRules

                  // copy data from rule corresponding to new s-polynomial to rewRule
                  register unsigned long _i = 0;
                  register int* _d          = rewRules->label[rewRules->size];
                  register int* _s          = multLabelTemp;
                  while( _i<_length )
                  {
                    _d[_i]  = _s[_i];
                    _i++;
                  }
                  rewRules->slabel[rewRules->size]  = ~multLabelShortExp;
                  rewRules->size++;

                }
                else
                {
                  // alloc more memory
                  register unsigned long _length  = currRing->N+1;
                  register unsigned long _ctr     = 0;
                  unsigned long insertOffset      = 0;
                  while( tempSpoly->next && expCmp(multLabelTempExp, tempSpoly->next->labelExp) == 1 )
                  {
                    insertOffset++;
                    tempSpoly = tempSpoly->next;
                  }
                  // insert rule after position rewRulesCurr+offset
                  // insert poly after tempSpoly
                  _ctr      = 0;
                  for( ; _ctr<rewRulesCurr+insertOffset+1 ; _ctr++ )
                  {
                    newRules->label[_ctr]     =  (int*) omAlloc( (currRing->N+1)*sizeof(int) );
                    register unsigned long _i = 0;
                    register int* _d          = newRules->label[_ctr];
                    register int* _s          = rewRules->label[_ctr];
                    while( _i<_length )
                    {
                      _d[_i]  = _s[_i];
                      _i++;
                    }
                    omFreeSize( rewRules->label[_ctr], (currRing->N+1)*sizeof(int) );
                    newRules->slabel[_ctr] = rewRules->slabel[_ctr];
                  }
                  // _ctr = rewRulesCurr+insertOffset+1 !
                  newRules->label[_ctr]     =  (int*) omAlloc( (currRing->N+1)*sizeof(int) );
                  register unsigned long _i = 0;
                  register int* _d          = newRules->label[_ctr];
                  register int* _s          = multLabelTemp;
                  while( _i<_length )
                  {
                    _d[_i]  = _s[_i];
                    _i++;
                  }
                  newRules->slabel[_ctr]  = ~multLabelShortExp;
                  newRules->size++;

                  for( ; _ctr<old; _ctr++ )
                  {
                    newRules->label[_ctr+1]   =  (int*) omAlloc( (currRing->N+1)*sizeof(int) );
                    register unsigned long _i = 0;
                    register int* _d          = newRules->label[_ctr+1];
                    register int* _s          = rewRules->label[_ctr];
                    while( _i<_length )
                    {
                      _d[_i]  = _s[_i];
                      _i++;
                    }
                    omFreeSize( rewRules->label[_ctr], (currRing->N+1)*sizeof(int) );
                    newRules->slabel[_ctr+1] = rewRules->slabel[_ctr];
                  }
                  _ctr++;
                  // _ctr is now bigger than all elements => add more memory for further 
                  // rules.
                  // NOTE that we have to increment _ctr as we have added a new element in the
                  // list. In the last for-loop we have allocated memory for _ctr+1, so need to 
                  // add 1 to _ctr, before allocating more memory as we would overwrite data
                  // otherwise!
                  for( ; _ctr<rewRulesSize; _ctr++ )
                  {
                    newRules->label[_ctr] =  (int*) omAlloc( (currRing->N+1)*sizeof(int) );
                  }

                  omFreeSize( rewRules->slabel, old*sizeof(unsigned long) );
                  omFreeSize( rewRules, sizeof(RewRules) );
                  *rewRulesP  = rewRules  = newRules;
                  //tempSpoly   = spolysLast;
                }
#if F5EDEBUG2
                Print("MEMORY ALLOCATED -- %p\n", rewRules->label[0]);
#endif
              } 
              // insert the new element at the right position, i.e. at the
              // end of the list of spolynomials

              if( NULL != newPoly )
              {
                pNorm( newPoly );
              }
              // even if newPoly = 0 we need to add it to the list of s-polynomials
              // to keep it with the list of rew rules synchronized!
              Spoly* spNew      = (Spoly*) omAlloc( sizeof(struct Spoly) );
              spNew->p          = newPoly;
              spNew->labelExp   = multLabelTempExp;
              spNew->next       = tempSpoly->next;
              tempSpoly->next   = spNew;
              tempSpoly         = spNew;
#if F5EDEBUG2
              Print("SIZES AFTER: %ld < %ld ?\n",rewRules->size, rewRulesSize);
              Print("LIST OF SPOLYS TO BE REDUCED: \n---------------\n");
              Spoly* lalasp = spTemp;
              unsigned long rewRulesTemp  = rewRulesCurr;
              while( lalasp )
              {
                Print("%p -- ",lalasp->p);
                pWrite( pHead(lalasp->p) );
                lalasp = lalasp->next;
                Print("RULE #%d of %ld -- ",rewRulesTemp, rewRules->size);
                for( int _l=0; _l<currRing->N+1; _l++ )
                {
                  Print("%d  ",rewRules->label[rewRulesTemp][_l]);
                }
                Print("\n-------------------------------------\n");
                rewRulesTemp++;
              }
              Print("---------------\n");
              lalasp = spolysFirst;
#endif
#if F5EDEBUG1
              Print("ADDED TO LIST OF SPOLYS TO BE REDUCED: \n---------------\n");
              pWrite( pHead(newPoly) );
              Print("---------------\n");
#endif
              */ // end of basic algorithm stuff!

                // get back on track for the old poly which has to be checked for 
                // reductions by the following element in gCurr
                isMult    = FALSE;
              redundant = TRUE;
              temp      = temp->next;
              if( temp )
              {
                goto startagainTop;
              }
              else
              {
                break;
              }
            }
            else
            {
              // this is the ggv criterion:
              // the element to be reduced as well as the multiplied reducer have
              // the same leading monomial as polynomials & the same leading 
              // monomial as labels
              // => check the coefficients of the labels! 
              if( pLmCmp( multLabelTempExp, spLabelExp ) == 0 )
              { 
                // SUPER TOP REDUCTION IN GGV
                if( 
                    n_Equal ( pGetCoeff(kBucketGetLm(bucket)), 
                      pGetCoeff(temp->p), 
                      currRing ) 
                  )
                {
                  superTop  = TRUE;
                  temp      = temp->next;
                  if( temp )
                  {
                    goto startagainTop;
                  }
                  else
                  {
                    break;
                  }
                  /*
                     if( spTemp->next )
                     {
                     spTemp  = spTemp->next;
                     pDelete( &spTemp->p );
                     omFreeSize( spDel, sizeof(Spoly) );
                     Print("here4\n");
                     goto startComplete;
                     }
                     else
                     {
                     pDelete( &spDel->p );
                     omFreeSize( spDel, sizeof(Spoly) );
                     }
                   */
                }
                // leading monomials of signatures are equal, but leading 
                // coefficients are different!
                else
                {
                  // else we can go on and reduce sp
                  // The multiplied reducer will be reduced w.r.t. strat before the 
                  // bucket reduction starts!

                  // NOTE that we have to adjust the coefficient of the corresponding rule
                  // due to ggv rules!
                  static poly multiplier = pOne();
                  static poly multReducer;
                  getExpFromIntArray( multTemp, multiplier, numVariables, shift, 
                      negBitmaskShifted, offsets
                      );
                  // throw away the leading monomials of reducer and bucket
                  p_SetCoeff( multiplier, multCoeff2, currRing );
                  pSetm( multiplier );
                  //p_SetCoeff( multiplier, pGetCoeff(kBucketGetLm(bucket)), currRing );
                  kBucketExtractLm(bucket);
                  // build the multiplied reducer (note that we do not need the leading
                  // term at all!
#if F5EDEBUG2
                  Print("MULT: %p\n", multiplier );
                  pWrite( multiplier );
#endif
                  multReducer = pp_Mult_mm( temp->p->next, multiplier, currRing );
#if F5EDEBUG2
                  Print("MULTRED BEFORE: \n" );
                  pWrite( pHead(multReducer) );
#endif
                  //multReducer = reduceByRedGBPoly( multReducer, strat );
#if F5EDEBUG2
                  Print("MULTRED AFTER: \n" );
                  pWrite( pHead(multReducer) );
#endif
                  //  length must be computed after the reduction with 
                  //  redGB!
                  tempLength = pLength( multReducer );
                  // reduce polynomial
                  kBucket_Add_q( bucket, pNeg(multReducer), &tempLength ); 
                  numberReductions++;
                  // adjust the coefficient of the signature
                  // compute 1 / (1-multCoeff2)
                  number shifter =  n_Sub ( 
                      nInit(1), 
                      multCoeff2, 
                      currRing);                
                  shifter = n_Invers( shifter, currRing );
                  // multiply spTemp->p with shifter
                  kBucket_Mult_n( bucket, shifter);
#if F5EDEBUG2
                  Print("AFTER REDUCTION STEP: ");
                  pWrite( kBucketGetLm(bucket) );
#endif
                  if( canonicalize++ % 40 )
                  {
                    kBucketCanonicalize( bucket );
                    canonicalize = 0;
                  }
                  superTop  = FALSE;
                  isMult    = FALSE;
                  redundant = FALSE;
                  if( kBucketGetLm( bucket ) )
                  {
                    temp  = gCurrFirst;
                  }
                  else
                  {
                    break;
                  }
                  goto startagainTop;

                }
              }
              else
              {
                // else we can go on and reduce sp
                // The multiplied reducer will be reduced w.r.t. strat before the 
                // bucket reduction starts!
                static poly multiplier = pOne();
                static poly multReducer;
                getExpFromIntArray( multTemp, multiplier, numVariables, shift, 
                    negBitmaskShifted, offsets
                    );
                // throw away the leading monomials of reducer and bucket
                p_SetCoeff( multiplier, multCoeff2, currRing );
                pSetm( multiplier );
                //p_SetCoeff( multiplier, pGetCoeff(kBucketGetLm(bucket)), currRing );
                kBucketExtractLm(bucket);
                // build the multiplied reducer (note that we do not need the leading
                // term at all!
#if F5EDEBUG2
                Print("MULT: %p\n", multiplier );
                pWrite( multiplier );
#endif
                multReducer = pp_Mult_mm( temp->p->next, multiplier, currRing );
#if F5EDEBUG2
                Print("MULTRED BEFORE: \n" );
                pWrite( pHead(multReducer) );
#endif
                //multReducer = reduceByRedGBPoly( multReducer, strat );
#if F5EDEBUG2
                Print("MULTRED AFTER: \n" );
                pWrite( pHead(multReducer) );
#endif
                //  length must be computed after the reduction with 
                //  redGB!
                tempLength = pLength( multReducer );
                // reduce polynomial
                kBucket_Add_q( bucket, pNeg(multReducer), &tempLength ); 
                numberReductions++;
#if F5EDEBUG2
                Print("AFTER REDUCTION STEP: ");
                pWrite( kBucketGetLm(bucket) );
#endif
                if( canonicalize++ % 40 )
                {
                  kBucketCanonicalize( bucket );
                  canonicalize = 0;
                }
                superTop  = FALSE;
                isMult    = FALSE;
                redundant = FALSE;
                if( kBucketGetLm( bucket ) )
                {
                  temp  = gCurrFirst;
                }
                else
                {
                  break;
                }
                goto startagainTop;

              }
            }
          }
          // isMult = 0 => multTemp = 1 => we do not need to test temp->p by any
          // criterion again => go on with reduction steps
               else
               {
                 multCoeff1          = pGetCoeff( kBucketGetLm(bucket) );
                 multCoeff2          = pGetCoeff( temp->p );
                 multCoeff2          = n_Div( multCoeff1, multCoeff2, currRing );
                 static poly tempNeg  = pInit();
                 // throw away the leading monomials of reducer and bucket
                 tempNeg       = pCopy( temp->p );
                 tempLength    = pLength( tempNeg->next );
                 p_Mult_nn( tempNeg, multCoeff2, currRing );
                 pSetm( tempNeg );
                 kBucketExtractLm( bucket );
#if F5EDEBUG2
                 Print("REDUCTION WITH: ");
                 pWrite( temp->p );
#endif
                 kBucket_Add_q( bucket, pNeg(tempNeg->next), &tempLength ); 
                 numberReductions++;
#if F5EDEBUG2
                 Print("AFTER REDUCTION STEP: ");
                 pWrite( kBucketGetLm(bucket) );
#endif
                 if( canonicalize++ % 40 )
                 {
                   kBucketCanonicalize( bucket );
                   canonicalize = 0;
                 }
                 superTop  = FALSE;
                 redundant = FALSE;
                 if( kBucketGetLm( bucket ) )
                 {
                   temp  = gCurrFirst;
                 }
                 else
                 {
                   break;
                 }
                 goto startagainTop;
               } 
          }
          temp  = temp->next;
        }
      // we know that sp = 0 at this point!
      sp  = kBucketExtractLm( bucket );
#if F5EDEBUG1
      Print("END OF TOP REDUCTION:  ");
      pWrite(kBucketGetLm(bucket));
#endif
#if F5EDEBUG3
      pTest( sp );
#endif
      // tail reduction
#if F5ETAILREDUCTION
      while ( kBucketGetLm( bucket ) )
      {
        // search for reducers in the list gCurr
        temp = gCurrFirst;
        while ( temp )
        {
startagainTail:
          bucketExp = ~( pGetShortExpVector(kBucketGetLm(bucket)) );
#if F5EDEBUG3
          Print("HERE TAILREDUCTION AGAIN %p -- %p\n",temp, temp->next);
          Print("SPOLY RIGHT NOW: ");
          pWrite( sp );
          Print("POSSIBLE REDUCER: ");
          pWrite( temp->p );
          Print("BUCKET LM: ");
          pWrite( kBucketGetLm(bucket) );
          pTest( sp );
#endif
          if( isDivisibleGetMult( 
                temp->p, temp->sExp, kBucketGetLm( bucket ), 
                bucketExp, &multTemp, &isMult
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
                multLabelTemp[i]  = multTemp[i] + rewRules->label[temp->rewRule][i];
              }

              multLabelShortExp  = getShortExpVecFromArray( multLabelTemp );

              // test the multiplied label by both criteria 

              // no criteria tests for the basic algorithm!
              /*
                 if( !criterion1( multLabelTemp, multLabelShortExp, f5Rules, strat ) && 
                 !criterion2( multLabelTemp, multLabelShortExp, rewRules, temp->rewRule )
                 )
                 { 
                 */ 
              poly multTempExp = pOne();
              poly multLabelTempExp = pOne();

              getExpFromIntArray( multLabelTemp, multLabelTempExp, numVariables,
                  shift, negBitmaskShifted, offsets
                  );   

              // if a higher label reduction should be done we do NOT reduce at all
              // we want to be fast in the tail reduction part
              if( pLmCmp( multLabelTempExp, spLabelExp ) == 1 )
              {            
                isMult    = FALSE;
                redundant = TRUE;
                temp      = temp->next;
                if( temp )
                {
                  goto startagainTail;
                }
                else
                {
                  break;
                }
              }
              multCoeff1    = pGetCoeff( kBucketGetLm(bucket) );
              multCoeff2    = pGetCoeff( temp->p );
              multCoeff2    = n_Div( multCoeff1, multCoeff2, currRing );
              poly multiplier = pOne();
              getExpFromIntArray( multTemp, multiplier, numVariables, shift, 
                  negBitmaskShifted, offsets
                  );
              // throw away the leading monomials of reducer and bucket
              p_SetCoeff( multiplier, multCoeff2, currRing );
              pSetm( multiplier );
#if F5EDEBUG3
              pTest( multiplier );
#endif
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
              isMult  = FALSE;
              if( kBucketGetLm( bucket ) )
              {
                temp  = gCurrFirst;
              }
              else
              {
                goto kBucketLmZero;
              }
              goto startagainTail;
              /*
                 }
                 */
            }
            // isMult = 0 => multTemp = 1 => we do not need to test temp->p by any
            // criterion again => go on with reduction steps
            else
            {
              multCoeff1    = pGetCoeff( kBucketGetLm(bucket) );
              multCoeff2    = pGetCoeff( temp->p );
              multCoeff2    = n_Div( multCoeff1, multCoeff2, currRing );
              poly tempNeg  = pInit();
              // throw away the leading monomials of reducer and bucket
              tempNeg       = pCopy( temp->p );
              p_Mult_nn( tempNeg, multCoeff2, currRing );
              pSetm( tempNeg );
              tempLength    = pLength( tempNeg->next );
              kBucketExtractLm(bucket);
              kBucket_Add_q( bucket, pNeg(tempNeg->next), &tempLength ); 
              if( canonicalize++ % 40 )
              {
                kBucketCanonicalize( bucket );
                canonicalize = 0;
              }
              if( kBucketGetLm( bucket ) )
              {
                temp  = gCurrFirst;
              }
              else
              {
                goto kBucketLmZero;
              }
              goto startagainTail;
            } 
          }
          temp  = temp->next;
        }
        // here we know that 
        sp =  p_Merge_q( sp, kBucketExtractLm(bucket), currRing );
#if F5EDEBUG3
        pTest(sp);
        Print("MERGED NEW TAIL: ");
        pWrite( sp );
#endif
      }
      // no tail reduction
#else
      while( kBucketGetLm(bucket) )
      {
        sp = p_Merge_q( sp, kBucketExtractLm(bucket), currRing );  
      }
#endif // Tail reduction yes/no   
kBucketLmZero: 
      // otherwise sp is reduced to zero and we do not need to add it to gCurr
      // Note that even in this case the corresponding rule is already added to
      // rewRules list!
      if( sp )
      {
        if( !superTop )
        {
          // we have not reduced the tail w.r.t. redGB as in this case it is not really necessary to have
          // the "right" leading monomial
          //  => now we have to reduce w.r.t. redGB again!
          sp = reduceByRedGBPoly( sp, strat );
          numberReductions++;
          //pNorm( spTemp->p ); 
          // add sp together with rewRulesLast to gCurr!!!
          Lpoly* newElement     = (Lpoly*) omAlloc( sizeof(Lpoly) );
          newElement->next      = NULL;
          newElement->p         = sp; 
          newElement->sExp      = pGetShortExpVector(sp); 
          newElement->rewRule   = rewRulesCurr; 
          newElement->redundant = redundant;
          // update pointer to last element in gCurr list
          (*gCurrLast)->next    = newElement;
          *gCurrLast            = newElement;
#if F5EDEBUG0
          Print("ADDED TO BASIS: ");
          pWrite( (*gCurrLast)->p );
          poly pSig = pOne(); 
          for( int lale = 1; lale < (currRing->N+1); lale++ )
          {
            pSetExp( pSig, lale, rewRules->label[rewRulesCurr][lale] );
          }
          pWrite( pSig );
          pTest( (*gCurrLast)->p );
          pDelete( &pSig );
#endif
          criticalPairPrev( 
              *gCurrLast, gCurrFirst, strat, *f5Rules, *rewRules, cp, numVariables, 
              shift, negBitmaskShifted, offsets 
              );
          criticalPairCurr( 
              *gCurrLast, gCurrFirst, strat, *f5Rules, *rewRules, cp, numVariables, 
              shift, negBitmaskShifted, offsets 
              );
        }
        else
        {
          // we have done a super top reduction!
          // => delete poly and its label completely
#if F5EDEBUG0
          Print("SUPER TOP REDUCTION!\n");
          pWrite( pHead(sp) );
          poly pSig = pOne(); 
          for( int lale = 1; lale < (currRing->N+1); lale++ )
          {
            pSetExp( pSig, lale, rewRules->label[rewRulesCurr][lale] );
          }
          pWrite( pSig );
          pTest( (gCurrFirst)->p );
          pDelete( &pSig );
#endif
          superTopReductions++;

        }    
      }
      else // spTemp->p == 0
      {
        // if spTemp->p = 0 we have to add the corresponding rewRule to the array
        // of f5Rules
#if F5EDEBUG0
        Print("ZERO REDUCTION!\n");
        poly pSig = pOne(); 
        for( int lale = 1; lale < (currRing->N+1); lale++ )
        {
          pSetExp( pSig, lale, rewRules->label[rewRulesCurr][lale] );
        }
        pWrite( pSig );
        pTest( (gCurrFirst)->p );
        pDelete( &pSig );
#endif
        zeroReductions++;
#if F5EDEBUG2
        Print("SIZES BEFORE: %ld < %ld ?\n",f5Rules->size, f5RulesSize);
        Print("ADDRESS: %p\n", f5Rules->label[0]);
#endif
        // get the corresponding offsets for the insertion of the element in the two lists:
        if( f5Rules->size<f5RulesSize )
        {
          // copy data from critical pair rule to rewRule
          register unsigned long _length  = currRing->N+1;
          register unsigned long _i       = 0;
          register int* _d                = f5Rules->label[f5Rules->size];
          register int* _s                = rewRules->label[rewRulesCurr];
          while( _i<_length )
          {
            _d[_i]  = _s[_i];
            _i++;
          }
          f5Rules->slabel[f5Rules->size]  = rewRules->slabel[rewRulesCurr];
          f5Rules->coeff[f5Rules->size]   = rewRules->coeff[rewRulesCurr];
          f5Rules->size++;
        }
        else
        {
#if F5EDEBUG1
          Print("ALLOC MORE MEMORYi -- %p\n", f5Rules->label[0]);
#endif
          unsigned int old    = f5RulesSize;
          f5RulesSize         = 3*f5RulesSize;
          F5Rules* newRules   = (F5Rules*) omAlloc( sizeof(F5Rules) );
          newRules->coeff     = (number*)omAlloc( f5RulesSize*sizeof(number) );
          newRules->label     = (int**) omAlloc( f5RulesSize*sizeof(int*) );
          newRules->slabel    = (unsigned long*)omAlloc( f5RulesSize*sizeof(unsigned long) );
          newRules->size      = f5Rules->size;
          // add element at the end 
          register unsigned long _length  = currRing->N+1;
          register unsigned long _ctr     = 0;
          for( ; _ctr<old; _ctr++ )
          {
            newRules->label[_ctr]     =  (int*) omAlloc( (currRing->N+1)*sizeof(int) );
            register unsigned long _i = 0;
            register int* _d          = newRules->label[_ctr];
            register int* _s          = f5Rules->label[_ctr];
            while( _i<_length )
            {
              _d[_i]  = _s[_i];
              _i++;
            }
            omFreeSize( f5Rules->label[_ctr], (currRing->N+1)*sizeof(int) );
            newRules->slabel[_ctr]  = f5Rules->slabel[_ctr];
            newRules->coeff[_ctr]   = f5Rules->coeff[_ctr];
          }
          omFreeSize( f5Rules->slabel, old*sizeof(unsigned long) );
          omFreeSize( f5Rules->coeff, old*sizeof(unsigned long) );
          for( ; _ctr<f5RulesSize; _ctr++ )
          {
            newRules->label[_ctr] =  (int*) omAlloc( (currRing->N+1)*sizeof(int) );
          }
          omFreeSize( f5Rules, sizeof(RewRules) );
          *f5RulesP  = f5Rules  = newRules;
          // now we can go on adding the new rule to f5Rules

          // copy data from rule corresponding to new s-polynomial to rewRule
          register unsigned long _i = 0;
          register int* _d          = f5Rules->label[f5Rules->size];
          register int* _s          = rewRules->label[rewRulesCurr];
          while( _i<_length )
          {
            _d[_i]  = _s[_i];
            _i++;
          }
          f5Rules->slabel[f5Rules->size]  = rewRules->slabel[rewRulesCurr];
          f5Rules->coeff[f5Rules->size]   = rewRules->coeff[rewRulesCurr];
          f5Rules->size++;
#if F5EDEBUG2
          Print("MEMORY ALLOCATED -- %p\n", f5Rules->label[0]);
#endif
        } 

        pDelete( &sp );
      }
      // free memory of bucket
      kBucketDeleteAndDestroy( &bucket );
#if F5EDEBUG1
      Print("CURRREDUCTION-END \n");
      Print("HERE1 -- %p -- %p\n", rewRules, rewRules->label[0]);
#endif
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
  if( pLmCmp(cp->mLabelExp, cp2->mLabelExp) == -1 )
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
    if( pLmCmp(cp->mLabelExp, cp2->mLabelExp) == -1 )
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
  p_SetRingOfLm( np, currRing );
  poly expTemp  =  pOne();
  getExpFromIntArray( exp, expTemp, numVariables, shift, negBitmaskShifted, 
                      offsets 
                    );
  static number n  = nInit(1);
  p_MemCopy_LengthGeneral( np->exp, expTemp->exp, NUMVARS );
  pNext(np) = NULL;
  pSetCoeff0(np, n);
  p_Setm( np, currRing );
  omFree( expTemp );
  return np;
}



poly createSpoly( Cpair* cp, int numVariables, int* shift, unsigned long* negBitmaskShifted,
                  int* offsets, poly spNoether, int use_buckets, ring tailRing, 
                  TObject** R
                )
{
  
#if F5EDEBUG1
  Print("CREATESPOLY - BEGINNING %p\n", cp );
#endif
  LObject Pair( currRing );
  Pair.p1  = cp->p2;
  Pair.p2  = cp->p1;
#if F5EDEBUG1
  Print( "P1: %p\n", cp->p1 );
  pWrite(cp->p1);
  Print( "P2: &p\n", cp->p2 );
  pWrite(cp->p2);
#endif
  poly m1 = multInit( cp->mult2, numVariables, shift, 
                      negBitmaskShifted, offsets 
                    );
  poly m2 = multInit( cp->mult1, numVariables, shift, 
                      negBitmaskShifted, offsets 
                    );
#if F5EDEBUG2
  Print("M1: %p ",m1);
  pWrite(m1);
  Print("M2: %p ",m2);
  pWrite(m2);
#endif
#ifdef KDEBUG
  create_count_f5++;
#endif
  kTest_L( &Pair );
  poly p1 = Pair.p1;
  poly p2 = Pair.p2;

  p2  = pp_Mult_mm( p2, m2, currRing );
  return p2;

  // #####################################################
  poly last;
  Pair.tailRing = tailRing;

  assume(p1 != NULL);
  assume(p2 != NULL);
  assume(tailRing != NULL);

  poly a1 = pNext(p1), a2 = pNext(p2);
  /// this is a little hack for GGV:
  /// We want m1*p1 - c*m2*p2 when computing the s-polynomial.
  /// In the following, m1*p1 will be multiplied by lc2(=1)
  /// and m2*p2 will be multiplied by lc1(=already precomputed coeff
  /// for s-polynomial computation.
  number lc2 = cp->coeff2;
  number lc1 = nInit(1);
#if F5EDEBUG1
  Print("COEFF1: ");
  Print( "%d\n",lc1 );
  Print("COEFF2: ");
  Print( "%d\n",lc2 );
#endif
  /*
  pSetCoeff0(m1, lc2);
  pSetCoeff0(m2, lc1);  // and now, m1 * LT(p1) == m2 * LT(p2)
  poly res = p_Minus_mm_Mult_qq( pp_Mult_mm(cp->p1, m1, currRing), m2, cp->p2, currRing );
  return res;
  */
  int co=0, ct = ksCheckCoeff( &lc1, &lc2 ); // as lc1 = lc2 = 1 => 3=ksCheckCoeff(&lc1, &lc2); !!!

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
#if F5EDEBUG2
  Print("Setting lead coeffs of multipliers while generating s-polynomial:\n");
  Print("M1: ");
  pWrite( m1 );
  Print("M2: ");
  pWrite( m2 );
#endif
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
    Print("A2: ");
    pWrite(a2);
    assume(l2 == pLength(a2));
  }
  else
    a2 = tailRing->p_Procs->pp_Mult_mm(a2, m2, tailRing,last);
    Print("A2i: ");
    pWrite(a2);
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
#if F5EDEBUG1
  Print("CREATESPOLY - END\n");
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
    PrintS("reduce ");h->wrp();//PrintS(" with ");with->wrp();//PrintLn();
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
    PrintS("to ");h->wrp();//PrintLn();
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
  }
}

//------------------------------------------------------------------------
// END static stuff from kstd1.cc 
//------------------------------------------------------------------------

void prepRedGBReduction(kStrategy strat, ideal F, ideal Q, int lazyReduce)
{
  /*- creating temp data structures------------------- -*/
  BITSET save_test=test;
  test|=Sy_bit(OPT_REDTAIL);
  initBuchMoraCrit(strat);
  strat->initEcart = initEcartBBA;
  strat->enterS = enterSBba;
#ifndef NO_BUCKETS
  strat->use_buckets = (!TEST_OPT_NOT_BUCKETS) && (!rIsPluralRing(currRing));
#endif
  /*- set S -*/
  strat->sl = -1;
  /*- init local data struct.---------------------------------------- -*/
  /*Shdl=*/initS(F,Q,strat);
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
  /*- compute------------------------------------------------------- -*/
  //if ((TEST_OPT_INTSTRATEGY)&&(lazyReduce==0))
  //{
  //  for (i=strat->sl;i>=0;i--)
  //    pNorm(strat->S[i]);
  //}
#if F5EDEBUG2
  Print("CREATED SPOLY BEFORE REDUCTION WITH REDGB:  ");
  pWrite( q );
#endif
  kTest(strat);
  if (TEST_OPT_PROT) { PrintS("r"); mflush(); }
  int max_ind;
  return q;

  //---------------------------------------------------------------
  //---------------------------------------------------------------
  //---------------------------------------------------------------
  p = redNF(pCopy(q),max_ind,lazyReduce & KSTD_NF_NONORM,strat);
  if ((p!=NULL)&&((lazyReduce & KSTD_NF_LAZY)==0))
  {
    if (TEST_OPT_PROT) { PrintS("t"); mflush(); }
    #ifdef HAVE_RINGS
    if (rField_is_Ring())
    {
      p = redtailBba_Z(p,max_ind,strat);
    }
    else
    #endif
    {
      BITSET save=test;
      test &= ~Sy_bit(OPT_INTSTRATEGY);
      p = redtailBba(p,max_ind,strat,(lazyReduce & KSTD_NF_NONORM)==0);
      test=save;
    }
  }
  test=save_test;
  if (TEST_OPT_PROT) PrintLn();
  return p;
}



poly reduceByRedGBPoly( poly q, kStrategy strat, int lazyReduce )
{
  LObject h;
  h.p = q;
  redHomog( &h, strat );
  if ((h.p!=NULL)&&((lazyReduce & KSTD_NF_LAZY)==0))
  {
    if (TEST_OPT_PROT) { PrintS("t"); mflush(); }
    #ifdef HAVE_RINGS
    if (rField_is_Ring())
    {
      h.p = redtailBba_Z(h.p,strat->sl,strat);
    }
    else
    #endif
    {
      BITSET save=test;
      test &= ~Sy_bit(OPT_INTSTRATEGY);
      h.p = redtailBba(h.p,strat->sl,strat,(lazyReduce & KSTD_NF_NONORM)==0);
      test=save;
    }
  }
  //Print("H.P : ");
  //pWrite( h.p );
  return h.p;
  //----------------------------------------------------------------------
  //----------------------------------------------------------------------
  //----------------------------------------------------------------------
  poly  p;
  int   i;
  int   j;
  int   o;
  BITSET save_test=test;
  
  /*- compute------------------------------------------- -*/
#if F5EDEBUG3
  pTest( q );
#endif
  /*- compute------------------------------------------------------- -*/
  //if ((TEST_OPT_INTSTRATEGY)&&(lazyReduce==0))
  //{
  //  for (i=strat->sl;i>=0;i--)
  //    pNorm(strat->S[i]);
  //}
  kTest(strat);
  if (TEST_OPT_PROT) { PrintS("r"); mflush(); }
  int max_ind;
  p = redNF(pCopy(q),max_ind,lazyReduce & KSTD_NF_NONORM,strat);
  if ((p!=NULL)&&((lazyReduce & KSTD_NF_LAZY)==0))
  {
    if (TEST_OPT_PROT) { PrintS("t"); mflush(); }
    #ifdef HAVE_RINGS
    if (rField_is_Ring())
    {
      p = redtailBba_Z(p,max_ind,strat);
    }
    else
    #endif
    {
      BITSET save=test;
      test &= ~Sy_bit(OPT_INTSTRATEGY);
      p = redtailBba(p,max_ind,strat,(lazyReduce & KSTD_NF_NONORM)==0);
      test=save;
    }
  }
  test=save_test;
  if (TEST_OPT_PROT) PrintLn();
  return p;
}



void clearStrat(kStrategy strat, ideal F, ideal Q)
{
#if F5EDEBUG3
  Print("CLEARSTRAT - BEGINNING\n");
#endif
  /*- release temp data------------------------------- -*/
  omfree(strat->sevS);
  omfree(strat->ecartS);
  omfree(strat->T);
  omfree(strat->sevT);
  omfree(strat->R);
  omfree(strat->S_2_R);
  omfree(strat->L);
  omfree(strat->B);
  omfree(strat->fromQ);
  idDelete(&strat->Shdl);
#if F5EDEBUG3
  Print("CLEARSTRAT - END\n");
#endif
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


inline void getExpFromIntArray( const int* exp, poly r, 
                                int numVariables, int* shift, unsigned long* 
                                negBitmaskShifted, int* offsets
                              )
{
  register int i = numVariables;
  for( ; i; i--)
  {
    register int shiftL   =   shift[i];
#if F5EDEBUG3
    Print("%d. EXPONENT CREATION %d\n",i,exp[i]);
#endif
    unsigned long ee      =   exp[i];
    ee                    =   ee << shiftL;
    register int offsetL  =   offsets[i];
    r->exp[offsetL]       &=  negBitmaskShifted[i];
    r->exp[offsetL]       |=  ee;
  }
  r->exp[currRing->pCompIndex] = exp[0];
  pSetm( r );
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
#if F5EDEBUG2
    Print("ISDIVISIBLE-BEGINNING \n");
#endif
#if F5EDEBUG3
  pWrite(pHead(a));
  Print("%ld\n",pGetShortExpVector(a));
  pWrite(pHead(b));
  Print("%ld\n",~pGetShortExpVector(b));
  Print("SHORT EXP TEST -- BOOLEAN? %ld\n",(sev_a & not_sev_b));
  p_LmCheckPolyRing1(a, currRing);
  p_LmCheckPolyRing1(b, currRing);
#endif
  if (sev_a & not_sev_b)
  {
    pAssume1(_p_LmDivisibleByNoComp(a, currRing, b, currRing) == FALSE);
    *isMult = FALSE;
#if F5EDEBUG2
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
      if (p_GetExp(a,i,currRing) > p_GetExp(b,i,currRing))
      {
        *isMult = FALSE;
#if F5EDEBUG2
    Print("ISDIVISIBLE-END2 \n");
#endif
        return FALSE;
      }
      (*mult)[i] = (p_GetExp(b,i,currRing) - p_GetExp(a,i,currRing)); 
      if( ((*mult)[i])>0 )
      {
        *isMult = TRUE;
      }
      i--;
    }
    while (i);
    (*mult)[0]  = 0;
#ifdef HAVE_RINGS
#if F5EDEBUG2
    Print("ISDIVISIBLE-END3 \n");
#endif
    return nDivBy(p_GetCoeff(b, r), p_GetCoeff(a, r));
#else
#if F5EDEBUG2
    Print("ISDIVISIBLE-END4 \n");
#endif
    return TRUE;
#endif
  }
#if F5EDEBUG2
    Print("ISDIVISIBLE-END5 \n");
#endif
  return FALSE;
}
#endif
// HAVE_F5C
