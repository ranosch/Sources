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
  ideal r = idInit(1, F->rank);
  // save the first element in ideal r, initialization of iteration process
  r->m[0] = F->m[0];
  // counter over the remaining generators of the input ideal F
  int gen;
  for(gen=1; gen<IDELEMS(F); gen++) 
  {
    // computation of r: a groebner basis of <F[0],...,F[gen]> = <r,F[gen]>
    //Print("%d\n",gen);
    //pWrite(r->m[0]);
    r = f5cIter(F->m[gen], r);
    // the following interreduction is the essential idea of F5C.
    // NOTE that we do not need the old rules from previous iteration steps
    // => we only interreduce the polynomials and forget about their labels
    //r = kInterRed(r);
    //idDelete(&r);
    //r = r1;
    //kNF
  //Print("interred:");
  //pWrite(r->m[0]);
  //pWrite(r->m[1]);
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
  f5Rules->slabel = (long*) omalloc((currRing->N+1)*sizeof(long)); 
  for(i=0; i<IDELEMS(redGB); i++) 
  {
    f5Rules->label[i]  = (int*) omalloc((currRing->N+1)*sizeof(int));
    //pWrite(redGB->m[i]);
    pGetExpV(redGB->m[i], f5Rules->label[i]);
    f5Rules->slabel[i] = pGetShortExpVector(redGB->m[i]); 
  } 
  // reduce and initialize the list of Lpolys with the current ideal generator p
  p = kNF(redGB, currQuotient, p);  
  //Print("kNF:");
  //pWrite(redGB->m[0]);
  //pWrite(p);
  /******************************
   * TO DO
   *****************************/
  idInsertPoly(redGB,p);
  idCompactify(redGB);
  Lpoly gCurr = {NULL, p, NULL};  
  
  return redGB;
}


/*
  Print("SHORT EXP VECTOR 1:  %ld\n", pGetShortExpVector(id->m[0]));
  int* expVec   = new int[(r->N)+1];
  pGetExpV(id->m[0],expVec);
  Print("EXP VECTOR 1: %d\n",expVec[1]);
  Label* label  = new Label(expVec);
  Print("EXP VECTOR 2: %d\n", label->getExpVec()[1]);
  Print("SHORT EXP VECTOR 2:  %ld\n", label->getShortExpVec());
  //Print("%ld\n", label->computeShortExpVec(expVec)); 
  Print("SHORT EXP VECTOR 1:  %ld\n", pGetShortExpVector(id->m[1]));
  //int* expVec   = new int[(r->N)+1];
  pGetExpV(id->m[1],expVec);
  Print("EXP VECTOR 1: %d\n",expVec[1]);
  Label* label2  = new Label(expVec);
  Print("EXP VECTOR 2: %d\n", label2->getExpVec()[1]);
  Print("SHORT EXP VECTOR 2:  %ld\n", label2->getShortExpVec());

  return id;
}
*/
#endif
// HAVE_F5C
