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

/// NOTE that the input must be homogeneous to guarantee termination and
/// correctness. Thus these properties are assumed in the following.
ideal f5cMain(ideal F, ideal Q) 
{
  if(idIs0(F)) 
  {
    return idInit(1,F->rank);
  }
  // interreduction of the input ideal F
  F = kInterRed(F);
  ideal r = idInit(1,F->rank);
  // save the first element in ideal r, initialization of iteration process
  r->m[0] = F->m[0];
  // counter over the remaining generators of the input ideal F
  int gen;
  for(gen=1; gen<IDELEMS(F); gen++) 
  {
    // computation of r: a groebner basis of <F[0],...,F[gen]> = <r,F[gen]>
    r = f5cIter(F->m[gen],r);
    // the following interreduction is the essential idea of F5C.
    // NOTE that we do not need the old rules from previous iteration steps
    // => we only interreduce the polynomials and forget about their labels
    r = kInterRed(r);
  }
  return idInit(1,F->rank);
}


ideal f5cIter(poly p, ideal redGB) 
{
  int i;
  // create array of leading monomials of previously computed elements in redGB
  F5Rules* f5Rules = (F5Rules*) omalloc(IDELEMS(redGB)*sizeof(struct F5Rules));
  
  for(i=0; i<IDELEMS(redGB); i++) 
  {
    //f5Rules[i].label  = (int*) omalloc((currRing->N+1)*sizeof(int));
    //pGetExpV(redGB->m[i],f5Rules[i].label);
    f5Rules[i].slabel = pGetShortExpVector(redGB->m[i]); 
  } 
  // reduce and initialize the list of Lpolys with the current ideal generator p
  p = kNF(redGB,currQuotient,p);  
  /******************************
   * TO DO
   *****************************/
  //Lpoly gCurr = {NULL,p,NULL,pGetShortExpVector(pOne()),NULL,NULL,0};  
  /*
   * no need to set this label to anything since it is not used in the
   * following at all
  gCurr->label  = (int*) omalloc((r->N+1)*sizeof(int));
  pGetExp
  */
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
