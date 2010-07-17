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

/** 
 * @brief \c f5cMain() is the main function of the F5 implementation in the
 * Singular kernel. It starts the computations of a Groebner basis of \c F.
 * This is done iteratively on the generators of \c F and degree-wise in each
 * iteration step. 
 * The implemented version is not the standard F5 Algorithm, but the
 * variant F5C (for using reduced Groebner basis after each iteration step)
 * combined with the variant F5+ (for a guaranteed termination of the
 * algorithm).
 * NOTE that the input must be homogeneous to guarantee termination and
 * correctness.
 *
 * LITERATURE:
 * - F5 Algorithm:  http://www-calfor.lip6.fr/~jcf/Papers/F02a.pdf
 * - F5C Algorithm: http://arxiv.org/abs/0906.2967
 * - F5+ Algorithm: to be confirmed
 * 
 * @param \c F is the ideal for which a Groebner basis shall be computed.
 * @param \c Q is the quotientring.
 * 
 * @return A Groebner basis of the the input ideal \c F.
 */
ideal f5cMain(ideal F, ideal Q) {
  if(idIs0(F)) {
    return idInit(1,F->rank);
  }
  // interreduction of the input ideal F
  F = kInterRed(F);
  ideal r = idInit(1,F->rank);
  // save the first element in ideal r, initialization of iteration process
  r->m[0] = F->m[0];
  // counter over the remaining generators of the input ideal F
  int gen;
  for(gen=1; gen<IDELEMS(F); gen++) {
    // computation of r: a groebner basis of <F[0],...,F[gen]> = <r,F[gen]>
    r = f5cIter(F->m[gen],r);
    // the following interreduction is the essential idea of F5C.
    // NOTE that we do not need the old rules from previous iteration steps
    // => we only interreduce the polynomials and forget about their labels
    r = kInterRed(r);
  }
  return idInit(1,F->rank);
}


/** 
 * @brief \c f5cIter() computes a Groebner basis of < \c p , \c redGB > using
 * the criteria of Faugere's F5 Algorithm
 * 
 * @param \c p New element from the initial ideal \c F of \c f5cMain() which
 * starts the new iteration step.
 * @param \c redGB Already computed and afterwards reduced Groebner basis of
 * the generators up to element \c p of the input ideal \c F of \c f5cMain() .
 * 
 * @return A (possibly) not reduced Groebner basis of < \c p , \c redGB >.
 */
ideal f5cIter(poly p, ideal redGB) {
  int i;
  // create array of leading monomials of previously computed elements in redGB
  F5Rules* f5Rules = (F5Rules*) omalloc(IDELEMS(redGB)*sizeof(struct F5Rules));
  
  for(i=0; i<IDELEMS(redGB); i++) {
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
