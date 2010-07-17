/****************************************
*  Computer Algebra System SINGULAR     *
****************************************/
/* $Id$ */
/*
* ABSTRACT: f5gb interface
*/
#ifndef F5_HEADER
#define F5_HEADER

#ifdef HAVE_F5
#include "f5data.h"
#include "f5lists.h"


/* testing ars stuff */
struct testPoly {
  poly leading;
  long idx;
  testPoly* next;
};



struct testPair {
  poly leastcommon;
  long idx1;
  long idx2;
  testPair* next;
};
/* testing ars stuff */

/*
======================================================
sort polynomials in ideal i by decreasing total degree
======================================================
*/
void qsortDegree(poly* left, poly* right);

/*!
 * ======================================================================
 * builds the sum of the entries of the exponent vectors, i.e. the degree
 * of the corresponding monomial
 * ======================================================================
*/
long sumVector(int* v, int k);

/**
==========================================================================
compare monomials, i.e. divisibility tests for criterion 1 and criterion 2
==========================================================================
*/
bool compareMonomials(int* m1, int** m2, int numberOfRuleOlds);


/*
==================================================
computes incrementally gbs of subsets of the input 
gb{f_m} -> gb{f_m,f_(m-1)} -> gb{f_m,...,f_1}  
==================================================
*/
LList* F5inc(int i, poly f_i, LList* gPrev,LList* reducers, ideal gbPrev, poly ONE, LTagList* lTag, RList* rules, RTagList* rTag, int plus ,int termination);

/*
================================================================
computes a list of critical pairs for the next reduction process
the first element is always "useful" thus the critical pair 
computed is either "useful" or "useless" depending on the second 
element which generates the critical pair.
first element in gPrev is always the newest element which must
build critical pairs with all other elements in gPrev
================================================================
*/
void criticalPair(LList* f5CriterionPairs, LList* reducers, ideal gbPrev, LList* gPrev, CListOld* critPairs, LTagList* lTag, RTagList* rTag, RList* RuleOlds, PList* rejectedGBList, int plus);


bool checkDGB(LList* gPrev);


/*
 * Arris Check if we are finished after the current degree step:
 * Checks all remaining critical pairs, i.e. those of higher degree,
 * by the two Buchberger criteria.
 * return value: 0, if all remaining critical pairs are deleted by 
 *                  Buchberger's criteria
 *               1, otherwise
 */
bool arrisCheck(CNode* first,LNode* firstGCurr, long arrisdeg); 
void arsCheck(testPoly* checkedPrev,testPair* checkedPairs); 

/*
================================================================
computes a list of critical pairs for the next reduction process
the first element is always "useless" thus the critical pair 
computed is "useless".
first element in gPrev is always the newest element which must
build critical pairs with all other elements in gPrev
================================================================
*/
void criticalPair2(LList* gPrev, CListOld* critPairs, LTagList* lTag, RTagList* rTag, RList* RuleOlds, PList* rejectedGBList);

/*
========================================
Criterion 1, i.e. Faugere's F5 Criterion
========================================
*/
inline bool criterion1(LList* gPrev, poly t, LNode* l, LTagList* lTag);

/*
=====================================
Criterion 2, i.e. Rewritten Criterion
=====================================
*/
inline bool criterion2(int idx, poly t, LNode* l, RList* RuleOlds, RTagList* rTag);

/*
==========================================================================================================
Criterion 2, i.e. Rewritten Criterion, for its second call in sPols(), with added lastRuleOldTested parameter
==========================================================================================================
*/
inline bool criterion2(poly t, LPolyOld* l, RList* RuleOlds, RuleOld* testedRuleOld);

/*
 * check for useful pairs in the given subset of critical pairs
 */
int computeUsefulMinDeg(CNode* first);

/*
==================================
Computation of S-Polynomials in F5
==================================
*/
inline void computeSPols(CNode* first, RTagList* rTag, RList* RuleOlds, LList* sPolyList, PList* rejectedGBList);

/*
========================================================================
reduction including subalgorithm topReduction() using Faugere's criteria
========================================================================
*/
inline void reduction(LList* reducers, LList* sPolyList, CListOld* critPairs, LList* gPrev, RList* RuleOlds, LTagList* lTag, RTagList* rTag,
                 ideal gbPrev, PList* rejectedGBList, int plus);


/*
==================================
Computation of S-Polynomials in F5 -- TEST STUFF FOR F5 CRITERION ELEMENTS!
==================================
*/
void computeSPolsTest(LList* f5CriterionElements,int currIdx, poly u1, poly p1, poly u2, poly p2, LList* gPrev, ideal gbPrev, LTagList* lTag, RTagList* rTag, RList* rules, LList* reducers); 


void reduceTest(LList* f5CriterionElements, LNode* l,LList* gPrev,ideal gbPrev,LTagList* lTag,RTagList* rTag,RList* rules,LList* reducers);

/*
========================================================================
reduction including subalgorithm topReduction() using Faugere's criteria
========================================================================
*/
inline void newReduction(testPoly* checkedPrev, testPair* checkedPairs, LList* f5CriterionElements, LList* sPolyList, CListOld* critPairs, LList* gPrev, LList* reducers, RList* rules, LTagList* lTag, RTagList* rTag, ideal gbPrev, int termination, PList* rejectedGBList, int plus);

/*!
 * ================================================================================
 * searches for reducers of temp similar to the symbolic preprocessing of F4  and 
 * divides them into a "good" and "bad" part:
 * 
 * the "good" ones are the reducers which do not corrupt the label of temp, with
 * these the normal form of temp is computed
 *
 * the "bad" ones are the reducers which corrupt the label of temp, they are tested 
 * later on for possible new RuleOlds and S-polynomials to be added to the algorithm
 * ================================================================================
 */
void findReducers(testPoly* checkedPrev, testPair* checkedPairs, LList* f5CriterionElements, LNode* l, LList* sPolyList, ideal gbPrev, LList* gPrev, LList* reducers, CListOld* critPairs, RList* rules, LTagList* lTag, RTagList* rTag, int termination, PList* rejectedGBList, int plus); 

/*
=====================================================================================
top reduction in F5, i.e. reduction of a given S-polynomial by labeled polynomials of
the same index whereas the labels are taken into account
=====================================================================================
*/
inline void topReduction(LList* reducers, LNode* l, LList* sPolyList, LList* gPrev, CListOld* critPairs, RList* RuleOlds, LTagList* lTag, RTagList* rTag, ideal gbPrev, PList* rejectedGBList, int plus); 

/*
=======================================================================================
merging 2 polynomials p & q without requiring that all monomials of p & q are different
if there are equal monomials in p & q only one of these monomials (always that of p!)
is taken into account
=======================================================================================

poly p_MergeEq_q(poly p, poly q, const ring r);
*/    
/*
=====================================================================
subalgorithm to find a possible reductor for the labeled polynomial l
=====================================================================
*/
inline LNode* findReductor(LNode* l, LList* sPolyList, LNode* gPrevRedCheck, LList* gPrev, RList* RuleOlds, LTagList* lTag,RTagList* rTag);

/*
======================================
main function of our F5 implementation
======================================
*/
ideal F5main(ideal i, ring r, int opt, int plus, int termination);

#endif
#endif
