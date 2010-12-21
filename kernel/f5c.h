/*****************************************************************************\
 * Computer Algebra System SINGULAR    
\*****************************************************************************/
/** @file f5c.h
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


#ifndef F5C_HEADER
#define F5C_HEADER

#ifdef HAVE_F5C
#include "kutil.h"  // needs to be here and not in "f5c.cc" since 
                    // "reduceByRedGBCritPair" uses "TObject" as a 
                    // parameter


//------------------------------------------------------------------------------
//------------------------------ STRUCTURES ------------------------------------
//------------------------------------------------------------------------------

/// @struct \c F5Rules
/// \c F5Rules is the structure of an array of rules checked in the F5 criterion
/// representing a monomial by an integer vector resp a long, the short
/// exponent vector.
struct F5Rules 
{
  unsigned long   size;   ///< current number of rules in the list
  number*         coeff;  ///< coefficients of the labels
  int**           label;  ///< array of exponent vectors of the rules
  unsigned long*  slabel; ///< array of short exponent vecotrs of the rules
                          ///   of the F5 Criterion
};

 

/// @struct \c RewRules
/// @brief \c RewRules is the structure of a rule checked in the Rewritten criterion
/// representing a monomial by an integer vector resp a long, the short
/// exponent vector.
struct RewRules 
{
  unsigned long   size;   ///< current number of rules in the list
  number*         coeff;  ///< coefficients of the labels
  int**           label;  ///< array of exponent vectors of the rules
  unsigned long*  slabel; ///< array of short exponent vecotrs of the rules
};

 

/// @struct \c Lpoly 
/// @brief \c Lpoly is the structure of a linked list of labeled polynomials, 
/// i.e. elements consisting of a polynomial \c p and a label computed by F5C+ 
/// The label is defined as an integer vector 
/// TODO----resp. in a short exponent vector form as a long in \c slabel . 
/// TODO----\c f5Rules and \c rewRules are an array resp. a list of rules (i.e. int 
/// vectors + shortExponentVectors) which are tested by the 
/// TODO----criteria of F5 in further computations.
/// TODO----\c redundant checks if the element is redundant for the gröbner basis. 
/// TODO----Note that the elements are still non-redundant for F5C+. 
struct Lpoly 
{
  Lpoly*        next;     ///< pointer to the next element in the linked list
  poly          p;        ///< polynomial part
  unsigned long sExp;     ///< short exponent vector of the leading monomial of \c p
  unsigned long rewRule;  ///< idx of the corresponding label in rewRules
  BOOLEAN   redundant;    ///< Lpoly redundant?
  // NOTE: You do not need the short exponent vector as you never check
  // with this, but only with multiples of it in the critical pair
  //long    slabel; ///< short exponent vector of the label/signature
  // keep this in mind for your idea about improving the check of rules and
  // making it parallizable:
  // The idea is to store for each labeled poly the uniquely defined lists of
  // F5Rules and RewRules where the multiplicities are even cancelled out. Thus
  // we have less checks (no multiples of rules are checked!) and no
  // multiplicities have to be computed when the rule checks are done.
  // -----------------------
  //struct F5Rules  f5Rules;
  //struct RewRules rewRules;
  // -----------------------   
};



/// @struct \c Spoly 
/// @brief \c Spoly is the structure of a linked list of s-polynomials, 
struct Spoly 
{
  Spoly*          next;     ///<  pointer to the next element in the linked list
  unsigned long*  labelExp; ///<  exponent vector of the corresponding critical pair
                            ///   Note that this has to be stored, although we have 
                            ///   already computed the corresponding rewriting rule 
                            ///   as this rule does not include Singular's internal 
                            ///   exponent representation.
  poly            p;        ///<  s-polynomial
};



/// @struct \c Cpair 
/// @brief \c Cpair is the structure of the list of critical pairs in F5C+
/// containing the corresponding polynomials, the multiplied labels, and the
/// multipliers.
struct Cpair 
{
  Cpair*          next;       ///<  next critical pair sorted by label
  unsigned long*  mLabelExp;  ///<  exponent vector of the label of 
                              ///   the critical pair: this element is needed
                              ///   for sorting the critical pairs in 
                              ///   \c computeSpols() by the given ordering
  int*            mLabel1;    ///<  exponent vector of the 1st multiplier * label 
                              ///   of p1
  unsigned long   smLabel1;   ///<  short exponent vector of \c mLabel1
  int*            mult1;      ///<  multiplier of the 1st poly
  poly            p1;         ///<  1st labeled poly
  unsigned long   rewRule1;   ///<  index of rule for criterion2 checks
  number          coeff2;     ///<  coefficient the 2nd generator has to be multiplied with
  int*            mLabel2;    ///<  exponent vector of the 2nd multiplier * label 
                              ///   of p2
  unsigned long   smLabel2;   ///<  short exponent vector of \c mLabel2
  int*            mult2;      ///<  multiplier of the 2nd poly
  poly            p2;         ///<  2nd labeled poly
  unsigned long   rewRule2;   ///<  index of rule for criterion2 checks
};



/// @struct \c CpairDegBound
/// @brief This is the structure of linked list of linked lists of critical
/// pairs.
/// Each node of the linked list is a linked list of critical pairs of degree
/// \c deg. This structure is sorted by degree,
/// whereas the deg-lists themselves are not sorted at this point. This will 
/// be done by a merge sort in \c computeSpols.
/// @sa computeSpols
struct CpairDegBound
{
  CpairDegBound*  next;   ///<  next linked list of critical pairs of next 
                          ///   higher degree
  long            deg;    ///<  degree of all critical pairs in this linked list
  Cpair*          cp;     ///<  first element in critical pair-deg-linked list
  unsigned int    length; ///<  number of critical pairs of degree \c deg
};



//--------------------------------------------------------------------------------
//--------------------------- FUNCTIONS & PROCEDURES -----------------------------
//--------------------------------------------------------------------------------

/// @brief \c f5cMain is the main function of the F5 implementation in the
/// Singular kernel. It starts the computations of a Groebner basis of \c F.
/// This is done iteratively on the generators of \c F and degree-wise in each 
/// iteration step. 
/// The implemented version is not the standard F5 Algorithm, but the
/// variant F5C (for using reduced Groebner basis after each iteration step)
/// combined with the variant F5+ (for a guaranteed termination of the
/// algorithm).
/// @return ideal which represents the Groebner basis of the input ideal \c F
ideal f5cMain (
  ideal F,        ///<[in]  ideal for which a Groebner basis is computed
  ideal Q = NULL  ///<[in]  the quotient ring, if not specified it is NULL
              ); 

 

/// @brief \c f5cIter() computes a Groebner basis of < \c p , \c redGB > using
/// the criteria of Faugere's F5 Algorithm in the variant F5+.
/// @return A (possibly) not reduced Groebner basis of < \c p , \c redGB >.
/// @sa f5cMain
ideal f5cIter (
  poly p,                       ///<[in]  new element from the initial ideal \c F of 
                                ///       \c f5cMain which starts the new iteration step
  ideal redGB,                  ///<[in]  already computed and reduced Groebner basis 
                                ///       of the ideal generated by all initial elements 
                                ///       up to \c p 
  int numVariables,             ///<[in] global stuff for faster exponent computations
  int* shift,                   ///<[in] global stuff for faster exponent computations
  unsigned long* negBit,        ///<[in] global stuff for faster exponent computations
  int* offsets                  ///<[in] global stuff for faster exponent computations
              ); 



/// @brief \c criticalPairInit() computes all critical pairs of the previously
/// computed Groebner basis \c gPrev and the newly added element \c p , which is 
/// the only element in \c gCurr at this point. So this procedure is only used
/// at the very beginning of a new iteration step in F5e. Note that at this
/// point no rewrite rule exists, thus we do not need \c RewRules .
/// @sa insertCritPair, criticalPairCurr, criticalPairPrev
void criticalPairInit ( 
  Lpoly* gCurr,                     ///<[in]  this is the labeled 
                                    ///       polynomial of p at this point
  const kStrategy strat,            ///<[in]  reduced Groebner basis computed in 
                                    ///       the previous iteration step  
  const F5Rules& f5Rules,           ///<[in]  list of exponent vectors to check the F5 
                                    ///       Criterion, i.e. Criterion 1
  const RewRules& rewRules,         ///<[in]  list of exponent vectors to check the Rewritten
                                    ///       Criterion, i.e. Criterion 2
  CpairDegBound** bounds,           ///<[in,out]  list of critical pair 
                                    ///           degree bounds               
  int numVariables,                 ///<[in] global stuff for faster exponent computations
  int* shift,                       ///<[in] global stuff for faster exponent computations
  unsigned long* negBitmaskShifted, ///<[in] global stuff for faster exponent computations
  int* offsets                      ///<[in] global stuff for faster exponent computations
                      );



/// @brief \c criticalPairPrev() computes all critical pairs of the previously
/// computed Groebner basis \c gPrev and the newly added element \c p , which is 
/// the only element in \c gCurr at this point. So this procedure is only used
/// at the very beginning of a new iteration step in F5e. Note that at this
/// point no rewrite rule exists, thus we do not need \c RewRules .
/// @sa insertCritPair, criticalPairCurr, criticalPairInit
void criticalPairPrev ( 
  Lpoly* gCurrNew,                  ///<[in]  essentially this is the labeled 
                                    ///       polynomial of p at this point
  Lpoly* gCurr,                     ///<[in]  essentially this is the labeled 
                                    ///       polynomial of p at this point
  const kStrategy strat,            ///<[in]  reduced Groebner basis computed in 
                                    ///       the previous iteration step  
  const F5Rules& f5Rules,           ///<[in]  list of exponent vectors to check the F5 
                                    ///       Criterion
  const RewRules& rewRules,         ///<[in]  list of exponent vectors to check the Rewritten
                                    ///       Criterion, i.e. Criterion 2
  CpairDegBound** bounds,           ///<[in,out]  list of critical pair 
                                    ///           degree bounds               
  int numVariables,                 ///<[in] global stuff for faster exponent computations
  int* shift,                       ///<[in] global stuff for faster exponent computations
  unsigned long* negBitmaskShifted, ///<[in] global stuff for faster exponent computations
  int* offsets                      ///<[in] global stuff for faster exponent computations
                      );



/// @brief \c criticalPairCurr() computes all critical pairs of the previously
/// computed Groebner basis \c gPrev and the newly added element \c p , which is 
/// the only element in \c gCurr at this point. So this procedure is only used
/// at the very beginning of a new iteration step in F5e. Note that at this
/// point no rewrite rule exists, thus we do not need \c RewRules .
/// @sa insertCritPair, criticalPairPrev, criticalPairInit
void criticalPairCurr ( 
  Lpoly* gCurrNew,          ///<[in]  essentially this is the labeled 
                            ///       polynomial of p at this point
  Lpoly* gCurr,             ///<[in]  essentially this is the labeled 
                            ///       polynomial of p at this point
  const kStrategy  strat,   ///<[in]  reduced Groebner basis computed in 
                            ///       the previous iteration step  
  const F5Rules& f5Rules,   ///<[in]  list of exponent vectors to check the F5 
                            ///       Criterion
  const RewRules& rewRules, ///<[in]  list of exponent vectors to check the Rewritten
                            ///       Criterion, i.e. Criterion 2
  CpairDegBound** bounds,   ///<[in,out]  list of critical pair 
                            ///           degree bounds               
  int numVariables,         ///<[in] global stuff for faster exponent computations
  int* shift,               ///<[in] global stuff for faster exponent computations
  unsigned long* negBit,    ///<[in] global stuff for faster exponent computations
  int* offsets              ///<[in] global stuff for faster exponent computations
                      );



/// @brief \c insertCritPair() inserts \c critPair into the linked list of
/// critical pairs.
/// @sa criticalPairPrev, criticalPairCurr 
void insertCritPair (
  Cpair*          critPair, ///<[in]      new critical pair to be inserted
  long            deg,      ///<[in]      degree of \c critPair
  CpairDegBound** bound     ///<[in,out]  first element of the list of 
                            ///           critical pair degree bounds
                    );



/// @brief \c criterion1() checks the multiplied label of a generator of a
/// critical pair by the F5 Criterion
/// @return 1, if the label is detected by the F5 Criterion; 0, else
/// @sa criterion2
inline BOOLEAN criterion1 (
  const int*          mLabel,  ///<[in]  multiplied labeled to be checked
  const unsigned long smLabel, ///<[in]  corresponding short exponent vector
  const F5Rules*      f5Rules  ///<[in]  rules (integer vectors) for F5 Criterion checks
                          );



/// @brief \c criterion2() checks the multiplied label of a generator of a
/// critical pair by the Rewritten Criterion 
/// @return 1, if the label is detected by the Rewritten Criterion; 0, else
/// @sa criterion1
inline BOOLEAN criterion2 (
  const int*          mLabel,     ///<[in]  multiplied labeled to be checked
  const unsigned long smLabel,    ///<[in]  corresponding short exponent vector
  const RewRules*   rewRules,     ///<[in]  rules for Rewritten Criterion checks
  const unsigned long rewRulePos  ///<[in]  position from which the rule check 
                                  ///       should start
                          );



/// @brief \c computeSpols() computes the s-polynomials of critical pairs of 
/// lowest given degree which are not detected by the Rewritten Criterion.
/// @sa criticalPairInit, criticalPairPrev, criticalPairCurr
void computeSpols (
  kStrategy strat,            ///<[in]  strategy to reduce elements w.r.t. \c redGB
  CpairDegBound*  critPairs,  ///<[in]  pointer to the first critical pair of 
                              ///       the lowest given degree. Note that this
                              ///       linked list of critical pairs is NOT  
                              ///       sorted.
  ideal           redGB,      ///<[in]  reducers of earlier iteration steps
  Lpoly**         gCurr,      ///<[in,out]  pointer to the list of reducers of the 
                              ///           current iteration step
  F5Rules**  f5Rules,         ///<[in]  rules for F5 Criterion checks
  RewRules** rewRules,        ///<[in]  rules for Rewritten Criterion checks
  int numVariables,           ///<[in]  global stuff for faster exponent computations
  int* shift,                 ///<[in]  global stuff for faster exponent computations
  unsigned long* negBit,      ///<[in]  global stuff for faster exponent computations
  int* offsets                ///<[in]  global stuff for faster exponent computations
                  );



/// @brief \c kBucketCopyToPoly copies the data from \c bucket into \c poly and
/// does NOT destroy \c bucket! This is needed for "higher label reductions" in
/// F5's top-reduction procedure.
/// @sa currReduction
inline void kBucketCopyToPoly (
  kBucket_pt bucket,  ///[in,out] bucket, still alive after function call
  poly *p,            ///[in,out] poly that gets the data of the bucket copied
  int *length         ///[in,out] length of the poly
                              );

  
  
/// @brief \c currReduction() reduces a list s-polynomial \c sp by those labeled
/// polynomials computed in the current iteration step, whose multiples are not
/// detected by any of F5's criteria.
/// Note that if a higher label reduction takes place, possibly new rules 
/// and s-polynomials are added during the procedure and reduced in the following.
/// @sa computeSpols, reducedByRedGBCritPair
void currReduction  ( 
  kStrategy strat,        ///<[in]      strategy to reduce elements w.r.t. \c redGB
                          ///           needed for possible reduction of newly
                          ///           generated polys during higher label
                          ///           reductions  
  Spoly* spolyFirst,      ///<[in]  first s-polynomial in the list to be reduced
  Spoly* spolyLast,       ///<[in]  last s-polynomial in the list to be reduced
  RewRules** rewRules,    ///<[in,out]  rewrite rules 
  unsigned long currPos,  ///<[in,out]  position in the rewRules array of the first
                          ///           rewrite rule of this degree step
  ideal redGB,            ///<[in]  previous GB for reduction & generation of new 
                          ///       critical pairs 
  CpairDegBound** cp,     ///<[in,out]  pointer of the deg bound critical pair list,
                          ///           needed for sorting of newly computed critical
                          ///           pairs
  Lpoly* gCurrFirst,      ///<[in,out]  reducers of the current iteration step.
                          ///           Note this has to be a pointer of a pointer
                          ///           as the corresponding value is changed when
                          ///           new elements are added to gCurr.
  Lpoly** gCurrLast,      ///<[in,out]  reducers of the current iteration step.
                          ///           Note this has to be a pointer of a pointer
                          ///           as the corresponding value is changed when
                          ///           new elements are added to gCurr.
  F5Rules** f5Rules,      ///<[in]      rules for F5 Criterion checks
  int*  multTemp,         ///<[in]      integer exponent vector for the mulitples
                          ///           of the reducers
  int*  multLabelTemp,    ///<[in]      integer exponent vector for the mulitples
                          ///           of the labels of reducers
  int numVariables,       ///<[in]  global stuff for faster exponent computations
  int* shift,             ///<[in]  global stuff for faster exponent computations
  unsigned long* negBit,  ///<[in]  global stuff for faster exponent computations
  int* offsets           ///<[in]  global stuff for faster exponent computations
                    );



/// @brief \c sort() sorts the linked list of critical pairs whose first element 
/// is \c cp
/// @return Pointer to the first critical pair in the sorted linked list.
/// @sa merge
Cpair* sort (
  Cpair* cp,          ///<[in,out]  first element of a linked list of critical 
                      ///           pairs which needs to be sorted
  unsigned int length /// <[in]     number of elements in the linked list
                      ///           starting with \c cp
            );



/// @brief \c merge() is the merging procedure of the sort function used to
/// sort linked lists of critical pairs
/// @return pointer to the first critical pair in the sorted, merged linked
/// list generated by the lists of \c cp and \c cp2.
/// @sa sort
Cpair* merge  (
  Cpair* cp,  ///<[in]  1st element of a linked list of critical pairs
  Cpair* cp2  ///<[in]  2nd element of a linked list of critical pairs
              );



/// @brief \c multInit gets the monomial out of an integer vector representing 
/// the monomials exponent vector
/// @return monomial with exponent vector = \c exp
/// @sa createSpoly
inline poly multInit  ( 
  const int* exp,         ///<[in]  exponent vector we compute a corresponding 
                          ///       monomial of
  int numVariables,       ///<[in]  global stuff for faster exponent computations
  int* shift,             ///<[in]  global stuff for faster exponent computations
  unsigned long* negBit,  ///<[in]  global stuff for faster exponent computations
  int* offsets            ///<[in]  global stuff for faster exponent computations
                      );



/// @brief \c createSpoly() computes the s-polynomial of the critical pair \c
/// cp . This is different from the standard s-polynomial creation in SINGULAR
/// as we already know the multipliers of the two generators of \c cp. 
/// @return s-polynomial of \c cp
/// @sa multInit
poly createSpoly  ( 
  Cpair* cp,              ///<[in] critical pair 
  int numVariables,       ///<[in] global stuff for faster exponent computations 
  int* shift,             ///<[in] global stuff for faster exponent computations 
  unsigned long* negBit,  ///<[in] global stuff for faster exponent computations
  int* offsets,           ///<[in] global stuff for faster exponent computations
  poly spNoether = NULL,  ///<[in] needed for creation of s-polynomial 
  int use_buckets=0,      ///<[in] needed for creation of s-polynomial
  ring tailRing=currRing, ///<[in] needed for creation of s-polynomial
  TObject** R = NULL      ///<[in] needed for creation of s-polynomial
                  );



///////////////////////////////////////////////////////////////////////////
// INTERREDUCTION STUFF: HANDLED A BIT DIFFERENT FROM SINGULAR KERNEL    //
///////////////////////////////////////////////////////////////////////////

/// @brief \c prepRedGBRed() prepares the structure \c strat for all reduction 
/// steps of newly computed polynomials in this iteration step with elements of
/// the previous iteration steps, i.e. elements in \c redGB .
/// @sa reduceByRedGB
void prepRedGBReduction (
  kStrategy strat,      ///<[in,out]  reduction structure for this iteration
                        ///           step
  ideal F,              ///<[in]      the reduced Groebner basis of the 
                        ///           previous iteration step
  ideal Q=currQuotient, ///<[in]      quotient ring
  int   lazyReduce=0    ///<[in]      option to reduce lazy
                        );



/// @brief \c reduceByRedGBCritPair() takes a critical pair \c cp, computes the 
/// corresponding s-polynomial and reduces it w.r.t. the reduced Groebner
/// basis \c redGB which was computed in the previous iteration steps. 
/// For this reduction we use the precomputed strategy \c strat.
/// @return the s-polynomial corresponding to \c cp, reduced w.r.t. \c redGB
/// @sa prepRedGBReduction 
poly reduceByRedGBCritPair  ( 
  Cpair*    cp,           ///<[in]  critical pair whose corresponding s-polynomial
                          ///       is reduced w.r.t. \c redGB resp. \c strat
  kStrategy strat,        ///<[in]  strategy to reduce elements w.r.t. \c redGB
  int numVariables,       ///<[in]  global stuff for faster exponent computations
  int* shift,             ///<[in]  global stuff for faster exponent computations
  unsigned long* negBit,  ///<[in]  global stuff for faster exponent computations
  int* offsets,           ///<[in]  global stuff for faster exponent computations
  int  lazyReduce=0       ///<[in]  option to reduce lazy
                            );



/// @brief \c reduceByRedGBPoly() takes a polynomial \c q and reduces it w.r.t. 
/// the reduced Groebner basis \c redGB which was computed in the previous 
/// iteration steps. For this reduction we use the precomputed strategy \c strat.
/// @return the polynomial corresponding to \c cp, reduced w.r.t. \c redGB
/// @sa prepRedGBReduction 
poly reduceByRedGBPoly  ( 
  poly      q,            ///<[in]  polynomial which is to be reduced w.r.t. 
                          ///       \c redGB 
  kStrategy strat,        ///<[in]  strategy to reduce elements w.r.t. \c redGB
  int       lazyReduce=0  ///<[in]  option to reduce lazy
                        );



/// @brief \c clearStrat() deletes the strategy \c strat which was used in the 
/// current iteration step to reduce all newly generated s-polynomials by the 
/// already computed reduced Groebner basis \c redGB .
/// @sa prepRedGBReduction, reduceByRedGB
void clearStrat (
  kStrategy strat,          ///<[in]  strategy used for reduction w.r.t. \c redGB
                            ///       in the current iteration step
  ideal     F,              ///<[in]  reduced Groebner basis for which \c strat was 
                            ///       computed, i.e. \c redGB
  ideal     Q=currQuotient  ///<[in]  quotient ring
                );



///////////////////////////////////////////////////////////////////////////
// MEMORY & INTERNAL EXPONENT VECTOR STUFF: HANDLED A BIT DIFFERENT FROM //
// SINGULAR KERNEL                                                       //
///////////////////////////////////////////////////////////////////////////

/// @brief \c getShortExpVecFromArray() computes the short exponent vector of a
/// given integer vector representing a monomial.
/// @return short exponent vector of the input
/// @sa p_GetShortExpVector
unsigned long getShortExpVecFromArray (
  int*  a,            ///<[in]  integer vector for which the short exponent 
                      ///       vector is to be computed
  ring  r = currRing  ///<[in]  corresponding ring, default is \c currRing
                                      );



/// @brief Generating a corresponding exponent vector (long*) to an 
/// integer vector.
inline void getExpFromIntArray (
  const int*      exp,    ///<[in] integer exponent vector
  unsigned long*  r,      ///<[in,out] corresponding exponent vector of \c exp
  int numVariables,       ///<[in] global stuff for faster exponent computations
  int* shift,             ///<[in] global stuff for faster exponent computations
  unsigned long* negBit,  ///<[in] global stuff for faster exponent computations
  int* offsets            ///<[in] global stuff for faster exponent computations
                    );



/// @brief F5e's own GetBitFields
/// @sa GetBitFields getShortExpVecFromArray
/// @return bit fields of exponent vectors in SINGULAR
inline unsigned long GetBitFieldsF5e (
  int e,          ///<  value in integer vector
  unsigned int s, ///<  position in integer vector  
  unsigned int n  ///<  BIT_SIZEOF_LONG / currRing->N
                                            );


/// @brief Comparison of two SINGULAR-internal exponent vectors
/// @return 0 if a=b / 1 if a>b / -1 if a<b
/// @sa pLmCmp, p_MemCmp_LengthGeneral_OrdGeneral 
inline int expCmp (
  const unsigned long* a, ///<  SINGULAR-internal exponent vector
  const unsigned long* b  ///<  SINGULAR-internal exponent vector
                  );



/// @brief \c isDivisibleGetMult() is a special version of SINGULAR's internal
/// \c pLmShortDivisibleBy which does not only test for divisibility, but also 
/// stores the possible result of the division in an integer exponent vector.
/// @return 1 if the \c a divides \c b, 0 otherwise
/// @sa pLmShortDivisibleBy, multInit
static inline BOOLEAN isDivisibleGetMult ( 
  poly a,                   ///<[in] possible reducer of poly \c b
  unsigned long sev_a,      ///<[in] short exponent vector of poly \c a
  poly b,                   ///<[in] poly to be reduced
  unsigned long not_sev_b,  ///<[in] neg short exponent vector of poly \c b 
  int** mult,               ///<[in,out] pointer to the possible multiplier
                            ///          for the reduction of \c b by \c a
  BOOLEAN* isMult           ///<[in,out]  pointer to boolean which checks when
                            ///           lm(a) | lm(b) if lm(a) < lm(b)
                            ///           (isMult=1) or lm(a)=lm(b) (isMult=0)
                                      );
#endif
// HAVE_F5C
#endif
// F5C_HEADER
