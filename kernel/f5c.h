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


/// @struct \c F5Rules
/// \c F5Rules is the structure of an array of rules checked in the F5 criterion
/// representing a monomial by an integer vector resp a long, the short
/// exponent vector.
struct F5Rules 
{
  unsigned long     size;   ///<  number of elements in redGB 
  int**             label;  ///<  pointer to an array of exponent vectors for checks
                            ///   of the F5 Criterion
  unsigned long*  slabel; ///<  pointer to the corresponding short exponent
                            ///   vectors for faster checks of divisibility
};

 

/// @struct \c RewRules
/// @brief \c RewRules is the structure of a rule checked in the Rewritten criterion
/// representing a monomial by an integer vector resp a long, the short
/// exponent vector.
struct RewRules 
{
  RewRules*     next;   ///< pointer to the next element in the linked list
  int*          label;  ///< exponent vector of the rule
  unsigned long slabel; ///< short exponent vecotr of the rule
};

 

/// @struct \c Lpoly 
/// @brief \c Lpoly is the structure of a linked list of labeled polynomials, 
/// i.e. elements consisting of a polynomial \c p and a label computed by F5C+ 
/// The label is defined as an integer vector 
/// TODO----resp. in a short exponent vector form as a long in \c slabel . 
/// TODO----\c f5Rules and \c rewRules are an array resp. a list of rules (i.e. int vectors + shortExponentVectors) which are tested by the 
/// TODO----criteria of F5 in further computations.
/// TODO----\c redundant checks if the element is redundant for the gröbner basis. 
/// TODO----Note that the elements are still non-redundant for F5C+. 
struct Lpoly 
{
  Lpoly*  next;         ///< pointer to the next element in the linked list
  poly    p;            ///< polynomial part
  int*    label;        ///< exponent vector, i.e. the label/signature
  bool    redundant;    ///< Lpoly redundant?
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

 

/// @struct \c Cpair 
/// @brief \c Cpair is the structure of the list of critical pairs in F5C+
/// containing the corresponding polynomials, the multiplied labels, and the
/// multipliers.
struct Cpair 
{
  Cpair*        next;     ///<  next critical pair sorted by label
  long          ldeg;     ///<  degree of the label, needed for ordering
  int*          mlabel1;  ///<  exponent vector of the 1st multiplier * label of p1
  unsigned long smlabel1; ///<  short exponent vector of \c mlabel1
  int*          mult1;    ///<  multiplier of the 1st poly
  poly          p1;       ///<  1st poly
  int*          mlabel2;  ///<  exponent vector of the 2nd multiplier * label of p2
  unsigned long smlabel2; ///<  short exponent vector of \c mlabel2
  int*          mult2;    ///<  multiplier of the 2nd poly
  poly          p2;       ///<  2nd poly
};



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
  poly p,     ///<[in]  new element from the initial ideal \c F of \c f5cMain 
              ///       which starts the new iteration step
  ideal redGB ///<[in]  already computed and reduced Groebner basis of the ideal 
              ///       generated by all initial elements up to \c p 
              ); 



/// @brief \c criticalPairInit() computes all critical pairs of the previously
/// computed Groebner basis \c gPrev and the newly added element \c p , which is 
/// the only element in \c gCurr at this point. So this procedure is only used
/// at the very beginning of a new iteration step in F5e. Note that at this
/// point no rewrite rule exists, thus we do not need \c RewRules .
/// @sa insertCritPair
void criticalPairInit ( 
  const Lpoly& gCurr,     ///<[in]  essentially this is the labeled 
                          ///       polynomial of p at this point
  const ideal redGB,      ///<[in]  reduced Groebner basis computed in 
                          ///       the previous iteration step  
  const F5Rules& f5Rules, ///<[in]  list of exponent vectors to check the F5 
                          ///       Criterion
  Cpair* critPairs        ///<[in,out]  list of critical pairs               
                      );



/// @brief \c getShortExpVecFromArray() computes the short exponent vector of a
/// given integer vector representing a monomial.
/// @return short exponent vector of the input
/// @sa p_GetShortExpVector
unsigned long getShortExpVecFromArray (
  int*  a,            ///<[in]  integer vector for which the short exponent 
                      ///       vector is to be computed
  ring  r = currRing  ///<[in]  corresponding ring, default is \c currRing
                                      );


/// @brief \c insertCritPair() inserts \c critPair into the linked list of
/// critical pairs.
/// @return address of the first element of the list of critical pairs
/// @sa criticalPairInit 
Cpair* insertCritPair (
  Cpair*  critPair,       ///<[in]      new critical pair to be inserted
  Cpair*  critPairsFirst  ///<[in,out]  first element of the list of 
                          ///           critical pairs
                      );



/// @brief \c criterion1() checks the multiplied label of a generator of a
/// critical pair by the corresponding 
/// @return 1, if the label is detected by the F5 Criterion; 0, else
bool criterion1 (
  const int*          mlabel1,  ///<[in]  multiplied labeled to be checked
  const unsigned long smlabel1, ///<[in]  corresponding short exponent vector
  const F5Rules&      f5Rules   ///<[in]  rules for F5 Criterion checks
                );

#endif
// HAVE_F5C
#endif
// F5C_HEADER
