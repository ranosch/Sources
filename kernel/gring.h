#ifndef GRING_H
#define GRING_H
/****************************************
*  Computer Algebra System SINGULAR     *
****************************************/
/* $Id$ */
/*
* ABSTRACT additional defines etc for --with-plural
*/

#ifdef HAVE_PLURAL


#include <kernel/structs.h>
#include <kernel/ring.h>
#include <kernel/matpol.h>

// the part, related to the interface
// Changes r, Assumes that all other input belongs to curr
BOOLEAN nc_CallPlural(matrix cc, matrix dd, poly cn, poly dn, ring r,
                      bool bSetupQuotient = false,
                      bool bCopyInput = true,
                      bool bBeQuiet = false,
                      ring curr = currRing,
                      bool dummy_ring = false 
		      /* allow to create a nc-ring with 1 variable*/);

// BOOLEAN nc_CheckOrdCondition(matrix D, ring r);
// BOOLEAN nc_CheckOrdCondition(ring r); // with D == r->GetNC()->D

BOOLEAN nc_CheckSubalgebra(poly PolyVar, ring r);

// BOOLEAN nc_InitMultiplication(ring r); // should call nc_p_ProcsSet!
// NOTE: instead of constructing nc_struct and calling nc_InitMultiplication yourself - just create C, D and call nc_CallPlural!!!


BOOLEAN rIsLikeOpposite(ring rBase, ring rCandidate);


// set pProcs table for rGR and global variable p_Procs
// this should be used by p_ProcsSet in p_Procs_Set.h
void nc_p_ProcsSet(ring rGR, p_Procs_s* p_Procs);

// this function should be used inside QRing definition!
// we go from rG into factor ring rGR with factor ideal rGR->qideal.
bool nc_SetupQuotient(ring rGR, const ring rG = NULL, bool bCopy = false); // rG == NULL means that there is no base G-algebra


// used by "rSum" from ring.cc only! 
// purpose init nc structure for initially commutative ring:
// "creates a commutative nc extension; "converts" comm.ring to a Plural ring"
ring nc_rCreateNCcomm(ring r); 

void nc_rKill(ring r); // complete destructor

BOOLEAN nc_rComplete(const ring src, ring dest, bool bSetupQuotient = true); // in ring.cc

bool nc_rCopy(ring res, const ring r, bool bSetupQuotient);

// for p_Minus_mm_Mult_qq in pInline2.h
poly nc_p_Minus_mm_Mult_qq(poly p, const poly m, const poly q, int &lp,
                                    const int, const poly, const ring r);

// // for p_Plus_mm_Mult_qq in pInline2.h
// returns p + m*q destroys p, const: q, m
poly nc_p_Plus_mm_Mult_qq(poly p, const poly m, const poly q, int &lp,
                              const int, const ring r);


// poly _gnc_p_Mult_q(poly p, poly q, const int copy, const ring r);

// general multiplication:
poly _nc_p_Mult_q(poly p, poly q, const ring r);
poly _nc_pp_Mult_qq(const poly p, const poly q, const ring r);


/* subst: */
poly nc_pSubst(poly p, int n, poly e);

/* copy : */
poly nc_p_CopyGet(poly a, const ring r);
poly nc_p_CopyPut(poly a, const ring r);

void nc_PolyPolyRed(poly &b, poly p, number *c);



poly nc_CreateShortSpoly(poly p1, poly p2, const ring r=currRing);


/* brackets: p will be destroyed... */
poly nc_p_Bracket_qq(poly p, const poly q);

/* twostd: */
ideal twostd(ideal I);
/* Ann: */
ideal Approx_Step(ideal L);

/* complete reduction routines */

matrix nc_PrintMat(int a, int b, ring r, int metric);

poly p_CopyEmbed(poly p, ring srcRing, int shift, int par_shift);
poly pOppose(ring Rop, poly p);
ideal idOppose(ring Rop, ideal I);


// const int GRMASK = 1 << 1;
const int SCAMASK = 1; // For backward compatibility
const int TESTSYZSCAMASK = 0x0100 | SCAMASK; //

// NCExtensions Mask Property 
int& getNCExtensions();
int  setNCExtensions(int iMask);

// Test
bool ncExtensions(int iMask); //  = 0x0FFFF


// returns the LCM of the head terms of a and b with the given component 
// NOTE: coeff will be created but remains undefined(zero?) 
poly p_Lcm(const poly a, const poly b, const long lCompM, const ring r);

// returns the LCM of the head terms of a and b with component = max comp. of a & b
// NOTE: coeff will be created but remains undefined(zero?) 
poly p_Lcm(const poly a, const poly b, const ring r);



// //////////////////////////////////////////////////////////////////////// //
// NC inlines

inline nc_struct*& GetNC(ring r)
{
  return r->GetNC();
} 

inline nc_type& ncRingType(nc_struct* p)
{
  assume(p!=NULL);
  return (p->ncRingType());
}

inline nc_type ncRingType(ring r) // Get
{
  if(rIsPluralRing(r))
    return (ncRingType(r->GetNC()));
  else
    return (nc_error);
}

inline void ncRingType(ring r, nc_type t) // Set
{
  assume((r != NULL) && (r->GetNC() != NULL));
  ncRingType(r->GetNC()) = t;
}

inline void ncRingType(nc_struct* p, nc_type t) // Set
{
  assume(p!=NULL);
  ncRingType(p) = t;
}


// //////////////////////////////////////////////////////

// returns m*p, does neither destroy p nor m
inline poly nc_mm_Mult_pp(const poly m, const poly p, const ring r)
{
  assume(rIsPluralRing(r));
  assume(r->GetNC()->p_Procs.mm_Mult_pp!=NULL);
  return r->GetNC()->p_Procs.mm_Mult_pp(m, p, r);
//  return pp_Mult_mm( p, m, r);
}


// returns m*p, does destroy p, preserves m
inline poly nc_mm_Mult_p(const poly m, poly p, const ring r)
{
  assume(rIsPluralRing(r));
  assume(r->GetNC()->p_Procs.mm_Mult_p!=NULL);
  return r->GetNC()->p_Procs.mm_Mult_p(m, p, r);
//   return p_Mult_mm( p, m, r);
}

inline poly nc_CreateSpoly(const poly p1, const poly p2, const ring r)
{
  assume(rIsPluralRing(r));
  assume(r->GetNC()->p_Procs.SPoly!=NULL);
  return r->GetNC()->p_Procs.SPoly(p1, p2, r);
}

inline poly nc_ReduceSpoly(const poly p1, poly p2, const ring r)
{
  assume(rIsPluralRing(r));
  assume(r->GetNC()->p_Procs.ReduceSPoly!=NULL);
#ifdef PDEBUG
//  assume(p_LmDivisibleBy(p1, p2, r));
#endif
  return r->GetNC()->p_Procs.ReduceSPoly(p1, p2, r);
}

/*
inline void nc_PolyReduce(poly &b, const poly p, number *c, const ring r) // nc_PolyPolyRed
{
  assume(rIsPluralRing(r));
//  assume(r->GetNC()->p_Procs.PolyReduce!=NULL);
//  r->GetNC()->p_Procs.PolyReduce(b, p, c, r);
}
*/

inline void nc_kBucketPolyRed(kBucket_pt b, poly p, number *c)
{
  assume(rIsPluralRing(currRing));

//   return gnc_kBucketPolyRedNew(b, p, c);

  assume(currRing->GetNC()->p_Procs.BucketPolyRed!=NULL);
  return currRing->GetNC()->p_Procs.BucketPolyRed(b, p, c);
}

inline void nc_BucketPolyRed_Z(kBucket_pt b, poly p, number *c)
{
  assume(rIsPluralRing(currRing));

//   return gnc_kBucketPolyRed_ZNew(b, p, c);

  assume(currRing->GetNC()->p_Procs.BucketPolyRed_Z!=NULL);
  return currRing->GetNC()->p_Procs.BucketPolyRed_Z(b, p, c);

}

inline ideal nc_GB(const ideal F, const ideal Q, const intvec *w, const intvec *hilb, kStrategy strat)
{
  assume(rIsPluralRing(currRing));

  assume(currRing->GetNC()->p_Procs.GB!=NULL);
  return currRing->GetNC()->p_Procs.GB(F, Q, w, hilb, strat);

/*
  if (rHasLocalOrMixedOrder(currRing))
  {
    assume(currRing->GetNC()->p_Procs.LocalGB!=NULL);
    return currRing->GetNC()->p_Procs.LocalGB(F, Q, w, hilb, strat);
  } else
  {
    assume(currRing->GetNC()->p_Procs.GlobalGB!=NULL);
    return currRing->GetNC()->p_Procs.GlobalGB(F, Q, w, hilb, strat);
  }
*/
}


// Macros used to access upper triangle matrices C,D... (which are actually ideals) // afaik
//#define UPMATELEM(i,j,nVar) ( (nVar * ((i)-1) - ((i) * ((i)-1))/2 + (j)-1)-(i) )
static inline int UPMATELEM(const int i, const int j, const int nVar)
{
   assume(i < j);
   assume(0 < i && j <= nVar);

   return (nVar * ((i)-1) - ((i) * ((i)-1))/2 + (j)-1)-(i);
}



// inline const nc_struct* GetNC() const { return GetBasering()->GetNC(); } 


// read only access to NC matrices C/D:
// get C_{i,j}, 1 <= row = i < j = col <= N
inline poly GetC( const ring r, int i, int j ) 
{
  assume(r!= NULL && rIsPluralRing(r));
  const matrix C = GetNC(r)->C;
  assume(C != NULL);
  const int ncols = C->ncols;
  assume( (i > 0) && (i < j) && (j <= ncols) );
  return ( C->m[ncols * ((i)-1) + (j)-1] );
}

// get D_{i,j}, 1 <= row = i < j = col <= N
inline poly GetD( const ring r, int i, int j ) 
{
  assume(r!= NULL && rIsPluralRing(r));
  const matrix D = GetNC(r)->D;
  assume(D != NULL);
  const int ncols = D->ncols;
  assume( (i > 0) && (i < j) && (j <= ncols) );
  return ( D->m[ncols * ((i)-1) + (j)-1] );
}


#ifdef PLURAL_INTERNAL_DECLARATIONS

// we need nc_gr_initBba for sca_gr_bba and gr_bba.
void nc_gr_initBba(ideal F,kStrategy strat); 
BOOLEAN gnc_InitMultiplication(ring r, bool bSetupQuotient = false); // just for a moment


#ifndef HIDEVARIABLE
# define HIDEVARIABLE(x) UNUSED__ ## x
#endif

#ifndef UNUSED

# if defined(__GNUC__)
#   define UNUSED(x) HIDEVARIABLE(x) __attribute__((unused)) 
# elif defined(__LCLINT__) 
#  define UNUSED(x) /*@unused@*/ HIDEVARIABLE(x)
# else 
#  define UNUSED(x) HIDEVARIABLE(x)
# endif

#endif

#define UNUSED_ARGUMENT(x) (void) HIDEVARIABLE(x)


static inline poly nc_GetMT(const int UNUSED(i), const int UNUSED(j), const matrix MT, const int a = 1, const int b = 1, const ring_const UNUSED(r) = currRing)
{
   UNUSED_ARGUMENT(i);   
   UNUSED_ARGUMENT(j);   
   UNUSED_ARGUMENT(r);   

   assume(MT != NULL);
   
   assume(a > 0 && b > 0);
   assume(a <= MATROWS(MT));
   assume(b <= MATCOLS(MT));
   
   return MATELEM(MT,a,b);
}

static inline poly nc_GetMT(const int i, const int j, matrix const *MT, const int a = 1, const int b = 1, const ring_const r = currRing)
{
   assume(MT != NULL);
   assume(j < i);
   const int N = r->N;
   assume(0 < j && i <= N);

   const int id = UPMATELEM(j, i, N); ///< Note the reversion!

   if(true)
   {
      assume( r->GetNC()->ppMTsize != NULL );
      const int s = r->GetNC()->ppMTsize[id];
      assume(a <= s);
      assume(b <= s);
   }  

   return nc_GetMT(i, j, MT[id], a, b, r);
}


// get var(i)^a * var(j)^b // x_i = y,  x_j = x !
// assumes i > j
// either a = b = 1, or it is in the cache...
static inline poly nc_GetMT(const int i, const int j, const int a = 1, const int b = 1, const ring_const r = currRing)
{
   assume(r != NULL);
   return nc_GetMT(i, j, r->GetNC()->ppMT, a, b, r);
}

static inline poly nc_SetMT(const int UNUSED(i), const int UNUSED(j), matrix MT, const int a, const int b, poly p, const ring_const UNUSED(r) = currRing)
{
   UNUSED_ARGUMENT(i);   
   UNUSED_ARGUMENT(j);   
   UNUSED_ARGUMENT(r);   

   assume(MT != NULL);
   
   assume(a > 0 && b > 0);
   assume(a <= MATROWS(MT));
   assume(b <= MATCOLS(MT));
   
   MATELEM(MT,a,b) = p;
}

static inline void nc_SetMT(const int i, const int j, matrix *MT, const int a, const int b, poly p, const ring_const r = currRing)
{
   assume(MT != NULL);
   assume(j < i);
   const int N = r->N;
   assume(0 < j && i <= N);

   const int id = UPMATELEM(j, i, N); ///< Note the reversion!

   if(true)
   {
      assume( r->GetNC()->ppMTsize != NULL );
      const int s = r->GetNC()->ppMTsize[id];
      assume(a <= s);
      assume(b <= s);
   }  

   nc_SetMT(i, j, MT[id], a, b, p, r);
}

static inline void nc_SetMT(const int i, const int j, const int a, const int b, poly p, const ring_const r = currRing)
{
   assume(r != NULL);
   nc_SetMT(i, j, r->GetNC()->ppMT, a, b, p, r);
}


static inline int nc_GetMTsize(const int id, int const *MTsize, const ring_const UNUSED(r) = currRing)
{
   UNUSED_ARGUMENT(r);
   assume(MTsize != NULL);
   const int s = MTsize[id];
   return s;
}

static inline int nc_GetMTsize(const int i, const int j, const ring_const r = currRing)
{
   assume(r != NULL);
   assume(j < i);
   const int N = r->N;
   assume(0 < j && i <= N);

   const int id = UPMATELEM(j, i, N); ///< Note the reversion!

   return nc_GetMTsize(id, r->GetNC()->ppMTsize, r);
}



#endif // PLURAL_INTERNAL_DECLARATIONS

#endif // HAVE_PLURAL :(
#endif // 
