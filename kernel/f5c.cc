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

#include <kernel/mod2.h>

#ifdef HAVE_F5C
#include <omalloc/omalloc.h>
#include <kernel/options.h>
#include <kernel/kutil.h>
#include <kernel/kInline.cc>
#include <kernel/polys.h>
#include <kernel/febase.h>
#include <kernel/kstd1.h>
#include <kernel/khstd.h>
#include <kernel/stairc.h>
#include <kernel/weight.h>
#include <kernel/intvec.h>
#include <kernel/ideals.h>
#include <kernel/timer.h>
#include <kernel/kbuckets.h>
#include <kernel/f5c.h>
#include <unistd.h>

#ifdef HAVE_PLURAL
#include <kernel/sca.h>
#endif


// define if tailrings should be used
#define HAVE_TAIL_RING

// define if buckets should be used
#define MORA_USE_BUCKETS

#ifndef NDEBUG
# define MYTEST 0
#else /* ifndef NDEBUG */
# define MYTEST 0
#endif /* ifndef NDEBUG */

#if MYTEST 
#ifdef HAVE_TAIL_RING
#undef HAVE_TAIL_RING
#endif /* ifdef HAVE_TAIL_RING */
#endif /* if MYTEST */

#ifdef NDEBUG
#undef NDEBUG
#endif
#ifdef PDEBUG
#undef PDEBUG
#define PDEBUG 0 
#endif
#ifdef KDEBUG
static int f5_count = 0;
#endif /* KDEBUG */
void kDebugPrint(kStrategy strat);



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
unsigned long rewRulesSize      = 0;
unsigned long f5RulesSize       = 0;
unsigned long stratSize         = 0;
unsigned long numberReductions  = 0;
unsigned long number1Reductions = 0;
unsigned long zeroReductions    = 0;
 
/// NOTE that the input must be homogeneous to guarantee termination and
/// correctness. Thus these properties are assumed in the following.
ideal f5cMain ( ideal F, ideal Q, tHomog h,intvec ** w, intvec *hilb,
                int syzComp, int newIdeal, intvec *vw ) 
{
  if( idIs0(F) )
  {
    return idInit(1,F->rank);
  }
  
  ideal r;
  BOOLEAN b         = pLexOrder, toReset  = FALSE;
  BOOLEAN delete_w  = ( w==NULL );
  kStrategy strat   = new skStrategy;

  if( !TEST_OPT_RETURN_SB ) 
  {
    strat->syzComp  = syzComp;
  }
  if( TEST_OPT_SB_1 )
  {
    strat->newIdeal = newIdeal;
  }
  if( rField_has_simple_inverse() )
  {
    strat->LazyPass = 20;
  }
  else
  {
    strat->LazyPass = 2;
  }
  strat->LazyDegree   = 1;
  strat->enterOnePair = enterOnePairNormal;
  strat->chainCrit    = critF5;
  strat->ak           = idRankFreeModule(F);
  strat->kModW        = kModW  = NULL;
  strat->kHomW        = kHomW  = NULL;
  if( vw != NULL )
  {
    pLexOrder     = FALSE;
    strat->kHomW  = kHomW = vw;
    pFDegOld      = pFDeg;
    pLDegOld      = pLDeg;
    pSetDegProcs( kHomModDeg );
    toReset       = TRUE;
  }
  if( h==testHomog )
  {
    if( strat->ak==0 )
    {
      h = ( tHomog )idHomIdeal( F, Q );
      w = NULL;
    }
    else 
    {
      if( !TEST_OPT_DEGBOUND )
      {
        h = ( tHomog )idHomModule( F, Q, w );
      }
    }
  }
  pLexOrder = b;
  if( h==isHomog )
  {
    if( strat->ak>0 && (w!=NULL) && (*w!=NULL) )
    {
      strat->kModW  = kModW = *w;
      if( vw == NULL )
      {
        pFDegOld  = pFDeg;
        pLDegOld  = pLDeg;
        pSetDegProcs(kModDeg);
        toReset   = TRUE;
      }
    }
    pLexOrder = TRUE;
    if( hilb==NULL )
    {
      strat->LazyPass *=  2;
    }
  }
  strat->homog  = h;
#ifdef KDEBUG
  idTest( F );
  idTest( Q );

#if MYTEST
  if( TEST_OPT_DEBUG )
  {
    PrintS( "// kSTD: currRing: " );
    rWrite( currRing );
  }
#endif

#endif
#ifdef HAVE_PLURAL
  if ( rIsPluralRing(currRing) )
  {
    // z2homog: for Z2 product criterion
    const BOOLEAN bIsSCA  = rIsSCA( currRing ) && strat->z2homog; 
    strat->no_prod_crit   = !bIsSCA;
    if( w!=NULL )
    {
      r = nc_GB( F, Q, *w, hilb, strat );
    }
    else
    {
      r = nc_GB( F, Q, NULL, hilb, strat );
    }
  }
  else
#endif
#ifdef HAVE_RINGS
  if( rField_is_Ring(currRing) )
  { 
    r = bba( F, Q, NULL, hilb, strat );
  } 
  else
#endif
  {
    if( pOrdSgn==-1 )
    {
      if( w!=NULL )
      {
        r = mora( F, Q, *w, hilb, strat );
      }
      else
      {
        r = mora( F, Q, NULL, hilb, strat );
      }
    }
    else
    {
      if( w!=NULL )
      {
        r = doF5( F, Q, *w, hilb, strat );
      }
      else
      {
        r = doF5( F, Q, NULL, hilb, strat );
      }
    }
  }
#ifdef KDEBUG
  idTest( r );
#endif
  if( toReset )
  {
    kModW = NULL;
    pRestoreDegProcs( pFDegOld, pLDegOld );
  }
  pLexOrder = b;
  HCord     = strat->HCord;
  delete( strat );
  if( (delete_w) && (w!=NULL) && (*w!=NULL) ) 
  {
    delete *w;
  }
  return r;
}



ideal doF5( ideal F, ideal Q, intvec *w, intvec *hilb, kStrategy strat )
{
#ifdef KDEBUG
  f5_count++;
  int loop_count = 0;
#endif /* KDEBUG */
  om_Opts.MinTrack = 5;
  int srmax,lrmax, red_result = 1;
  int olddeg, reduc;
  int hilbeledeg  = 1, hilbcount = 0, minimcnt = 0;
  BOOLEAN withT = FALSE;

  // set Gebauer-Moeller, honey, sugarCrit
  initF5( strat ); 
  initBuchMoraPos( strat );
  initHilbCrit( F, Q, &hilb, strat );
  initBba( F, strat );
  // set enterS, spSpolyShort, reduce, red, initEcart, initEcartPair
  initSTLF5( F, Q, strat );
  if( strat->minim>0 ) 
  {
    strat->M  = idInit( IDELEMS(F), F->rank );
  }
  srmax = strat->sl;
  reduc = olddeg = lrmax = 0;

#ifndef NO_BUCKETS
  if( !TEST_OPT_NOT_BUCKETS )
  {
    strat->use_buckets = 1;
  }
#endif

  // redtailBBa against T for inhomogenous input
  if( !TEST_OPT_OLDSTD )
  {
    withT = !strat->homog;
  }

  // strat->posInT = posInT_pLength;
  kTest_TS( strat );

#ifdef KDEBUG
#if MYTEST
  if( TEST_OPT_DEBUG )
  {
    PrintS( "bba start GB: currRing: " );
    rDebugPrint( currRing );
    PrintLn();
  }
#endif /* MYTEST */
#endif /* KDEBUG */

#ifdef HAVE_TAIL_RING
  // create strong gcd poly computes with tailring and S[i] ->to be fixed  
  if( !idIs0(F) && (!rField_is_Ring()) )  
  {
    kStratInitChangeTailRing( strat );
  }
#endif
  if( BVERBOSE(23) )
  {
    if( test_PosInT!=NULL ) 
    {
      strat->posInT = test_PosInT;
    }
    if( test_PosInL!=NULL ) 
    {
      strat->posInL = test_PosInL;
    }
    kDebugPrint( strat );
  }


#ifdef KDEBUG
  kDebugPrint( strat );
#endif
  /* compute------------------------------------------------------- */
  for( int _ctr=1; _ctr<IDELEMS(F); _ctr++ )
  {
      //////////////////////////////////////////////
      // ADDING NEW POLY TO STRAT: NEXT ITERATION //
      //////////////////////////////////////////////
    pWrite( F->m[_ctr] );
    Print("HERE\n");
    addSL( _ctr, F, Q, strat );
    Print("HERE\n");
  Print( "ITERATION %d\n", _ctr );
  while( strat->Ll>=0 )
  {
    Print("START WHILE\n");
    if( strat->Ll>lrmax ) 
    {
      // stat.
      lrmax =strat->Ll;
    }
#ifdef KDEBUG
    loop_count++;
    if( TEST_OPT_DEBUG ) 
    {
      messageSets( strat );
    }
#endif
    if( strat->Ll==0 ) 
    {
      strat->interpt  = TRUE;
    }
    if( TEST_OPT_DEGBOUND && 
        ((strat->honey && (strat->L[strat->Ll].ecart+pFDeg(strat->L[strat->Ll].p,currRing)>Kstd1_deg))
        || ((!strat->honey) && (pFDeg(strat->L[strat->Ll].p,currRing)>Kstd1_deg))) )
    {
      /*
       *stops computation if
       * 24 IN test and the degree +ecart of L[strat->Ll] is bigger then
       *a predefined number Kstd1_deg
       */
      while ( (strat->Ll>=0) && 
              (strat->L[strat->Ll].p1!=NULL) && (strat->L[strat->Ll].p2!=NULL) && 
              ((strat->honey && (strat->L[strat->Ll].ecart+pFDeg(strat->L[strat->Ll].p,currRing)>Kstd1_deg))
              || ((!strat->honey) && (pFDeg(strat->L[strat->Ll].p,currRing)>Kstd1_deg)))
            )
      {
        deleteInL( strat->L, &strat->Ll, strat->Ll, strat );
      }
      if( strat->Ll<0 ) 
      {
        break;
      }
      else 
      {
        strat->noClearS = TRUE;
      }
    }
    /* picks the last element from the lazyset L */
    strat->P = strat->L[strat->Ll];
    strat->Ll--;

    if( pNext(strat->P.p)==strat->tail )
    {
      // deletes the short spoly
#ifdef HAVE_RINGS
      if( rField_is_Ring(currRing) )
      {
        pLmDelete( strat->P.p );
      }
      else
#endif
        pLmFree( strat->P.p );
      strat->P.p  = NULL;
      poly m1     = NULL, m2 = NULL;

      // check that spoly creation is ok
      while( strat->tailRing != currRing &&
             !kCheckSpolyCreation(&(strat->P), strat, m1, m2) )
      {
        assume( m1==NULL && m2==NULL );
        // if not, change to a ring where exponents are at least
        // large enough
        if( !kStratChangeTailRing(strat) )
        {
          WerrorS( "OVERFLOW..." );
          break;
        }
      }
      // create the real one
      ksCreateSpoly(  &(strat->P), NULL, strat->use_buckets,
                      strat->tailRing, m1, m2, strat->R );
    }
    else 
    {
      if( strat->P.p1==NULL )
      {
        if( strat->minim>0 )
          strat->P.p2 = p_Copy( strat->P.p, currRing, strat->tailRing );
        // for input polys, prepare reduction
        strat->P.PrepareRed( strat->use_buckets );
      }
    }
  
    if( (strat->P.p==NULL) && (strat->P.t_p==NULL) )
    {
      red_result = 0;
    }
    else
    {
      if( TEST_OPT_PROT )
      {
        message(  (strat->honey ? strat->P.ecart : 0) + strat->P.pFDeg(),
                  &olddeg, &reduc, strat, red_result  );
      }
  
      /* reduction of the element choosen from L */

      red_result = strat->red( &strat->P, strat );
      if( errorreported )  
      { 
        break;
      }
    }

    if( strat->overflow )
    {
      if( !kStratChangeTailRing(strat) ) 
      { 
        Werror("OVERFLOW.."); 
        break;
      }
    }

    // reduction to non-zero new poly
    if( red_result==1 )
    {
      // get the polynomial (canonicalize bucket, make sure P.p is set)
      strat->P.GetP( strat->lmBin );

      /* statistic */
      if( TEST_OPT_PROT ) 
      {
        PrintS( "s" );
      }

      int pos = posInS( strat, strat->sl, strat->P.p, strat->P.ecart );

#ifdef KDEBUG
#if MYTEST
      PrintS( "New S: " ); 
      pDebugPrint( strat->P.p ); 
      PrintLn();
#endif /* MYTEST */
#endif /* KDEBUG */

      // reduce the tail and normalize poly
      // in the ring case we cannot expect LC(f) = 1,
      // therefore we call pContent instead of pNorm
      if( (TEST_OPT_INTSTRATEGY) || (rField_is_Ring(currRing)) )
      {
        strat->P.pCleardenom();
        if( (TEST_OPT_REDSB) || (TEST_OPT_REDTAIL) )
        {
          strat->P.p = redtailBba( &(strat->P), pos-1, strat, withT );
          strat->P.pCleardenom();
        }
      }
      else
      {
        strat->P.pNorm();
        if( (TEST_OPT_REDSB) || (TEST_OPT_REDTAIL) )
        {
          strat->P.p  = redtailBba( &(strat->P), pos-1, strat, withT );
        }
      }

#ifdef KDEBUG
      if( TEST_OPT_DEBUG )
      {
        PrintS( "new s:" );
        strat->P.wrp();
        PrintLn();
      }
#if MYTEST
      PrintS("New (reduced) S: "); 
      pDebugPrint(strat->P.p); 
      PrintLn();
#endif /* MYTEST */
#endif /* KDEBUG */

      // min_std stuff
      if( (strat->P.p1==NULL) && (strat->minim>0) )
      {
        if( strat->minim==1 )
        {
          strat->M->m[minimcnt] = p_Copy( strat->P.p, currRing, strat->tailRing );
          p_Delete( &strat->P.p2, currRing, strat->tailRing );
        }
        else
        {
          strat->M->m[minimcnt] = strat->P.p2;
          strat->P.p2 = NULL;
        }
        if( (strat->tailRing!=currRing) && pNext(strat->M->m[minimcnt])!=NULL )
        {
          pNext( strat->M->m[minimcnt] )  = strat->p_shallow_copy_delete(
                                                pNext(strat->M->m[minimcnt]),
                                                strat->tailRing, currRing,
                                                currRing->PolyBin       );
        }
        minimcnt++;
      }

      // enter into S, L, and T
      enterT( strat->P, strat );
#ifdef HAVE_RINGS
      if( rField_is_Ring(currRing) )
      {
        superenterpairs(  strat->P.p, strat->sl, strat->P.ecart, 
                          pos, strat, strat->tl );
      }
      else
#endif
      enterpairs( strat->P.p, strat->sl, strat->P.ecart, pos, strat, strat->tl );
      // posInS only depends on the leading term
      strat->enterS( strat->P, pos, strat, strat->tl );

      if( hilb!=NULL ) 
      {
        khCheck( Q, w, hilb, hilbeledeg, hilbcount, strat );
      }
      if( strat->P.lcm!=NULL )
      {
#ifdef HAVE_RINGS
        pLmDelete( strat->P.lcm );
#else
        pLmFree( strat->P.lcm );
#endif
      }
      if( strat->sl>srmax ) 
      {
        srmax = strat->sl;
      }
    }
    else 
    {
      if( (strat->P.p1==NULL) && (strat->minim>0) )
      {
        p_Delete( &strat->P.p2, currRing, strat->tailRing );
      }
    }
#ifdef KDEBUG
    memset( &(strat->P), 0, sizeof(strat->P) );
#endif /* KDEBUG */
    kTest_TS( strat );
    Print("END WHILE\n");
  }

  }
#ifdef KDEBUG
#if MYTEST
  PrintS( "bba finish GB: currRing: " ); 
  rWrite( currRing );
#endif /* MYTEST */
  if( TEST_OPT_DEBUG ) 
  {
    messageSets( strat );
  }
#endif /* KDEBUG */

  if( TEST_OPT_SB_1 )
  {
    int k = 1;
    int j;
    while( k<=strat->sl )
    {
      j = 0;
      loop
      {
        if( j>=k ) 
        {
          break;
        }
        clearS( strat->S[j], strat->sevS[j], &k, &j, strat );
        j++;
      }
      k++;
    }
  }

  /* complete reduction of the standard basis--------- */
  if( TEST_OPT_REDSB )
  {
    completeReduce( strat );
#ifdef HAVE_TAIL_RING
    if( strat->completeReduce_retry )
    {
      // completeReduce needed larger exponents, retry
      // to reduce with S (instead of T)
      // and in currRing (instead of strat->tailRing)
      cleanT( strat );
      strat->tailRing = currRing;
      int i;
      for( i=strat->sl; i>=0; i-- ) 
      {
        strat->S_2_R[i] = -1;
      }
      completeReduce( strat );
    }
#endif
  }
  else 
  {
    if( TEST_OPT_PROT ) 
    {
      PrintLn();
    }
  }

  // -------------- release temp data ----------------- 
  exitBuchMora( strat );
  if( TEST_OPT_WEIGHTM )
  {
    pRestoreDegProcs( pFDegOld, pLDegOld );
    if( ecartWeights )
    {
      omFreeSize( (ADDRESS)ecartWeights, (pVariables+1)*sizeof(short) );
      ecartWeights  = NULL;
    }
  }
  if( TEST_OPT_PROT ) 
  {
    messageStat( srmax, lrmax, hilbcount, strat );
  }
  if( Q!=NULL ) 
  {
    updateResult( strat->Shdl, Q, strat );
  }

#ifdef KDEBUG
#if MYTEST
  PrintS( "bba_end: currRing: " ); 
  rWrite( currRing );
#endif /* MYTEST */
#endif /* KDEBUG */
  idTest( strat->Shdl );

  return( strat->Shdl );
}



static poly redGlobalF5( poly h, int maxIndex, kStrategy strat )
{
  int j = 0;
  unsigned long not_sev = ~ pGetShortExpVector( h );

  while( j<=maxIndex )
  {
    if( pLmShortDivisibleBy(strat->S[j], strat->sevS[j], h, not_sev) )
    {
      h = ksOldSpolyRed( strat->S[j], h, strat->kNoetherTail() );
      if( h==NULL ) 
      {
        return NULL;
      }
      j       = 0;
      not_sev = ~ pGetShortExpVector( h );    
    }
    else 
    {
      j++;
    }
  }
  return h;
}



static poly redLocalF5( poly h, int maxIndex, kStrategy strat )
{
  int j = 0;
  int  e, l;
  unsigned long not_sev = ~ pGetShortExpVector( h );

  if( maxIndex>=0 )
  {
    e = pLDeg( h, &l, currRing ) - pFDeg( h, currRing );
    do
    {
      if( pLmShortDivisibleBy(strat->S[j], strat->sevS[j], h, not_sev)
          && ((e>=strat->ecartS[j]) || strat->kHEdgeFound) )
      {
#ifdef KDEBUG
        if( TEST_OPT_DEBUG )
        {
          PrintS( "reduce " );
          wrp( h );
          Print( " with S[%d] (", j );
          wrp( strat->S[j] );
        }
#endif
        h = ksOldSpolyRed( strat->S[j], h, strat->kNoetherTail() );
#ifdef KDEBUG
        if( TEST_OPT_DEBUG )
        {
          PrintS( ")\nto " ); 
          wrp( h ); 
          PrintLn();
        }
#endif
        // pDelete(&h);
        if( h==NULL ) 
        {
          return NULL;
        }
        e       = pLDeg( h, &l, currRing ) - pFDeg( h, currRing );
        j       = 0;
        not_sev = ~ pGetShortExpVector( h );
      }
      else 
      {
        j++;
      }
    }
    while( j<=maxIndex );
  }
  return h;
}



ideal f5cIter ( 
                poly p, ideal redGB, int numVariables, int* shift, 
                unsigned long* negBitmaskShifted, int* offsets
              )
{
#if F5EDEBUG1
  Print("F5CITER-BEGIN\n");
  Print("NEXT ITERATION ELEMENT: ");
  pWrite( pHead(p) );
#endif
#if F5EDEBUG3
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
  prepRedGBReduction( strat, redGB );
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
  // set global variables for the sizes of F5 & Rewritten Rules available
  rewRulesSize        = f5RulesSize = 2*(strat->sl+1);
  stratSize           = strat->sl+1;
  // create array of leading monomials of previously computed elements in redGB
  F5Rules* f5Rules    = (F5Rules*) omAlloc(sizeof(struct F5Rules));
  RewRules* rewRules  = (RewRules*) omAlloc(sizeof(struct RewRules));
  // malloc memory for all rules
  f5Rules->label      = (int**) omAlloc(f5RulesSize*sizeof(int*));
  f5Rules->slabel     = (unsigned long*) omAlloc(f5RulesSize*
                        sizeof(unsigned long)); 
  
  // malloc two times the size of the previous Groebner basis
  // Note that we possibly need more memory in this iteration step!
  rewRules->label     = (int**) omAlloc((rewRulesSize)*sizeof(int*));
  rewRules->slabel    = (unsigned long*) omAlloc((rewRulesSize)*
                        sizeof(unsigned long)); 
  // Initialize a first (dummy) rewrite rule for the initial polynomial of this
  // iteration step:
  // (a) Note that we are allocating & setting all entries to zero for this first 
  //     rewrite rule.
  // (b) Note also that the size of strat is >=1.
  rewRules->label[0]    = (int*) omAlloc0( (currRing->N+1)*sizeof(int) );
  rewRules->slabel[0]   = 0;
  for(i=1; i<rewRulesSize; i++) 
  {
    rewRules->label[i]  =  (int*) omAlloc( (currRing->N+1)*sizeof(int) );
  } 
  pTest( redGB->m[0] );
  // use the strategy strat to get the F5 Rules:
  // When preparing strat we have already computed & stored the short exonent
  // vectors there => do not recompute them again 
  for( i=0; i<stratSize; i++ ) 
  {
    f5Rules->label[i]   =  (int*) omAlloc( (currRing->N+1)*sizeof(int) );
    pGetExpV( strat->S[i], f5Rules->label[i] );
    f5Rules->slabel[i]  = strat->sevS[i];
  } 
  // alloc memory for the rest of the labels
  for( ; i<f5RulesSize; i++ ) 
  {
    f5Rules->label[i]   = (int*) omAlloc( (currRing->N+1)*sizeof(int) );
  } 

  rewRules->size  = 1;
  f5Rules->size   = stratSize;
  // reduce and initialize the list of Lpolys with the current ideal generator p
#if F5EDEBUG3
  Print("Before reduction\n");
  pTest( p );
#endif
  //p = kNF( redGB, NULL, p );
  p = reduceByRedGBPoly( p, strat );
#if F5EDEBUG3
  Print("After reduction: ");
  pTest( p );
  pWrite( pHead(p) );
#endif
  if( p )
  {
    pNorm( p );  
    Lpoly* gCurr      = (Lpoly*) omAlloc( sizeof(Lpoly) );
    gCurr->next       = NULL;
    gCurr->sExp       = pGetShortExpVector( p );
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
#if F5EDEBUG2
      Print("%d INSERT TO REDGB: ",counter);
      pWrite( gCurrFirst->p );
#endif
      idInsertPoly( redGB, gCurrFirst->p );
      temp        = gCurrFirst;
      gCurrFirst  = gCurrFirst->next;
      omFree( temp );
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
  for( i=0; i<f5RulesSize; i++ )
  {
    omFreeSize( f5Rules->label[i], (currRing->N+1)*sizeof(int) );
  }
  omFreeSize( f5Rules->label, f5RulesSize*sizeof(int*) );
  omFreeSize( f5Rules, sizeof(F5Rules) );
  
  for( i=0; i<rewRulesSize; i++ )
  {
    omFreeSize( rewRules->label[i], (currRing->N+1)*sizeof(int) );
  }
  omFreeSize( rewRules->slabel, rewRulesSize*sizeof(unsigned long) );
  omFreeSize( rewRules->label, rewRulesSize*sizeof(int*) );
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
    if(!criterion1(cpTemp->mLabel1, cpTemp->smLabel1, &f5Rules, strat)) 
    {
      // completing the construction of the new critical pair and inserting it
      // to the list of critical pairs 
      cpTemp->p2        = strat->S[i];
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
  if(!criterion1(cpTemp->mLabel1, cpTemp->smLabel1, &f5Rules, strat)) 
  {
    // completing the construction of the new critical pair and inserting it
    // to the list of critical pairs 
    cpTemp->p2        = strat->S[strat->sl];
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
    
    // testing the F5 Criterion
#if F5EDEBUG1
    Print("2nd generator of pair: ");
    pWrite( pHead(strat->S[i]) );
#endif
    if( !criterion1(cpTemp->mLabel1, cpTemp->smLabel1, &f5Rules, strat) &&
        !criterion2(cpTemp->mLabel1, cpTemp->smLabel1, &rewRules, cpTemp->rewRule1)
      )
    {
      // completing the construction of the new critical pair and inserting it
      // to the list of critical pairs 
      cpTemp->p2        = strat->S[i];
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
    pWrite( pHead(strat->S[strat->sl]) );
#endif
  // testing the F5 Criterion
  if( !criterion1(cpTemp->mLabel1, cpTemp->smLabel1, &f5Rules, strat) &&
      !criterion2(cpTemp->mLabel1, cpTemp->smLabel1, &rewRules, cpTemp->rewRule1)
    )
  {
    // completing the construction of the new critical pair and inserting it
    // to the list of critical pairs 
    cpTemp->p2        = strat->S[strat->sl];
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
  unsigned long* mLabelExp;
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
        pairNeeded          =   TRUE;
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
      if( 
          !criterion1(cpTemp->mLabel1, cpTemp->smLabel1, &f5Rules, strat) 
          && !criterion1(cpTemp->mLabel2, cpTemp->smLabel2, &f5Rules, strat) 
          && !criterion2(cpTemp->mLabel1, cpTemp->smLabel1, &rewRules, cpTemp->rewRule1)
          && !criterion2(cpTemp->mLabel2, cpTemp->smLabel2, &rewRules, cpTemp->rewRule2)
        ) 
      {
        // completing the construction of the new critical pair and inserting it
        // to the list of critical pairs 
        // now we really need the memory for the exp label
        cpTemp->mLabelExp   = pOne();
        getExpFromIntArray( cpTemp->mLabel1, cpTemp->mLabelExp, 
                            numVariables, shift, negBitmaskShifted, offsets
                          );
        getExpFromIntArray( cpTemp->mLabel2, checkExp, numVariables,
                            shift, negBitmaskShifted, offsets
                          );
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
    pairNeeded  = TRUE;
    gCurrIter   = gCurrIter->next;
  }
  // same critical pair processing for the last element in gCurr
  // This is outside of the loop to keep memory low, since we know that after
  // this element no new memory for a critical pair must be allocated.
  cpTemp->p2  = gCurrIter->p;
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
      pairNeeded          =   TRUE;
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
    
    // testing the F5 Criterion
    if( 
        !criterion1(cpTemp->mLabel1, cpTemp->smLabel1, &f5Rules, strat) 
        && !criterion1(cpTemp->mLabel2, cpTemp->smLabel2, &f5Rules, strat) 
        && !criterion2(cpTemp->mLabel1, cpTemp->smLabel1, &rewRules, cpTemp->rewRule1)
        && !criterion2(cpTemp->mLabel2, cpTemp->smLabel2, &rewRules, cpTemp->rewRule2)
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
      // first element in last has equal label
      if( pLmCmp(cp->mLabelExp, tempForDel->mLabelExp) == 0 )
      {
            cp->next          = tempForDel->next;
            tempForDel->next  = cp;
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
            cp->next          = tempForDel->next;
            tempForDel->next  = cp;
          }
          if( pLmCmp(cp->mLabelExp, (tempForDel->next)->mLabelExp) == -1 )
          {
            cp->next          = tempForDel->next;
            tempForDel->next  = cp;
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
                            const F5Rules* f5Rules, const kStrategy strat
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



inline void newCriterion1 ( CpairDegBound** cp, const F5Rules* f5Rules )
{
  int i = 0;
  int j = currRing->N;
  // the currently computed s-polynomials corresponds to the first
  // critical pair, it is not deleted yet
  Cpair* temp = (*cp)->cp;
#if F5EDEBUG1
  Print("CRITERION1-BEGINNING\nTested Element: ");
#endif
  i = stratSize;
nextElement:

  while( temp->next )
  {
#if F5EDEBUG2
    Print("F5 Rule: ");
    while( j )
    {
      Print("%d ",f5Rules->label[f5Rules->size-1][(currRing->N)-j]);
      j--;
    }
    j = currRing->N;
    Print("\n %ld\n", f5Rules->slabel[f5Rules->size-1]);
#endif
    if(!((temp->next)->smLabel1 & f5Rules->slabel[f5Rules->size-1]))
    {
      while(j)
      {
        if((temp->next)->mLabel1[j] < f5Rules->label[f5Rules->size-1][j])
        {
          j = currRing->N;
          temp = temp->next;
          goto nextElement;
        }
        j--;
      }
#if F5EDEBUG1
      Print("CRITERION1-END-DETECTED \n");
#endif
      // detected => delete temp->next in list!
      Cpair* tempForDel = temp->next;
      temp->next        = (temp->next)->next;
    }
  }
#if F5EDEBUG1
  Print("CRITERION1-END \n");
#endif
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
    //cp                    = cp->next;
    //omFree( cpDel );
    // save current position of rewrite rules in array to synchronize them at the end of
    // currReduction() with the corresponding labeled polynomial
    rewRulesCurr  = (*rewRules)->size;

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
      if( 
          !criterion2(temp->mLabel1, temp->smLabel1, (*rewRules), temp->rewRule1) &&
          (!temp->mLabel2 || !criterion2(temp->mLabel2, temp->smLabel2, (*rewRules), temp->rewRule2)) 
        )
      {
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
          newRules->label                 = (int**) omAlloc( rewRulesSize*sizeof(int*) );
          newRules->slabel                = (unsigned long*)omAlloc( rewRulesSize*sizeof(unsigned long) );
          newRules->size                  = (*rewRules)->size;
          register unsigned long _length  = currRing->N+1;
          register unsigned long ctr      = 0;
          for( ; ctr<old; ctr++ )
          {
            newRules->label[ctr]      =  (int*) omAlloc( (currRing->N+1)*sizeof(int) );
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
        pWrite( pHead(sp) );
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
          // store the s-polynomial in the linked list for further
          // reductions in currReduction()
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
      cp->cp    = (cp->cp)->next;
      temp     = cp->cp;
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
  //}
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
  // check needed to ensure termination of F5 (see F5+)
  // this will be added to all new labeled polynomials to check
  // when to terminate the algorithm
  BOOLEAN redundant = FALSE;
  int i;
  unsigned long multLabelShortExp;
  static int tempLength           = 0;
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
    bucketExp = ~( pGetShortExpVector(kBucketGetLm(bucket)) );
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
#if F5EDEBUG2
      Print("TO BE REDUCED: ");
      pWrite( kBucketGetLm(bucket) );
      Print("POSSIBLE REDUCER %p ",temp->p);
      pTest( temp->p );
      pWrite(pHead(temp->p));
#endif
      // loop over elements of lower index, i.e. elements in strat
      /*for( int ctr=0; ctr<IDELEMS(redGB); ctr++ )
      {
        if( isDivisibleGetMult( redGB->m[ctr], strat->sevS[ctr], kBucketGetLm( bucket ), 
              bucketExp, &multTemp, &isMult
              ) 
          )
        {
          //multCoeff1          = pGetCoeff( kBucketGetLm(bucket) );
          //multCoeff2          = pGetCoeff( redGB->m[ctr] );
          //multCoeff2          = n_Div( multCoeff1, multCoeff2, currRing );

          static poly multiplier = pOne();
          static poly multReducer;
          getExpFromIntArray( multTemp, multiplier, numVariables, shift, 
              negBitmaskShifted, offsets
              );
          // throw away the leading monomials of reducer and bucket
          //p_SetCoeff( multiplier, multCoeff2, currRing );
          pSetm( multiplier );
          p_SetCoeff( multiplier, pGetCoeff(kBucketGetLm(bucket)), currRing );
          kBucketExtractLm(bucket);
          // build the multiplied reducer (note that we do not need the leading
          // term at all!
#if F5EDEBUG2
          Print("MULT: %p\n", multiplier );
          pWrite( multiplier );
          Print("POLY: \n" );
          pWrite( redGB->m[ctr]->next );
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
          //superTop  = FALSE;
          isMult    = FALSE;
          redundant = FALSE;
          if( kBucketGetLm( bucket ) )
          {
            temp  = gCurrFirst;
          }
          else
          {
            sp  = NULL;
            goto kBucketLmZero;
          }
          bucketExp = ~( pGetShortExpVector(kBucketGetLm(bucket)) );
          goto startagainTop;

        }
      }*/
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
          
          // test the multiplied label by both criteria 
          if( !criterion1( multLabelTemp, multLabelShortExp, f5Rules, strat ) && 
              !criterion2( multLabelTemp, multLabelShortExp, rewRules, temp->rewRule )
            )
          { 
            static unsigned long* multTempExp = (unsigned long*) 
                            omAlloc0( NUMVARS*sizeof(unsigned long) );
            poly multLabelTempExp = pOne(); 
            getExpFromIntArray( multLabelTemp, multLabelTempExp, numVariables,
                                shift, negBitmaskShifted, offsets
                              );   
            // if a higher label reduction takes place we need to create
            // a new Lpoly with the higher label and store it in a different 
            // linked list for later reductions

            if( pLmCmp( multLabelTempExp, spLabelExp ) == 1 )
            {            
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
            // else we can go on and reduce sp
            // The multiplied reducer will be reduced w.r.t. strat before the 
            // bucket reduction starts!
            static poly multiplier = pOne();
            static poly multReducer;
            getExpFromIntArray( multTemp, multiplier, numVariables, shift, 
                                negBitmaskShifted, offsets
                              );
            // throw away the leading monomials of reducer and bucket
            pSetm( multiplier );
            p_SetCoeff( multiplier, pGetCoeff(kBucketGetLm(bucket)), currRing );
            kBucketExtractLm(bucket);
            // build the multiplied reducer (note that we do not need the leading
            // term at all!
#if F5EDEBUG2
            Print("MULT: %p\n", multiplier );
            pWrite( multiplier );
#endif
            multReducer = pp_Mult_mm( temp->p->next, multiplier, currRing );
#if F5EDEBUG2
            Print("MULTRED BEFORE: %p\n", *multReducer );
            pWrite( pHead(multReducer) );
#endif
            multReducer = reduceByRedGBPoly( multReducer, strat );
#if F5EDEBUG2
            Print("MULTRED AFTER: %p\n", *multReducer );
            pWrite( pHead(multReducer) );
#endif
            //  length must be computed after the reduction with 
            //  redGB!
            tempLength = pLength( multReducer );
            
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
            bucketExp = ~( pGetShortExpVector(kBucketGetLm(bucket)) );
            goto startagainTop;
          }
        }
        // isMult = 0 => multTemp = 1 => we do not need to test temp->p by any
        // criterion again => go on with reduction steps
        else
        {
          number coeff  = pGetCoeff(kBucketGetLm(bucket));
          static poly tempNeg  = pInit();
          // throw away the leading monomials of reducer and bucket
          tempNeg       = pCopy( temp->p );
          tempLength    = pLength( tempNeg->next );
          p_Mult_nn( tempNeg, coeff, currRing );
          pSetm( tempNeg );
          kBucketExtractLm(bucket);
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
          redundant = FALSE;
          if( kBucketGetLm( bucket ) )
          {
            temp  = gCurrFirst;
            bucketExp = ~( pGetShortExpVector(kBucketGetLm(bucket)) );
            goto startagainTop;
          }
          else
          {
            break;
          }
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
            if( !criterion1( multLabelTemp, multLabelShortExp, f5Rules, strat ) && 
                !criterion2( multLabelTemp, multLabelShortExp, rewRules, temp->rewRule )
              )
            {  
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
              poly multiplier = pOne();
              getExpFromIntArray( multTemp, multiplier, numVariables, shift, 
                                  negBitmaskShifted, offsets
                                );
              // throw away the leading monomials of reducer and bucket
              p_SetCoeff( multiplier, pGetCoeff(kBucketGetLm(bucket)), currRing );
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
            p_Mult_nn( tempNeg, coeff, currRing );
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
      // we have not reduced the tail w.r.t. redGB as in this case it is not really necessary to have
      // the "right" leading monomial
      //  => now we have to reduce w.r.t. redGB again!
      sp = reduceByRedGBPoly( sp, strat );
      pNorm( sp ); 
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
      Print("ELEMENT ADDED TO GCURR: ");
      pWrite( pHead((*gCurrLast)->p) );
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
        }
        omFreeSize( f5Rules->slabel, old*sizeof(unsigned long) );
        for( ; _ctr<f5RulesSize; _ctr++ )
        {
          newRules->label[_ctr] =  (int*) omAlloc( (currRing->N+1)*sizeof(int) );
        }
        omFreeSize( f5Rules, sizeof(F5Rules) );
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
        f5Rules->size++;
#if F5EDEBUG2
        Print("MEMORY ALLOCATED -- %p\n", f5Rules->label[0]);
#endif

      // now check all already computed critical pairs by this new rule
      // added to the F5Rules
      newCriterion1( cp, f5Rules ); 

      } 
      pDelete( &sp );
    }
    // free memory of bucket
    kBucketDeleteAndDestroy( &bucket );
  // free memory
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
#if F5EDEBUG2
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
  BOOLEAN b         = pLexOrder;
  BOOLEAN toReset   = FALSE;
  BOOLEAN delete_w  = TRUE;
  intvec* hilb      = NULL;
  intvec** w        = NULL;

  if ( rField_has_simple_inverse() )
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
  strat->ak           = idRankFreeModule( F );
  strat->kModW        = kModW = NULL;
  strat->kHomW        = kHomW = NULL;
  // initialising the strategy for redGB-reductions
  tHomog h;
  if ( strat->ak == 0 )
  {
    h = (tHomog)idHomIdeal( F, Q );
    w = NULL;
  }
  else if ( !TEST_OPT_DEGBOUND )
  {
    h = (tHomog)idHomModule( F, Q, w );
  }
  pLexOrder = b;
  if ( h==isHomog )
  {
    pLexOrder = TRUE;
    if ( hilb==NULL ) 
    {
      strat->LazyPass *=  2;
    }
  }
  strat->homog  = h;
#ifdef KDEBUG
  idTest(F);
  idTest(Q);
#endif

  // copied from bba() in kstd2.cc
  om_Opts.MinTrack  = 5;
  int srmax,  lrmax, red_result = 1;
  int olddeg, reduc;
  int hilbeledeg  = 1,  hilbcount = 0,  minimcnt  = 0;
  BOOLEAN withT   = FALSE;

  //initBuchMoraCrit( strat ); /*set Gebauer, honey, sugarCrit*/
  initBuchMoraPos( strat );
  //initHilbCrit( F, Q, &hilb, strat );
  initBba( F, strat );
  initBuchMora( F, Q, strat );
  if ( strat->minim>0 )
  {
    strat->M=idInit( IDELEMS(F), F->rank );
  }
  srmax = strat->sl;
  reduc = olddeg = lrmax = 0;

#ifndef NO_BUCKETS
  if (!TEST_OPT_NOT_BUCKETS)
    strat->use_buckets = 1;
#endif

#ifdef HAVE_TAIL_RING
  if(!idIs0(F) &&(!rField_is_Ring()))  // create strong gcd poly computes with tailring and S[i] ->to be fixed
    kStratInitChangeTailRing(strat);
#endif
  if (BVERBOSE(23))
  {
    if (test_PosInT!=NULL) strat->posInT=test_PosInT;
    if (test_PosInL!=NULL) strat->posInL=test_PosInL;
  }

  /*- test, if a unit is in F -*/
  if ((strat->sl>=0)
#ifdef HAVE_RINGS
       && nIsUnit(pGetCoeff(strat->S[0]))
#endif
       && pIsConstant(strat->S[0]))
  {
    while (strat->sl>0) deleteInS(strat->sl,strat);
  }
  // customized version of initS which also enters elements to T
  initST( F, Q, strat );
}



//---------------------------------------------------------------------------
//-----Customized version of initS which also enters elements to T-----------
//---------------------------------------------------------------------------
void initST( ideal F, ideal Q, kStrategy strat )
{
  int   i,pos;

  if (  Q!=NULL ) 
  {
    i = ((IDELEMS(F)+IDELEMS(Q)+(setmaxTinc-1))/setmaxTinc)*setmaxTinc;
  }
  else
  {
    i = ((IDELEMS(F)+(setmaxTinc-1))/setmaxTinc)*setmaxTinc;
  }
  strat->ecartS = (intset)omAlloc( i*sizeof(int) );
  strat->sevS   = (unsigned long*)omAlloc0( i*sizeof(unsigned long) );
  strat->S_2_R  = (int*)omAlloc0( i*sizeof(int) );
  strat->fromQ  = NULL;
  strat->Shdl   = idInit( i,F->rank );
  strat->S      = strat->Shdl->m;
  /*- put polys into S -*/
  if (Q!=NULL)
  {
    strat->fromQ  = (intset)omAlloc( i*sizeof(int) );
    memset( strat->fromQ, 0, i*sizeof(int) );
    for ( i=0; i<IDELEMS(Q); i++ )
    {
      if ( Q->m[i]!=NULL )
      {
        LObject h;
        h.p = pCopy(Q->m[i]);
        if ( TEST_OPT_INTSTRATEGY )
        {
          //pContent(h.p);
          h.pCleardenom(); // also does a pContent
        }
        else
        {
          h.pNorm();
        }
        if ( pOrdSgn==-1 )
        {
          deleteHC( &h, strat );
        }
        if ( h.p!=NULL )
        {
          strat->initEcart( &h );
          if ( strat->sl==-1 )
          {
            pos =0;
          }
          else
          {
            pos = posInS( strat, strat->sl, h.p, h.ecart );
          }
          h.sev = pGetShortExpVector( h.p );
          strat->enterS( h, pos, strat, -1 );
          strat->fromQ[pos] = 1;
        }
      }
    }
  }
  for ( i=0; i<IDELEMS(F); i++ )
  {
    if ( F->m[i]!=NULL )
    {
      LObject h;
      h.p = pCopy( F->m[i] );
      if (pOrdSgn==-1)
      {
        cancelunit(&h);  /*- tries to cancel a unit -*/
        deleteHC(&h, strat);
      }
      if (h.p!=NULL)
      // do not rely on the input being a SB!
      {
        if (TEST_OPT_INTSTRATEGY)
        {
          //pContent(h.p);
          h.pCleardenom(); // also does a pContent
        }
        else
        {
          h.pNorm();
        }
        strat->initEcart(&h);
        if (strat->sl==-1)
          pos =0;
        else
          pos = posInS(strat,strat->sl,h.p,h.ecart);
        h.sev = pGetShortExpVector(h.p);
        strat->enterS(h,pos,strat,-1);
        enterT( h, strat );
      }
    }
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
  /*- compute------------------------------------------------------- -*/
  //if ((TEST_OPT_INTSTRATEGY)&&(lazyReduce==0))
  //{
  //  for (i=strat->sl;i>=0;i--)
  //    pNorm(strat->S[i]);
  //}
  kTest(strat);
  if (TEST_OPT_PROT) { PrintS("r"); mflush(); }
  int max_ind;
  //----------------------------------------------------------------------
  //------------Possible optimization later on ---------------------------
  //----------------------------------------------------------------------
  LObject h;
  int red_result;
  h.p = q;
  red_result  = strat->red( &h, strat );
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
  return h.p;

  //return q;

  //------------------------------------------------------------------  
  //------------------------------------------------------------------  
  //------------------------------------------------------------------  
  //------------------------------------------------------------------  
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
      //p = redtailBba(p,max_ind,strat,(lazyReduce & KSTD_NF_NONORM)==0);
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
  int red_result;
  h.p = q;
  red_result  = strat->red( &h, strat );
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
  cleanT( strat );
  if ( Q!=NULL ) 
  {
    updateResult( strat->Shdl, Q, strat );
  }
  kModW = NULL;
  pRestoreDegProcs( pFDegOld, pLDegOld );
  HCord=strat->HCord;
  omfree( strat->sevS );
  omfree( strat->ecartS );
  omfree( strat->T );
  omfree( strat->sevT );
  omfree( strat->R );
  omfree( strat->S_2_R );
  omfree( strat->L );
  omfree( strat->B );
  omfree( strat->fromQ );
  idDelete( &strat->Shdl );
  delete( strat );
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
