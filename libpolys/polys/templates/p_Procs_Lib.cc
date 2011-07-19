/****************************************
*  Computer Algebra System SINGULAR     *
****************************************/
/***************************************************************
 *  File:    p_Procs_Lib.cc
 *  Purpose: source for shared library of p_Procs
 *  Author:  obachman (Olaf Bachmann)
 *  Created: 12/00
 *  Version: $Id$
 *******************************************************************/

#ifdef DYNAMIC_VERSION
#define LINKAGE extern "C"
#else
#define LINKAGE
#endif

#include "config.h"
#include <misc/auxiliary.h>

#ifdef HAVE_FACTORY
#include <factory/factory.h>
#endif

#include <polys/monomials/p_polys.h>
#include <polys/monomials/ring.h>
#include <polys/templates/p_Procs.h>
#include <polys/templates/p_Numbers.h>
#include <polys/templates/p_MemCmp.h>
#include <polys/templates/p_MemAdd.h>
#include <polys/templates/p_MemCopy.h>
#include <polys/kbuckets.h>

#include "templates/p_Procs.inc"

