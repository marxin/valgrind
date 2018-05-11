
/*--------------------------------------------------------------------*/
/*--- A tool to produce a chronological log of functions/data access  */
/*--------------------------------------------------------------------*/

/*
  This file is part of Icegrind, an example Valgrind tool that produces
  a log of mmap()ed area accesses.

  Copyright (C) 2010 Mozilla Foundation
     
  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License as
  published by the Free Software Foundation; either version 2 of the
  License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful, but
  WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA
  02111-1307, USA.

  The GNU General Public License is contained in the file COPYING.
*/

#include "pub_tool_basics.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_oset.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_vki.h"
#include "pub_tool_libcfile.h"
#include "pub_tool_vkiscnums.h"
#include "pub_tool_xarray.h"
#include "pub_tool_clientstate.h"
#include "pub_tool_stacktrace.h"
#include "pub_tool_threadstate.h"
#include "pub_tool_aspacemgr.h"
#include "pub_tool_machine.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_aspacemgr.h"

/*------------------------------------------------------------*/
/*--- Stuff for --trace-mem                                ---*/
/*------------------------------------------------------------*/

#define MAX_DSIZE    512

typedef
IRExpr 
IRAtom;


typedef
struct {
  IRAtom*    addr;
  Int        size;
}
  Event;

/* Up to this many unnotified events are allowed.  Must be at least two,
   so that reads and writes to the same address can be merged into a modify.
   Beyond that, larger numbers just potentially induce more spilling due to
   extending live ranges of address temporaries. */
#define N_EVENTS 4

/* Maintain an ordered list of memory events which are outstanding, in
   the sense that no IR has yet been generated to do the relevant
   helper calls.  The SB is scanned top to bottom and memory events
   are added to the end of the list, merging with the most recent
   notified event where possible (Dw immediately following Dr and
   having the same size and EA can be merged).

   This merging is done so that for architectures which have
   load-op-store instructions (x86, amd64), the instr is treated as if
   it makes just one memory reference (a modify), rather than two (a
   read followed by a write at the same address).

   At various points the list will need to be flushed, that is, IR
   generated from it.  That must happen before any possible exit from
   the block (the end, or an IRStmt_Exit).  Flushing also takes place
   when there is no space to add a new event.

   If we require the simulation statistics to be up to date with
   respect to possible memory exceptions, then the list would have to
   be flushed before each memory reference.  That's a pain so we don't
   bother.

   Flushing the list consists of walking it start to end and emitting
   instrumentation IR for each event, in the order in which they
   appear. */

static Event events[N_EVENTS];
static Int   events_used = 0;

typedef struct
{
  Addr addr;
  SizeT size;
} addr_tuple;

static Word addr_compare (const void *a, const void *b) {
  const addr_tuple *a1 = (const addr_tuple *)a;
  const addr_tuple *b1 = (const addr_tuple *)b;
  return a1->addr - b1->addr;
}

static OSet *seen_addresses = NULL;

static void
report (addr_tuple *t)
{
  VG_(printf)("ma:%p:%ld\n", t->addr, t->size);
}

// not sure if I should make use of size
static VG_REGPARM(2) void inspect_addr(Addr addr, SizeT size)
{
  addr_tuple key;
  key.addr = addr;

  addr_tuple *r = VG_(OSetGen_LookupWithCmp)(seen_addresses, &key, addr_compare);
  if (r)
  {
    if (r->size < size)
    {
      r->size = size;
      report (r);
    }
    return;
  }

  r = VG_(OSetGen_AllocNode)(seen_addresses, sizeof(addr_tuple));
  r->addr = addr;
  r->size = size;
  VG_(OSetGen_Insert)(seen_addresses, r);

  report (r);
}

static void flushEvents(IRSB* sb)
{
  Int        i;
  void*      helperAddr;
  IRExpr**   argv;
  IRDirty*   di;
  Event*     ev;

  for (i = 0; i < events_used; i++) {

    ev = &events[i];
    helperAddr =  inspect_addr;

    // Add the helper.
    argv = mkIRExprVec_2( ev->addr, mkIRExpr_HWord( ev->size ) );
    di   = unsafeIRDirty_0_N( /*regparms*/2, 
                              "inspect_addr", VG_(fnptr_to_fnentry)( helperAddr ),
                              argv );
    addStmtToIRSB( sb, IRStmt_Dirty(di) );
  }

  events_used = 0;
}

static
void addEvent ( IRSB* sb, IRAtom* daddr, Int dsize )
{
  Event* evt;
  tl_assert(isIRAtom(daddr));
  tl_assert(dsize >= 1 && dsize <= MAX_DSIZE);
  if (events_used == N_EVENTS)
    flushEvents(sb);
  tl_assert(events_used >= 0 && events_used < N_EVENTS);
  evt = &events[events_used];
  evt->addr  = daddr;
  evt->size  = dsize;
  events_used++;
}

/*------------------------------------------------------------*/
/*--- Basic tool functions                                 ---*/
/*------------------------------------------------------------*/

static void lk_post_clo_init(void)
{
  seen_addresses = VG_(OSetGen_Create)(0, addr_compare, VG_(malloc), "seen addresses",
                                VG_(free) );
}

static
IRSB* lk_instrument ( VgCallbackClosure* closure,
                      IRSB* sbIn,
                      const VexGuestLayout* layout,
                      const VexGuestExtents* vge,
                      const VexArchInfo* archinfo_host,
                      IRType gWordTy, IRType hWordTy )
{
  Int        i;
  IRSB*      sbOut;
  IRTypeEnv* tyenv = sbIn->tyenv;

  if (gWordTy != hWordTy) {
    /* We don't currently support this case. */
    VG_(tool_panic)("host/guest word size mismatch");
  }

  /* Set up SB */
  sbOut = deepCopyIRSBExceptStmts(sbIn);

  // Copy verbatim any IR preamble preceding the first IMark
  i = 0;
  while (i < sbIn->stmts_used && sbIn->stmts[i]->tag != Ist_IMark) {
    addStmtToIRSB( sbOut, sbIn->stmts[i] );
    i++;
  }

 
 
  for (/*use current i*/; i < sbIn->stmts_used; i++) {
    IRStmt* st = sbIn->stmts[i];
    if (!st || st->tag == Ist_NoOp) continue;
       
    switch (st->tag) {
    case Ist_NoOp:
    case Ist_AbiHint:
    case Ist_Put:
    case Ist_PutI:
    case Ist_MBE:
      addStmtToIRSB( sbOut, st );
      break;

    case Ist_IMark:
           
      //      inspect_addr( st->Ist.IMark.addr, st->Ist.IMark.len);

      addEvent( sbOut, mkIRExpr_HWord( (HWord)st->Ist.IMark.addr ),
                            st->Ist.IMark.len );

      addStmtToIRSB( sbOut, st );
      break;

    case Ist_LoadG:
      {
	IRLoadG* lg       = st->Ist.LoadG.details;
	IRType   type     = Ity_INVALID; /* loaded type */
	IRType   typeWide = Ity_INVALID; /* after implicit widening */
	typeOfIRLoadGOp(lg->cvt, &typeWide, &type);
	tl_assert(type != Ity_INVALID);
	addEvent( sbOut, lg->addr, sizeofIRType(type));
	addStmtToIRSB( sbOut, st );
	break;
      }

    case Ist_WrTmp: 
      {
        IRExpr* data = st->Ist.WrTmp.data;
        if (data->tag == Iex_Load) {
          addEvent( sbOut, data->Iex.Load.addr,
                    sizeofIRType(data->Iex.Load.ty) );
        }
      }
           
      addStmtToIRSB( sbOut, st );
      break;

    case Ist_Store:
      {
        IRExpr* data  = st->Ist.Store.data;
        addEvent( sbOut, st->Ist.Store.addr,
                  sizeofIRType(typeOfIRExpr(tyenv, data)) );
        addStmtToIRSB( sbOut, st );
        break;
      }
    case Ist_Dirty: {
      {
        Int      dsize;
        IRDirty* d = st->Ist.Dirty.details;
        if (d->mFx != Ifx_None) {
          // This dirty helper accesses memory.  Collect the details.
          tl_assert(d->mAddr != NULL);
          tl_assert(d->mSize != 0);
          dsize = d->mSize;
          if (d->mFx == Ifx_Read || d->mFx == Ifx_Modify)
            addEvent( sbOut, d->mAddr, dsize );
          if (d->mFx == Ifx_Write || d->mFx == Ifx_Modify)
            addEvent( sbOut, d->mAddr, dsize );
        } else {
          tl_assert(d->mAddr == NULL);
          tl_assert(d->mSize == 0);
        }
      }
      addStmtToIRSB( sbOut, st );
      break;
    }

    case Ist_CAS: {
      /* We treat it as a read and a write of the location.  I
         think that is the same behaviour as it was before IRCAS
         was introduced, since prior to that point, the Vex
         front ends would translate a lock-prefixed instruction
         into a (normal) read followed by a (normal) write. */
      Int    dataSize;
      IRType dataTy;
      IRCAS* cas = st->Ist.CAS.details;
      tl_assert(cas->addr != NULL);
      tl_assert(cas->dataLo != NULL);
      dataTy   = typeOfIRExpr(tyenv, cas->dataLo);
      dataSize = sizeofIRType(dataTy);
      if (cas->dataHi != NULL)
        dataSize *= 2; /* since it's a doubleword-CAS */
           
      addEvent( sbOut, cas->addr, dataSize );
      addEvent( sbOut, cas->addr, dataSize );
            
      addStmtToIRSB( sbOut, st );
      break;
    }

    case Ist_LLSC: {
      IRType dataTy;
      if (st->Ist.LLSC.storedata == NULL) {
        /* LL */
        dataTy = typeOfIRTemp(tyenv, st->Ist.LLSC.result);
        addEvent( sbOut, st->Ist.LLSC.addr,
                  sizeofIRType(dataTy) );
      } else {
        /* SC */
        dataTy = typeOfIRExpr(tyenv, st->Ist.LLSC.storedata);
        addEvent( sbOut, st->Ist.LLSC.addr,
                  sizeofIRType(dataTy) );
      }
      addStmtToIRSB( sbOut, st );
      break;
    }

    case Ist_Exit:
      flushEvents(sbOut);
           
      addStmtToIRSB( sbOut, st );      // Original statement

      break;

    default:
      tl_assert(0);
    }
  }

  /* At the end of the sbIn.  Flush outstandings. */
  flushEvents(sbOut);
   
  return sbOut;
}

static void lk_fini(Int exitcode)
{
  VG_(umsg)("I am done.\n");
}

// borrowed from pub_core_aspacemgr.h
extern SysRes VG_(am_mmap_file_float_valgrind)
   ( SizeT length, UInt prot, Int fd, Off64T offset );

static void lk_pre_clo_init(void)
{
  VG_(details_name)            ("Icegrind");
  VG_(details_version)         (NULL);
  VG_(details_description)     ("A tool to produce a chronological log of function/data access to aid with optimizing cold startup and memory usage");
    VG_(details_copyright_author)(
                                  "Copyright (C) 2010, and GNU GPL'd, by Mozilla Corporation.");
  VG_(details_bug_reports_to)  (VG_BUGS_TO);
  VG_(details_avg_translation_sizeB) ( 200 );

  VG_(basic_tool_funcs)          (lk_post_clo_init,
                                  lk_instrument,
                                  lk_fini);
}

VG_DETERMINE_INTERFACE_VERSION(lk_pre_clo_init)

/*--------------------------------------------------------------------*/
/*--- end                                                ice_main.c ---*/
/*--------------------------------------------------------------------*/

