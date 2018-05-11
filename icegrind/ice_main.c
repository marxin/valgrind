
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

typedef struct {
  const char *filename;
  OSet *symbols;
  int fd; // descriptor for log output
} symbol_table;

typedef struct {
  Word addr; // mapped address
  Word end; // addr + length
  Word offset; // offset within file
  symbol_table *symbol_table; // symbols mapped in by this library
  OSet *sub_mmaps;
}  mmap_area;

struct Symbol{
  Word offset;
  Word end; // offset + length
  SizeT namelen;
  char *name; // these are actually section names
}  __attribute__((__packed__));

typedef struct Symbol Symbol;

// this works on both mmap_area & Symbol structs
static Word mmap_lookup (const void *a, const void *b) {
  const mmap_area *key = (const mmap_area *) a;
  const mmap_area *elem = (const mmap_area *) b;
  if (key->addr >= elem->addr && key->addr < elem->end)
    return 0;
  return key->addr - elem->addr;
}

static Word symbol_compare (const void *a, const void *b) {
  const symbol_table *key = (const symbol_table *)a;
  const symbol_table *elem = (const symbol_table *)b;
  return VG_(strcmp)(key->filename, elem->filename);
}

static OSet *mmaps = NULL;
static OSet *symbols = NULL;

static void log_new_symbol(symbol_table *table, Symbol *symbol) {
  if (!table->fd) {
    const int len = VG_(strlen)(table->filename)+5;
    char *buf = VG_(malloc)("symbol_table", len);
    VG_(snprintf)(buf, len, "%s.log", table->filename);
    VG_(printf)("outputting to %s\n",buf);
    SysRes r = VG_(open)(buf, VKI_O_WRONLY | VKI_O_CREAT | VKI_O_TRUNC, 0644);
    tl_assert(!sr_isError(r));
    table->fd = sr_Res(r);
  }
  VG_(write)(table->fd, symbol->name, symbol->namelen);
  VG_(write)(table->fd, "\n", 1);
  
  //ExeContext* now = VG_(record_ExeContext)( VG_(get_running_tid)(), 0);
  //VG_(printf)("Faulting in %s\n", symbol->name);
  //VG_(get_and_pp_StackTrace)(VG_(get_running_tid)(), 10);
  //VG_(pp_ExeContext)(now);
  //VG_(exit)(127); 
}


/* addr: address to look up
   target_mmaps: set of mmaps to look in
   failret: return value to return if the address is not found
*/
static mmap_area* find_mmap(Addr addr, OSet *target_mmaps, mmap_area *failret) {
  mmap_area key;
  key.addr = addr;
  mmap_area *ret = VG_(OSetGen_LookupWithCmp)(target_mmaps, &key, mmap_lookup);
  if (!ret)
    return failret;

  OSet *sub_mmaps = ret->sub_mmaps;
  if (!sub_mmaps)
    return ret;
  
  return find_mmap(addr, sub_mmaps, ret);
}

// not sure if I should make use of size
static VG_REGPARM(2) void inspect_addr(Addr addr, SizeT size)
{
  Symbol skey;

//  VG_(printf)("access: %p: %ld\n", addr, size);

  // this doesn't work for nested mmaps yet
  mmap_area *match = find_mmap(addr, mmaps, NULL);
  if (!match || !match->symbol_table) return;
  OSet *mysymbols = match->symbol_table->symbols;

  skey.offset = addr - match->addr + match->offset; 
  Symbol *smatch = VG_(OSetGen_LookupWithCmp)(mysymbols, &skey, mmap_lookup);
  if (!smatch) {
    //  VG_(printf)("???@%p\n", skey.offset);
    return;
  }
  log_new_symbol(match->symbol_table, smatch);
  VG_(OSetGen_Remove)(mysymbols, smatch);
  VG_(OSetGen_FreeNode)(symbols, smatch);
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

    case Ist_LoadG:
      // TODO
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

static OSet* parse_symbols(char *buf, char *endbuf) {
  OSet *mysymbols = VG_(OSetGen_Create)(0, NULL, VG_(malloc), "symbols",
                                        VG_(free) );
  char *p = buf;
  int i = 0;
  long total = (long)endbuf - (long)buf;
  while(p && p < endbuf) {
    Word offset = VG_(strtoll16)(p, &p);
    tl_assert(offset && p && *p == '\t');
    //skip \t
    p++;
    Word length = VG_(strtoll16)(p, &p);
    tl_assert(length && p && *p == '\t');
    char *name = ++p;
    p = VG_(strchr)(name, ' ');
    if (!p)
      p = VG_(strchr)(name, '\n');
    tl_assert(p);
    int len = p - name;
    Symbol *s = VG_(OSetGen_AllocNode)(mysymbols, sizeof(Symbol));
    s->offset = offset;
    s->end = offset + length;
    s->namelen = len;
    s->name = name;
    if ((i++ & 0xFFF)==0xFFF) {
      long pos = (long)p - (long)buf;
      VG_(printf)("%ld%%\n", pos*100/total);
    }
    VG_(OSetGen_Insert)(mysymbols, s);
    // move to next line
    p = VG_(strchr)(p, '\n');
    tl_assert(p);
    p++;
  }
  return mysymbols;
}

// borrowed from pub_core_aspacemgr.h
extern SysRes VG_(am_mmap_file_float_valgrind)
   ( SizeT length, UInt prot, Int fd, Off64T offset );

static symbol_table* find_symbol_table(const char *symbol_file) {
  symbol_table t;
  t.filename = symbol_file;
  symbol_table *table = VG_(OSetGen_Lookup)(symbols, &t);
  
  if (table) {
    if (table->symbols)
      return table;
    else 
      return NULL;
  }

  table = VG_(OSetGen_AllocNode)(symbols, sizeof(symbol_table));
  table->filename = VG_(strdup)("symbol_table", symbol_file);
  table->symbols = NULL;
  table->fd = 0;
  VG_(OSetGen_Insert)(symbols, table);

  static const char suffix[] = "%s.sections";
  char *filename= VG_(malloc)("symbolname", VG_(strlen)(symbol_file) + sizeof(suffix));
  VG_(sprintf)(filename, suffix, symbol_file);
  SysRes r = VG_(open)(filename, VKI_O_RDONLY, 0);
  VG_(free)(filename);
  if (sr_isError(r)) {
    return NULL;
  }
  int fd = sr_Res(r);
  int length = VG_(lseek) (fd, 0, VKI_SEEK_END);
  VG_(lseek) (fd, 0, VKI_SEEK_SET);
  char *buf;
  // leave the mmap hanging around as we will be referencing it
  r = VG_(am_mmap_file_float_valgrind) ( length, VKI_PROT_READ, fd, 0 );
  VG_(close)(fd);
  if (!sr_isError(r)) {
    buf = sr_Res(r);
    VG_(printf)("parsing symbols for %s\n", symbol_file);
    table->symbols = parse_symbols(buf, buf + length);
    VG_(printf)("Parsed %s\n", symbol_file);
  } else {
    VG_(printf)("Failed to mmap %s\n", symbol_file);
  }
  return table;
}

static void track_mmap(NSegment const * seg) {
  /* Ignore non-file mappings */
  if (  (seg->kind != SkFileC))
    return;

  char *filename = VG_(am_get_filename)(seg);

  symbol_table *table = find_symbol_table(filename);
  if (!table)
    return;

  mmap_area *a = VG_(OSetGen_AllocNode)(mmaps, sizeof(mmap_area));
  a->addr = seg->start;
  a->offset = seg->offset;
  a->end = seg->end;
  a->symbol_table = table;
  a->sub_mmaps = NULL;

  VG_(OSetGen_ResetIter)(mmaps);
  mmap_area *iterator_mmap = NULL;
  while((iterator_mmap = VG_(OSetGen_Next)(mmaps)) != NULL) {
    if (iterator_mmap->addr < a->addr && iterator_mmap->end > a->end) {
      if (0)
        VG_(printf)("nested ");
      if (!iterator_mmap->sub_mmaps) {
        iterator_mmap->sub_mmaps = VG_(OSetGen_Create)(0, NULL, VG_(malloc), "sub_mmaps", VG_(free));
      }
      break;
    }
  }

  // hack, sometimes we see 2 things mapped in same address, which is should be impossible
  /* mmap_area *match = VG_(OSetGen_Remove)(mmaps, a);
     if (match) {
     VG_(printf)("mmap: Skipping error: %s and %s(discarding) both claim to be mapped at %p!\n",
     myfile->file, match->symbol_table ? match->symbol_table->filename : "(unknown)", a->addr);
     VG_(OSetGen_FreeNode)(mmaps, match);
     }*/
  if (0)
    VG_(printf)("mmap %s addr:%p len:%p  offset:%p \n", 
                filename,(void *)a->addr, (void *)(a->end - a->addr), (void *)a->offset);

  VG_(OSetGen_Insert)(mmaps, a);

}

static void track_munmap(Addr addr, SizeT length) {
  mmap_area fake;
  fake.addr = addr;
  mmap_area *match = VG_(OSetGen_Remove)(mmaps, &fake);
  if (!match) {
    //      VG_(printf)("munmap: Failed to find a mmmap()==%p\n", fake.addr);
    return;
  } else if (match->end - match->addr != length) {
    VG_(printf)("munmap: Unhandled %p is unmapped with %p, but mapped with %p\n", 
                (void *)fake.addr, (void *)length, (void *)(match->end - match->addr));
  }
  if (0)
    VG_(printf)("munmap %s addr:%p length:%p\n", match->symbol_table->filename,
                (void *)match->addr, (void *)(match->end - match->addr));
  VG_(get_and_pp_StackTrace)(VG_(get_running_tid)(), 10);
  VG_(OSetGen_FreeNode)(mmaps, match);
}

static void lk_pre_clo_init(void)
{
  mmaps = VG_(OSetGen_Create)(0, NULL, VG_(malloc), "mmaps",
                              VG_(free) );
  symbols = VG_(OSetGen_Create)(0, symbol_compare, VG_(malloc), "symbols",
                                VG_(free) );
  
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
  VG_(needs_mmap_notify)(track_mmap, track_munmap);
}

VG_DETERMINE_INTERFACE_VERSION(lk_pre_clo_init)

/*--------------------------------------------------------------------*/
/*--- end                                                ice_main.c ---*/
/*--------------------------------------------------------------------*/

