// -*-Mode: C++;-*- // technically C99
// $Id$

//************************* System Include Files ****************************

#include <string.h>
#include <stdio.h>
#include <assert.h>

//*************************** User Include Files ****************************

#include "mips-unwind-interval.h"

#include "csprof-malloc.h"
#include "pmsg.h"
#include "atomic-ops.h"

//*************************** Forward Declarations **************************

static const char* frame_ty_string(framety_t ty); 


//***************************************************************************
// global variables
//***************************************************************************

long ui_cnt = 0;
long suspicious_cnt = 0;


//***************************************************************************
// interface operations 
//***************************************************************************

unw_interval_t* new_ui(char* start_addr, framety_t ty, frameflg_t flgs,
		       int sp_pos, int bp_pos, int ra_arg,
		       unw_interval_t* prev)
{
  unw_interval_t* u = (unw_interval_t*)csprof_malloc(sizeof(unw_interval_t));

  u->common.start = start_addr;
  u->common.end = 0;
  u->common.prev = (splay_interval_t*)prev;
  u->common.next = NULL;

  u->ty   = ty;
  u->flgs = flgs;

  u->sp_pos  = sp_pos;
  u->bp_pos  = bp_pos;
  u->ra_arg  = ra_arg;

  fetch_and_add(&ui_cnt, 1);

  return u;
}


void 
dump_ui(unw_interval_t* u, int dump_to_stdout)
{
  char buf[256];
  
  sprintf(buf, "start=%p end=%p ty=%s flgs=%d sp_pos=%d bp_pos=%d ra_arg=%d next=%p prev=%p\n",
	  (void*)u->common.start, (void*)u->common.end,
	  frame_ty_string(u->ty), u->flgs, u->sp_pos, u->bp_pos, u->ra_arg,
	  u->common.next, u->common.prev);

  EMSG(buf);
  if (dump_to_stdout) { 
    fprintf(stderr, "%s", buf);
    fflush(stderr);
  }
}


//***************************************************************************

long 
ui_count(void)
{
  return ui_cnt;
}


long 
suspicious_count(void)
{
  return suspicious_cnt;
}


void
suspicious_interval(void *pc) 
{
  EMSG("suspicous interval for pc = %p", pc);
  fetch_and_add(&suspicious_cnt,1);
}


void 
link_ui(unw_interval_t* current, unw_interval_t* next)
{
  current->common.end = next->common.start;
  current->common.next= (splay_interval_t *)next;
}


//***************************************************************************
// private operations 
//***************************************************************************

static const char*
frame_ty_string(framety_t ty)
{
#define frame_ty_string_STR(s) case s: return #s

  switch (ty) {
    frame_ty_string_STR(FrmTy_NULL);
    frame_ty_string_STR(FrmTy_SP);
    frame_ty_string_STR(FrmTy_BP);
    default:
      assert(0);
  }
  return NULL;
}