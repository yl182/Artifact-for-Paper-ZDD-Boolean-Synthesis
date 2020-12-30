#include <stdio.h>

#include "cuddInt.h"
#include "cuddObj.hh"

#include "bed.h"
#include "cudd2bed.h"

#include <sys/time.h>
#include <sys/resource.h>

#ifdef LINUX
#include <bsd/signal.h>
#else // SOLARIS supported
#include <signal.h>
#endif

extern "C" {
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/custom.h>
#include <caml/memory.h>
#include <caml/fail.h>
#include <caml/callback.h>
};

#undef bed_zero
#undef bed_one

extern Cudd ddManager;
extern DdManager *manager;
extern struct custom_operations dd_ops;

static inline BDD* bdd_ptr(value v)
{
  return (BDD*)Data_custom_val(v);
}

static inline BDD& bdd_val(value v)
{
  return (BDD&)*(BDD*)Data_custom_val(v);
}

static inline value alloc_bdd(DdNode *d)
{
  value v = alloc_custom(&dd_ops, sizeof(BDD), 0, 1);
  BDD w = BDD(&ddManager, d);
  Cudd_Ref(d);
  memcpy(bdd_ptr(v), &w, sizeof(BDD));
  return v;
}

extern const bed_node bed_zero, bed_one;

static inline bed_node* bed_ptr(value v)
{
  return (bed_node*)Data_custom_val(v);
}

static inline bed_node& bed_val(value v)
{
  return (bed_node&)*(bed_node*)Data_custom_val(v);
}

static void free_bed(value v)
{
  bed_deref(bed_val(v));
}

int compare_bed(const value v1, const value v2)
{
  return bed_val(v1) - bed_val(v2);
}

struct custom_operations bed_ops = {
  "BED",
  free_bed,
  compare_bed,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default
};

static inline value alloc_res(bed_node d)
{
  value v = alloc_custom(&bed_ops, sizeof(bed_node), 0, 1);
  bed_ref(d);
  bed_val(v)=d;
  return v;
}

extern "C" value ml_bed_init(value v1, value v2)
{
  CAMLparam2(v1, v2);
  CAMLlocal1(res);
  bed_init(Int_val(v1), Int_val(v2));
  res = Val_unit;
  CAMLreturn(res);
}

extern "C" value ml_bed_done(value v)
{
  CAMLparam0();
  CAMLlocal1(res);
  bed_done();
  res = Val_unit;
  CAMLreturn(res);
}

extern "C" value ml_bed_mk(value v, value o, value l, value h)
{
  CAMLparam4(v, o, l, h);
  CAMLlocal1(res);
  bed_node r = bed_mk((bed_var)Int_val(v), (bed_op)Int_val(o), bed_val(l), bed_val(h));
  res = alloc_res(r);
  CAMLreturn(res);
}

extern "C" value ml_bed_upone(value v, value b)
{
  CAMLparam2(v, b);
  CAMLlocal1(res);
  bed_node r = bed_upone(Int_val(v), bed_val(b));
  res = alloc_res(r);
  CAMLreturn(res);
}

extern "C" value ml_bed_upall(value b)
{
  CAMLparam1(b);
  CAMLlocal1(res);
  bed_node r = bed_upall(bed_val(b));
  res = alloc_res(r);
  CAMLreturn(res);
}

extern "C" value ml_bed_apply(value o, value l, value h)
{
  CAMLparam3(o,l,h);
  CAMLlocal1(res);
  bed_node r = bed_apply((bed_op)Int_val(o), bed_val(l), bed_val(h));
  res = alloc_res(r);
  CAMLreturn(res);
}

extern "C" value ml_bed_is_reachable(value s, value d)
{
  CAMLparam2(s,d);
  CAMLlocal1(res);
  if (bed_is_reachable(bed_val(s), bed_val(d)))
    res = Val_true;
  else
    res = Val_false;
  CAMLreturn(res);
}

extern "C" value ml_bed_is_bdd(value b)
{
  CAMLparam1(b);
  CAMLlocal1(res);
  if (bed_is_bdd(bed_val(b)))
    res = Val_true;
  else
    res = Val_false;
  CAMLreturn(res);
}

extern "C" value ml_bed_size(value b)
{
  CAMLparam1(b);
  CAMLlocal1(res);
  int i = bed_node_count(bed_val(b));
  res = Val_int(i);
  CAMLreturn(res);
}

extern "C" value ml_bed_get_one(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  res = alloc_res(bed_one);
  CAMLreturn(res);
}

extern "C" value ml_bed_get_zero(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  res = alloc_res(bed_zero);
  CAMLreturn(res);
}

extern "C" value ml_bed_l(value b)
{
  CAMLparam1(b);
  CAMLlocal1(res);
  bed_node r = bed_get_low(bed_val(b));
  res = alloc_res(r);
  CAMLreturn(res);
}

extern "C" value ml_bed_h(value b)
{
  CAMLparam1(b);
  CAMLlocal1(res);
  bed_node r = bed_get_high(bed_val(b));
  res = alloc_res(r);
  CAMLreturn(res);
}

extern "C" value ml_bed_v(value b)
{
  CAMLparam1(b);
  CAMLlocal1(res);
  bed_var r = bed_get_var(bed_val(b));
  res = Val_int(r);
  CAMLreturn(res);
}

extern "C" value ml_bed_o(value b)
{
  CAMLparam1(b);
  CAMLlocal1(res);
  bed_op r = bed_get_op(bed_val(b));
  res = Val_int(r);
  CAMLreturn(res);
}

extern "C" value ml_bdd_to_bed(value b)
{
  CAMLparam1(b);
  CAMLlocal1(res);
  bed_node r = bdd_to_bed(manager, bdd_val(b).getNode());
  res = alloc_res(r);
  CAMLreturn(res);
}

extern "C" value ml_bed_to_bdd(value b)
{
  CAMLparam1(b);
  CAMLlocal1(res);
  DdNode *r = bed_to_bdd(manager, bed_val(b));
  res = alloc_bdd(r);
  CAMLreturn(res);
}
