#include <stdio.h>

#include "cuddInt.h"
#include "cuddObj.hh"

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


Cudd ddManager;
DdManager *manager = ddManager.getManager();

static value * ocaml_minor_gc, *ocaml_major_gc, *ocaml_spaceout_handler, *ocaml_timeout_handler;

static inline DD* dd_ptr(value v)
{
  return (DD*)Data_custom_val(v);
}

static inline DD& dd_val(value v)
{
  return (DD&)*(DD*)Data_custom_val(v);
}

static inline BDD* bdd_ptr(value v)
{
  return (BDD*)Data_custom_val(v);
}

static inline BDD& bdd_val(value v)
{
  return (BDD&)*(BDD*)Data_custom_val(v);
}

static void free_dd(value v)
{
  DdNode *n = bdd_val(v).getNode();
  Cudd_RecursiveDeref(ddManager.getManager(), n);
}

int compare_dd(const value v1, const value v2)
{
  if (bdd_val(v1) == bdd_val(v2))
    return 0;
  else
    return bdd_ptr(v1) - bdd_ptr(v2);
}

struct custom_operations dd_ops = {
  "Cudd/OCaml",
  &free_dd,
  &compare_dd,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default
};

static inline value alloc_res()
{
  value v = alloc_custom(&dd_ops, sizeof(BDD), 0, 1);
  BDD one = ddManager.bddOne();
  Cudd_Ref(one.getNode());
  memcpy(bdd_ptr(v), &one, sizeof(BDD));
  return v;
}

#define CUDD_ML_ONE_OP(name, statement) extern "C" value name(value v) \
{ \
CAMLparam1(v);\
CAMLlocal1(res);\
BDD work = statement;\
res = alloc_res();\
bdd_val(res) = work;\
CAMLreturn(res);\
}

#define CUDD_ML_ONE_INT(name, statement) extern "C" value name(value v) \
{ \
CAMLparam1(v);\
CAMLlocal1(res);\
int i = statement;\
CAMLreturn(Val_int(i));\
}

#define CUDD_ML_ONE_UNIT(name, statement) extern "C" value name(value v) \
{ \
CAMLparam1(v);\
CAMLlocal1(res);\
statement;\
CAMLreturn(Val_unit);\
}

#define CUDD_ML_TWO_OP(name, statement) extern "C" value name(value v1, value v2) \
{ \
CAMLparam2(v1, v2);\
CAMLlocal1(res);\
BDD work = statement;\
res = alloc_res();\
bdd_val(res) = work;\
CAMLreturn(res);\
}

#define CUDD_ML_THREE_OP(name, statement) extern "C" value name(value v1, value v2, value v3) \
{ \
CAMLparam3(v1, v2, v3);\
CAMLlocal1(res);\
BDD work = statement;\
res = alloc_res();\
bdd_val(res) = work;\
CAMLreturn(res);\
}

BDD make_cube_int(value v)
{
  value x = v;
  int count = 0;
  while (Int_val(x) != 0) {
    count++;
    x = Field(x,1);
  }
  BDD *var = new BDD[count];
  int *sign = new int[count];
  x = v;
  count = 0;
  while (Int_val(x) != 0) {
    var[count] = ddManager.bddVar(Int_val(Field(x,0)));
    sign[count++] = 1;
    x = Field(x,1);
  }
  BDD work =  ddManager.bddComputeCube(var, sign, count);
  delete[] var;
  delete[] sign;
  return work;
}

extern "C" int pre_gc_hook(DdManager *dd, char *s, void *p)
{
  callback(*ocaml_minor_gc, Val_unit);
  return 1;
}

extern "C" int pre_reorder_hook(DdManager *dd, char *s, void *p)
{
  callback(*ocaml_major_gc, Val_unit);
  return 1;
}

CUDD_ML_ONE_OP(bdd_one, ddManager.bddOne());
CUDD_ML_ONE_OP(bdd_zero, ddManager.bddZero());
CUDD_ML_ONE_OP(bdd_t, BDD(bdd_val(v).manager(), Cudd_T(Cudd_Regular(bdd_val(v).getNode()))));
CUDD_ML_ONE_OP(bdd_e, BDD(bdd_val(v).manager(), Cudd_E(Cudd_Regular(bdd_val(v).getNode()))));
CUDD_ML_ONE_OP(bdd_var, ddManager.bddVar(Int_val(v)));
CUDD_ML_ONE_OP(bdd_not, ~bdd_val(v));
CUDD_ML_ONE_OP(bdd_makecube, make_cube_int(v));
CUDD_ML_ONE_OP(bdd_support, bdd_val(v).Support());

CUDD_ML_ONE_INT(bdd_size, bdd_val(v).nodeCount());
CUDD_ML_ONE_INT(bdd_top, bdd_val(v).getNode()->index);

CUDD_ML_ONE_INT(bdd_total_vars, ddManager.ReadSize());
CUDD_ML_ONE_UNIT(bdd_enable_reorder, ddManager.AutodynEnable(CUDD_REORDER_SIFT));
CUDD_ML_ONE_UNIT(bdd_disable_reorder, ddManager.AutodynDisable());
CUDD_ML_ONE_UNIT(bdd_enable_reorder_report, ddManager.EnableReorderingReporting());
CUDD_ML_ONE_UNIT(bdd_disable_reorder_report, ddManager.DisableReorderingReporting());


CUDD_ML_TWO_OP(bdd_and, bdd_val(v1) * bdd_val(v2));
CUDD_ML_TWO_OP(bdd_or, bdd_val(v1) + bdd_val(v2));
CUDD_ML_TWO_OP(bdd_diff, bdd_val(v1) - bdd_val(v2));
CUDD_ML_TWO_OP(bdd_constrain, bdd_val(v1).Constrain(bdd_val(v2)));
CUDD_ML_TWO_OP(bdd_exists, bdd_val(v2).ExistAbstract(bdd_val(v1)));
CUDD_ML_TWO_OP(bdd_forall, bdd_val(v2).UnivAbstract(bdd_val(v1)));

CUDD_ML_TWO_OP(bdd_underapprox, bdd_val(v1).UnderApprox(Int_val(v2)));
CUDD_ML_TWO_OP(bdd_overapprox, bdd_val(v1).OverApprox(Int_val(v2)));

CUDD_ML_THREE_OP(bdd_andexist, bdd_val(v2).AndAbstract(bdd_val(v1), bdd_val(v3)));
CUDD_ML_THREE_OP(bdd_make_node, ddManager.bddVar(Int_val(v1))*bdd_val(v2)+(!ddManager.bddVar(Int_val(v1)))*bdd_val(v3));

extern "C" void c_spaceout_handler(char *s)
{
  callback(*ocaml_spaceout_handler, Val_unit);
}

extern "C" void c_timeout_handler(int i)
{
  callback(*ocaml_timeout_handler, Val_unit);
}

extern "C" value bdd_init(value v)
{
  CAMLparam0();
  ocaml_minor_gc = caml_named_value("ocaml_minor_gc");
  ocaml_major_gc = caml_named_value("ocaml_major_gc");
  ocaml_spaceout_handler = caml_named_value("ocaml_spaceout_handler");
  ocaml_timeout_handler = caml_named_value("ocaml_timeout_handler");
  //  ddManager.AddHook(&pre_gc_hook, CUDD_PRE_GC_HOOK);
  //  ddManager.AddHook(&pre_reorder_hook, CUDD_PRE_REORDERING_HOOK);
  ddManager.setHandler(c_spaceout_handler);
#ifndef BENCHMARK
//  if (sizeof(void*)==4)
//    Cudd_SetMaxMemory(ddManager.getManager(), 384*1024*1024);
//  if (sizeof(void*)==8)
    Cudd_SetMaxCacheHard(ddManager.getManager(), 64l*1024l*1024l);
  Cudd_SetMaxMemory(ddManager.getManager(), 1900l*1024*1024);
  struct rlimit rt;
  getrlimit(RLIMIT_CPU, &rt);
  rt.rlim_cur = 1000;   
  setrlimit(RLIMIT_CPU, &rt);
  signal(SIGXCPU, c_timeout_handler);
#else
  Cudd_SetMaxMemory(ddManager.getManager(), 960*1024*1024);
  Cudd_SetMaxCacheHard(ddManager.getManager(), 64l*1024l*1024l);
#endif
  CAMLreturn(Val_unit);
}

extern "C" value set_timeout(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  struct rlimit rt;
  getrlimit(RLIMIT_CPU, &rt);
  rt.rlim_cur = Int_val(v);   
  setrlimit(RLIMIT_CPU, &rt);
  signal(SIGXCPU, c_timeout_handler);
  res = Val_unit;
  CAMLreturn(res);
}

extern "C" value update_time_limit(value v)
{
  CAMLparam1(v);
  struct rlimit rt;
  getrlimit(RLIMIT_CPU, &rt);
  rt.rlim_cur = Int_val(v);
  setrlimit(RLIMIT_CPU, &rt);
  CAMLreturn(Val_unit);
}

extern "C" value bdd_info(value v)
{
  CAMLparam0();
  Cudd_PrintInfo(manager,stdout);
  CAMLreturn(Val_unit);
}
