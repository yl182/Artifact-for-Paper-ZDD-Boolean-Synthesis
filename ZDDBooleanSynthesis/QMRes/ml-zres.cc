#include <stdio.h>

#include "cuddInt.h"
#include "cuddObj.hh"
extern "C" {
#include "manip.h"
  namespace RGL {
#include "set.h"
  };
};

extern "C" {
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/custom.h>
#include <caml/memory.h>
#include <caml/fail.h>
#include <caml/callback.h>
};

extern Cudd ddManager;
extern DdManager *manager;
extern struct custom_operations dd_ops;

extern int invertVars;
extern int totalVars;
extern int print_active;

static inline DdNode** zdd_ptr(value v)
{
  return (DdNode**)Data_custom_val(v);
}

static inline DdNode*& zdd_val(value v)
{
  return (DdNode*&)(*((DdNode**)Data_custom_val(v)));
}

static void free_zdd(value v)
{
  DdNode *n = zdd_val(v);
  Cudd_RecursiveDerefZdd(manager, n);
}

int compare_zdd(const value v1, const value v2)
{
  if (zdd_val(v1) == zdd_val(v2))
    return 0;
  else
    return zdd_val(v1) - zdd_val(v2);
}

struct custom_operations zres_ops = {
  "Zres/OCaml",
  &free_zdd,
  &compare_zdd,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default
};

static inline value alloc_res(DdNode *d)
{
  value v = alloc_custom(&zres_ops, sizeof(DdNode*), 0, 1);
  Cudd_Ref(d);
  *(zdd_ptr(v))=d;
  return v;
}

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

extern "C" value print_active_vars(value v)
{
  CAMLparam0();
  CAMLlocal1(res);
  print_active = 1;
  res = Val_unit;
  CAMLreturn(res);
}

extern "C" value zdd_var(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  res = Val_int(zdd_val(v)->index);
  CAMLreturn(res);
}

extern "C" value zdd_t(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  DdNode* work = cuddT(zdd_val(v));
  res = alloc_res(work);
  Cudd_RecursiveDerefZdd(manager, work);
  CAMLreturn(res);
}

extern "C" value zdd_e(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  DdNode* work = cuddE(zdd_val(v));
  res = alloc_res(work);
  Cudd_RecursiveDerefZdd(manager, work);
  CAMLreturn(res);
}

DdNode *make_clause_int(value v)
{
  CAMLparam1(v);
  CAMLlocal1(x);
  x = v;
  int count = 0;
  while (Int_val(x) != 0) {
    count++;
    x = Field(x,1);
  }
  int *var = new int[count];
  x = v;
  count = 0;
  while (Int_val(x) != 0) {
    int index = Int_val(Field(x,0));
    if (index < 0)
      var[count++] = (-index)*2+1;
    else
      var[count++] = index*2;
    x = Field(x,1);
  }
  DdNode *work = DD_ONE(manager);
  cuddRef(work);
  for (int i=count-1;i>=0;i--) {
    //    printf("%d ",var[i]);
    DdNode *w2 = Cudd_zddChange(manager, work, var[i]);
    cuddRef(w2);
    Cudd_RecursiveDerefZdd(manager, work);
    work = w2;
  }
  //  printf("\n");
  //  fflush(stdout);
  delete[] var;
  return work;
}

extern "C" value build_clause(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  DdNode* work = make_clause_int(v);
  res = alloc_res(work);
  Cudd_RecursiveDerefZdd(manager, work);
  CAMLreturn(res);
}

extern "C" value clause_set_change(value v1, value v2)
{
  CAMLparam2(v1, v2);
  CAMLlocal1(res);
  DdNode *w = Cudd_zddChange(manager, zdd_val(v1), Int_val(v2));
  cuddRef(w);
  res = alloc_res(w);
  Cudd_RecursiveDerefZdd(manager, w);
  CAMLreturn(res);
}

extern "C" value clause_set_getzdd(value v1, value v2, value v3)
{
  CAMLparam3(v1, v2, v3);
  CAMLlocal1(res);
  DdNode *w = cuddZddGetNode(manager, Int_val(v1), zdd_val(v2), zdd_val(v3));
  cuddRef(w);
  res = alloc_res(w);
  Cudd_RecursiveDerefZdd(manager, w);
  CAMLreturn(res);
}

extern "C" value add_lit(value v1, value v2)
{
  CAMLparam2(v1, v2);
  CAMLlocal1(res);
  DdNode *w = Cudd_zddChange(manager, zdd_val(v2), Int_val(v1));
  cuddRef(w);
  res = alloc_res(w);
  Cudd_RecursiveDerefZdd(manager, w);
  CAMLreturn(res);
}

extern "C" value split_subset(value v1, value v2)
{
  CAMLparam2(v1, v2);
  CAMLlocal4(res,work1, work2, work3);
  DdNode *z = zdd_val(v2);
  DdNode *t = Cudd_zddSubset1(manager, z, Int_val(v1)*2);
  cuddRef(t);
  DdNode *temp = Cudd_zddSubset0(manager, z, Int_val(v1)*2);
  cuddRef(temp);
  DdNode *f = Cudd_zddSubset1(manager, temp, Int_val(v1)*2+1);
  cuddRef(f);
  DdNode *n = Cudd_zddSubset0(manager, temp, Int_val(v1)*2+1);
  cuddRef(n);
  Cudd_RecursiveDerefZdd(manager, temp);
  res = alloc_tuple(3);
  work1 = alloc_res(t);
  Store_field(res, 0, work1);
  Cudd_RecursiveDerefZdd(manager, t);
  work2 = alloc_res(f);
  Store_field(res, 1, work2);
  Cudd_RecursiveDerefZdd(manager, f);
  work3 = alloc_res(n);
  Store_field(res, 2, work3);
  Cudd_RecursiveDerefZdd(manager, n);
  CAMLreturn(res);
}

extern "C" value get_empty_set(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  DdNode* work = DD_ZERO(manager);
  cuddRef(work);
  res = alloc_res(work);
  Cudd_RecursiveDerefZdd(manager, work);
  CAMLreturn(res);
}

extern "C" value sub_free_union(value v1, value v2)
{
  CAMLparam2(v1, v2);
  CAMLlocal1(res);
  //  printf("starting union\n");
  //  fflush(stdout);
  DdNode* work = zdd_myunion(manager, zdd_val(v1), zdd_val(v2));
  cuddRef(work);
  //  printf("union done\n");
  //  fflush(stdout);
  res = alloc_res(work);
  Cudd_RecursiveDerefZdd(manager, work);
  CAMLreturn(res);
}

extern "C" value unit_prop(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  DdNode *w, *w2, *w3;
  w = zdd_val(v);
  cuddRef(w);
  do {
    w2 = find_unit_literals(manager, w);
    cuddRef(w2);
    if (w2 != DD_ONE(manager)) {
      w3 = apply_literals(manager, w, w2);
      //      break;
    } else {
      w3 = w;
      break;
    }
    cuddRef(w3);
    Cudd_RecursiveDerefZdd(manager, w);
    Cudd_RecursiveDerefZdd(manager, w2);
    w = w3;
  } while (1);
  res = alloc_res(w3);
  cuddDeref(w3);
  CAMLreturn(res);
}

extern "C" value find_unit_lits(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  DdNode* work = find_unit_literals(manager, zdd_val(v));
  cuddRef(work);
  res = alloc_res(work);
  Cudd_RecursiveDerefZdd(manager, work);
  CAMLreturn(res);
}

extern "C" value find_existential_unit_lits(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  DdNode* work = find_existential_unit_literals(manager, zdd_val(v));
  cuddRef(work);
  res = alloc_res(work);
  Cudd_RecursiveDerefZdd(manager, work);
  CAMLreturn(res);
}

extern "C" value get_support(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  DdNode* work = get_zdd_support(manager, zdd_val(v));
  cuddRef(work);
  res = alloc_bdd(work);
  Cudd_RecursiveDeref(manager, work);
  CAMLreturn(res);
}

extern "C" value get_support_z(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  DdNode* work = get_zdd_support_2(manager, zdd_val(v));
  cuddRef(work);
  res = alloc_res(work);
  Cudd_RecursiveDerefZdd(manager, work);
  CAMLreturn(res);
}

extern "C" value filter_taut(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  DdNode* work = filtre_tautologie(manager, zdd_val(v));
  cuddRef(work);
  res = alloc_res(work);
  Cudd_RecursiveDerefZdd(manager, work);
  CAMLreturn(res);
}

extern "C" value remove_univ_arb(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  DdNode* work = remove_universal_literals(manager, zdd_val(v),1);
  cuddRef(work);
  res = alloc_res(work);
  Cudd_RecursiveDerefZdd(manager, work);
  CAMLreturn(res);
}

extern "C" value remove_univ_exist_before_univ(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  DdNode* work = remove_universal_literals(manager, zdd_val(v),0);
  cuddRef(work);
  res = alloc_res(work);
  Cudd_RecursiveDerefZdd(manager, work);
  CAMLreturn(res);
}

extern "C" value apply_lits(value v1, value v2)
{
  CAMLparam2(v1, v2);
  CAMLlocal1(res);
  DdNode* work = apply_literals(manager, zdd_val(v1), zdd_val(v2));
  cuddRef(work);
  res = alloc_res(work);
  Cudd_RecursiveDerefZdd(manager, work);
  CAMLreturn(res);
}

extern "C" value bound_cube(value v1, value v2)
{
  CAMLparam2(v1, v2);
  CAMLlocal1(res);
  int b = Int_val(v2);
  DdNode *c = zdd_val(v1);
  while (!Cudd_IsConstant(c)) {
    fflush(stdout);
    if (c->index <= b) {
      c = cuddT(c);
    } else
      break;
  }
  res = alloc_res(c);
  CAMLreturn(res);
}

extern "C" value apply_lits_bounded(value v1, value v2, value v3)
{
  CAMLparam3(v1, v2, v3);
  CAMLlocal1(res);
  int b = Int_val(v3);
  DdNode *c = zdd_val(v2);
  while (!Cudd_IsConstant(c)) {
    if (c->index < b)
      c = cuddT(c);
    else
      break;
  }
  DdNode* work = apply_literals(manager, zdd_val(v1), c);
  cuddRef(work);
  res = alloc_res(work);
  Cudd_RecursiveDerefZdd(manager, work);
  CAMLreturn(res);
}

extern "C" value clause_distribution(value v1, value v2)
{
  CAMLparam2(v1, v2);
  CAMLlocal1(res);
  DdNode* work;
  work = zdd_myproduct(manager, zdd_val(v1), zdd_val(v2));
  cuddRef(work);
  res = alloc_res(work);
  Cudd_RecursiveDerefZdd(manager, work);
  CAMLreturn(res);
}

extern "C" value clause_distribution_bdd(value v1, value v2)
{
  CAMLparam2(v1, v2);
  CAMLlocal1(res);
  DdNode *work, *work2, *work3, *work4;
  work = build_bdd_noquant(manager, zdd_val(v1));
  cuddRef(work);
  work2 = build_bdd_noquant(manager, zdd_val(v2));
  cuddRef(work2);
  work3 = Cudd_bddOr(manager, work, work2);
  cuddRef(work3);
  printf("%d %d %d\n", Cudd_DagSize(work), Cudd_DagSize(work2), Cudd_DagSize(work3)); 
  Cudd_RecursiveDeref(manager, work);
  Cudd_RecursiveDeref(manager, work2);
  work = Cudd_zddIsopFlip01(manager, work3, work3,&work2);
  cuddRef(work2);
  cuddRef(work);
  Cudd_RecursiveDeref(manager, work);
  res = alloc_res(work2);
  Cudd_RecursiveDerefZdd(manager, work2);
  CAMLreturn(res);
}

extern "C" value bdd_to_clause_set(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  DdNode *w, *w2;
  w2 = Cudd_zddIsopFlip01(manager, bdd_val(v).getNode(), bdd_val(v).getNode(), &w);
  cuddRef(w);
  cuddRef(w2);
  Cudd_RecursiveDeref(manager, w2);
  res = alloc_res(w);
  Cudd_RecursiveDerefZdd(manager, w);
  CAMLreturn(res);
}

extern "C" value bdd_choose_clause_set(value v1, value v2)
{
  CAMLparam2(v1, v2);
  CAMLlocal1(res);
  DdNode *w, *w2;
  w2 = Cudd_zddIsopFlip01(manager, bdd_val(v1).getNode(), bdd_val(v2).getNode(), &w);
  cuddRef(w);
  cuddRef(w2);
  Cudd_RecursiveDeref(manager, w2);
  res = alloc_res(w);
  Cudd_RecursiveDerefZdd(manager, w);
  CAMLreturn(res);
}

extern "C" value clause_subtraction(value v1, value v2)
{
  CAMLparam2(v1, v2);
  CAMLlocal1(res);
  DdNode* work;
  work = zdd_mydiff(manager, zdd_val(v1), zdd_val(v2));
  cuddRef(work);
  res = alloc_res(work);
  Cudd_RecursiveDerefZdd(manager, work);
  CAMLreturn(res);
}

extern "C" value qbf_pure_adjust(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  DdNode* work;
  work = adjust_pure_literals(manager, zdd_val(v));
  cuddRef(work);
  res = alloc_res(work);
  Cudd_RecursiveDerefZdd(manager, work);
  CAMLreturn(res);
}

extern "C" value clause_set_size(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  int size = Cudd_zddDagSize(zdd_val(v));
  if (zdd_val(v) == DD_ZERO(manager))
    size = -1;
  res = Val_int(size);
  CAMLreturn(res);  
}

extern "C" value clause_set_clauses(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  int size = (int) Cudd_CountPathsToNonZero(zdd_val(v));
  if (zdd_val(v) == DD_ZERO(manager))
    size = -1;
  res = Val_int(size);
  CAMLreturn(res);  
}

extern "C" value init_zres(value v)
{
  CAMLparam0();
  CAMLlocal1(res);
  Cudd_AutodynDisable(manager);
  Cudd_zddVarsFromBddVars(manager, 2);
  res = Val_unit;
  CAMLreturn(res);
}

extern "C" value set_quantifier_map(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  for (int i=0;i<Wosize_val(v);i++) {
    nesting[i] = Int_val(Field(v,i));
  }
  res = Val_unit;
  CAMLreturn(res);
}

extern "C" value make_all_assignments(value v1, value v2)
{
  CAMLparam2(v1, v2);
  CAMLlocal1(res);
  DdNode* work;
  work = build_all_cubes(manager, Int_val(v1), Int_val(v2));
  cuddRef(work);
  res = alloc_res(work);
  Cudd_RecursiveDerefZdd(manager, work);
  CAMLreturn(res);
}

extern "C" value remove_unwit_assignments(value v1, value v2)
{
  CAMLparam2(v1, v2);
  CAMLlocal1(res);
  DdNode* work;
  work = subtract_unwit_clauses(manager, zdd_val(v1), zdd_val(v2));
  cuddRef(work);
  res = alloc_res(work);
  Cudd_RecursiveDerefZdd(manager, work);
  CAMLreturn(res);
}

extern "C" value clause_set_to_bdd(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  DdNode ***buckets = (DdNode ***)malloc(sizeof(DdNode **)*totalVars);
  int *bucklen = (int *)calloc(sizeof(int), totalVars);
  //  DdNode* work = build_bdd(manager, zdd_val(v),DD_ONE(manager));
  DdNode *work = build_bdd(manager, zdd_val(v), buckets, bucklen);
  cuddRef(work);
  res = alloc_bdd(work);
  for (int i=0;i<totalVars;i++) {
    if (bucklen[i]!=0) {
      for (int j=0;j<bucklen[i];j++)
	Cudd_RecursiveDeref(manager, buckets[i][j]);
      free(buckets[i]);
    }
  }
  free(buckets);
  free(bucklen);
  Cudd_RecursiveDeref(manager, work);
  CAMLreturn(res);
}

extern "C" value clause_set_to_bdd_nextbucket(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  DdNode* work = build_bdd_easyquant(manager, zdd_val(v),DD_ONE(manager));
  cuddRef(work);
  res = alloc_bdd(work);
  Cudd_RecursiveDeref(manager, work);
  CAMLreturn(res);
}

extern "C" value clause_set_to_bdd_quant(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  DdNode *vv = zdd_val(v);
  DdGen *g;
  DdNode *w,*r;
  DdNode **u;
  int *sign;
  int max = 0,i;
  Cudd_ForeachNode(manager, vv, g, w) {
    if (w != DD_ONE(manager) && w != DD_ZERO(manager))
      max = (max > w->index/2?max:w->index/2);
  }
  u = (DdNode **)alloca(sizeof(DdNode *)*max);
  sign = (int *)alloca(sizeof(int)*max);
  for (i=0;i<max;i++) {
    u[i] = Cudd_bddIthVar(manager, i+1);
    sign[i] = 1;
  }
  w = Cudd_bddComputeCube(manager, u, sign, max);
  cuddRef(w);
  r = build_bdd_quant(manager, vv, w);
  cuddRef(r);
  Cudd_RecursiveDeref(manager, w);
  res = alloc_bdd(r);
  Cudd_RecursiveDeref(manager, r);
  CAMLreturn(res);
}

extern "C" value clause_set_to_bdd_noquant(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  //DdNode* work = build_bdd(manager, zdd_val(v),DD_ONE(manager));
  DdNode* work = build_bdd_noquant(manager, zdd_val(v));
  cuddRef(work);
  res = alloc_bdd(work);
  Cudd_RecursiveDeref(manager, work);
  CAMLreturn(res);
}

extern "C" value clause_set_to_bdd_quant_new(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  //DdNode* work = build_bdd(manager, zdd_val(v),DD_ONE(manager));
  DdNode* work = build_bdd_quant_new(manager, zdd_val(v));
  cuddRef(work);
  res = alloc_bdd(work);
  Cudd_RecursiveDeref(manager, work);
  CAMLreturn(res);
}

extern "C" value clause_set_quant(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  DdNode* work = build_zdd_quant_new(manager, zdd_val(v));
  cuddRef(work);
  res = alloc_res(work);
  Cudd_RecursiveDerefZdd(manager, work);
  CAMLreturn(res);
}

extern "C" value clause_set_to_bdd_allquant(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  //DdNode* work = build_bdd(manager, zdd_val(v),DD_ONE(manager));
  DdNode* work = build_bdd_allquant(manager, zdd_val(v),0);
  cuddRef(work);
  res = alloc_bdd(work);
  Cudd_RecursiveDeref(manager, work);
  CAMLreturn(res);
}

extern "C" value clause_set_to_bdd_bed(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  //DdNode* work = build_bdd(manager, zdd_val(v),DD_ONE(manager));
  DdNode* work = build_bdd_allquant(manager, zdd_val(v),1);
  cuddRef(work);
  res = alloc_bdd(work);
  Cudd_RecursiveDeref(manager, work);
  CAMLreturn(res);
}

extern "C" value cnf_to_dnf(value v1, value v2)
{
  CAMLparam2(v1, v2);
  CAMLlocal1(res);
  DdNode *work = cnf2dnf(manager, zdd_val(v1), Int_val(v2));
  cuddRef(work);
  res = alloc_bdd(work);
  Cudd_RecursiveDeref(manager, work);
  CAMLreturn(res);
}

extern "C" value invert_bdd_order(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  invertVars = 1;
  CAMLreturn(Val_unit);
}

extern "C" value set_num_vars(value v)
{
  CAMLparam1(v);
  CAMLlocal1(res);
  totalVars = Int_val(v);
  CAMLreturn(Val_unit);
}


extern "C" value set_no_quantification(value v)
{
  CAMLparam0();
  CAMLlocal1(res);
  use_earlyquantification = 0;
  CAMLreturn(Val_unit);
}

extern "C" value dd_shuffle_heap(value v)
{
  CAMLparam1(v);
  CAMLlocal2(x,res);
  int bddVars = manager->size;
  int zddVars = manager->sizeZ;
  int alloc = (bddVars*2>zddVars?bddVars*2:zddVars);
  alloc = ((totalVars+1)*2>alloc?(totalVars+1)*2:alloc);
  int *perm = (int *)alloca(alloc*sizeof(int));
  int i,j;
  RGL::set_t s = RGL::alloc_set(0);
  for (i=0;i<alloc;i++) {
    if (i<alloc/2) {
      Cudd_bddIthVar(manager, i);
      s = RGL::put_set(s, i);
    }
  }
  printf("bvars = %d, zvars = %d, alloc = %d\n", manager->size, manager->sizeZ, alloc);
  fflush(stdout);
  i=0;
  x = v;
//  perm[i++] = 0;
//  RGL::remove_set(s, 0);
  while (Int_val(x)!=0) {
    int var;
    var = Int_val(Field(x,0));
    perm[i] = var;
    RGL::remove_set(s, var);
    //    printf("perm[%d] = %d\n", i, var);
    x = Field(x,1);
    i++;
  }
  for (j=0;j<RGL::size_set(s);i++,j++)
    perm[i] = s[j];
  for (;i<alloc;i++)
    perm[i] = i;
  RGL::free_set(s);
  Cudd_ShuffleHeap(manager, perm);
  Cudd_zddVarsFromBddVars(manager, 2);
  /*  printf("BDD heap shuffled, ZDD=%d\n", Cudd_ReadZddSize(manager));
  fflush(stdout);
  i=0;
  x=v;
  perm[i++] = 0;
  perm[i++] = 1;
  while (Int_val(x)!=0) {
    int var = Int_val(Field(x,0));
    perm[i++] = (var+1)*2;
    perm[i++] = (var+1)*2+1;
    x = Field(x,1);
  }
  for (;i<alloc;i++)
    perm[i] = i;
    Cudd_zddShuffleHeap(manager, perm);*/
  CAMLreturn(Val_unit);
}

extern "C" value print_clauses_ml(value v)
{
  CAMLparam1(v);
  print_clauses(manager, zdd_val(v), "out.cnf");
  CAMLreturn(Val_unit);
}
