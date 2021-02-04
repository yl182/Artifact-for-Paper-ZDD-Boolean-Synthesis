#include <stdio.h>
#include <stdlib.h>
#include "cudd.h"
#include "cuddInt.h"

#include "manip.h"

#include "set.h"

#include "bed.h"
#include "cudd2bed.h"

#undef bed_one
#undef bed_zero
extern const bed_node bed_one, bed_zero;

//#define UNION_CLAUSE_SETS

int totalVars = 1000;
int invertVars = 0;

int print_active = 0;

void print_bdd_support(DdManager *dd, DdNode *f)
{
  DdNode *s, *w;
  s = Cudd_Support(dd, f);
  cuddRef(s);
  w = s;
  while (!Cudd_IsConstant(w)) {
    printf("%d ",Cudd_Regular(w)->index);
    w = cuddT(Cudd_Regular(w));
  }
  printf("\n");
  Cudd_RecursiveDeref(dd, s);
}

void print_bdd_support_2(DdManager *dd, DdNode *f, DdNode *g)
{
  DdNode *s1, *s2, *s;
  s1 = Cudd_Support(dd, f);
  cuddRef(s1);
  s2 = Cudd_Support(dd, g);
  cuddRef(s2);
  s = Cudd_bddAnd(dd, s1, s2);
  cuddRef(s);
  Cudd_RecursiveDeref(dd, s1);
  Cudd_RecursiveDeref(dd, s2);
  print_bdd_support(dd, s);
  Cudd_RecursiveDeref(dd, s);
}

DdNode *getNode(DdManager *dd, int index)
{
  //  printf("%d:%d, ", invertVars, invertVars?(totalVars-index):index);
  if (invertVars)
    return Cudd_bddIthVar(dd, totalVars-index);
  else
    return Cudd_bddIthVar(dd, index);
}

int getNodeIndex(int index)
{
  if (invertVars)
    return totalVars-index;
  else
    return index;
}

DdNode *build_all_cubes_int(DdManager *dd, int start, int end)
{
  int i;
  DdNode *w, *x, *y;
  y = DD_ONE(dd);
  cuddRef(y);
  for (i=end;i>=start;i--) {
    x = cuddZddGetNode(dd, i*2+1, y, DD_ZERO(dd));
    if (x == NULL) {
      Cudd_RecursiveDeref(dd, y);
      return NULL;
    }
    cuddRef(x);
    w = cuddZddGetNode(dd, i*2, y, x);
    if (w == NULL) {
      Cudd_RecursiveDeref(dd, y);
      Cudd_RecursiveDeref(dd, x);
      return NULL;
    }
    cuddRef(w);
    cuddDeref(x);
    cuddDeref(y);
    y=w;
  }
  cuddDeref(w);
  return w;
}

DdNode *build_all_cubes(DdManager *dd, int start, int end)
{
  DdNode *res;
  
  do {
    dd->reordered = 0;
    res = build_all_cubes_int(dd, start, end);
  } while (dd->reordered == 1);
  return(res);
}

DdNode *subtract_unwit_clauses(DdManager *dd, DdNode *c, DdNode *a)
{
  DdNode *one = DD_ONE(dd), *zero = DD_ZERO(dd);
  DdNode *res, *t, *e, *work;
  int topa, topc;
  if (c == zero) 
    return a;
  if (c == one)
    return zero;
  if (a == zero)
    return zero;
  res = cuddCacheLookup2Zdd(dd, subtract_unwit_clauses, c, a);
  if (res != NULL)
    return(res);
  topc = c->index;
  topa = a->index;
  if (topc == topa) {
    //    printf("$");
    t = subtract_unwit_clauses(dd, cuddE(c), cuddT(a));
    if (t == NULL) {
      return NULL;
    }
    cuddRef(t);
#ifndef UNION_CLAUSE_SETS 
    work = subtract_unwit_clauses(dd, cuddT(c), cuddE(a));
    if (work == NULL) {
      Cudd_RecursiveDerefZdd(dd, t);
      return NULL;
    }
    cuddRef(work);
    e = subtract_unwit_clauses(dd, cuddE(c), work);
    if (e == NULL) {
      Cudd_RecursiveDerefZdd(dd, t);
      Cudd_RecursiveDerefZdd(dd, work);
      return NULL;
    }
    cuddRef(e);
    Cudd_RecursiveDerefZdd(dd, work);
    res = cuddZddGetNode(dd, topc, t, e);
    if (res == NULL) {
      Cudd_RecursiveDerefZdd(dd, t);
      Cudd_RecursiveDerefZdd(dd, e);
      return NULL;
    }
    cuddRef(res);
    Cudd_RecursiveDerefZdd(dd, t);
    Cudd_RecursiveDerefZdd(dd, e);
#else
    if (t != zero) {
      res = t;
    } else {
      work = Cudd_zddUnion(dd, cuddT(c), cuddE(c));
      if (work == NULL) {
	Cudd_RecursiveDerefZdd(dd, t);
	return NULL;
      }
      cuddRef(work);
      e = subtract_unwit_clauses(dd, work, cuddE(a));
      if (e == NULL) {
	Cudd_RecursiveDerefZdd(dd, t);
	Cudd_RecursiveDerefZdd(dd, work);
	return NULL;
      }
      cuddRef(e);
      res = e;
      Cudd_RecursiveDerefZdd(dd, work);
    }
#endif
  } else if (topc < topa) {
    //    printf("#");
#ifndef UNION_CLAUSE_SETS
    work = subtract_unwit_clauses(dd, cuddT(c), a);
    if (work == NULL)
      return NULL;
    cuddRef(work);
    res = subtract_unwit_clauses(dd, cuddE(c), work);
#else
    work = Cudd_zddUnion(dd, cuddT(c), cuddE(c));
    if (work == NULL)
      return NULL;
    cuddRef(work);
    res = subtract_unwit_clauses(dd, work, a);
#endif
    if (res == NULL) {
      Cudd_RecursiveDerefZdd(dd, work);
      return NULL;
    }
    cuddRef(res);
    Cudd_RecursiveDerefZdd(dd, work);
  } else { /* topc > topa */ 
    //    printf("&");
#ifndef UNION_CLAUSE_SETS
    t = subtract_unwit_clauses(dd, c, cuddT(a));
    if (t == NULL)
      return NULL;
    cuddRef(t);
    e = subtract_unwit_clauses(dd, c, cuddE(a));
    if (e == NULL) {
      Cudd_RecursiveDerefZdd(dd, t);
      return NULL;
    }
    cuddRef(e);
    res = cuddZddGetNode(dd, topa, t, e);
    if (res == NULL) {
      Cudd_RecursiveDerefZdd(dd, t);
      Cudd_RecursiveDerefZdd(dd, e);
      return NULL;
    }
    cuddRef(res);
    cuddDeref(t);
    cuddDeref(e);    
#else
    work = Cudd_zddUnion(dd, cuddT(a), cuddE(a));
    if (work == NULL)
      return NULL;
    cuddRef(work);
    res = subtract_unwit_clauses(dd, c, work);
    if (res == NULL) {
      Cudd_RecursiveDerefZdd(dd, work);
      return NULL;
    }
    cuddRef(res);
    Cudd_RecursiveDerefZdd(dd, work);
#endif
  }
  cuddCacheInsert2(dd, subtract_unwit_clauses, c, a, res);
  cuddDeref(res);
  return res;
}

DdNode *build_bdd_noquant(DdManager *dd, DdNode *f)
{
  DdNode *t, *e, *res, *tmp1, *tmp2;
  DdNode *one = DD_ONE(dd);
  if (f == one)
    return Cudd_Not(one);
  if (f == DD_ZERO(dd))
    return one;
  res = cuddCacheLookup1(dd, build_bdd_noquant, f);
  if (res != NULL)
    return res;
  
  tmp1 = build_bdd_noquant(dd, cuddT(f));
  if (tmp1 == NULL)
    return NULL;
  cuddRef(tmp1);
  if (f->index%2==0) 
    t = Cudd_bddOr(dd, tmp1, getNode(dd, f->index/2));
  else
    t = Cudd_bddOr(dd, tmp1, Cudd_Not(getNode(dd, f->index/2)));
  if (t == NULL) {
    Cudd_RecursiveDeref(dd, tmp1);
    return NULL;
  }
  cuddRef(t);
  Cudd_RecursiveDeref(dd, tmp1);
  if (t != Cudd_Not(one)) {
    e = build_bdd_noquant(dd, cuddE(f));
    if (e == NULL) {
      Cudd_RecursiveDeref(dd, t);
      return NULL;
    }
    cuddRef(e);
    res = Cudd_bddAnd(dd, t, e);
    if (res == NULL) {
      Cudd_RecursiveDeref(dd, t);
      Cudd_RecursiveDeref(dd, e);
      return NULL;
    }
    cuddRef(res);
    Cudd_RecursiveDeref(dd, t);
    Cudd_RecursiveDeref(dd, e);
  } else {
    res = t;
  }
  //  printf("%d:%d ", f->index/2, Cudd_DagSize(res));
  // fflush(stdout);
  cuddCacheInsert1(dd, build_bdd_noquant, f, res);
  cuddDeref(res);
  return res;
}

DdNode *cube(DdManager *dd, unsigned int min, unsigned int max)
{
  DdNode *var[max+1];
  int sign[max+1];
  int i;
  if (min>max) min = max;
  for (i=min;i<=max;i++) {
    var[i] = getNode(dd, i);
    sign[i] = 1;
  }
  return Cudd_bddComputeCube(dd, var+min, sign+min, max-min+1);
}

DdNode *build_bdd_rec(DdManager *dd, DdNode *f, DdNode *chain, int curvar)
{
  DdNode *zone = DD_ONE(dd), *zzero = DD_ZERO(dd);
  DdNode *bone = DD_ONE(dd), *bzero = Cudd_Not(bone);
  DdNode *t, *e, *tt, *ee, *res, *tmp1, *tmp2, *work;
  if (f == zone) 
    return bzero;
  if (f == zzero)
    return chain;
  if (chain == bzero)
    return bzero;
  res = cuddCacheLookup(dd, (int)build_bdd_rec, f, chain, Cudd_bddIthVar(dd, curvar));
  if (res != NULL)
    return res;

  //  t = cuddT(f);
  //  e = cuddE(f);
  t = Cudd_zddSubset1(dd, f, curvar*2);
  cuddRef(t);
  e = Cudd_zddSubset0(dd, f, curvar*2);
  cuddRef(e);
  tmp1 = build_bdd_noquant(dd, t);
  if (tmp1==NULL) {
    Cudd_RecursiveDerefZdd(dd, t);
    Cudd_RecursiveDerefZdd(dd, e);
    return NULL;
  }
  cuddRef(tmp1);
  Cudd_RecursiveDerefZdd(dd, t);
  tt = Cudd_bddOr(dd, tmp1, getNode(dd, f->index/2));
  if (tt == NULL) {
    Cudd_RecursiveDeref(dd, tmp1);
    Cudd_RecursiveDerefZdd(dd, e);
    return NULL;
  }
  cuddRef(tt);
  Cudd_RecursiveDeref(dd, tmp1);
  work = Cudd_zddSubset1(dd, e, curvar*2+1);
  cuddRef(work);
  tmp1 = build_bdd_noquant(dd, work);
  if (tmp1 == NULL) {
    Cudd_RecursiveDeref(dd, tt);
    Cudd_RecursiveDerefZdd(dd, e);
    Cudd_RecursiveDerefZdd(dd, work);
    return NULL;
  }
  cuddRef(tmp1);
  Cudd_RecursiveDerefZdd(dd, work);
  ee = Cudd_bddOr(dd, tmp1, Cudd_Not(getNode(dd, f->index/2)));
  if (ee == NULL) {
    Cudd_RecursiveDeref(dd, tt);
    Cudd_RecursiveDeref(dd, tmp1);
    Cudd_RecursiveDerefZdd(dd, e);
    Cudd_RecursiveDerefZdd(dd, work);
    return NULL;
  }
  cuddRef(ee);
  Cudd_RecursiveDeref(dd, tmp1);
  work = Cudd_bddAnd(dd, tt, ee);
  if (work == NULL) {
    Cudd_RecursiveDeref(dd, tt);
    Cudd_RecursiveDeref(dd, ee);
    Cudd_RecursiveDerefZdd(dd, e);
    return NULL;
  }
  cuddRef(work);
  Cudd_RecursiveDeref(dd, tt);
  Cudd_RecursiveDeref(dd, ee);
  ee = Cudd_zddSubset0(dd, e, curvar*2+1);
  if (ee == NULL) {  
    Cudd_RecursiveDerefZdd(dd, work);
    Cudd_RecursiveDerefZdd(dd, e);
    return NULL;
  }
  cuddRef(ee);
  Cudd_RecursiveDerefZdd(dd, e);
  tmp1 = cube(dd, curvar, curvar);
  //  printf("(%d,%d) ", Cudd_Regular(chain)->index, f->index/2);
  if (tmp1 == NULL) {
    Cudd_RecursiveDeref(dd, work);
    Cudd_RecursiveDerefZdd(dd, ee);
    return NULL;
  }
  cuddRef(tmp1);

  if (print_active) {
    print_bdd_support_2(dd, chain, work);
    //    printf("Quantifying:\n");
    //    print_bdd_support(dd, tmp1);
  }
  
  tmp2 = Cudd_bddAndAbstract(dd, chain, work, tmp1);
  //  printf("[%d:%d]", Cudd_Regular(chain)->index, Cudd_DagSize(tmp2));
  //  fflush(stdout);
  //tmp2 = Cudd_bddAnd(dd, work, chain);
  if (tmp2 == NULL) {
    Cudd_RecursiveDeref(dd, work);
    Cudd_RecursiveDeref(dd, tmp1);
    return NULL;
  }
  cuddRef(tmp2);
  Cudd_RecursiveDeref(dd, work);
  Cudd_RecursiveDeref(dd, tmp1);
  //  printf("{%d:%d} ", f->index/2, Cudd_DagSize(tmp2));
  //  fflush(stdout);
  res = build_bdd_rec(dd, ee, tmp2, curvar+1);
  if (res == NULL) {
    Cudd_RecursiveDeref(dd, tmp2);
    return NULL;
  }
  cuddRef(res);
  Cudd_RecursiveDeref(dd, tmp2);
  //  printf("[%d:%d] ", f->index/2, Cudd_DagSize(res));
  //  fflush(stdout);
  cuddCacheInsert(dd, (int)build_bdd_rec, f, chain, Cudd_bddIthVar(dd, curvar), res);
  cuddDeref(res);
  return res;
}

DdNode *build_bdd(DdManager *dd, DdNode *f, DdNode *chain)
{
  return build_bdd_rec(dd, f, chain, 0);
}

DdNode *limit_cube(DdManager *dd, DdNode *cube, set_t s)
{
  DdNode *work, *res;
  if (cube == DD_ONE(dd))
    return cube;
  if (contains_set(s, cube->index))
    return limit_cube(dd, cuddT(cube), s);
  work = limit_cube(dd, cuddT(cube), s);
  cuddRef(work);
  res = cuddUniqueInter(dd, cube->index, work, Cudd_Not(DD_ONE(dd)));
  cuddRef(res);
  cuddDeref(work);
  cuddDeref(res);
  return res;
}

DdNode *restrict_cube(DdManager *dd, DdNode *t, DdNode *e, DdNode *cube, int index)
{
  DdNode *work;
  set_t k = alloc_set(0);
  DdGen *g;
  int *sign;
  int i, size;
  if (cube == DD_ONE(dd))
    return cube;
  k = put_set(k, getNodeIndex(index));
  Cudd_ForeachNode(dd, t, g, work) {
    if ((work != DD_ONE(dd)) && (work != DD_ZERO(dd)))
      k = put_set(k, getNodeIndex(work->index/2));
  }
  Cudd_ForeachNode(dd, e, g, work) {
    if ((work != DD_ONE(dd)) && (work != DD_ZERO(dd)))
      k = put_set(k, getNodeIndex(work->index/2));
  }
  size = size_set(k);
  work = limit_cube(dd, cube, k);
  free_set(k);
  return work;
}

DdNode *build_bdd_quant_rec(DdManager *dd, DdNode *f, DdNode *cube, int curvar)
{
  DdNode *zone = DD_ONE(dd), *zzero = DD_ZERO(dd);
  DdNode *bone = DD_ONE(dd), *bzero = Cudd_Not(bone);
  DdNode *t, *e, *tt, *ee, *res, *tmp1, *tmp2, *work;
  if (f == zone) 
    return bzero;
  if (f == zzero)
    return bone;
  res = cuddCacheLookup(dd, (int)build_bdd_quant_rec, f, cube, Cudd_bddIthVar(dd, curvar));
  if (res != NULL)
    return res;

  t = Cudd_zddSubset1(dd, f, curvar*2);
  cuddRef(t);
  tmp1 = Cudd_zddSubset0(dd, f, curvar*2);
  cuddRef(tmp1);
  e = Cudd_zddSubset1(dd, tmp1, curvar*2+1);
  cuddRef(e);
  ee = Cudd_zddSubset0(dd, tmp1, curvar*2+1);
  cuddRef(ee);
  Cudd_RecursiveDerefZdd(dd, tmp1);

  tmp2 = restrict_cube(dd, t, e, cube, f->index/2);
  cuddRef(tmp2);
  work = build_bdd_quant_rec(dd, ee, tmp2, curvar+1);
  cuddRef(work);
  Cudd_RecursiveDeref(dd, tmp2);
  Cudd_RecursiveDerefZdd(dd, ee);
  if (work != bzero) {
    tmp1 = build_bdd_noquant(dd, t);
    cuddRef(tmp1);
    tt = Cudd_bddOr(dd, tmp1, getNode(dd, f->index/2));
    cuddRef(tt);
    Cudd_RecursiveDeref(dd, tmp1);
    tmp1 = build_bdd_noquant(dd, e);
    cuddRef(tmp1);
    ee = Cudd_bddOr(dd, tmp1, Cudd_Not(getNode(dd, f->index/2)));
    cuddRef(ee);
    Cudd_RecursiveDeref(dd, tmp1);
    tmp1 = Cudd_bddAnd(dd, tt, ee);
    cuddRef(tmp1);
    Cudd_RecursiveDeref(dd, tt);
    Cudd_RecursiveDeref(dd, ee);

    if (print_active) {
      print_bdd_support_2(dd, work, tmp1);
    }
    
    res = Cudd_bddAndAbstract(dd, work, tmp1, cube);
    cuddRef(res);
    Cudd_RecursiveDeref(dd, work);
    Cudd_RecursiveDeref(dd, tmp1);
  } else {
    res = work;
  }
  Cudd_RecursiveDerefZdd(dd, t);
  Cudd_RecursiveDerefZdd(dd, e);
  //  printf("res = %d\n", Cudd_DagSize(res));
  //  fflush(stdout);
  cuddCacheInsert(dd, (int)build_bdd_quant_rec, f, cube, Cudd_bddIthVar(dd, curvar), res);
  cuddDeref(res);
  return res;
}

DdNode *build_bdd_quant(DdManager *dd, DdNode *f, DdNode *cube)
{
  return build_bdd_quant_rec(dd, f, cube, 0);
}

DdNode *conjunction_empty_all(DdManager *dd, DdNode **nodes, int size)
{
  DdNode *one = DD_ONE(dd), *zero = Cudd_Not(DD_ONE(dd));
  DdNode **callbuffer = (DdNode **)alloca(sizeof(DdNode *)*size);
  int i, s;
  int minindex = 65535;
  int index;
  DdNode *res;
  unsigned long cache1 = 0;
  //  printf("called with size=%d\n", size);
  for (i=0;i<size;i++) {
    if (nodes[i] == one) {
      nodes[i] = nodes[size-1];
      size--;
      i--;
      continue;
    }
    if (nodes[i] == zero) {
      //  printf("returning zero\n");
      return zero;
    }
    //    cache1 = (cache1*7)^(unsigned long)nodes[i];
    index = Cudd_Regular(nodes[i])->index;
    minindex = (minindex>index?index:minindex);
  }
  if (size == 0)
    return one;
  //  res = cuddCacheLookup1(dd, (DdNode * (*)(DdManager *, DdNode *))conjunction_empty_all, (DdNode *)cache1);
  //  if (res != NULL)
  //  return res;
  for (i=0,s=0;i<size;i++) {
    if (Cudd_Regular(nodes[i])->index == minindex)
      if (!Cudd_IsComplement(nodes[i])) {
	callbuffer[s++] = cuddT(nodes[i]);
      } else {
	callbuffer[s++] = Cudd_Not(cuddT(Cudd_Regular(nodes[i])));
      }
    else
      callbuffer[s++] = nodes[i];
  } 
  res = conjunction_empty_all(dd, callbuffer, s);
  if (res == one) {
    //    cuddCacheInsert1(dd, (DdNode * (*)(DdManager *, DdNode *))conjunction_empty_all, (DdNode *)cache1, res);
    return one;
  }
  for (i=0,s=0;i<size;i++) {
    if (Cudd_Regular(nodes[i])->index == minindex)
      if (!Cudd_IsComplement(nodes[i])) {
	callbuffer[s++] = cuddE(nodes[i]);
      } else {
	callbuffer[s++] = Cudd_Not(cuddE(Cudd_Regular(nodes[i])));
      }
    else
      callbuffer[s++] = nodes[i];
  }
  res = conjunction_empty_all(dd, callbuffer, s);
  //  cuddCacheInsert1(dd, (DdNode * (*)(DdManager *, DdNode *))conjunction_empty_all, (DdNode *)cache1, res);
  return res;
}

DdNode *check_empty_bed(DdManager *dd, DdNode **nodes, int size)
{
  bed_node *n = (bed_node*)alloca(sizeof(bed_node)*size);
  int i;
  bed_node w, w2;
  int lastvar = 0;
  bed_new_variables(2*totalVars+2);
  for (i=0;i<size;i++) {
    n[i] = bdd_to_bed(dd, nodes[i]);
    bed_ref(n[i]);
  }
  w = n[0];
  for (i=1;i<size;i++) {
    w2 = bed_mk_op(BED_AND, w, n[i]);
    bed_ref(w2);
    bed_deref(w);
    while (bed_get_var(n[i])>lastvar) {
      w = bed_mk_exists(lastvar++, w2);
      bed_ref(w);
      bed_deref(w2);
      w2 = w;
    }
    bed_deref(n[i]);
    w = w2;
  }
  while (totalVars+1>lastvar) {
    w2 = bed_mk_exists(lastvar, w);
    lastvar++;
    bed_ref(w2);
    bed_deref(w);
    w = w2;
  }
  
  for (i=0;i<totalVars+1;i++) {
    w2 = bed_upone(i, w);
    bed_ref(w2);
    //   printf("%d:%d,",i,bed_node_count(w2));
    //    fflush(stdout);
    bed_deref(w);
    w = w2;
  }
  //  w = bed_upall(w2);
  if (w == bed_zero) {
    return Cudd_Not(DD_ONE(dd));
  } else {
    return DD_ONE(dd);
  }
}

DdNode *build_bdd_allquant(DdManager *dd, DdNode *f, int usebed)
{
  int size = totalVars*2;
  DdNode **work = (DdNode **)alloca(sizeof(DdNode *)*size);
  DdNode **work2 = (DdNode **)alloca(sizeof(DdNode *)*size);
  DdNode *g = f, *t, *tmp1;
  DdNode *w, *w2;
  int i=0,j,k;
  while (g != DD_ZERO(dd)) {
    tmp1 = build_bdd_noquant(dd, cuddT(g));
    if (tmp1 == NULL)
      return NULL;
    cuddRef(tmp1);
    if (g->index%2==0) 
      t = Cudd_bddOr(dd, tmp1, getNode(dd, g->index/2));
    else
      t = Cudd_bddOr(dd, tmp1, Cudd_Not(getNode(dd, g->index/2)));
    if (t == NULL) {
      Cudd_RecursiveDeref(dd, tmp1);
      return NULL;
    }
    cuddRef(t);
    Cudd_RecursiveDeref(dd, tmp1);
    work[i++] = t;
    g = cuddE(g);
  }
  w = work[0];
  cuddRef(w);
  for (j=1,k=0;j<i;j++) {
    if (Cudd_DagSize(w)<1000) {
      w2 = Cudd_bddAnd(dd, w, work[j]);
      cuddRef(w2);
      Cudd_RecursiveDeref(dd, w);
      w = w2;
    } else {
      work2[k++] = w;
      if (j<i) {
	w = work[j];
	cuddRef(w);
      } else
	w = NULL;
    }
  }
  if (w != NULL)
    work2[k++] = w;
  if (usebed) 
    return check_empty_bed(dd, work2, k);
  else
    return conjunction_empty_all(dd, work2, k);
}

DdNode *clause_set_to_bdd(DdManager *dd, DdNode *f, int vars)
{
  DdNode *work, *res;
  int i;
  int v = vars*2;
  int *perm = (int *)alloca(sizeof(int)*(v+1)*2);
  work = Cudd_zddPortToBdd(dd, f);
  if (work == NULL)
    return NULL;
  cuddRef(work);
  for (i=0;i<=v;i++) {
    perm[i] = i*2;
    perm[vars+i+1] = i*2+1;
  }
  res = Cudd_bddPermute(dd, work, perm);
  if (res == NULL) {
    Cudd_RecursiveDeref(dd, work);
    return NULL;
  }
  cuddRef(res);
  Cudd_RecursiveDeref(dd, work);
  cuddDeref(res);
  return res;
}

DdNode *constraints(DdManager *dd, int vars)
{
  int i;
  DdNode *work, *work2, *work3;
  DdNode *res = Cudd_Not(DD_ONE(dd));
  cuddRef(res);
  for (i=vars*2;i>=0;i--) {
    work = Cudd_bddOr(dd, Cudd_Not(getNode(dd, i*2)), getNode(dd, i*2+1));
    if (work == NULL)
      return NULL;
    cuddRef(work);
    work2 = Cudd_bddOr(dd, work, res);
    if (work2 == NULL) {
      Cudd_RecursiveDeref(dd, work);
      return NULL;
    }
    cuddRef(work2);
    Cudd_RecursiveDeref(dd, work);
    Cudd_RecursiveDeref(dd, res);
    res = work2;
  }
  work3 = Cudd_Not(DD_ONE(dd));
  cuddRef(work3);
  for (i=vars*2;i>=0;i--) {
    work = Cudd_bddAnd(dd, getNode(dd, i*2), getNode(dd, i*2+1));
    cuddRef(work);
    work2 = Cudd_bddOr(dd, work, work3);
    cuddRef(work2);
    Cudd_RecursiveDeref(dd, work);
    Cudd_RecursiveDeref(dd, work3);
    work3 = work2;
  }
  work = Cudd_bddAnd(dd, work3, res);
  cuddRef(work);
  Cudd_RecursiveDeref(dd, work3);
  Cudd_RecursiveDeref(dd, res);
  res = work;
  cuddDeref(res);
  return res;
}

DdNode *restrictions(DdManager *dd, int vars)
{
  int i;
  DdNode *work, *work2;
  DdNode *res = DD_ONE(dd);
  cuddRef(res);
  for (i=vars;i>=0;i--) {
    work = Cudd_bddOr(dd, Cudd_Not(getNode(dd, i*4+1)), Cudd_Not(getNode(dd, i*4+3)));
    if (work == NULL)
      return NULL;
    cuddRef(work);
    work2 = Cudd_bddAnd(dd, work, res);
    if (work2 == NULL) {
      Cudd_RecursiveDeref(dd, work);
      return NULL;
    }
    cuddRef(work2);
    Cudd_RecursiveDeref(dd, work);
    Cudd_RecursiveDeref(dd, res);
    res = work2;
  }
  cuddDeref(res);
  return res;
}

DdNode *make_cube(DdManager *dd, int vars)
{
  DdNode *var[(vars+1)*2];
  int sign[(vars+1)*2];
  int i;
  for (i=0;i<=(vars+1)*2;i++) {
    var[i] = getNode(dd, i*2);
    sign[i] = 1;
  }
  return Cudd_bddComputeCube(dd, var, sign, (vars+1)*2);  
}

DdNode *cnf2dnf(DdManager *dd, DdNode *f, int vars)
{
  DdNode *clauses, *cube, *cons, *rest, *res;
  DdNode *work;
  cube = make_cube(dd, vars);
  cuddRef(cube);
  //  Cudd_PrintMinterm(dd, cube);
  //  printf("cube = %d\n", Cudd_DagSize(cube));
  //  fflush(stdout);
  clauses = clause_set_to_bdd(dd, f, vars);
  cuddRef(clauses);
  //  Cudd_PrintMinterm(dd, clauses);
  //  printf("clauses = %d\n", Cudd_DagSize(clauses));
  //  fflush(stdout);
  cons = constraints(dd, vars);
  cuddRef(cons);
  //  Cudd_PrintMinterm(dd, cons);
  //  printf("cons = %d\n", Cudd_DagSize(cons));
  //  fflush(stdout);
  rest = restrictions(dd, vars);
  cuddRef(rest);
  //  Cudd_PrintMinterm(dd, rest);
  //  printf("rest = %d\n", Cudd_DagSize(rest));
  //  fflush(stdout);
  work = Cudd_bddOr(dd, Cudd_Not(cons), Cudd_Not(rest));
  cuddRef(work);
  //  work = Cudd_Not(Cudd_bddAndAbstract(dd, clauses, Cudd_Not(cons), cube));
  //cuddRef(work);
  //  Cudd_PrintMinterm(dd, work);
  //  printf("work = %d\n", Cudd_DagSize(work));
  //  fflush(stdout);
  
  res = Cudd_Not(Cudd_bddAndAbstract(dd, clauses, work, cube));
  cuddRef(res);
  /*  Cudd_RecursiveDeref(dd, cube);
  Cudd_RecursiveDeref(dd, clauses);
  Cudd_RecursiveDeref(dd, cons);  
  res = Cudd_bddAnd(dd, work, rest);
  cuddRef(res);*/
  //  Cudd_PrintMinterm(dd, res);
  //  printf("res = %d\n", Cudd_DagSize(res));
  //  fflush(stdout);
  Cudd_RecursiveDeref(dd, work);
  Cudd_RecursiveDeref(dd, rest);
  cuddDeref(res);
  return res;
}


