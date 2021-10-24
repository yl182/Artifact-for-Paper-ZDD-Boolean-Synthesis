#include <stdio.h>
#include "cudd2bed.h"
#include "cache.h"

#undef bed_one
#undef bed_zero

#define TAG_TOBDD 135
#define TAG_FROMBDD 136

extern const bed_node bed_one, bed_zero;

bed_node bdd_to_bed(DdManager *dd, DdNode *f)
{
  DdNode *fv, *fnv;
  bed_node l, h, res;
  Cache *p;
  if (f == DD_ONE(dd))
    return bed_one;
  if (f == Cudd_Not(DD_ONE(dd)))
    return bed_zero;
  p = cache_get(TAG_FROMBDD, (unsigned int)f, 0, 0, 0);
  if (cache_match(p, TAG_FROMBDD, (unsigned int)f, 0, 0, 0)) {
    return (bed_node)p->r1;
  }
  if (Cudd_IsComplement(f)) {
    f = Cudd_Regular(f);
    fv = Cudd_Not(cuddT(f));
    fnv = Cudd_Not(cuddE(f));
  } else {
    fv = cuddT(f);
    fnv = cuddE(f);
  }
  l = bdd_to_bed(dd, fv);
  h = bdd_to_bed(dd, fnv);
  res = bed_mk_var(f->index, l, h);
  cache_insert(p, TAG_FROMBDD, (unsigned int)f, 0, 0, 0, res, 0);
  return res;
}

DdNode *bed_to_bdd_int(DdManager *dd, bed_node f)
{
  bed_node l, h;
  DdNode *t, *e, *res;
  Cache *p;
  int v;
  if (f == bed_one)
    return DD_ONE(dd);
  if (f == bed_zero)
    return Cudd_Not(DD_ONE(dd));
  p = cache_get(TAG_TOBDD, f, 0, 0, 0);
  if (cache_match(p, TAG_TOBDD, f, 0, 0, 0)) {
    return (DdNode*)p->r1;
  }
  v = bed_get_var(f);
  l = bed_get_low(f);
  h = bed_get_high(f);
  t = bed_to_bdd_int(dd, l);
  cuddRef(t);
  e = bed_to_bdd_int(dd, h);
  cuddRef(e);
  res = cuddUniqueInter(dd, v, t, e);
  cuddRef(res);
  cuddDeref(t);
  cuddDeref(e);
  cache_insert(p, TAG_TOBDD, f, 0, 0, 0, (unsigned int)res, 0);
  return res;
}

DdNode *bed_to_bdd(DdManager *dd, bed_node f)
{
  DdNode *res;
  if (!bed_is_bdd(f))
    f = bed_upall(f);
  res = bed_to_bdd_int(dd, f);
  cuddDeref(res);
  return res;
}
