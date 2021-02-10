#include <stdio.h>
#include <stdlib.h>
#include <util/util.h>
#include <st.h>
#include <cudd.h>

#include "epdInt.h"
#include "cuddInt.h"

#include "manip.h"
/* #define LOCALDBG   */
/* #define AUTOCHECK */

#ifdef AUTOCHECK
int premier_cas_xpxn_xpxn = 0;
int premier_cas_xpxn_xp = 0;
int premier_cas_xpxn_xn = 0;
int premier_cas_xpxn_D = 0;
int premier_cas_xp_xp = 0;
int premier_cas_xp_xn = 0;
int premier_cas_xn_xn = 0;
int premier_cas_x_D = 0;
#endif
#define REF(i) (Cudd_Ref(i))

 DdManager * manager;

DdNode *
cuddCacheLookup1IntZdd(
  DdManager * table,
  void *op,
  DdNode * f, int i)
{
    int posn;
    DdCache *en,*cache;
    DdNode *data;

    cache = table->cache;
#ifdef DD_DEBUG
    if (cache == NULL) {
        return(NULL);
    }
#endif

    posn = ddCHash2(op,f,i,table->cacheShift);
    en = &cache[posn];
    if (en->data != NULL && en->f==f && en->h==(ptruint)op+i) {
	data = Cudd_Regular(en->data);
	table->cacheHits++;
	if (data->ref == 0) {
	    cuddReclaimZdd(table,data);
	}
	return(en->data);
    }

    /* Cache miss: decide whether to resize. */
    table->cacheMisses++;

    if (table->cacheSlack >= 0 &&
	table->cacheHits > table->cacheMisses * table->minHit) {
	cuddCacheResize(table);
    }

    return(NULL);

} /* end of cuddCacheLookup1IntZdd */

void
cuddCacheInsert1IntZdd(
  DdManager * table,
  void *op,
  DdNode * f,
  int i,
  DdNode * data)
{
    int posn;
    register DdCache *entry;

    posn = ddCHash2(op,f,i,table->cacheShift);
    entry = &table->cache[posn];

    if (entry->data != NULL) {
        table->cachecollisions++;
    }
    table->cacheinserts++;

    entry->f = f;
    entry->g = f;
    entry->h = (ptruint) op+i;
    entry->data = data;
#ifdef DD_CACHE_PROFILE
    entry->count++;
#endif

} /* end of cuddCacheInsert1IntZdd */

static inline int max(int a, int b)
{
  return (a>b?a:b);
}


DdNode * zdd_myproduct_aux(DdManager * dd, DdNode * zbdd_A, DdNode * zbdd_B);

DdNode * product_cas_xpxn_xpxn(DdManager * dd, DdNode * zbdd_A, DdNode * zbdd_B);
DdNode * product_cas_xpxn_xp(DdManager * dd, DdNode * zbdd_A, DdNode * zbdd_B);
DdNode * product_cas_xpxn_xn(DdManager * dd, DdNode * zbdd_A, DdNode * zbdd_B);
DdNode * product_cas_xpxn_D(DdManager * dd, DdNode * New_A, DdNode * zbdd_B);
DdNode * product_cas_xp_xp(DdManager * dd, DdNode * zbdd_A, DdNode * zbdd_B);
DdNode * product_cas_xp_xn(DdManager * dd, DdNode * zbdd_A, DdNode * zbdd_B);
DdNode * product_cas_xn_xn(DdManager * dd, DdNode * zbdd_A, DdNode * zbdd_B);
DdNode * product_cas_x_D(DdManager * dd, DdNode * New_A, DdNode * zbdd_B);

DdNode *get_zdd_support_aux(DdManager *dd, DdNode *f);



int get_depth(DdManager *dd, DdNode *f)
{
  DdNode *w, *supp = get_zdd_support_aux(dd, f);
  int d = 0;
  if (supp == NULL)
    return 0;
  cuddRef(supp);
  w = supp;
  while (!Cudd_IsConstant(w)) {
    d = max(d, nesting[w->index/2]);
  }
  return d;
}

DdNode *remove_universal_literals_arbitary_varord_aux(DdManager *dd, DdNode *f, int *depth)
{
  DdNode *one = DD_ONE(dd);
  DdNode *zero = DD_ZERO(dd);
  DdNode *t, *e, *res;
  int ftop, fv, d, dt, de;
  if (Cudd_IsConstant(f))
    return f;
  res = cuddCacheLookup1IntZdd(dd, (void*)remove_universal_literals_arbitary_varord_aux, f, *depth);
  if (res != NULL)
  return(res);
  ftop = f->index;
  fv = ftop/2;
  d = nesting[fv];
  if ((d&1)==1) {//existential
    dt = de = max(*depth, d);
  } else {
    dt = de = *depth;
  }
  t = remove_universal_literals_arbitary_varord_aux(dd, cuddT(f), &dt);
  if (t == NULL)
    return NULL;
  cuddRef(t);
  e = remove_universal_literals_arbitary_varord_aux(dd, cuddE(f), &de);
  if (e == NULL) {
    Cudd_RecursiveDerefZdd(dd, t);
    return NULL;
  }
  cuddRef(e);
  if (((d&1)==0)&&(d>*depth)) {//universal and quantified
    res = zdd_myunion(dd, t, e);
    if (res == NULL) {
      Cudd_RecursiveDerefZdd(dd, t);
      Cudd_RecursiveDerefZdd(dd, e);
      return NULL;
    }
    cuddRef(res);
    Cudd_RecursiveDerefZdd(dd, t);
    Cudd_RecursiveDerefZdd(dd, e);
    *depth = max(*depth, get_depth(dd, res));
  } else {
    res = cuddZddGetNode(dd, ftop, t, e);
    if (res == NULL) {
      Cudd_RecursiveDerefZdd(dd, t);
      Cudd_RecursiveDerefZdd(dd, e);
      return NULL;
    }
    cuddRef(res);
    cuddDeref(t);
    cuddDeref(e);
    *depth = max(*depth, max(dt, de));
  }
  cuddCacheInsert1IntZdd(dd, (void*)remove_universal_literals_arbitary_varord_aux, f, *depth, res);
  cuddDeref(res);
  return res;
}

DdNode *remove_universal_literals_exist_before_univ_aux(DdManager *dd, DdNode *f, int level)
{
  DdNode *one = DD_ONE(dd), *zero = DD_ZERO(dd), *res, *t, *e;
  int depth, origlevel = level;  
  if (Cudd_IsConstant(f))
    return f;
  //  res = cuddCacheLookup1IntZdd(dd, (void*)remove_universal_literals_exist_before_univ_aux, f, level);
  //  if (res != NULL)
  //    return res;
  depth = nesting[f->index/2];
  if ((depth&1)==1) { //existential
    level = max(level, nesting[f->index/2]);
  }
  printf("depth=%d, level=%d\n",depth, level);
  fflush(stdout);
  t = remove_universal_literals_exist_before_univ_aux(dd, cuddT(f), level);
  if (t == NULL)
    return NULL;
  cuddRef(t);
  e = remove_universal_literals_exist_before_univ_aux(dd, cuddE(f), origlevel);
  if (e == NULL) {
    Cudd_RecursiveDerefZdd(dd, t);
    return NULL;
  }
  cuddRef(e);
  if (((depth&1)==0)&&(depth>level)) {//universal and quantified
    printf("Quantifying %d\n", f->index/2);
    fflush(stdout);
    res = zdd_myunion(dd, t, e);
    if (res == NULL) {
      Cudd_RecursiveDerefZdd(dd, t);
      Cudd_RecursiveDerefZdd(dd, e);
      return NULL;
    }
    cuddRef(res);
    Cudd_RecursiveDerefZdd(dd, t);
    Cudd_RecursiveDerefZdd(dd, e);
  } else {
    res = cuddZddGetNode(dd, f->index, t, e);
    if (res == NULL) {
      Cudd_RecursiveDerefZdd(dd, t);
      Cudd_RecursiveDerefZdd(dd, e);
      return NULL;
    }
    cuddRef(res);
    cuddDeref(t);
    cuddDeref(e);
  }
  cuddCacheInsert1IntZdd(dd, (void*)remove_universal_literals_exist_before_univ_aux, f, origlevel, res);
  cuddDeref(res);
  return res;
}

DdNode *remove_universal_literals(DdManager *dd, DdNode *f, int arbvo)
{
  DdNode *res;
  
  if (arbvo) {
    do {
      dd->reordered = 0;
      res = remove_universal_literals_arbitary_varord_aux(dd, f, 0);
    } while (dd->reordered == 1);
  } else {
    do {
      dd->reordered = 0;
      res = remove_universal_literals_exist_before_univ_aux(dd, f, 0);
    } while (dd->reordered == 1);
  }
  return(res);
}

DdNode *find_existential_unit_literals_aux(DdManager *dd, DdNode *f)
{
  DdNode *one = DD_ONE(dd), *zero = DD_ZERO(dd);
  DdNode *t, *e, *w, *res;
  if (Cudd_IsConstant(f))
    return one;
  if (nesting[f->index/2]&1==0)
    return one;
  t = cuddT(f);
  e = cuddE(f);
  w = find_existential_unit_literals_aux(dd, e);
  if (w == NULL)
    return NULL;
  cuddRef(w);
  if ((t == one)||(nesting[t->index/2]&1==0)) {
    res = Cudd_zddChange(dd, w, f->index);
    if (res == NULL) {
      Cudd_RecursiveDerefZdd(dd, w);
      return NULL;
    }
    cuddRef(res);
    Cudd_RecursiveDerefZdd(dd, w);
  } else {
    res = w;
  }
  cuddDeref(res);
  return res;  
}

DdNode *universal(DdManager *dd, DdNode *f)
{
  DdNode *one = DD_ONE(dd), *zero = DD_ZERO(dd), *res;
  if (f==one)
    return one;
  if (f==zero)
    return zero;
  res = cuddCacheLookup1Zdd(dd, universal, f);
  if (res != NULL)
    return(res);
  if (universal(dd, cuddE(f))==one) {
    cuddCacheInsert1(dd, universal, f, one);
    return one;
  }
  if ((nesting[f->index/2]&1)==1) {
    cuddCacheInsert1(dd, universal, f, zero);
    return zero;
  }
  res = universal(dd, cuddT(f));
  cuddCacheInsert1(dd, universal, f, res);
  return res;
}

DdNode *universal_after_level(DdManager *dd, DdNode *f, int lev)
{
  DdNode *one = DD_ONE(dd), *zero = DD_ZERO(dd), *res;
  if (f==one)
    return one;
  if (f==zero)
    return zero;
  res = cuddCacheLookup1IntZdd(dd, (void *)universal_after_level, f, lev);
  if (res != NULL)
    return(res);
  if (universal_after_level(dd, cuddE(f), lev)==one) {
    cuddCacheInsert1IntZdd(dd, (void *)universal_after_level, f, lev, one);
    return one;
  }
  if (((nesting[f->index/2]&1)==1)||(nesting[f->index/2]<lev)) {
    cuddCacheInsert1IntZdd(dd, (void *)universal_after_level, f, lev, zero);
    return zero;
  }
  res = universal_after_level(dd, cuddT(f),lev);
  cuddCacheInsert1IntZdd(dd, (void *)universal_after_level, f, lev, res);
  return res;
}

DdNode *find_qbf_unit_literals_aux(DdManager *dd, DdNode *f)
{
  DdNode *one = DD_ONE(dd), *zero = DD_ZERO(dd);
  DdNode *t, *e, *w, *w2, *res;
  if (Cudd_IsConstant(f))
    return one;
  res = cuddCacheLookup1Zdd(dd, find_qbf_unit_literals_aux, f);
  if (res != NULL)
    return(res);
  if (universal(dd, f)) {
    cuddCacheInsert1(dd, find_qbf_unit_literals_aux, f, zero);
    return zero;
  }
  t = cuddT(f);
  e = cuddE(f);
  w = find_qbf_unit_literals_aux(dd, e);
  if (w == NULL)
    return NULL;
  cuddRef(w);
  if ((nesting[f->index/2]&1)==0) { //universal
    w2 = find_qbf_unit_literals_aux(dd, t);
    if (w2 == NULL) {
      Cudd_RecursiveDerefZdd(dd, w);
      return NULL;
    }
    cuddRef(w2);
    //    printf("%%");
    //    fflush(stdout);
    res = Cudd_zddUnateProduct(dd, w, w2);
    if (res == NULL) {
      Cudd_RecursiveDerefZdd(dd, w);
      Cudd_RecursiveDerefZdd(dd, w2);
      return NULL;
    }
    cuddRef(res);
    Cudd_RecursiveDerefZdd(dd, w);
    Cudd_RecursiveDerefZdd(dd, w2);
  } else { // existential
    if (universal(dd, t)==one) {
      //      printf("Adding %d\n", f->index);
      //      fflush(stdout);
      res = Cudd_zddChange(dd, w, f->index);
      if (res == NULL) {
	Cudd_RecursiveDerefZdd(dd, w);
	return NULL;
      }
      cuddRef(res);
      Cudd_RecursiveDerefZdd(dd, w);
    } else
      res = w;
  }
  cuddCacheInsert1(dd, find_qbf_unit_literals_aux, f, res);
  cuddDeref(res);
  //  printf("returning %x\n",res);
  //  fflush(stdout);
  return res;
}

DdNode *find_qbf_unit_literals_level_aux(DdManager *dd, DdNode *f, int level)
{
  DdNode *one = DD_ONE(dd), *zero = DD_ZERO(dd);
  DdNode *t, *e, *w, *w2, *res;
  int l;
  if (Cudd_IsConstant(f))
    return one;
  res = cuddCacheLookup1IntZdd(dd, (void *)find_qbf_unit_literals_level_aux, f, level);
  if (res != NULL)
    return(res);
  t = cuddT(f);
  e = cuddE(f);
  w = find_qbf_unit_literals_level_aux(dd, e, level);
  if (w == NULL)
    return NULL;
  cuddRef(w);
  l = nesting[f->index/2];
  if ((l&1)==0) { //universal
    l = (l<level ? l : level);
    w2 = find_qbf_unit_literals_level_aux(dd, t, l);
    if (w2 == NULL) {
      Cudd_RecursiveDerefZdd(dd, w);
      return NULL;
    }
    cuddRef(w2);
    //    printf("%%");
    //    fflush(stdout);
    res = Cudd_zddUnateProduct(dd, w, w2);
    if (res == NULL) {
      Cudd_RecursiveDerefZdd(dd, w);
      Cudd_RecursiveDerefZdd(dd, w2);
      return NULL;
    }
    cuddRef(res);
    Cudd_RecursiveDerefZdd(dd, w);
    Cudd_RecursiveDerefZdd(dd, w2);
  } else { // existential
    if ((l<level) && (universal_after_level(dd, t, l)==one)) {
      //      printf("Adding %d\n", f->index);
      //      fflush(stdout);
      res = Cudd_zddChange(dd, w, f->index);
      if (res == NULL) {
	Cudd_RecursiveDerefZdd(dd, w);
	return NULL;
      }
      cuddRef(res);
      Cudd_RecursiveDerefZdd(dd, w);
    } else
      res = w;
  }
  cuddCacheInsert1IntZdd(dd, (void *)find_qbf_unit_literals_level_aux, f, level, res);
  cuddDeref(res);
  //  printf("returning %x\n",res);
  //  fflush(stdout);
  return res;
}

DdNode *find_existential_unit_literals(DdManager *dd, DdNode *f)
{
  DdNode *res;
  
  do {
    dd->reordered = 0;
    res = find_qbf_unit_literals_level_aux(dd, f,1000000);
  } while (dd->reordered == 1);
  return(res);
}

/* Generate a cube of all the unit literals in the clause set */
DdNode *find_unit_literals_aux(DdManager *dd, DdNode *f) {
  DdNode *one = DD_ONE(dd);
  DdNode *t, *e, *w, *res;
  if (Cudd_IsConstant(f)) {
    return one;
  }
  t = cuddT(f);
  e = cuddE(f);
  w = find_unit_literals_aux(dd, e);
  if (w == NULL)
    return NULL;
  cuddRef(w);
  if (t==one) {
    res = Cudd_zddChange(dd, w, f->index);
    if (res == NULL) {
      Cudd_RecursiveDerefZdd(dd, w);
      return NULL;
    }
    cuddRef(res);
    Cudd_RecursiveDerefZdd(dd, w);
  } else {
    res = w;
  }
  cuddDeref(res);
  return res;
}

DdNode *find_unit_literals(DdManager *dd, DdNode *f)
{
  DdNode *res;
  
  do {
    dd->reordered = 0;
    res = find_unit_literals_aux(dd, f);
  } while (dd->reordered == 1);
  return(res);
}

DdNode *adjust_pure_literals_aux(DdManager *dd, DdNode *f)
{
  DdNode *one = DD_ONE(dd), *zero = DD_ZERO(dd);
  DdNode *t, *res, *res2;
  int i;
  if (Cudd_IsConstant(f))
    return f;
  t = adjust_pure_literals_aux(dd, cuddT(f));
  if (t == NULL)
    return t;
  cuddRef(t);
  i = f->index;
  if ((nesting[i/2]&1)==0) { //universal
    res = Cudd_zddChange(dd, t, i^1);
    cuddRef(res);
    /*    i = i^1;    
    res2 = Cudd_zddChange(dd, res, i);
    cuddRef(res2);
    Cudd_RecursiveDerefZdd(dd, res);
    res = res2;*/
  } else {
    res = Cudd_zddChange(dd, t, i);
    cuddRef(res);
  }
  if (res == NULL) {
    Cudd_RecursiveDerefZdd(dd, t);
    return NULL;
  }
  Cudd_RecursiveDerefZdd(dd, t);
  cuddDeref(res);
  return res;
}

DdNode *adjust_pure_literals(DdManager *dd, DdNode *f)
{
  DdNode *res;
  do {
    dd->reordered = 0;
    res = adjust_pure_literals_aux(dd, f);
  } while (dd->reordered == 1);
  return(res);
}

DdNode *get_zdd_support_aux(DdManager *dd, DdNode *f)
{
  DdNode *one = DD_ONE(dd), *ts, *es, *w, *res;
  int ftop;
  if (Cudd_IsConstant(f))
    return one;
  res = cuddCacheLookup1Zdd(dd, get_zdd_support_aux, f);
  if (res != NULL)
    return(res);
  ftop = f->index;
  ts = get_zdd_support_aux(dd, cuddT(f));
  if (ts == NULL)
    return NULL;
  cuddRef(ts);
  es = get_zdd_support_aux(dd, cuddE(f));
  if (es == NULL) {
    Cudd_RecursiveDerefZdd(dd, ts);
    return NULL;
  }
  cuddRef(es);
  w = zdd_myproduct_aux(dd, ts, es);
  if (w == NULL) {
    Cudd_RecursiveDerefZdd(dd, ts);
    Cudd_RecursiveDerefZdd(dd, es);
    return NULL;
  }
  cuddRef(w);
  Cudd_RecursiveDerefZdd(dd, ts);
  Cudd_RecursiveDerefZdd(dd, es);
  if (cuddT(f) != DD_ZERO(dd)) {
    res = Cudd_zddChange(dd, w, ftop);
    if (res == NULL)
      return NULL;
    cuddRef(res);
    Cudd_RecursiveDerefZdd(dd, w);
  } else {
    res = w;
  }
  cuddCacheInsert1(dd, get_zdd_support_aux, f, res);
  cuddDeref(res);
  return res;
}

DdNode *get_zdd_support(DdManager *dd, DdNode *f)
{
  DdNode *res;
  
  do {
    dd->reordered = 0;
    res = Cudd_Support(dd, f);
  } while (dd->reordered == 1);
  return(res);
}

DdNode *get_zdd_support_2(DdManager *dd, DdNode *f)
{
  DdNode *res;
  
  do {
    dd->reordered = 0;
    res = get_zdd_support_aux(dd, f);
  } while (dd->reordered == 1);
  return(res);
}

DdNode *apply_literals_aux_old(DdManager *dd, DdNode *f, DdNode *unit)
{
  DdNode *one = DD_ONE(dd), *zero = DD_ZERO(dd);
  DdNode *t, *e, *res, *rt, *re, *w, *w2, *et, *ee;
  int topf, topu, topuu;
  if (unit == zero)
    return one;
  if (unit == one)
    return f;
  if (Cudd_IsConstant(f))
    return f;
  res = cuddCacheLookup2Zdd(dd, apply_literals_aux_old, f, unit);
  if (res != NULL)
    return(res);

  //    printf("Applying %d on %d\n", unit->index, f->index);
  //    fflush(stdout);
  
  topf = f->index;
  topu = unit->index;
  topuu = topu ^ 0x1;
  if (topf == topu) {
    e = cuddE(f);
    if (e->index == topuu) {
      //printf("$");
      et = cuddT(e);
      ee = cuddE(e);
      w = zdd_myunion(dd, et, ee);
      if (w == NULL)
	return NULL;
      cuddRef(w);
      res = apply_literals_aux_old(dd, w, cuddT(unit));
      if (res == NULL) {
	Cudd_RecursiveDerefZdd(dd, w);
	return NULL;
      }
      cuddRef(res);
      Cudd_RecursiveDerefZdd(dd, w);
      cuddDeref(res);
    } else {
      //      printf("@");
      res = apply_literals_aux_old(dd, e, cuddT(unit));
      if (res == NULL)
	return NULL;
    }
  } else if (topf == topuu) {
    //printf("!");
    t = cuddT(f);
    e = cuddE(f);
    if (e->index == topu) {
      //      printf("*");
      e = cuddE(e);
    }
    w = zdd_myunion(dd, t, e);
    if (w == NULL)
      return NULL;
    cuddRef(w);
    res = apply_literals_aux_old(dd, w, cuddT(unit));
    if (res == NULL) {
      Cudd_RecursiveDerefZdd(dd, w);
      return NULL;
    }
    cuddRef(res);
    Cudd_RecursiveDerefZdd(dd, w);
    cuddDeref(res);
  } else {
    if (topf/2 > topu/2) {
      //      printf("^");
      res = apply_literals_aux_old(dd, f, cuddT(unit));
    } else {
      //      printf("&");
      t = apply_literals_aux_old(dd, cuddT(f), unit);
      if (t == NULL)
	return NULL;
      cuddRef(t);
      e = apply_literals_aux_old(dd, cuddE(f), unit);
      if (e == NULL) {
	Cudd_RecursiveDerefZdd(dd, t);
	return NULL;
      }
      cuddRef(e);
      res = cuddZddGetNode(dd, topf, t, e);
      if (res == NULL) {
	Cudd_RecursiveDerefZdd(dd, t);
	Cudd_RecursiveDerefZdd(dd, e);
	return NULL;
      }
      cuddDeref(t);
      cuddDeref(e);
    }
  }
  cuddCacheInsert2(dd, apply_literals_aux_old, f, unit, res);

  return res;
}

DdNode *apply_literals_aux(DdManager *dd, DdNode *f, DdNode *unit)
{
  DdNode *one = DD_ONE(dd), *zero = DD_ZERO(dd);
  DdNode *t, *e, *res, *rt, *re, *w, *w2, *et, *ee;
  int topf, topu, topuu;

  if (unit == zero)
    return one;
  if (unit == one)
    return f;
  if (Cudd_IsConstant(f))
    return f;
  res = cuddCacheLookup2Zdd(dd, apply_literals_aux, f, unit);
  if (res != NULL)
    return(res);

  //  printf("Applying %d on %d\n", unit->index, f->index);
  //  fflush(stdout);
  
  topf = f->index;
  topu = unit->index;
  topuu = topu ^ 0x1;
  if (dd->permZ[topf] == dd->permZ[topu]) {
    e = cuddE(f);
    if ((Cudd_IsNonConstant(e))&&(dd->permZ[e->index] == dd->permZ[topuu])) {
      //      printf("$");
      et = cuddT(e);
      ee = cuddE(e);
      w = zdd_myunion(dd, et, ee);
      if (w == NULL)
	return NULL;
      cuddRef(w);
      res = apply_literals_aux(dd, w, cuddT(unit));
      if (res == NULL) {
	Cudd_RecursiveDerefZdd(dd, w);
	return NULL;
      }
      cuddRef(res);
      Cudd_RecursiveDerefZdd(dd, w);
      cuddDeref(res);
    } else {
      //      printf("@");
      res = apply_literals_aux(dd, e, cuddT(unit));
      if (res == NULL)
	return NULL;
    }
  } else if (dd->permZ[topf] == dd->permZ[topuu]) {
    //    printf("!");
    t = cuddT(f);
    e = cuddE(f);
    if ((Cudd_IsNonConstant(e))&&(dd->permZ[e->index] == dd->permZ[topu])) {
      //      printf("*");
      e = cuddE(e);
    }
    w = zdd_myunion(dd, t, e);
    if (w == NULL)
      return NULL;
    cuddRef(w);
    res = apply_literals_aux(dd, w, cuddT(unit));
    if (res == NULL) {
      Cudd_RecursiveDerefZdd(dd, w);
      return NULL;
    }
    cuddRef(res);
    Cudd_RecursiveDerefZdd(dd, w);
    cuddDeref(res);
  } else {
    if (dd->permZ[topf]/2 > dd->permZ[topu]/2) {
      //      printf("^");
      res = apply_literals_aux(dd, f, cuddT(unit));
    } else {
      //      printf("&");
      t = apply_literals_aux(dd, cuddT(f), unit);
      if (t == NULL)
	return NULL;
      cuddRef(t);
      e = apply_literals_aux(dd, cuddE(f), unit);
      if (e == NULL) {
	Cudd_RecursiveDerefZdd(dd, t);
	return NULL;
      }
      cuddRef(e);
      res = cuddZddGetNode(dd, topf, t, e);
      if (res == NULL) {
	Cudd_RecursiveDerefZdd(dd, t);
	Cudd_RecursiveDerefZdd(dd, e);
	return NULL;
      }
      cuddRef(res);
      cuddDeref(t);
      cuddDeref(e);
      cuddDeref(res);
    }
  }
  cuddCacheInsert2(dd, apply_literals_aux, f, unit, res);
  //  fflush(stdout);

  return res;
}

DdNode *apply_literals(DdManager *dd, DdNode *f, DdNode *unit)
{
  DdNode *res, *w;
  
  do {
    dd->reordered = 0;
    w = filtre_tautologie(dd, unit);
    cuddRef(w);
//    Cudd_RecursiveDerefZdd(dd, w);
    if (w != unit) {
      res = DD_ONE(dd);
    } else {
      res = apply_literals_aux(dd, f, unit);
    }
    Cudd_RecursiveDerefZdd(dd, w);
  } while (dd->reordered == 1);
  return(res);
}

/* Elimine 'On the Fly' les cas triviaux de tautologies */
/* dans le cas de variables adjacentes dans l'ordre */
/* Usage : tmp = filtre(zbdd); REF(tmp); DEREF(zbdd); zbdd = tmp; */
DdNode * filtre_tautologie(DdManager * dd, DdNode *zbdd) {
  DdNode *xn, *tmp;
  DdNode *f1, *f0;
  


 if(Cudd_IsConstant(zbdd)) {
    REF(zbdd);
    Cudd_Deref(zbdd);
    return (zbdd);
  }

  if (! (zbdd->index & 0x1)) {
    xn = cuddT(zbdd);
    
    if(Cudd_IsConstant(xn)) {
      REF(zbdd);
      Cudd_Deref(zbdd);
      return (zbdd);
    }
    if( ((zbdd->index)>>1) == ((xn->index)>>1)) {
      f1 = cuddE(xn);
      REF(f1);
      f0 = cuddE(zbdd);
      REF(f0);
      tmp = cuddZddGetNode(dd,zbdd->index, f1 , f0);      
      if (tmp == NULL) {
	DEREF(f0);
	DEREF(f1);
	return(NULL);
      }
      REF(tmp);
      DEREF(f0);
      DEREF(f1);
      Cudd_Deref(tmp);
      /* peut-etre attention aux anciens resultats en cache ?*/
      return(tmp);
    }
  }
  
  REF(zbdd);
  Cudd_Deref(zbdd);
  return(zbdd);
}

/* Fait une union en empechant les subsomptions */
DdNode *
zdd_myUnion_aux(
  DdManager * zdd,
  DdNode * P,
  DdNode * Q)
{
    int		p_top, q_top;
    DdNode	*empty = DD_ZERO(zdd), *t, *e, *s, *res;
    DdManager	*table = zdd;



    if (P == empty)
	return(Q);
    if (Q == empty)
	return(P);
    if (P == Q)
	return(P);

    /* Check cache */
    res = cuddCacheLookup2Zdd(table, zdd_myUnion_aux, P, Q);
    if (res != NULL)
	return(res);

    if (cuddIsConstant(P))
	p_top = P->index;
    else
	p_top = zdd->permZ[P->index];
    if (cuddIsConstant(Q))
	q_top = Q->index;
    else
	q_top = zdd->permZ[Q->index];
    if (p_top < q_top) {
	e = zdd_myUnion_aux(zdd, cuddE(P), Q);
	if (e == NULL) return (NULL);
	cuddRef(e);
	s = zdd_mydiff_aux(zdd, cuddT(P), e);
	if(s==NULL) {DEREF(e);return(NULL);}
	cuddRef(s);
	res = cuddZddGetNode(zdd, P->index, s, e);
	if (res == NULL) {
	    Cudd_RecursiveDerefZdd(table, e);
	    Cudd_RecursiveDerefZdd(table, s);
	    return(NULL);
	}
	cuddDeref(e);
	cuddDeref(s);
    } else if (p_top > q_top) {
	e = zdd_myUnion_aux(zdd, P, cuddE(Q));
	if (e == NULL) return(NULL);
	cuddRef(e);
	s = zdd_mydiff_aux(zdd, cuddT(Q), e);
	if (s == NULL) {
	  Cudd_RecursiveDerefZdd(table, e);
	  return(NULL);}
	cuddRef(s);
	res = cuddZddGetNode(zdd, Q->index, s, e);
	if (res == NULL) {
	    Cudd_RecursiveDerefZdd(table, e);
	    Cudd_RecursiveDerefZdd(table, s);
	    return(NULL);
	}
	cuddDeref(e);
	cuddDeref(s);
    } else {
	t = zdd_myUnion_aux(zdd, cuddT(P), cuddT(Q));
	if (t == NULL) return(NULL);
	cuddRef(t);
	e = zdd_myUnion_aux(zdd, cuddE(P), cuddE(Q));
	if (e == NULL) {
	    Cudd_RecursiveDerefZdd(table, t);
	    return(NULL);
	}
	cuddRef(e);
	s =  zdd_mydiff_aux(zdd, t, e);
	if (s == NULL) {
	  Cudd_RecursiveDerefZdd(table, t);
	  Cudd_RecursiveDerefZdd(table, e);
	  return(NULL);}
  
	cuddRef(s);
	Cudd_RecursiveDerefZdd(table, t);

	res = cuddZddGetNode(zdd, P->index, s, e);
	if (res == NULL) {
	    Cudd_RecursiveDerefZdd(table, s);
	    Cudd_RecursiveDerefZdd(table, e);
	    return(NULL);
	}
	cuddDeref(s);
	cuddDeref(e);
    }

    cuddCacheInsert2(table, zdd_myUnion_aux, P, Q, res);

    return(res);

} /* end of zdd_myUnion_aux */


DdNode * zdd_myunion(DdManager * dd, DdNode * Zbdd_A, DdNode * Zbdd_B) {
    DdNode	*res;

    do {
	dd->reordered = 0;
	res = zdd_myUnion_aux(dd, Zbdd_A, Zbdd_B);
    } while (dd->reordered == 1);
    return(res);
}


DdNode * product_cas_xpxn_D(DdManager * dd, DdNode * New_A, DdNode * zbdd_B){
DdNode * tmp, *tmp2, *tmp3, *tmp4, *tmp5;
DdNode * f0, *f1, *r, *f0g0, *f1g0, *f0g1;

#ifdef LOCALDBG
 printf(" Cas xp,xn x D "); fflush(stdout);
 printf(" New_A :\n");PRMIN(New_A);
 printf(" zbdd_B :\n");PRMIN(zbdd_B); fflush(stdout);
#endif

#ifdef AUTOCHECK
 if((dd->permZ[New_A->index] >> 1) != (dd->permZ[cuddE(New_A)->index] >> 1 ))
   {fprintf(stderr,"Autocheck product_cas_xpxn_D failed 1\n");
   fprintf(stderr, "levels : %d, %d\n",dd->permZ[New_A->index], (dd->permZ[cuddE(New_A)->index]));
   exit(1);}
 if((dd->permZ[New_A->index] >> 1) == (dd->permZ[zbdd_B->index] >>1)) {
   fprintf(stderr,"Autocheck product_cas_xpxn_D failed 2\n");
   exit(1);}
 if (!premier_cas_xpxn_D) {
   fprintf(stdout,"** First entered xpxn_D **\n");
   premier_cas_xpxn_D = 1;
 }
#endif

 tmp = cuddE(New_A);
 if (tmp == NULL) {
   return(NULL); }
 REF(tmp);

 tmp2 = cuddE(tmp);
 if (tmp2 == NULL) {
   DEREF(tmp);
   return(NULL);}
 REF(tmp2);

 /* tmp : Af0
    tmp2 : Af0g0 */

 /* f0g0 : Af0g0 x D */
 f0g0 = zdd_myproduct_aux(dd, tmp2, zbdd_B);
 if(f0g0 == NULL) {
   DEREF(tmp);
   DEREF(tmp2);
   return(NULL);
 }
 REF(f0g0);
 DEREF(tmp2);
      
 /* tmp2 : Af0g1 */
 tmp2 = cuddT(tmp);
 if (tmp2==NULL) {
   DEREF(tmp);
   return(NULL);}
 REF(tmp2);

 /* tmp3 : Af0g1 x D */
 tmp3 = zdd_myproduct_aux(dd, tmp2, zbdd_B);
 if (tmp3 == NULL) {
   DEREF(tmp);
   DEREF(tmp2);
   DEREF(f0g0);
   return(NULL);
 }
 REF(tmp3);
 DEREF(tmp2);

 /* Elimination des subsomptions */
 /* f0g1 : pure (Af0g1 x D) */
 f0g1 = zdd_mydiff_aux(dd, tmp3, f0g0);
 if (f0g1 == NULL) {
   DEREF(tmp);
   DEREF(tmp3);
   DEREF(f0g0);
   return(NULL);
 }
 REF(f0g1);
 DEREF(tmp3);
 DEREF(tmp);

 f0 = cuddZddGetNode(dd, New_A->index + 1, f0g1, f0g0);
 if (f0 == NULL) {
   DEREF(f0g1);
   DEREF(f0g0);
   return(NULL);
 }
 REF(f0);
 DEREF(f0g1);

 /* tmp : f1 */
 tmp = cuddT(New_A);
 REF(tmp);

 /* tmp2 : f1 x D */
 tmp2 = zdd_myproduct_aux(dd, tmp, zbdd_B);
 if (tmp2 == NULL) {
   DEREF(f0);
   DEREF(tmp);
   DEREF(f0g0);
   return(NULL);
 }
 REF(tmp2);
 DEREF(tmp);
      
 /* f1 : pure (f1 x D) */
 f1 = zdd_mydiff_aux(dd, tmp2, f0g0);
 if (f1 == NULL) {
   DEREF(f0);
   DEREF(tmp2);
   DEREF(f0g0);
   return(NULL);
 }
 REF(f1);
 DEREF(tmp2);
 DEREF(f0g0);
 
 r = cuddZddGetNode(dd, New_A->index, f1, f0);
 if (r == NULL) {
   DEREF(f1);
   DEREF(f0);
   return(NULL);
 }
 REF(r);
 DEREF(f1);
 DEREF(f0);

#ifdef LOCALDBG
 printf("(Fin cas xp,xn x D)"); fflush(stdout);PRMIN(r);fflush(stdout);
#endif

 return(r);

}


DdNode * product_cas_x_D(DdManager * dd, DdNode * New_A, DdNode * zbdd_B){
DdNode * tmp, *tmp2, *tmp3, *tmp4, *tmp5;
DdNode * f0, *f1, *r;

#ifdef LOCALDBG
 printf(" Cas x x D (%d,%d)",dd->permZ[New_A->index],dd->permZ[zbdd_B->index]); fflush(stdout);
#endif
#ifdef AUTOCHECK
 if((New_A->index >> 1) == (zbdd_B->index>>1)) {
   fprintf(stderr,"Autocheck product_cas_x_D failed 1\n");
   exit(1);}
 if ((!Cudd_IsConstant(cuddE(New_A))) && ((dd->permZ[New_A->index]>>1) == (dd->permZ[cuddE(New_A)->index] >> 1)))
   {fprintf(stderr,"Autocheck product_cas_x_D failed 2\n");
   fprintf(stderr, "levels : %d, %d\n",dd->permZ[New_A->index], (dd->permZ[cuddE(New_A)->index]));
   exit(1);}
 if (!premier_cas_x_D) {
   fprintf(stdout,"** First entered x_D **\n");
   premier_cas_x_D = 1;
 }
#endif

 tmp = cuddE(New_A);
 if (tmp == NULL) {
   return(NULL);
 }
 REF(tmp);
 f0 = zdd_myproduct_aux(dd, tmp, zbdd_B);
 if (f0 == NULL) {
   DEREF(tmp);
   return(NULL);
 }
 REF(f0);
 DEREF(tmp);
	
 tmp = cuddT(New_A);
 if (tmp == NULL) {
   DEREF(f0);
   return(NULL);
 }
 REF(tmp);

 tmp2 = zdd_myproduct_aux(dd, tmp, zbdd_B);
 if (tmp2 == NULL) {
   DEREF(tmp);
   DEREF(f0);
   return(NULL);
 }
 REF(tmp2);
 DEREF(tmp);
 f1 = zdd_mydiff_aux(dd, tmp2, f0);
 if (f1 == NULL) {
   DEREF(tmp2);
   DEREF(f0);
   return(NULL);
 }
 REF(f1);
 DEREF(tmp2);
 r = cuddZddGetNode(dd, New_A->index, f1, f0);
 if (r == NULL) {
   DEREF(f1);
   DEREF(f0);
   return(NULL);
 }
 REF(r);
 DEREF(f1);
 DEREF(f0);
 return(r);
}

DdNode * product_cas_xp_xp(DdManager * dd, DdNode * zbdd_A, DdNode * zbdd_B){
DdNode * tmp, *tmp2, *tmp3, *tmp4, *tmp5;
DdNode * f0, *f1, *r;

#ifdef LOCALDBG
 printf(" Cas xp x xp "); fflush(stdout);
#endif
#ifdef AUTOCHECK
 if((zbdd_A->index) != (zbdd_B->index)) {
   fprintf(stderr,"Autocheck product_cas_xp_xp failed 1\n");
   exit(1);}
 if ((!Cudd_IsConstant(cuddE(zbdd_A))) && ((dd->permZ[zbdd_A->index]>>1) == (dd->permZ[cuddE(zbdd_A)->index] >> 1)))
   {fprintf(stderr,"Autocheck product_cas_xp_xp failed 2\n");
   exit(1);}
 if ((!Cudd_IsConstant(cuddE(zbdd_B))) && ((dd->permZ[zbdd_B->index]>>1) == (dd->permZ[cuddE(zbdd_B)->index] >> 1)))
   {fprintf(stderr,"Autocheck product_cas_xp_xp failed 3\n");
   exit(1);}
 if (dd->permZ[zbdd_A->index] != dd->permZ[zbdd_A->index]) 
   {fprintf(stderr,"Autocheck product_cas_xp_xp failed 4\n");
   exit(1);}
/*  if (dd->permZ[zbdd_A->index] */
 if (!premier_cas_xp_xp) {
   fprintf(stdout,"** First entered xp_xp **\n");
   premier_cas_xp_xp = 1;
 }

#endif


 /* Cas xp x xp */
 tmp = cuddE(zbdd_A);
 if (tmp == NULL) {
   return(NULL);}
 REF(tmp);
 tmp2 = cuddE(zbdd_B);
 if (tmp2 == NULL) {
   DEREF(tmp);
   return(NULL);}
 REF(tmp2);
 /* A0 x B0 */
 f0 = zdd_myproduct_aux(dd, tmp, tmp2);
 if (f0 == NULL) {
   DEREF(tmp);
   DEREF(tmp2);
   return(NULL);}
 REF(f0);
	    
 tmp3 = cuddT(zbdd_A);
 if (tmp3 == NULL) {
   DEREF(tmp);
   DEREF(tmp2);
   DEREF(f0);
   return(NULL);}
 REF(tmp3);	 
 /* A1 x B0 */
 tmp4 = zdd_myproduct_aux(dd, tmp3, tmp2);
 if (tmp4 == NULL) {
   DEREF(tmp);
   DEREF(tmp2);
   DEREF(f0);
   DEREF(tmp3);
   return(NULL);}
 REF(tmp4);
 /* tmp : Af0
    tmp2 : Bf0
    f0 : Af0 x Bf0 
    tmp3 : Af1
    tmp4 : Af1 x Bf0 */
#ifdef LOCALDBG
 printf("A1xB0:\n");
 PRMIN(tmp4);
#endif

 DEREF(tmp2);
	    
 tmp5 = cuddT(zbdd_B);
 if (tmp5 == NULL) {
   DEREF(tmp);
   DEREF(tmp2);
   DEREF(f0);
   DEREF(tmp3);
   DEREF(tmp4);
   return(NULL);}
 REF(tmp5);

 /* tmp5 : Bf1
    tmp2 : Af1 x Bf1 */
 tmp2 = zdd_myproduct_aux(dd, tmp3, tmp5);
 if (tmp2 == NULL) {
   DEREF(tmp);
   DEREF(tmp5);
   DEREF(f0);
   DEREF(tmp3);
   DEREF(tmp4);
   return(NULL);}
 REF(tmp2);

#ifdef LOCALDBG
 printf("A1xB1:\n");
 PRMIN(tmp2);
#endif

 DEREF(tmp3);
 /* tmp3 : (Af1 x Bf1) U (Af1 x Bf0) */
 tmp3 = zdd_myUnion_aux(dd, tmp2, tmp4);
 if (tmp3 == NULL) {
   DEREF(tmp);
   DEREF(tmp5);
   DEREF(f0);
   DEREF(tmp2);
   DEREF(tmp4);
   return(NULL);}
 REF(tmp3);
 DEREF(tmp2);
 DEREF(tmp4);
	    
 /* tmp2 : Af0 x Bf1 */
 tmp2 = zdd_myproduct_aux(dd, tmp, tmp5);
 if (tmp2 == NULL) {
   DEREF(tmp);
   DEREF(tmp3);
   DEREF(tmp5);
   DEREF(f0);
   return(NULL);}
 REF(tmp2);
 DEREF(tmp);
 DEREF(tmp5);

#ifdef LOCALDBG
 printf("A0xB1:\n");
 PRMIN(tmp2);
#endif

 /* tmp4 : (Af0 x Bf1) U (Af1 x Bf1) U (Af1 x Bf0) */
 tmp4 = zdd_myUnion_aux(dd, tmp2, tmp3);
 if (tmp4 == NULL) {
   DEREF(tmp2);
   DEREF(tmp3);
   DEREF(f0);
   return(NULL);}
 REF(tmp4);
 DEREF(tmp2);
 DEREF(tmp3);

#ifdef LOCALDBG
 printf("U(A1xB0, B1x A0, A1xB1) :\n");
 PRMIN(tmp4);
#endif

	    /* Elimination des subsomptions */
 f1 = zdd_mydiff_aux(dd, tmp4, f0);
 if (f1 == NULL) {
   DEREF(f0);
   DEREF(tmp4);
   return(NULL);}
 REF(f1);
 DEREF(tmp4);

#ifdef LOCALDBG
 printf("U(A1xB0, B1x A0, A1xB1) - (A0xB0):\n");
 PRMIN(f1);
#endif
	    
 r = cuddZddGetNode(dd, zbdd_A->index, f1, f0);
 if (r ==NULL) {
   DEREF(f0);
   DEREF(f1);
   return(NULL);}
 REF(r);
	    
 DEREF(f1);
 DEREF(f0);
 return(r);
}



DdNode * product_cas_xp_xn(DdManager * dd, DdNode * zbdd_A, DdNode * zbdd_B){
DdNode * tmp, *tmp2, *tmp3, *tmp4, *tmp5;
DdNode * f0g0, *f0g1, *f1, *f0, *r;

#ifdef LOCALDBG
 printf(" Cas xp x xn "); fflush(stdout);
#endif
#ifdef AUTOCHECK
 if((zbdd_A->index) == (zbdd_B->index)) {
   fprintf(stderr,"Autocheck product_cas_xp_xn failed 1\n");
   exit(1);}
 if ((!Cudd_IsConstant(cuddE(zbdd_A))) && ((dd->permZ[zbdd_A->index]>>1) == (dd->permZ[cuddE(zbdd_A)->index] >> 1)))
   {fprintf(stderr,"Autocheck product_cas_xp_xn failed 2\n");
   exit(1);}
 if ((dd->permZ[zbdd_A->index]  != (dd->permZ[zbdd_B->index] - 1)))
   {fprintf(stderr,"Autocheck product_cas_xp_xn failed 3\n");
   exit(1);}
/*  if (dd->permZ[zbdd_A->index] */
 if (!premier_cas_xp_xn) {
   fprintf(stdout,"** First entered xp_xn **\n");
   premier_cas_xp_xn = 1;
 }
#endif

 tmp = cuddE(zbdd_A);
 if (tmp==NULL) return(NULL);
 REF(tmp);
 
 tmp2 = cuddE(zbdd_B);
 if (tmp2 == NULL) {
   DEREF(tmp);
   return(NULL);
 }
 REF(tmp2);

 /* f0g0 : Af0 x Bg0 */
 f0g0 = zdd_myproduct_aux(dd, tmp, tmp2);
 if (f0g0 == NULL) {
   DEREF(tmp);
   DEREF(tmp2);
   return(NULL);
 }
 REF(f0g0);
#ifdef LOCALDBG 
 printf("f0g0 :\n");PRMIN(f0g0);
#endif

 tmp3 = cuddT(zbdd_B);
 if(tmp3==NULL) {
   DEREF(tmp);
   DEREF(tmp2);
   DEREF(f0g0);
   return(NULL);
 }
 REF(tmp3);

 /* tmp : Af0
    tmp2 : Bg0
    tmp3 : Bg1 */
  
 /* tmp4 : Af0 x Bg1 */
 tmp4 = zdd_myproduct_aux(dd, tmp, tmp3);
 if (tmp4==NULL) {
   DEREF(tmp);
   DEREF(tmp2);
   DEREF(tmp3);
   DEREF(f0g0);
   return(NULL);
 }
 REF(tmp4);

 /* f0g1 : pure (Af0 x Bg1) */
 f0g1 = zdd_mydiff_aux(dd, tmp4, f0g0);
 if (f0g1==NULL) {
   DEREF(tmp);
   DEREF(tmp2);
   DEREF(tmp3);
   DEREF(f0g0);
   DEREF(tmp4);
   return(NULL);
 }
 REF(f0g1);
#ifdef LOCALDBG 
 printf("f0g1 :\n");PRMIN(f0g1);
#endif
 
 DEREF(tmp4);
 DEREF(tmp3);
 DEREF(tmp);

 f0 = cuddZddGetNode(dd, zbdd_B->index, f0g1, f0g0);
 if (f0 == NULL) {
   DEREF(tmp2);
   DEREF(f0g0);
   DEREF(f0g1);
   return(NULL);
 }
 REF(f0);
#ifdef LOCALDBG 
 printf("f0 :\n");PRMIN(f0);
#endif

 DEREF(f0g1);

 tmp3 = cuddT(zbdd_A);
 if(tmp3==NULL) {
   DEREF(tmp2);
   DEREF(f0g0);
   DEREF(f0);
   return(NULL);
 }
 REF(tmp3);
 /* tmp3 : Af1
    tmp4 : Af1 x Bg0 */
 tmp4 = zdd_myproduct_aux(dd, tmp3, tmp2);
 if (tmp4==NULL) {
   DEREF(tmp2);
   DEREF(tmp3);
   DEREF(f0g0);
   DEREF(f0);
   return(NULL);
 }
 REF(tmp4);

 /* f1 : pure (Af1 x Bg0) */
 f1 = zdd_mydiff_aux(dd, tmp4, f0g0);
 if (f1==NULL) {
   DEREF(tmp2);
   DEREF(tmp3);
   DEREF(f0g0);
   DEREF(f0);
   DEREF(tmp4);
   return(NULL);
 }
 REF(f1);

#ifdef LOCALDBG 
 printf("f1 :\n");PRMIN(f1);
#endif

 DEREF(tmp4);
 DEREF(tmp2);
 DEREF(tmp3);
 DEREF(f0g0);

 r = cuddZddGetNode(dd, zbdd_A->index, f1, f0);
 if (r ==NULL) {
   DEREF(f0);
   DEREF(f1);
   return(NULL);}
 REF(r);
	    
 DEREF(f1);
 DEREF(f0);
#ifdef LOCALDBG 
 printf("r :\n");PRMIN(r);
#endif

 return(r);
 
}

DdNode * product_cas_xn_xn(DdManager * dd, DdNode * zbdd_A, DdNode * zbdd_B){
#ifdef LOCALDBG
  printf("Cas xn x xn (appel a xp x xp->) ");fflush(stdout);
#endif
#ifdef AUTOCHECK
 if (!premier_cas_xn_xn) {
   fprintf(stdout,"** First entered xn_xn **\n");
   premier_cas_xn_xn = 1;
 }
#endif
  return(product_cas_xp_xp(dd,zbdd_A,zbdd_B));
}

DdNode * product_cas_xpxn_xpxn(DdManager * dd, DdNode * zbdd_A, DdNode * zbdd_B){
DdNode * tmp, *tmp2, *tmp3, *tmp4, *tmp5, *tmp6, *tmp7;
DdNode * f0g0, *f0g1, *f1, *f0, *r;

#ifdef LOCALDBG
 printf("Cas xpxn x xpxn ");fflush(stdout);
#endif 
#ifdef AUTOCHECK
 if((zbdd_A->index) != (zbdd_B->index)) {
   fprintf(stderr,"Autocheck product_cas_xpxn_xpxn failed 1\n");
   exit(1);}
 if ((dd->permZ[cuddE(zbdd_A)->index]) != (dd->permZ[cuddE(zbdd_B)->index]))
   {fprintf(stderr,"Autocheck product_cas_xpxn_xpxn failed 2\n");
   exit(1);}
 if((dd->permZ[zbdd_A->index] >> 1) != (dd->permZ[cuddE(zbdd_A)->index] >>1 ))
   {fprintf(stderr,"Autocheck product_cas_xpxn_xpxn failed 3\n");
   exit(1);}
 if((dd->permZ[zbdd_B->index] >> 1) != (dd->permZ[cuddE(zbdd_B)->index] >>1 ))
   {fprintf(stderr,"Autocheck product_cas_xpxn_xpxn failed 4\n");
   exit(1);}
 if (!premier_cas_xpxn_xpxn) {
   fprintf(stdout,"** First entered xpxn_xpxn **\n");
   premier_cas_xpxn_xpxn = 1;
 }

#endif

 tmp = cuddE(zbdd_A);
 if (tmp==NULL) return(NULL);
 REF(tmp);

 tmp2 = cuddE(zbdd_B);
 if(tmp2==NULL) {
   DEREF(tmp);
   return(NULL);}
 REF(tmp2);

 tmp3 = cuddE(tmp);
 if (tmp3 == NULL) {
   DEREF(tmp);
   DEREF(tmp2);
   return(NULL);}
 REF(tmp3);

 tmp4 = cuddE(tmp2);
 if(tmp4 == NULL) {
   DEREF(tmp3);
   DEREF(tmp2);
   DEREF(tmp);
   return(NULL);}
 REF(tmp4);

 /* f0g0 : Af0g0 x Bf0g0 */
 f0g0 = zdd_myproduct_aux(dd, tmp3, tmp4);

 if (f0g0 == NULL) {
   DEREF(tmp4);
   DEREF(tmp3);
   DEREF(tmp2);
   DEREF(tmp);
   return(NULL);}
 REF(f0g0);

 /* tmp   : Af0
    tmp2  : Bf0
    tmp3  : Af0g0
    tmp4  : Bf0g0 */

 tmp5 = cuddT(tmp);
 if (tmp5 == NULL) {
   DEREF(f0g0);
   DEREF(tmp4);
   DEREF(tmp3);
   DEREF(tmp2);
   DEREF(tmp);
   return(NULL);}
 REF(tmp5);
 DEREF(tmp);

 tmp6 = cuddT(tmp2);
 if(tmp6==NULL) {
   DEREF(tmp5);
   DEREF(f0g0);
   DEREF(tmp4);
   DEREF(tmp3);
   DEREF(tmp2);
   return(NULL);}
 REF(tmp6);
 DEREF(tmp2);
 /* tmp5 : Af0g1
    tmp6 : Bf0g1 */


 /* VOIR SI POSSIBLE FAIRE UNION tmp6, tmp7 puis produit avec tmp5 */
 /* r : Af0g1 x Bf0g1 */
 r = zdd_myproduct_aux(dd, tmp5,tmp6);
 if (r==NULL) {
   DEREF(tmp6);
   DEREF(tmp5);
   DEREF(f0g0);
   DEREF(tmp4);
   DEREF(tmp3);
   return(NULL);
 }
 REF(r);
 
 /* tmp7 : Af0g1 x Bf0g0 */
 tmp7 = zdd_myproduct_aux(dd,tmp5,tmp4);
 if(tmp7==NULL) {
   DEREF(r);
   DEREF(tmp6);
   DEREF(tmp5);
   DEREF(f0g0);
   DEREF(tmp4);
   DEREF(tmp3);
   return(NULL);
 }
 REF(tmp7);
 
 DEREF(tmp5);

 /* tmp5 : (Af0g1 x Bf0g1) U (Af0g1 x Bf0g0) */
 tmp5 = zdd_myUnion_aux(dd,tmp7,r);
 if (tmp5==NULL) {
   DEREF(r);
   DEREF(tmp6);
   DEREF(tmp7);
   DEREF(f0g0);
   DEREF(tmp4);
   DEREF(tmp3);
   return(NULL);
 }
 REF(tmp5);
 DEREF(r);
 DEREF(tmp7);

 /* tmp5 : Af0g1 x Bf0g0 U Af0g1 x Bf0g1 */

 /* tmp7 : Af0g0 x Bf0g1 */
 tmp7 = zdd_myproduct_aux(dd, tmp3, tmp6);
 if(tmp7==NULL) {
   DEREF(tmp6);
   DEREF(tmp5);
   DEREF(f0g0);
   DEREF(tmp4);
   DEREF(tmp3);
   return(NULL);
 }
 REF(tmp7);
 DEREF(tmp6);

 /* r =  (Af0g1 x Bf0g0) U (Af0g1 x Bf0g1) U  (Af0g0 x Bf0g1) */
 r = zdd_myUnion_aux(dd, tmp5, tmp7);
 if(r==NULL) {
   DEREF(tmp7);
   DEREF(tmp5);
   DEREF(f0g0);
   DEREF(tmp4);
   DEREF(tmp3);
   return(NULL);
 }
 REF(r);
 DEREF(tmp7);
 DEREF(tmp5);

 /* f0g1 : pure ((Af0g1 x Bf0g0) U (Af0g1 x Bf0g1) U  (Af0g0 x Bf0g1)) */
 f0g1 = zdd_mydiff_aux(dd, r, f0g0);
 if(f0g1 == NULL) {
   DEREF(r);
   DEREF(f0g0);
   DEREF(tmp4);
   DEREF(tmp3);
   return(NULL);
 }
 REF(f0g1);
 DEREF(r);

 f0 =  cuddZddGetNode(dd, zbdd_A->index+1, f0g1, f0g0);
 if(f0==NULL) {
   DEREF(f0g0);
   DEREF(tmp4);
   DEREF(tmp3);
   DEREF(f0g1);
   return(NULL);
 }
 REF(f0);
 DEREF(f0g1);
/*  printf("f0:\n");PRMIN(f0); fflush(stdout); */

 /* tmp   : Af0
    tmp2  : Bf0
    tmp3  : Af0g0
    tmp4  : Bf0g0 */

 /* tmp5 : Af1 */
 tmp5 = cuddT(zbdd_A);
 if(tmp5==NULL) {
   DEREF(f0);
   DEREF(tmp4);
   DEREF(tmp3);
   DEREF(f0g0);
   return(NULL);
 }
 REF(tmp5);

 /* tmp 6 : Bf1 */
 tmp6 = cuddT(zbdd_B);
 if(tmp6==NULL) {
   DEREF(tmp5);
   DEREF(f0);
   DEREF(tmp4);
   DEREF(tmp3);
   DEREF(f0g0);
   return(NULL);
 }
 REF(tmp6);
 
 /* tmp5 : Af1 
    tmp6 : Bf1 */

 /* r : Af1 x Bf1 */
 r = zdd_myproduct_aux(dd, tmp5,tmp6);
 if (r==NULL) {
   DEREF(f0);
   DEREF(tmp6);
   DEREF(tmp5);
   DEREF(f0g0);
   DEREF(tmp4);
   DEREF(tmp3);
   return(NULL);
 }
 REF(r);
 
 /* tmp7 : Af1 x Bf0g0 */
 tmp7 = zdd_myproduct_aux(dd,tmp5,tmp4);
 if(tmp7==NULL) {
   DEREF(f0);
   DEREF(r);
   DEREF(tmp6);
   DEREF(tmp5);
   DEREF(f0g0);
   DEREF(tmp4);
   DEREF(tmp3);
   return(NULL);
 }
 REF(tmp7);
 
 DEREF(tmp4);
 DEREF(tmp5);
 /* tmp5 : (Af1 x Bf1) U (Af1 x Bf0g0) */
 tmp5 = zdd_myUnion_aux(dd,tmp7,r);
 if (tmp5==NULL) {
   DEREF(f0);
   DEREF(r);
   DEREF(tmp6);
   DEREF(tmp7);
   DEREF(f0g0);
   DEREF(tmp3);
   return(NULL);
 }
 REF(tmp5);
 DEREF(r);
 DEREF(tmp7);


 /* tmp7 : Af0g0 x Bf1 */
 tmp7 = zdd_myproduct_aux(dd, tmp3, tmp6);
 if(tmp7==NULL) {
   DEREF(f0);
   DEREF(tmp6);
   DEREF(tmp5);
   DEREF(f0g0);
   DEREF(tmp3);
   return(NULL);
 }
 REF(tmp7);
 DEREF(tmp6);
 DEREF(tmp3);

 /* r : (Af0g0 x Bf1) U  (Af1 x Bf1) U (Af1 x Bf0g0) */
 r = zdd_myUnion_aux(dd, tmp5, tmp7);
 if(r==NULL) {
   DEREF(f0);
   DEREF(tmp7);
   DEREF(tmp5);
   DEREF(f0g0);
   return(NULL);
 }
 REF(r);
 DEREF(tmp7);
 DEREF(tmp5);

 /* f1 = pure ((Af0g0 x Bf1) U  (Af1 x Bf1) U (Af1 x Bf0g0) ) */
 f1 = zdd_mydiff_aux(dd, r, f0g0);
 if(f1 == NULL) {
   DEREF(f0);
   DEREF(r);
   DEREF(f0g0);
   return(NULL);
 }
 REF(f1);
 DEREF(r);
 DEREF(f0g0);

 r =  cuddZddGetNode(dd, zbdd_A->index, f1, f0);
 if( r==NULL) {
   DEREF(f0);
   DEREF(f1);
   return(NULL);
 }
 REF(r);
 DEREF(f0);
 DEREF(f1);

/*  printf("r:\n");PRMIN(r); fflush(stdout); */

 return(r);
}


DdNode * product_cas_xpxn_xn(DdManager * dd, DdNode * zbdd_A, DdNode * zbdd_B){
DdNode * tmp, *tmp2, *tmp3, *tmp4, *tmp5, *tmp6, *tmp7;
DdNode * f0g0, *f0g1, *f1, *f0, *r;

#ifdef LOCALDBG
printf("Cas xpxn x xn ");fflush(stdout);
#endif
#ifdef AUTOCHECK
 if((cuddE(zbdd_A)->index) != (zbdd_B->index)) 
   {fprintf(stderr,"Autocheck product_cas_xpxn_xn failed 1\n");
   exit(1);}
 if((dd->permZ[zbdd_A->index] >> 1) != (dd->permZ[cuddE(zbdd_A)->index] >>1 ))
   {fprintf(stderr,"Autocheck product_cas_xpxn_xn failed 2\n");
   exit(1);}
 if (!premier_cas_xpxn_xn) {
   fprintf(stdout,"** First entered xpxn_xn **\n");
   premier_cas_xpxn_xn = 1;
 }
#endif

 tmp =  cuddE(zbdd_A);
 if (tmp==NULL) return(NULL);
 REF(tmp);
 tmp2 = cuddE(zbdd_B);
 if(tmp2==NULL) {
   DEREF(tmp);
   return(NULL);
 }
 REF(tmp2);

 tmp3 = cuddE(tmp);
 if(tmp3==NULL){
   DEREF(tmp2);
   DEREF(tmp);
   return(NULL);
 }
 REF(tmp3);
 /* tmp  : Af0
    tmp2 : Bg0
    tmp3 : Af0g0 */

 f0g0 = zdd_myproduct_aux(dd,tmp3,tmp2);
 if (f0g0 == NULL) {
   DEREF(tmp2);
   DEREF(tmp3);
   DEREF(tmp);
   return(NULL);
 }
 REF(f0g0);
   
 /* tmp4 : Bg1 */
 tmp4 = cuddT(zbdd_B);
 if(tmp4==NULL) {
   DEREF(tmp2);
   DEREF(tmp3);
   DEREF(tmp);
   DEREF(f0g0);
   return(NULL);
 }
 REF(tmp4);

 /* tmp5 : Bg1 x Af0g0 */
 tmp5 = zdd_myproduct_aux(dd,tmp4,tmp3);
 if (tmp5==NULL) {
   DEREF(tmp4);
   DEREF(tmp2);
   DEREF(tmp3);
   DEREF(tmp);
   DEREF(f0g0);
   return(NULL);
 }
 REF(tmp5);                     /* Bg1 x Af0g0 */
 DEREF(tmp3);

 /* tmp7 : Af0g1 */
 tmp7 = cuddT(tmp);   /* Af0g1 */
 if (tmp7==NULL) {
   DEREF(tmp5);
   DEREF(tmp2);
   DEREF(tmp);
   DEREF(tmp4);
   DEREF(f0g0);
   return(NULL);
 }
 REF(tmp7);
 DEREF(tmp);
 
 /* tmp6 : Bg1 x Af0g1 */
 tmp6 = zdd_myproduct_aux(dd, tmp4, tmp7);   
 if(tmp6==NULL) {
   DEREF(tmp5);
   DEREF(tmp4);
   DEREF(tmp7);
   DEREF(tmp2);
   DEREF(f0g0);
   return(NULL);
 }
 REF(tmp6);                   /*Bg1 x Af0g1 */
 DEREF(tmp4);

 /* r : (Bg1 x Af0g1) U (Bg1 x Af0g0) */
 r = zdd_myUnion_aux(dd, tmp6, tmp5);
 if (r==NULL) {
   DEREF(tmp5);
   DEREF(tmp6);
   DEREF(tmp7);
   DEREF(tmp2);
   DEREF(f0g0);
   return(NULL);
 }
 REF(r);                    /* Bg1 x Af0g1 U Bg1 x Af0g0 */
 DEREF(tmp6);
 DEREF(tmp5);

 /* tmp5 : Bg0 x Af0g1 */
 tmp5 = zdd_myproduct_aux(dd, tmp2, tmp7);
 if (tmp5==NULL) {
   DEREF(tmp7);
   DEREF(tmp2);
   DEREF(f0g0);
   DEREF(r);
   return(NULL);
 }
 REF(tmp5);
 DEREF(tmp7);

 /* tmp6 : (Bg1 x Af0g1) U (Bg1 x Af0g0) U (Bg0 x Af0g1) */
 tmp6 = zdd_myUnion_aux(dd, r, tmp5);
 if (tmp6==NULL) {
   DEREF(tmp5);
   DEREF(tmp2);
   DEREF(f0g0);
   DEREF(r);
   return(NULL);
 }
 REF(tmp6);
 DEREF(tmp5);
 DEREF(r);
 

 /* f0g1 : pure ((Bg1 x Af0g1) U (Bg1 x Af0g0) U (Bg0 x Af0g1)) */
 f0g1 = zdd_mydiff_aux(dd, tmp6, f0g0);
 if (f0g1==NULL) {
   DEREF(tmp2);
   DEREF(f0g0);
   DEREF(tmp6);
   return(NULL);
 }
 REF(f0g1);
 DEREF(tmp6);

 f0 =  cuddZddGetNode(dd, zbdd_A->index+1, f0g1, f0g0);
 if(f0==NULL) {
   DEREF(tmp2);
   DEREF(f0g0);
   DEREF(f0g1);
   return(NULL);
 }
 REF(f0);
 DEREF(f0g1);
 
 /* tmp6 : Af1 */
 tmp6 = cuddT(zbdd_A);
 if(tmp6==NULL) {
   DEREF(tmp2);
   DEREF(f0g0);
   DEREF(f0);
   return(NULL);
 }
 REF(tmp6);
 
 /* r : Af1 x Bg0 */
 r = zdd_myproduct_aux(dd, tmp6, tmp2);
 if(r==NULL) {
   DEREF(tmp2);
   DEREF(f0g0);
   DEREF(f0);
   DEREF(tmp6);
   return(NULL);
 }
 REF(r);
 DEREF(tmp2);
 DEREF(tmp6);
 
 /* f1 : pure (Af1 x Bg0) */
 f1 = zdd_mydiff_aux(dd, r, f0g0);
 if (f1==NULL) {
   DEREF(r);
   DEREF(f0g0);
   DEREF(f0);
   return(NULL);
 }
 REF(f1);
 DEREF(f0g0);
 DEREF(r);

 r =  cuddZddGetNode(dd, zbdd_A->index, f1, f0);
 if (r==NULL) {
   DEREF(f1);
   DEREF(f0);
   return(NULL);
 }
 REF(r);
 DEREF(f1);
 DEREF(f0);

 return(r); 
}

DdNode * product_cas_xpxn_xp(DdManager * dd, DdNode * zbdd_A, DdNode * zbdd_B){
DdNode * tmp, *tmp2, *tmp3, *tmp4, *tmp5, *tmp6, *tmp7;
DdNode * f0g0, *f0g1, *f1, *f0, *r;
#ifdef LOCALDBG
 printf("Cas xpxn x xp ");fflush(stdout);
#endif 
#ifdef AUTOCHECK
 if((zbdd_A->index) != (zbdd_B->index))
   {fprintf(stderr,"Autocheck product_cas_xpxn_xp failed 1\n");
   exit(1);}
 if((dd->permZ[zbdd_A->index] >> 1) != (dd->permZ[cuddE(zbdd_A)->index] >>1 ))
   {fprintf(stderr,"Autocheck product_cas_xpxn_xp failed 2\n");
   exit(1);}
 if((dd->permZ[zbdd_B->index] >> 1) == (dd->permZ[cuddE(zbdd_B)->index] >>1))
   {fprintf(stderr,"Autocheck product_cas_xpxn_xp failed 3\n");
   exit(1);}
 if (!premier_cas_xpxn_xp) {
   fprintf(stdout,"** First entered xpxn_xp **\n");
   premier_cas_xpxn_xp = 1;
 }

#endif


 tmp =  cuddE(zbdd_A);
 if (tmp==NULL) return(NULL);
 REF(tmp);
 tmp2 = cuddE(zbdd_B);
 if(tmp2==NULL) {
   DEREF(tmp);
   return(NULL);
 }
 REF(tmp2);

 tmp3 = cuddE(tmp);
 if(tmp3==NULL){
   DEREF(tmp2);
   DEREF(tmp);
   return(NULL);
 }
 REF(tmp3);
 /* tmp  : Af0
    tmp2 : Bf0
    tmp3 : Af0g0 */

 f0g0 = zdd_myproduct_aux(dd,tmp3,tmp2);
 if (f0g0 == NULL) {
   DEREF(tmp2);
   DEREF(tmp3);
   DEREF(tmp);
   return(NULL);
 }
 REF(f0g0);
   
 /* tmp4 : Bf1 */
 tmp4 = cuddT(zbdd_B);
 if(tmp4==NULL) {
   DEREF(tmp2);
   DEREF(tmp3);
   DEREF(tmp);
   DEREF(f0g0);
   return(NULL);
 }
 REF(tmp4);   /* Bf1 */

 /* tmp5 : Bf1 x Af0g0 */
 tmp5 = zdd_myproduct_aux(dd,tmp4,tmp3);
 if (tmp5==NULL) {
   DEREF(tmp4);
   DEREF(tmp2);
   DEREF(tmp3);
   DEREF(tmp);
   DEREF(f0g0);
   return(NULL);
 }
 REF(tmp5);                     /* Bf1 x Af0g0 */
 DEREF(tmp3);

 /* tmp7 : Af1 */
 tmp7 = cuddT(zbdd_A);   /* Af1 */
 if (tmp7==NULL) {
   DEREF(tmp5);
   DEREF(tmp2);
   DEREF(tmp);
   DEREF(tmp4);
   DEREF(f0g0);
   return(NULL);
 }
 REF(tmp7);
 
 /* tmp6 : Bf1 x Af1 */
 tmp6 = zdd_myproduct_aux(dd, tmp4, tmp7);   
 if(tmp6==NULL) {
   DEREF(tmp5);
   DEREF(tmp4);
   DEREF(tmp7);
   DEREF(tmp2);
   DEREF(f0g0);
   return(NULL);
 }
 REF(tmp6);                   /*Bf1 x Af1 */
 DEREF(tmp4);

 /* r: (Bf1 x Af1) U (Bf1 x Af0g0) */ 
 r = zdd_myUnion_aux(dd, tmp6, tmp5); 
 if (r==NULL) {
   DEREF(tmp5);
   DEREF(tmp6);
   DEREF(tmp2);
   DEREF(tmp7);
   DEREF(f0g0);
   return(NULL);
 }
 REF(r);                    /* Bf1 x Af1 U Bf1 x Af0g0 */
 DEREF(tmp6);
 DEREF(tmp5);


 /* AJOUT DU 30-11-98 */
 /* tmp5 : Af1 x Bf0 */
 tmp5 = zdd_myproduct_aux(dd,tmp7,tmp2);
 if (tmp5==NULL) {
   DEREF(tmp2);
   DEREF(tmp7);
   DEREF(f0g0);
   DEREF(r);
  return(NULL);
 }
 REF(tmp5);
 DEREF(tmp7);
 /* (Bf1 x Af1) U (Bf1 x Af0g0) U (Af1 x Bf0) */
 tmp6 = zdd_myUnion_aux(dd, r, tmp5);
 if (tmp6==NULL) {
   DEREF(tmp2);
   DEREF(tmp5);
   DEREF(f0g0);
   DEREF(r);
   return(NULL);
 }
 REF(tmp6);
 DEREF(tmp5);
 DEREF(r);

 /* f1 = pure ((Bf1 x Af1) U (Bf1 x Af0g0) U (Af1 x Bf0)) */
 f1 = zdd_mydiff_aux(dd, tmp6, f0g0);
 if (f1==NULL) {
   DEREF(tmp2);
   DEREF(f0g0);
   DEREF(tmp6);
   return(NULL);
 }
 REF(f1);
 DEREF(tmp6);

 /* tmp6 : Af0g1 */
 tmp6 = cuddT(tmp);    /* Af0g1 */
 if(tmp6==NULL) {
   DEREF(tmp2);
   DEREF(f0g0);
   DEREF(f1);
   return(NULL);
 }
 REF(tmp6);
 DEREF(tmp);

 /* r : Af0g1 x Bf0 */
 r = zdd_myproduct_aux(dd, tmp6, tmp2);
 if(r==NULL) {
   DEREF(tmp2);
   DEREF(f0g0);
   DEREF(f1);
   DEREF(tmp6);
   return(NULL);
 }
 REF(r);                 /* Af0g1 x Bf0 */
 DEREF(tmp2);
 DEREF(tmp6);
 
 /* f0g1 : pure (Af0g1 x Bf0) */
 f0g1 = zdd_mydiff_aux(dd, r, f0g0);
 if (f0g1==NULL) {
   DEREF(r);
   DEREF(f0g0);
   DEREF(f1);
   return(NULL);
 }
 REF(f0g1);
 DEREF(r);

 f0 =  cuddZddGetNode(dd, zbdd_A->index+1, f0g1, f0g0);
 if(f0==NULL) {
   DEREF(f0g0);
   DEREF(f0g1);
   DEREF(f1);
   return(NULL);
 }
 REF(f0);
 DEREF(f0g1);
 DEREF(f0g0);

 r =  cuddZddGetNode(dd, zbdd_A->index, f1, f0);
 if (r==NULL) {
   DEREF(f1);
   DEREF(f0);
   return(NULL);
 }
 REF(r);
 DEREF(f1);
 DEREF(f0);

 return(r); 
}


/* Dans cette fonction : les variables doivent etre adjacentes */
DdNode * zdd_myproduct_aux(DdManager * dd, DdNode * zbdd_A, DdNode * zbdd_B) {

  DdNode *r, *tmp, *tmp1, *tmp2, *tmp3, *tmp4, *tmp5;
  DdNode *New_A, *New_B;
  DdNode *f1, *f0, *f0g0, *f0g1;
  int level_A, level_B;

#ifdef LOCALDBG
  printf("Fonctions debug avant product_aux :\n");
  Cudd_CheckKeys(manager);
  Cudd_DebugCheck(dd);
#endif

  if ((zbdd_A == DD_ZERO(dd)) || (zbdd_B == DD_ZERO(dd))) {
    return(DD_ZERO(dd));
  }
  if (cuddIsConstant(zbdd_A)) {
    return (zbdd_B);
  }
  if (cuddIsConstant(zbdd_B)) {
    return (zbdd_A);
  }


  level_A =  dd->permZ[zbdd_A->index];
  level_B =  dd->permZ[zbdd_B->index];

#ifdef LOCALDBG 
  printf("(lA:%d) (lB:%d) ",level_A, level_B); fflush(stdout);
#endif
  if (level_A > level_B)
    return(zdd_myproduct_aux(dd, zbdd_B, zbdd_A));

 

  r = cuddCacheLookup2Zdd(dd, zdd_myproduct_aux, zbdd_A, zbdd_B);
  if (r) return(r);


  if ((level_A>>1) == (level_B>>1)) /* Cas ou on a les deux meme vars */
    {
      if (level_A == level_B) {
	if (level_A & 0x1) {
	  /* Cas xn x xn */
	  r = product_cas_xn_xn(dd,zbdd_A,zbdd_B);
	  if(r==NULL) return(NULL);
	}
	else {
	  /* Cas xp, xn x xp   
	     OU xp x xp, xn 
	     OU xp x xp 
	     OU xp, xn x xp, xn 
	  */

	  New_A = filtre_tautologie(dd,zbdd_A);
	  if (New_A == NULL) return(NULL);
	  REF(New_A);
	  New_B = filtre_tautologie(dd,zbdd_B);
	  if(New_B==NULL) {
	    DEREF(New_A);
	    return(NULL);
	  }
	  REF(New_B);
	   
	  if ((New_A == DD_ZERO(dd)) || (New_B == DD_ZERO(dd))) {
	    DEREF(New_A);
	    DEREF(New_B);
	    return(DD_ZERO(dd));
	  }
	  if (cuddIsConstant(New_A)) {
	    DEREF(New_A);
	    Cudd_Deref(New_B);
	    return (New_B);
	  }
	  if (cuddIsConstant(New_B)) {
	    DEREF(New_B);
	    Cudd_Deref(New_A);
	    return (New_A);
	  }
	  
	  if (( ! Cudd_IsConstant(cuddE(New_A))) && 
	      ((level_A>>1) == ((dd->permZ[cuddE(New_A)->index])>>1))) 
	    {
	      /* Cas xp,xn x xp OU xp, xn x xp, xn */
	      if (( ! Cudd_IsConstant(cuddE(New_B))) &&
		  ((level_B>>1) == ((dd->permZ[cuddE(New_B)->index])>>1))) {
		/* Cas xp,xn x xp,xn */
		r = product_cas_xpxn_xpxn(dd,New_A, New_B);
		if (r==NULL) {
		  DEREF(New_A);
		  DEREF(New_B);
		  return(NULL);
		}
	      } 
	      else {
		/* Cas xp, xn x xp */
#ifdef LOCALDBG
		printf(" Cas xp, xn x xp "); fflush(stdout); 
#endif
		r = product_cas_xpxn_xp(dd,New_A,New_B);
		if (r==NULL) {
		  DEREF(New_A);
		  DEREF(New_B);
		  return(NULL);
		}
	      }
	    } /* Ce n'est donc pas xp,xn x xp OU xp, xn x xp, xn */
	  else { 
	      /*Cas xp x xp OU xp x xp, xn */
	      if ((! Cudd_IsConstant(cuddE(New_B))) && 
		  ((level_B>>1) == ((dd->permZ[cuddE(New_B)->index])>>1))) {
		/* Cas xp x xp, xn */
#ifdef LOCALDBG
		printf(" Cas xp x xp, xn "); fflush(stdout);
#endif
		r = product_cas_xpxn_xp(dd,New_B,New_A);
		if (r==NULL) {
		  DEREF(New_A);
		  DEREF(New_B);
		  return(NULL);
		}
	      }
	      else {
		r = product_cas_xp_xp(dd,New_A, New_B);
		if (r==NULL) {
		  DEREF(New_A);
		  DEREF(New_B);
		  return(NULL);
		}
		/**** Fin cas xp x xp *****/
	      }
	    }
	  DEREF(New_A);
	  DEREF(New_B);

	}
      } /* level_A == level_B */ 
      else { /* level_A <> level_B et deux memes vars */
	New_A = filtre_tautologie(dd,zbdd_A);
	if (New_A == NULL) return(NULL);
	REF(New_A);
	
	if (New_A == DD_ZERO(dd)) {
	  DEREF(New_A);
	  return DD_ZERO(dd);
	}
	if (New_A == DD_ONE(dd)) {
	  DEREF(New_A);
	    printf("ONE\n");
	  return zbdd_B;
	}
	
	/* Cas xp x xn ou xp,xn x xn*/
	if ((!Cudd_IsConstant(cuddE(New_A))) &&
	    ((level_A>>1) == ((dd->permZ[cuddE(New_A)->index])>>1))) {
	  r = product_cas_xpxn_xn(dd,New_A, zbdd_B);
	  if (r==NULL) {
	    DEREF(New_A);
	    return(NULL);}
	}else {
	  r = product_cas_xp_xn(dd,New_A, zbdd_B);
	  if(r==NULL) {
	    DEREF(New_A);
	    return(NULL);}
	}
	DEREF(New_A);
      }
    } 
  else { /* On a une vars x un ensemble sans la var */

      tmp = filtre_tautologie(dd, zbdd_A);
      if (tmp == NULL) {
	return(NULL);}
      REF(tmp);
      New_A = tmp;
      
      if (New_A == DD_ZERO(dd)) {
	  DEREF(New_A);
	  return DD_ZERO(dd);
      }
      if (New_A == DD_ONE(dd)) {
	DEREF(New_A);
	return zbdd_B;
      }
      
      level_A = dd->permZ[New_A->index];
      if ((!Cudd_IsConstant(cuddE(New_A))) &&
	  ((level_A>>1) == ((dd->permZ[(cuddE(New_A))->index])>>1))) {
	/* Cas Xp, Xn x D */

	/*       printf(" Cas Xp, Xn x D "); */


	r = product_cas_xpxn_D(dd, New_A, zbdd_B);
	if (r==NULL) {
	  DEREF(New_A);
	  return(NULL);}
	DEREF(New_A);
      }
      else {
	if (level_A - ((level_A>>1)<<1)) {
	  /* Cas Xn x D */
	  /* En fait les deux cas sont traites pareil */
	} else {
	  /* Cas Xp x D */
	}

	r = product_cas_x_D(dd, New_A, zbdd_B);
	if (r==NULL){
	  DEREF(New_A);
	  return(NULL);
	}

	DEREF(New_A);
      }
    
    }

#ifdef LOCALDBG
  printf("Resultat de \n");
  PRMIN(zbdd_A);
  printf("Distri sur \n");
  PRMIN(zbdd_B);
  printf("Donne :\n");
  PRMIN(r);
  printf("\n");
#endif

  cuddCacheInsert2(dd, zdd_myproduct_aux, zbdd_A, zbdd_B, r);
#ifdef LOCALDBG
  printf("Fonctions debug apres product_aux :\n");
  Cudd_CheckKeys(manager);
  Cudd_DebugCheck(dd);
#endif
  Cudd_Deref(r);



  return(r);
}

DdNode * zdd_myproduct(DdManager * dd, DdNode * Zbdd_A, DdNode * Zbdd_B) {
    DdNode	*res;

#ifdef LOCALDBG
  printf("Fonctions debug avant product :\n");
     Cudd_CheckKeys(manager);
  Cudd_DebugCheck(dd);
#endif
    do {
	dd->reordered = 0;
	res = zdd_myproduct_aux(dd, Zbdd_A, Zbdd_B);
    } while (dd->reordered == 1);

#ifdef LOCALDBG
  printf("Fonctions debug apres product :\n");
  Cudd_CheckKeys(manager);
  Cudd_DebugCheck(dd);
#endif

    return(res);
}


/* 01 69 35 15 50 */

DdNode *
zdd_mydiff_aux(
  DdManager * zdd,
  DdNode * P,
  DdNode * Q)
{
    int		p_top, q_top;
    DdNode	*empty = DD_ZERO(zdd), *t, *e, *res;
    DdManager	*table = zdd;

    statLine(zdd);
    if (P == empty)
	return(empty);
    if (Q == empty)
	return(P);
    if (P == Q)
	return(empty);

    //LS (A VERIFIER?)
    if (P == DD_ONE(zdd)) return(DD_ONE(zdd));
    if (Q == DD_ONE(zdd)) return(DD_ZERO(zdd));

    /* Check cache.  The cache is shared by Cudd_zddDiffConst(). */
    res = cuddCacheLookup2Zdd(table, zdd_mydiff_aux, P, Q);
    if (res != NULL && res != DD_NON_CONSTANT)
	return(res);

    if (cuddIsConstant(P))
	p_top = P->index;
    else
	p_top = zdd->permZ[P->index];
    if (cuddIsConstant(Q)) {
      //      return(P); // P != constant
	q_top = Q->index;
    }
    else
	q_top = zdd->permZ[Q->index];
    if (p_top < q_top) {
      e = zdd_mydiff_aux(zdd, cuddE(P), Q);
      if (e == NULL) return(NULL);
      cuddRef(e);
      t = zdd_mydiff_aux(zdd, cuddT(P), Q);
      // t = zdd_mydiff_aux(zdd, cuddT(P), cuddE(Q));
      if (t==NULL) {
	  Cudd_RecursiveDerefZdd(table, e);}
	cuddRef(t);

	res = cuddZddGetNode(zdd, P->index, t, e);
	if (res == NULL) {
	    Cudd_RecursiveDerefZdd(table, e);
	    Cudd_RecursiveDerefZdd(table, t);
	    return(NULL);
	}
	cuddDeref(e);
	cuddDeref(t);
    } else if (p_top > q_top) {
	res = zdd_mydiff_aux(zdd, P, cuddE(Q));
	if (res == NULL) return(NULL);
    } else {
	t = zdd_mydiff_aux(zdd, cuddT(P), cuddT(Q));
	if (t == NULL) return(NULL);
	cuddRef(t);
	e = zdd_mydiff_aux(zdd, t, cuddE(Q));
	if(e == NULL) {
	    Cudd_RecursiveDerefZdd(table, t);
	    return(NULL);
	}
	cuddRef(e);
	Cudd_RecursiveDerefZdd(table, t);
	t = e;
	e = zdd_mydiff_aux(zdd, cuddE(P), cuddE(Q));
	if (e == NULL) {
	    Cudd_RecursiveDerefZdd(table, t);
	    return(NULL);
	}
	cuddRef(e);
	res = cuddZddGetNode(zdd, P->index, t, e);
	if (res == NULL) {
	    Cudd_RecursiveDerefZdd(table, t);
	    Cudd_RecursiveDerefZdd(table, e);
	    return(NULL);
	}
	cuddDeref(t);
	cuddDeref(e);
    }

    cuddCacheInsert2(table, zdd_mydiff_aux, P, Q, res);

    return(res);

} /* end of zdd_mydiff_aux */



DdNode *
zdd_mydiff(
  DdManager * dd,
  DdNode * P,
  DdNode * Q)
{
    DdNode *res;

    do {
	dd->reordered = 0;
	res = zdd_mydiff_aux(dd, P, Q);
    } while (dd->reordered == 1);
    return(res);

} /* end of Cudd_zddDiff */


/* Copied from zddIsop.c in Cudd-2.3.1 */


DdNode	*
cuddZddIsopFlip01(
  DdManager * dd,
  DdNode * L,
  DdNode * U,
  DdNode ** zdd_I);


DdNode	*
Cudd_zddIsopFlip01(
  DdManager * dd,
  DdNode * L,
  DdNode * U,
  DdNode ** zdd_I)
{
    DdNode	*res;
    int		autoDynZ;

    autoDynZ = dd->autoDynZ;
    dd->autoDynZ = 0;

    do {
	dd->reordered = 0;
	res = cuddZddIsopFlip01(dd, Cudd_Not(U), Cudd_Not(L), zdd_I);
	//	res = cuddZddIsopFlip01(dd, L, U, zdd_I);
    } while (dd->reordered == 1);
    dd->autoDynZ = autoDynZ;
    return(res);

} /* end of Cudd_zddIsop */

DdNode	*
cuddZddIsopFlip01(
  DdManager * dd,
  DdNode * L,
  DdNode * U,
  DdNode ** zdd_I)
{
    DdNode	*one = DD_ONE(dd);
    DdNode	*zero = Cudd_Not(one);
    DdNode	*zdd_one = DD_ONE(dd);
    DdNode	*zdd_zero = DD_ZERO(dd);
    int		v, top_l, top_u;
    DdNode	*Lsub0, *Usub0, *Lsub1, *Usub1, *Ld, *Ud;
    DdNode	*Lsuper0, *Usuper0, *Lsuper1, *Usuper1;
    DdNode	*Isub0, *Isub1, *Id;
    DdNode	*zdd_Isub0, *zdd_Isub1, *zdd_Id;
    DdNode	*x;
    DdNode	*term0, *term1, *sum;
    DdNode	*Lv, *Uv, *Lnv, *Unv;
    DdNode	*r, *y, *z;
    int		index;
    DdNode *(*cacheOp)(DdManager *, DdNode *, DdNode *);

    statLine(dd);
    if (L == zero) {
	*zdd_I = zdd_zero;
    	return(zero);
    }
    if (U == one) {
	*zdd_I = zdd_one;
    	return(one);
    }

    if (U == zero || L == one) {
	printf("*** ERROR : illegal condition for ISOP (U < L).\n");
	exit(1);
    }

    /* Check the cache. We store two results for each recursive call.
    ** One is the BDD, and the other is the ZDD. Both are needed.
    ** Hence we need a double hit in the cache to terminate the
    ** recursion. Clearly, collisions may evict only one of the two
    ** results. */
    cacheOp = (DdNode *(*)(DdManager *, DdNode *, DdNode *)) cuddZddIsopFlip01;
    r = cuddCacheLookup2(dd, cuddBddIsop, L, U);
    if (r) {
	*zdd_I = cuddCacheLookup2Zdd(dd, cacheOp, L, U);
	if (*zdd_I)
	    return(r);
	else {
	    /* The BDD result may have been dead. In that case
	    ** cuddCacheLookup2 would have called cuddReclaim,
	    ** whose effects we now have to undo. */
	    cuddRef(r);
	    Cudd_RecursiveDeref(dd, r);
	}
    }

    top_l = dd->perm[Cudd_Regular(L)->index];
    top_u = dd->perm[Cudd_Regular(U)->index];
    v = ddMin(top_l, top_u);

    /* Compute cofactors. */
    if (top_l == v) {
	index = Cudd_Regular(L)->index;
    	Lv = Cudd_T(L);
    	Lnv = Cudd_E(L);
    	if (Cudd_IsComplement(L)) {
    	    Lv = Cudd_Not(Lv);
    	    Lnv = Cudd_Not(Lnv);
    	}
    }
    else {
	index = Cudd_Regular(U)->index;
        Lv = Lnv = L;
    }

    if (top_u == v) {
    	Uv = Cudd_T(U);
    	Unv = Cudd_E(U);
    	if (Cudd_IsComplement(U)) {
    	    Uv = Cudd_Not(Uv);
    	    Unv = Cudd_Not(Unv);
    	}
    }
    else {
        Uv = Unv = U;
    }

    Lsub0 = cuddBddAndRecur(dd, Lnv, Cudd_Not(Uv));
    if (Lsub0 == NULL)
	return(NULL);
    Cudd_Ref(Lsub0);
    Usub0 = Unv;
    Lsub1 = cuddBddAndRecur(dd, Lv, Cudd_Not(Unv));
    if (Lsub1 == NULL) {
	Cudd_RecursiveDeref(dd, Lsub0);
	return(NULL);
    }
    Cudd_Ref(Lsub1);
    Usub1 = Uv;

    Isub0 = cuddZddIsopFlip01(dd, Lsub0, Usub0, &zdd_Isub0);
    if (Isub0 == NULL) {
	Cudd_RecursiveDeref(dd, Lsub0);
	Cudd_RecursiveDeref(dd, Lsub1);
	return(NULL);
    }
    /*
    if ((!cuddIsConstant(Cudd_Regular(Isub0))) &&
	(Cudd_Regular(Isub0)->index != zdd_Isub0->index / 2 ||
	dd->permZ[index * 2] > dd->permZ[zdd_Isub0->index])) {
	printf("*** ERROR : illegal permutation in ZDD. ***\n");
    }
    */
    Cudd_Ref(Isub0);
    Cudd_Ref(zdd_Isub0);
    Isub1 = cuddZddIsopFlip01(dd, Lsub1, Usub1, &zdd_Isub1);
    if (Isub1 == NULL) {
	Cudd_RecursiveDeref(dd, Lsub0);
	Cudd_RecursiveDeref(dd, Lsub1);
	Cudd_RecursiveDeref(dd, Isub0);
	Cudd_RecursiveDerefZdd(dd, zdd_Isub0);
	return(NULL);
    }
    /*
    if ((!cuddIsConstant(Cudd_Regular(Isub1))) &&
	(Cudd_Regular(Isub1)->index != zdd_Isub1->index / 2 ||
	dd->permZ[index * 2] > dd->permZ[zdd_Isub1->index])) {
	printf("*** ERROR : illegal permutation in ZDD. ***\n");
    }
    */
    Cudd_Ref(Isub1);
    Cudd_Ref(zdd_Isub1);
    Cudd_RecursiveDeref(dd, Lsub0);
    Cudd_RecursiveDeref(dd, Lsub1);

    Lsuper0 = cuddBddAndRecur(dd, Lnv, Cudd_Not(Isub0));
    if (Lsuper0 == NULL) {
	Cudd_RecursiveDeref(dd, Isub0);
	Cudd_RecursiveDerefZdd(dd, zdd_Isub0);
	Cudd_RecursiveDeref(dd, Isub1);
	Cudd_RecursiveDerefZdd(dd, zdd_Isub1);
	return(NULL);
    }
    Cudd_Ref(Lsuper0);
    Lsuper1 = cuddBddAndRecur(dd, Lv, Cudd_Not(Isub1));
    if (Lsuper1 == NULL) {
	Cudd_RecursiveDeref(dd, Isub0);
	Cudd_RecursiveDerefZdd(dd, zdd_Isub0);
	Cudd_RecursiveDeref(dd, Isub1);
	Cudd_RecursiveDerefZdd(dd, zdd_Isub1);
	Cudd_RecursiveDeref(dd, Lsuper0);
	return(NULL);
    }
    Cudd_Ref(Lsuper1);
    Usuper0 = Unv;
    Usuper1 = Uv;

    /* Ld = Lsuper0 + Lsuper1 */
    Ld = cuddBddAndRecur(dd, Cudd_Not(Lsuper0), Cudd_Not(Lsuper1));
    if (Ld == NULL) {
	Cudd_RecursiveDeref(dd, Isub0);
	Cudd_RecursiveDerefZdd(dd, zdd_Isub0);
	Cudd_RecursiveDeref(dd, Isub1);
	Cudd_RecursiveDerefZdd(dd, zdd_Isub1);
	Cudd_RecursiveDeref(dd, Lsuper0);
	Cudd_RecursiveDeref(dd, Lsuper1);
	return(NULL);
    }
    Ld = Cudd_Not(Ld);
    Cudd_Ref(Ld);
    /* Ud = Usuper0 * Usuper1 */
    Ud = cuddBddAndRecur(dd, Usuper0, Usuper1);
    if (Ud == NULL) {
	Cudd_RecursiveDeref(dd, Isub0);
	Cudd_RecursiveDerefZdd(dd, zdd_Isub0);
	Cudd_RecursiveDeref(dd, Isub1);
	Cudd_RecursiveDerefZdd(dd, zdd_Isub1);
	Cudd_RecursiveDeref(dd, Lsuper0);
	Cudd_RecursiveDeref(dd, Lsuper1);
	Cudd_RecursiveDeref(dd, Ld);
	return(NULL);
    }
    Cudd_Ref(Ud);
    Cudd_RecursiveDeref(dd, Lsuper0);
    Cudd_RecursiveDeref(dd, Lsuper1);

    Id = cuddZddIsopFlip01(dd, Ld, Ud, &zdd_Id);
    if (Id == NULL) {
	Cudd_RecursiveDeref(dd, Isub0);
	Cudd_RecursiveDerefZdd(dd, zdd_Isub0);
	Cudd_RecursiveDeref(dd, Isub1);
	Cudd_RecursiveDerefZdd(dd, zdd_Isub1);
	Cudd_RecursiveDeref(dd, Ld);
	Cudd_RecursiveDeref(dd, Ud);
	return(NULL);
    }
    /*
    if ((!cuddIsConstant(Cudd_Regular(Id))) &&
	(Cudd_Regular(Id)->index != zdd_Id->index / 2 ||
	dd->permZ[index * 2] > dd->permZ[zdd_Id->index])) {
	printf("*** ERROR : illegal permutation in ZDD. ***\n");
    }
    */
    Cudd_Ref(Id);
    Cudd_Ref(zdd_Id);
    Cudd_RecursiveDeref(dd, Ld);
    Cudd_RecursiveDeref(dd, Ud);

    x = cuddUniqueInter(dd, index, one, zero);
    if (x == NULL) {
	Cudd_RecursiveDeref(dd, Isub0);
	Cudd_RecursiveDerefZdd(dd, zdd_Isub0);
	Cudd_RecursiveDeref(dd, Isub1);
	Cudd_RecursiveDerefZdd(dd, zdd_Isub1);
	Cudd_RecursiveDeref(dd, Id);
	Cudd_RecursiveDerefZdd(dd, zdd_Id);
	return(NULL);
    }
    Cudd_Ref(x);
    /* term0 = x * Isub0 */
    term0 = cuddBddAndRecur(dd, Cudd_Not(x), Isub0);
    if (term0 == NULL) {
	Cudd_RecursiveDeref(dd, Isub0);
	Cudd_RecursiveDerefZdd(dd, zdd_Isub0);
	Cudd_RecursiveDeref(dd, Isub1);
	Cudd_RecursiveDerefZdd(dd, zdd_Isub1);
	Cudd_RecursiveDeref(dd, Id);
	Cudd_RecursiveDerefZdd(dd, zdd_Id);
	Cudd_RecursiveDeref(dd, x);
	return(NULL);
    }
    Cudd_Ref(term0);
    Cudd_RecursiveDeref(dd, Isub0);
    /* term1 = x * Isub1 */
    term1 = cuddBddAndRecur(dd, x, Isub1);
    if (term1 == NULL) {
	Cudd_RecursiveDerefZdd(dd, zdd_Isub0);
	Cudd_RecursiveDeref(dd, Isub1);
	Cudd_RecursiveDerefZdd(dd, zdd_Isub1);
	Cudd_RecursiveDeref(dd, Id);
	Cudd_RecursiveDerefZdd(dd, zdd_Id);
	Cudd_RecursiveDeref(dd, x);
	Cudd_RecursiveDeref(dd, term0);
	return(NULL);
    }
    Cudd_Ref(term1);
    Cudd_RecursiveDeref(dd, x);
    Cudd_RecursiveDeref(dd, Isub1);
    /* sum = term0 + term1 */
    sum = cuddBddAndRecur(dd, Cudd_Not(term0), Cudd_Not(term1));
    if (sum == NULL) {
	Cudd_RecursiveDerefZdd(dd, zdd_Isub0);
	Cudd_RecursiveDerefZdd(dd, zdd_Isub1);
	Cudd_RecursiveDeref(dd, Id);
	Cudd_RecursiveDerefZdd(dd, zdd_Id);
	Cudd_RecursiveDeref(dd, term0);
	Cudd_RecursiveDeref(dd, term1);
	return(NULL);
    }
    sum = Cudd_Not(sum);
    Cudd_Ref(sum);
    Cudd_RecursiveDeref(dd, term0);
    Cudd_RecursiveDeref(dd, term1);
    /* r = sum + Id */
    r = cuddBddAndRecur(dd, Cudd_Not(sum), Cudd_Not(Id));
    r = Cudd_NotCond(r, r != NULL);
    if (r == NULL) {
	Cudd_RecursiveDerefZdd(dd, zdd_Isub0);
	Cudd_RecursiveDerefZdd(dd, zdd_Isub1);
	Cudd_RecursiveDeref(dd, Id);
	Cudd_RecursiveDerefZdd(dd, zdd_Id);
	Cudd_RecursiveDeref(dd, sum);
	return(NULL);
    }
    Cudd_Ref(r);
    Cudd_RecursiveDeref(dd, sum);
    Cudd_RecursiveDeref(dd, Id);

    // flipped 0/1 follows

    if (zdd_Isub1 != zdd_zero) {
	z = cuddZddGetNodeIVO(dd, index * 2 + 1, zdd_Isub1, zdd_Id);
	if (z == NULL) {
	    Cudd_RecursiveDerefZdd(dd, zdd_Isub0);
	    Cudd_RecursiveDerefZdd(dd, zdd_Isub1);
	    Cudd_RecursiveDerefZdd(dd, zdd_Id);
	    Cudd_RecursiveDeref(dd, r);
	    return(NULL);
	}
    }
    else {
	z = zdd_Id;
    }
    Cudd_Ref(z);
    if (zdd_Isub0 != zdd_zero) {
	y = cuddZddGetNodeIVO(dd, index * 2, zdd_Isub0, z);
	if (y == NULL) {
	    Cudd_RecursiveDerefZdd(dd, zdd_Isub0);
	    Cudd_RecursiveDerefZdd(dd, zdd_Isub1);
	    Cudd_RecursiveDerefZdd(dd, zdd_Id);
	    Cudd_RecursiveDeref(dd, r);
	    Cudd_RecursiveDerefZdd(dd, z);
	    return(NULL);
	}
    }
    else
	y = z;
    Cudd_Ref(y);

    Cudd_RecursiveDerefZdd(dd, zdd_Isub0);
    Cudd_RecursiveDerefZdd(dd, zdd_Isub1);
    Cudd_RecursiveDerefZdd(dd, zdd_Id);
    Cudd_RecursiveDerefZdd(dd, z);

    cuddCacheInsert2(dd, cuddBddIsop, L, U, r);
    cuddCacheInsert2(dd, cacheOp, L, U, y);

    Cudd_Deref(r);
    Cudd_Deref(y);
    *zdd_I = y;
    /*
    if (Cudd_Regular(r)->index != y->index / 2) {
	printf("*** ERROR : mismatch in indices between BDD and ZDD. ***\n");
    }
    */
    return(r);

} /* end of cuddZddIsop */


