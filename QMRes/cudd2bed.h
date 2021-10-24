#ifndef __CUDD2BED_H
#define __CUDD2BED_H

#include "cudd.h"
#include "cuddInt.h"
#include "bed.h"

extern "C" bed_node bdd_to_bed(DdManager *dd, DdNode *f);
extern "C" DdNode *bed_to_bdd(DdManager *dd, bed_node f);

#endif
