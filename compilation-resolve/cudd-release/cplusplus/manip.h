#define REF(i) (Cudd_Ref(i))
#define DEREF(i) (Cudd_RecursiveDerefZdd(dd,i))

 DdNode * filtre_tautologie(DdManager * dd, DdNode *zbdd);

 DdNode *
zdd_myUnion_aux(
  DdManager * zdd,
  DdNode * P,
  DdNode * Q);

 DdNode * zdd_myproduct_aux(DdManager * dd, DdNode * zbdd_A, DdNode * zbdd_B);

 DdNode * zdd_myproduct(DdManager * dd, DdNode * Zbdd_A, DdNode * Zbdd_B);

 DdNode * zdd_myunion(DdManager * dd, DdNode * Zbdd_A, DdNode * Zbdd_B);
 DdNode * zdd_myunion_aux(DdManager * dd, DdNode * Zbdd_A, DdNode * Zbdd_B);

 DdNode * zdd_mydiff(DdManager * zdd, DdNode * P, DdNode * Q);

 DdNode * zdd_mydiff_aux(DdManager * zdd, DdNode * P, DdNode * Q);

 DdNode *find_unit_literals(DdManager *dd, DdNode *f);
 DdNode *find_existential_unit_literals(DdManager *dd, DdNode *f);
 DdNode *adjust_pure_literals(DdManager *dd, DdNode *f);

 DdNode *apply_literals(DdManager *dd, DdNode *f, DdNode *unit);
 DdNode *get_zdd_support(DdManager *dd, DdNode *f);
 DdNode *get_zdd_support_2(DdManager *dd, DdNode *f);

 DdNode *remove_universal_literals(DdManager *dd, DdNode *f, int arbvo);

 void cuddCacheInsert1IntZdd(DdManager *table, void *op, DdNode *f, int i, DdNode *data);
 DdNode * cuddCacheLookup1IntZdd(DdManager *table, void *op, DdNode *f, int i);

 unsigned short nesting[32768];
 int use_earlyquantification;

 int is_qbf, qbf_alternation, qbf_vars;

 DdNode *build_all_cubes(DdManager *dd, int start, int end);
 DdNode *subtract_unwit_clauses(DdManager *dd, DdNode *c, DdNode *a);
 DdNode *build_bdd_easyquant(DdManager *dd, DdNode *f, DdNode *chain);
 DdNode *build_bdd(DdManager *dd, DdNode *f, DdNode ***, int *);
 DdNode *build_bdd_noquant(DdManager *dd, DdNode *f);
 DdNode *build_bdd_quant_new(DdManager *dd, DdNode *f);
 DdNode *build_bdd_allquant(DdManager *dd, DdNode *f, int usebed);
 DdNode *build_bdd_quant(DdManager *dd, DdNode *f, DdNode *cube);
 DdNode *cnf2dnf(DdManager *dd, DdNode *f, int vars);

 DdNode *build_zdd_quant_new(DdManager *dd, DdNode *f);

 void print_clauses(DdManager *dd, DdNode *f, char *filename);

 DdNode	*
Cudd_zddIsopFlip01(
  DdManager * dd,
  DdNode * L,
  DdNode * U,
  DdNode ** zdd_I);
