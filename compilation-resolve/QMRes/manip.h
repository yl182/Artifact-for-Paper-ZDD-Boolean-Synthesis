#define REF(i) (Cudd_Ref(i))
#define DEREF(i) (Cudd_RecursiveDerefZdd(manager,i))

EXTERN DdNode * filtre_tautologie(DdManager * dd, DdNode *zbdd);

EXTERN DdNode *
zdd_myUnion_aux(
  DdManager * zdd,
  DdNode * P,
  DdNode * Q);

EXTERN DdNode * zdd_myproduct_aux(DdManager * dd, DdNode * zbdd_A, DdNode * zbdd_B);

EXTERN DdNode * zdd_myproduct(DdManager * dd, DdNode * Zbdd_A, DdNode * Zbdd_B);

EXTERN DdNode * zdd_myunion(DdManager * dd, DdNode * Zbdd_A, DdNode * Zbdd_B);
EXTERN DdNode * zdd_myunion_aux(DdManager * dd, DdNode * Zbdd_A, DdNode * Zbdd_B);

EXTERN DdNode * zdd_mydiff(DdManager * zdd, DdNode * P, DdNode * Q);

EXTERN DdNode * zdd_mydiff_aux(DdManager * zdd, DdNode * P, DdNode * Q);

EXTERN DdNode *find_unit_literals(DdManager *dd, DdNode *f);
EXTERN DdNode *find_existential_unit_literals(DdManager *dd, DdNode *f);
EXTERN DdNode *adjust_pure_literals(DdManager *dd, DdNode *f);

EXTERN DdNode *apply_literals(DdManager *dd, DdNode *f, DdNode *unit);
EXTERN DdNode *get_zdd_support(DdManager *dd, DdNode *f);
EXTERN DdNode *get_zdd_support_2(DdManager *dd, DdNode *f);

EXTERN DdNode *remove_universal_literals(DdManager *dd, DdNode *f, int arbvo);

EXTERN void cuddCacheInsert1IntZdd(DdManager *table, void *op, DdNode *f, int i, DdNode *data);
EXTERN DdNode * cuddCacheLookup1IntZdd(DdManager *table, void *op, DdNode *f, int i);

extern unsigned short nesting[32768];
extern int use_earlyquantification;

extern int is_qbf, qbf_alternation, qbf_vars;

EXTERN DdNode *build_all_cubes(DdManager *dd, int start, int end);
EXTERN DdNode *subtract_unwit_clauses(DdManager *dd, DdNode *c, DdNode *a);
EXTERN DdNode *build_bdd_easyquant(DdManager *dd, DdNode *f, DdNode *chain);
EXTERN DdNode *build_bdd(DdManager *dd, DdNode *f, DdNode ***, int *);
EXTERN DdNode *build_bdd_noquant(DdManager *dd, DdNode *f);
EXTERN DdNode *build_bdd_quant_new(DdManager *dd, DdNode *f);
EXTERN DdNode *build_bdd_allquant(DdManager *dd, DdNode *f, int usebed);
EXTERN DdNode *build_bdd_quant(DdManager *dd, DdNode *f, DdNode *cube);
EXTERN DdNode *cnf2dnf(DdManager *dd, DdNode *f, int vars);

EXTERN DdNode *build_zdd_quant_new(DdManager *dd, DdNode *f);

EXTERN void print_clauses(DdManager *dd, DdNode *f, char *filename);

EXTERN DdNode	*
Cudd_zddIsopFlip01(
  DdManager * dd,
  DdNode * L,
  DdNode * U,
  DdNode ** zdd_I);
