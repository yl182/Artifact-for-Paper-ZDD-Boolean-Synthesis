#include <sys/types.h>
#include <sys/time.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <math.h>
#include <stdlib.h>
#include "cudd-release/cudd/cudd.h"
#include "cudd-release/cplusplus/cuddObj.hh"
#include <iostream>
#include <vector>


// ZDD with more vars---define zdd at the last step
int main (int argc, char *argv[])
{
    
	Cudd mgr;
	ZDD cl_012 = mgr.zddVar(0).Change(1).Change(2).Subset0(4).Subset0(3).Subset0(5);
	
	ZDD cl_345 = mgr.zddVar(5).Subset0(4).Subset0(3).Subset0(2).Subset0(1).Subset0(0).Change(4).Change(3);

	ZDD cl_234 = mgr.zddVar(2).Subset0(0).Subset0(1).Subset0(5).Subset0(4).Subset0(3).Change(4).Change(3);
	
	ZDD z = cl_012.Union(cl_345).Union(cl_234);
	std::vector<ZDD> zdds = {z};
	
	mgr.DumpDot(zdds, NULL, NULL, fopen("three_clauses.dot", "w"));
	
	return 0;
}




/*
// ZDD with only variable 1
int main (int argc, char *argv[])
{
    
	Cudd mgr;
	ZDD zdd1 = mgr.zddVar(1);
	

	std::vector<ZDD> zdds = {zdd1};
	
	mgr.DumpDot(zdds, NULL, NULL, fopen("mgr_only1var.dot", "w"));
	

	return 0;
}

*/
/*
//try: 0 to n
int main (int argc, char *argv[])
{
    
	Cudd mgr;
mgr.zddVar(0);
mgr.zddVar(3);
mgr.zddVar(4);
	ZDD zdd1 = mgr.zddVar(5);
	//mgr.zddVar(0);
	
	
	
	std::vector<ZDD> zdds = {zdd1};
	
	mgr.DumpDot(zdds, NULL, NULL, fopen("mgr_5vars.dot", "w"));
	

	return 0;
}

*/







