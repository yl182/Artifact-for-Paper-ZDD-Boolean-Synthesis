#include <sys/types.h>
#include <sys/time.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <math.h>
#include <stdlib.h>
#include <iostream>
#include <vector>
#include <fstream>   
#include <iterator>
#include <map>
#include <string>  
#include <algorithm>
#include "cudd.h"
#include "cuddObj.hh"
#include "qdimacs-reader/CnfFormula.hpp"
#include "qdimacs-reader/QCnfFormula.hpp"
#include "qdimacs-reader/QDimacsReader.hpp"  
#include "CNFtoZDDconverter.hpp"


// function to print clauses represented by a ZDD
void printZDD (ZDD z)
{
	return;

}

// ZDD with more vars---define zdd at the last step
int main (int argc, char *argv[])
{
	// std::cout << "argc = " << argc << std::endl;
	if (argc < 4 or argc > 4) {
		std::cout << "Usage: " << std::string(argv[0]) << " <filename> <flag for output ZDDs as dot files> <flag for printing details>" << std::endl;
		return 0;
	}
	const std::string str1(argv[1]);
	
	// by default, do not write to dot file, and do not output all details
	// can enable if set to "yes":
	// first flag = 1 means enabling the functionality to produce dot files (which can be converted to PNGs or PDFS) throught the end-to-end procedure 
	// second flag = 1 means enabling the functionlity to write all details of intermediate steps to output stream
	// default setting for flags are disabled, and under this mode the experimental results are written to csv and txt files.
	
	//std::cout << "argv[2] = " << argv[2] << "\n" << "argv[3] = " << argv[3] << std::endl;
	CNFtoZDDconverter c(strcmp(argv[2],"1")==0,strcmp(argv[3], "1")==0);
	// CNFtoZDDconverter c(0,0);
	c.convertCNFtoZDD(str1);



	//std::cerr
	// >: redirect &2: tostderr?

	
	/*
	std::chrono::steady_clock::time_point t0 = std::chrono::steady_clock::now();
	std::cout << "starting counting time..." << std::endl;
	int k = 0;
	for (int i = 0; i < 1000; i++) {
		for (int j = 0; j < 1000; j++) {
			std::cout << "*";
		}
	}
	std::chrono::steady_clock::time_point t1 = std::chrono::steady_clock::now();
	std::cout << "stop counting time..." << std::endl;
	std::chrono::steady_clock::duration timespan = t1-t0;
	std::cout << "duration.count " << timespan.count() << std::endl;
	std::cout << "duration.count (cast to milliseconds) " << (double)timespan.count() << std::endl;
	std::cout << "duration times num divided by den: " << (double)timespan.count() *std::chrono::steady_clock::period::num / std::chrono::steady_clock::period::den << " seconds" << std::endl;
	std::cout << "num " << std::chrono::steady_clock::period::num << std::endl;
	std::cout << "den " << std::chrono::steady_clock::period::den << std::endl;
	*/
	
	/*
	Cudd mgr;
	ZDD z =mgr.zddOne(50);// this is the 1-ZDD
	z = z.Change(21).Change(0);
	//ZDD z0 = mgr.zdd();//this is the 0-ZDD
	//.Change(0).Change(5);
	
	z = z.Change(3).Change(4).Change(0);
	ZDD z_ = mgr.zddOne(50).Change(10).Change(20).Change(3);
	z = z.Union(z_);
	BDD b = z.PortToBdd();// convert to BDD's isop

	std::vector<ZDD> zdd = {z};
	std::vector<BDD> bdd = {b};
	mgr.zddPrintSubtable();
	mgr.DumpDot(bdd, NULL, NULL, fopen("portToBdd.dot", "w"));
	std::cout << z.NodeReadIndex() << std::endl;// function of DD class to find root node's index
	
	*/
	//std::cout << (z == z0) << std::endl;

	/*Cudd mgr;
	
	ZDD z = mgr.zddVar(0).Subset0(1).Subset0(2).Change(1);
	std::vector<ZDD> zdd = {z};
	mgr.DumpDot(zdd, NULL, NULL, fopen("try1ZDD.dot", "w"));
	std::vector<int> v = {2};
	ZDD resolved = (mgr, z, v);
	zdd = {resolved};
	mgr.DumpDot(zdd, NULL, NULL, fopen("try2ZDD.dot", "w"));*/
	/*
	Cudd mgr;
	ZDD z1 = mgr.zddZero();
	std::vector<ZDD> zdd = {z1};
	mgr.DumpDot(zdd, NULL, NULL, fopen("try1ZDD.dot", "w"));
	*/
	//try block
	/*Cudd mgr;
	ZDD z1 = mgr.zddVar(1).Subset0(0).Subset0(2).Subset0(3).Subset0(4).Subset0(5).Subset0(6).Subset0(7).Change(3).Change(5);
	ZDD z3 = mgr.zddVar(0).Subset0(4).Subset0(1).Subset0(2).Subset0(3).Subset0(5).Subset0(6).Subset0(7);
	//ZDD z111 = mgr.zddVar(1).Subset0(0).Subset0(2);
	std::vector<ZDD> zdd13;
	ZDD z1_3 = z3.Union(z1);
	
	zdd13 = {z1_3};
	//zdd13 = {z111};
	mgr.DumpDot(zdd13, NULL, NULL, fopen("try1ZDD.dot", "w"));

	//ZDD z57 = mgr.zddVar(5).Subset0(0).Subset0(1).Subset0(2).Subset0(3).Subset0(4).Subset0(6).Subset0(7).Change(7);
	std::vector<ZDD> zdd57;
	//zdd57 = {z57};
	ZDD z222 = mgr.zddVar(1).Subset0(5).Subset0(0).Subset0(3).Subset0(4).Subset0(6).Subset0(7).Subset0(2).Change(3);
	zdd57 = {z222};
	mgr.DumpDot(zdd57, NULL, NULL, fopen("try2ZDD.dot", "w"));

	
	//ZDD z = z57.ClauseDistribution(z1_3);
	ZDD z = z1_3.ClauseDistribution(z222);
	std::vector<ZDD> zddor;
	zddor = {z};
	mgr.DumpDot(zddor, NULL, NULL, fopen("try3ZDD.dot", "w"));

	
	ZDD z_ = z1_3.SubSumptionFreeUnion(z222);
	std::vector<ZDD> zddunion;
	zddunion = {z_};
	mgr.DumpDot(zddunion, NULL, NULL, fopen("try4ZDD.dot", "w"));
*/
	/*Cudd mgr;
	ZDD z = mgr.zddVar(0);
	std::vector<ZDD> zdds;
	zdds = {z};
	mgr.DumpDot(zdds, NULL, NULL, fopen("try1ZDD.dot", "w"));
	std::cout << z.Count() << std::endl;

	
	ZDD z1 = mgr.zddVar(1);
	zdds = {z1};
	mgr.DumpDot(zdds, NULL, NULL, fopen("try2ZDD.dot", "w"));
	std::cout << z1.Count() << std::endl;

	
	ZDD z2 = mgr.zddVar(1).Subset0(0).Change(3).Change(3).Subset0(1);
	zdds = {z2};
	mgr.DumpDot(zdds, NULL, NULL, fopen("try3ZDD.dot", "w"));
	std::cout << z2.Count() << std::endl;
	*/
/*
	Cudd mgr;
	ZDD z = mgr.zddVar(1);
	// z: (1,2,3)
	z = z.Subset1(0).Change(2).Change(3);
	std::vector<ZDD> zdds = {z};
	mgr.DumpDot(zdds, NULL, NULL, fopen("try1ZDD.dot", "w"));

	ZDD z1 = mgr.zddVar(2).Subset0(0).Subset0(1).Subset0(3).Change(3);
	// z1: (2, 3)
	std::vector<ZDD> zdds2 = {z1};
	mgr.DumpDot(zdds2, NULL, NULL, fopen("try2ZDD.dot", "w"));

	ZDD z2 = mgr.zddVar(1);
	// z2: (1,4)
	z2 = z2.Subset0(0).Subset0(2).Subset0(3).Subset0(4).Change(4);
	std::vector<ZDD> zdds3 = {z2};
	mgr.DumpDot(zdds3, NULL, NULL, fopen("try3ZDD.dot", "w"));

	ZDD unioned = z.Union(z1).Union(z2);
	std::vector<ZDD> zdds_all = {unioned};
	// unioned: (1,2,3), (2,3), (1,4)
	mgr.DumpDot(zdds_all, NULL, NULL, fopen("try4ZDD.dot", "w"));

	std::vector<ZDD> tmp;
	ZDD z_1_plus = unioned.Subset1(1);
	tmp = {z_1_plus};
	mgr.DumpDot(tmp, NULL, NULL, fopen("try5ZDD.dot", "w"));

	ZDD z_1_minus = unioned.Subset1(2);
	tmp = {z_1_minus};
	mgr.DumpDot(tmp, NULL, NULL, fopen("try6ZDD.dot", "w"));

	ZDD z_1_prime = unioned.Subset0(1).Subset0(4);
	tmp = {z_1_prime};
	mgr.DumpDot(tmp, NULL, NULL, fopen("try7ZDD.dot", "w"));

*/
	//Change(3).Change(5);
	/*
	Cudd mgr;
	std::vector<int> subset0list= {0,1,2,3,4,5,6};
	std::vector<int> changelist = {3,5};

	ZDD newZDDofClause = mgr.zddVar(1);
	//return newZDDofClause;
	std::cout << "Start with Node " << 1 << std::endl;
	
	std::vector<ZDD> zdds = {newZDDofClause};
	std::cout << "Output ZDD for the CNF above to file " << "tryZDD1.dot" << std::endl;
	mgr.DumpDot(zdds, NULL, NULL, fopen("try1ZDD.dot", "w"));

	// subset0
	
	


	for (int i : subset0list) {
		if (i != 1) {
			newZDDofClause =newZDDofClause.Subset0(i);	
			std::cout << "Subset0 with Node " << i << std::endl;
		}

	}
	zdds = {newZDDofClause};
	std::cout << "Output ZDD for the CNF above to file " << "tryZDD2.dot" << std::endl;
	mgr.DumpDot(zdds, NULL, NULL, fopen("try2ZDD.dot", "w"));

	// change
	for (int i : changelist) {					
		if (i != 1) {
			newZDDofClause =newZDDofClause.Change(i);
			std::cout << "Change with Node " << i << std::endl;
		}
	}
	// return the ZDD of the clause
	zdds = {newZDDofClause};
	std::cout << "Output ZDD for the CNF above to file " << "tryZDD3.dot" << std::endl;
	mgr.DumpDot(zdds, NULL, NULL, fopen("try3ZDD.dot", "w"));
	
	*/
	return 0;
}
