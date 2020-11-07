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
#include <string>
#include <map>
#include <algorithm>
#include "qdimacs-reader/CnfFormula.hpp"
#include "qdimacs-reader/QCnfFormula.hpp"
#include "qdimacs-reader/QDimacsReader.hpp"
#include "CNFtoZDDconverter.hpp"

//constructors
CNFtoZDDconverter::CNFtoZDDconverter() {}


//helper functions: given a reference of a clause, return the ZDD representing the clause
ZDD CNFtoZDDconverter::CLtoZDD(const CnfClause& cl, Cudd mgr, int maxvar) {
	// convert literals into indices:
	std::vector<int> literals;
	for (int j : cl) {
		literals.push_back(indexConverter(j));
	}

	// draw ZDD for the clause
	ZDD newZDDofCL = mgr.zddVar(literals[0]);
	// eliminate other variables
	for (int innn = 0; innn <= 2*maxvar; innn++) {					if (innn != literals[0]) {
			newZDDofCL =newZDDofCL.Subset0(innn);
		}
	}
	// append other variables to the clause
	for (int innn = 0; innn <= 2*maxvar; innn++) {
		if (std::find(literals.begin(), literals.end(), innn) != literals.end()) {
			if (innn != literals[0]) {
				newZDDofCL =newZDDofCL.Change(innn);	
			}	
		}
	}
	// return the ZDD of the clause
	return newZDDofCL;
}

// helper function: given index->node index
int CNFtoZDDconverter::indexConverter(int g) {
	if (g < 0) {
		return (-1)*g*2;
	} else {
		return 2*g-1;
	}
}

// helper function: retrieve max given index of QCnf
int CNFtoZDDconverter::maxVarRange(const QCnfFormula& qcnf) {
	int a = *std::max_element(qcnf.universal_vars.begin(), qcnf.universal_vars.end());
	int b = *std::max_element(qcnf.existential_vars.begin(), qcnf.existential_vars.end());
	return std::max(a,b);

}

// map given indices to positive node indices-pairs
std::map<int,int> CNFtoZDDconverter::produce_indices_map(int maxvar) {
	std::map <int, int> index_map;
	for (int k=1; k <= maxvar; k++) {
		//for example, x3 and -x3: pair (3, 5) (-3, 6)
		index_map.insert(std::pair<int, int>(k, indexConverter(k)) );
		index_map.insert(std::pair<int, int>(-k, indexConverter((-1)*k)) );
	}
	return index_map;
}

//main converter
void CNFtoZDDconverter::convertCNFtoZDD(const std::string& path) {
	
	// from instream get CNF and lists of x's and y's variables
	QDimacsReader qreader;
	QCnfFormula qcnf = qreader.Read(path);
	CnfFormula cnf = qcnf.formula;

	// get the largest absolute value in given variable indices
	QCnfFormula qcnf2 = qcnf;
	int maxVar = maxVarRange(qcnf2);
	

	// produce map of given indices and node indices
	std::map <int, int> index_to_nodes_map = produce_indices_map(maxVar);
	
	// draw ZDDs of the i-th clause
	Cudd mgr;
	Cudd& mgr1 = mgr;

	// initiate a vector of clause-ZDDs
	std::vector<ZDD> CL_ZDDs;
	
	// iterate over clauses, build ZDDs and add them to CL_ZDDs
	const int n_clauses = cnf.size();
	for (int i = 0; i < n_clauses; i++) {
		if (cnf[i].size() <= 0) {
			continue;
			std::cout << "clause empty" << std::endl;
		}
		//CnfClause& cl;
		//cl = cnf[i];
		ZDD Z_cl = CLtoZDD(cnf[i], mgr1, maxVar);

		// add the ZDD of this clause to the vector of ZDDs
		CL_ZDDs.push_back(Z_cl);	
	}
	
	// union the clause-zdds into ZDD of the CNF
	if (CL_ZDDs.size() <= 0) {
		std::cout << "formula is empty, 0 clause-ZDDs" << std::endl;
	}
	ZDD unionedZDDs = CL_ZDDs[0];
	for (ZDD zdd : CL_ZDDs) {
		unionedZDDs = unionedZDDs.Union(zdd);
	}
	

	std::vector<ZDD> zdds = {unionedZDDs};
	// draw the entire CNF's ZDD
	ZDDtoDot(mgr1, zdds, "ZDD.dot", NULL, NULL);
	return;
	

}

//draw ZDD
void CNFtoZDDconverter::ZDDtoDot(Cudd& mgr, const std::vector<ZDD> z, const std::string dotfile, char** inames, char** onames) {
	mgr.DumpDot(z, NULL, NULL, fopen(dotfile.c_str(), "w"));
}










