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
#include <unordered_map>
#include <stdexcept>
#include "qdimacs-reader/CnfFormula.hpp"
#include "qdimacs-reader/QCnfFormula.hpp"
#include "qdimacs-reader/QDimacsReader.hpp"
#include "CNFtoZDDconverter.hpp"

//constructors
CNFtoZDDconverter::CNFtoZDDconverter() {}


std::runtime_error CNFtoZDDconverter::EmptyFormulaException(const std::string& filepath) const {
	return std::runtime_error(filepath + ", formula is empty, 0 clause-ZDDs");
}		

//helper functions: given a reference of a clause, return the ZDD representing the clause
ZDD CNFtoZDDconverter::ClausetoZDD(const CnfClause& cl, Cudd& mgr, int maxvar) {
	// convert literals into indices:
	std::vector<int> literals;
	for (int lit : cl) {
		literals.push_back(indexConverter(lit));
	}

	// draw ZDD for the clause
	ZDD newZDDofClause = mgr.zddVar(literals[0]);
	// eliminate other variables
	for (int i = 0; i <= 2*maxvar; i++) {					if (i != literals[0]) {
			newZDDofClause =newZDDofClause.Subset0(i);
		}
	}
	// append other variables to the clause
	for (int i = 0; i <= 2*maxvar; i++) {
		if (std::find(literals.begin(), literals.end(), i) != literals.end()) {
			if (i != literals[0]) {
				newZDDofClause =newZDDofClause.Change(i);	
			}	
		}
	}
	// return the ZDD of the clause
	return newZDDofClause;
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
std::unordered_map<int,int> CNFtoZDDconverter::produceIndicesMap(int maxvar) {
	std::unordered_map <int, int> index_map;
	for (int k=1; k <= maxvar; k++) {
		//for example, x3 and -x3: pair (3, 5) (-3, 6)
		index_map.insert(std::pair<int, int>(k, indexConverter(k)) );
		index_map.insert(std::pair<int, int>(-k, indexConverter((-1)*k)) );
	}
	return index_map;
}

//main converter
std::vector<ZDD> CNFtoZDDconverter::convertCNFtoZDD(const std::string& path) {
	
	// from instream get CNF and lists of x's and y's variables
	QDimacsReader qreader;
	QCnfFormula qcnf = qreader.Read(path);
	CnfFormula cnf = qcnf.formula;

	// get the largest absolute value in given variable indices
	QCnfFormula qcnf2 = qcnf;
	int maxVar = maxVarRange(qcnf2);
	

	// produce map of given indices and node indices
	std::unordered_map <int, int> index_to_nodes_map = produceIndicesMap(maxVar);
	
	// draw ZDDs of the i-th clause
	Cudd mgr;
	//Cudd& mgr1 = mgr;

	// initiate a vector of clause-ZDDs
	std::vector<ZDD> Clause_ZDDs;
	
	// iterate over clauses, build ZDDs and add them to Clause_ZDDs
	const int n_clauses = cnf.size();
	/*for (int i = 0; i < n_clauses; i++) {
		if (cnf[i].size() <= 0) {
			continue;
			std::cout << "clause empty" << std::endl;
		}
		//CnfClause& cl;
		//cl = cnf[i];
		ZDD Z_cl = ClausetoZDD(cnf[i], mgr, maxVar);

		// add the ZDD of this clause to the vector of ZDDs
		Clause_ZDDs.push_back(Z_cl);	
	}*/

	for (const CnfClause& clause : cnf) {
		if (clause.size() <= 0) {
			continue;
			std::cout << "clause empty" << std::endl;
		}
		//CnfClause& cl;
		//cl = cnf[i];
		ZDD Z_cl = ClausetoZDD(clause, mgr, maxVar);

		// add the ZDD of this clause to the vector of ZDDs
		Clause_ZDDs.push_back(Z_cl);	
	}
	
	// union the clause-zdds into ZDD of the CNF
	if (Clause_ZDDs.size() <= 0) {
		std::cout << "formula is empty, 0 clause-ZDDs" << std::endl;
		throw EmptyFormulaException(path); 
	}
	ZDD unionedZDDs = Clause_ZDDs[0];
	for (const ZDD& zdd : Clause_ZDDs) {
		unionedZDDs = unionedZDDs.Union(zdd);
	}
	

	std::vector<ZDD> zdds = {unionedZDDs};
	// draw the entire CNF's ZDD
	ZDDtoDot(mgr, zdds, "ZDD.dot", NULL, NULL);
	return zdds;
	

}

//draw ZDD
void CNFtoZDDconverter::ZDDtoDot(Cudd& mgr, const std::vector<ZDD> z, const std::string dotfile, char** inames, char** onames) {
	mgr.DumpDot(z, NULL, NULL, fopen(dotfile.c_str(), "w"));
}










