#include <sys/types.h>
#include <sys/time.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <math.h>
#include <stdlib.h>
#include <iostream>
#include <vector>
#include <string>
#include <map>
#include <algorithm>
#include <unordered_map>
#include <stdexcept>
#include "CnfFormula.hpp"
#include "QCnfFormula.hpp"
#include "QDimacsReader.hpp"
#include "CNFtoZDDconverter.hpp"
#include "cuddObj.hh"
#include "cudd.h"



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

	for (auto& n : index_map) {
		std::cout << n.first << "\t" << n.second << std::endl;
	}
	return index_map;
}

//draw ZDD
void CNFtoZDDconverter::ZDDtoDot(Cudd& mgr, const std::vector<ZDD> z, const std::string dotfile, char** inames, char** onames) {
	mgr.DumpDot(z, inames, onames, fopen(dotfile.c_str(), "w"));
}

//resolve a variable
ZDD CNFtoZDDconverter::Resolution(const ZDD& zdd, const std::vector<int> y_vars, std::unordered_map <int, int> index_map) const {
	ZDD resolvedZDD = zdd;
	for (int y : y_vars) {
		std::cout << "y posY negY " << std::endl;
		int posY = index_map[y];
		int negY = index_map[(-1)*y];
		std::cout << "inside resolution for loop\n" << y << " " << posY << " " << negY << std::endl;
		
		// build ZDDs for f_y^+, f_y^-, f_y'
		ZDD f_y_plus = zdd.Subset1(posY).Change(posY);
		
		ZDD f_y_minus = zdd.Subset1(negY).Change(negY);
		
		ZDD f_y_prime = zdd.Subset0(posY).Subset0(negY);
		std::cout << "no errors by this line" << std::endl;
		// core dumped after this line in first iteration
		ZDD f_y_plus_OR_f_y_minus = f_y_plus.ClauseDistribution(f_y_minus);
		std::cout << "no errors until this line" << std::endl;
		ZDD resolvedZDD = f_y_plus_OR_f_y_minus.SubSumptionFreeUnion(f_y_prime);
		
	}
	// core dumped before this line
	return resolvedZDD;
}

// check partial realizability
bool CNFtoZDDconverter::partialRealizability(const ZDD& zdd) const {
	if (zdd.Count() > 0) {
		return 1;
	} else {
		return 0;
	}
}
// check full realizability
bool CNFtoZDDconverter::fullRealizability(const ZDD& zdd, std::unordered_map <int, int> index_map, QCnfFormula& qcnf2 ) const {
	ZDD Resolved = Resolution(zdd, qcnf2.universal_vars, index_map);
	Resolved = Resolution(zdd, qcnf2.existential_vars, index_map);
	Cudd mgr2;
	ZDD zeroTerminal = mgr2.zddZero();
	if (Resolved == zeroTerminal) {
		return 0;
	}
	return 1;
	
}

//substitution helper function: cross(z)

ZDD CNFtoZDDconverter::crossZDD(const ZDD& z) const {
	Cudd mgr0;
	//??????????????????????????
	// only ZDD parameter, or more parameters like literals?
	return mgr0.zddZero();

}

ZDD CNFtoZDDconverter::negCrossZDD(const ZDD& z) const {
	Cudd mgr0;
	//??????????????????????????
	return mgr0.zddZero();

}

// substitution function
ZDD CNFtoZDDconverter::CNFtoDNF_Substitution(Cudd& mgr, int y, std::unordered_map <int, int>& index_map, int maxVar, const ZDD& z, CnfFormula& cnf, std::vector<ZDD>& Clause_ZDDs) {
	
	int num_clauses = cnf.size();
	std::vector<ZDD> newClausesZDDs;
	for (int i = 0; i < num_clauses; i++) {
		
		if (std::find(cnf[i].begin(), cnf[i].end(), y) != cnf[i].end()) {
			// CASE 1: pos y occurs
			// cnf[i].
			ZDD Z_cl = ClausetoZDD(cnf[i], mgr, maxVar);//clause ZDD
			int posY = index_map[y];
			int negY = index_map[(-1)*y];
			//ZDD f_y_minus = Z_cl.Subset1(negY).Change(negY);//witness we select (assume g0)
			ZDD newClauseZDD = Z_cl.Subset0(posY);

			// cross
			ZDD clauseSubstitution = crossZDD(Z_cl).ClauseDistribution(newClauseZDD);
			newClausesZDDs.push_back(clauseSubstitution);

			
		} else if (std::find(cnf[i].begin(), cnf[i].end(), (-1)*y) != cnf[i].end()) {
			// CASE 2: neg y occurs in clause
			// 
			ZDD Z_cl = ClausetoZDD(cnf[i], mgr, maxVar);//clause ZDD
			int posY = index_map[y];
			int negY = index_map[(-1)*y];
			//ZDD f_y_minus = Z_cl.Subset1(negY).Change(negY);//witness we select (assume g0)
			ZDD newClauseZDD = Z_cl.Subset0(negY);

			// cross
			ZDD clauseSubstitution = negCrossZDD(Z_cl).ClauseDistribution(newClauseZDD);
			newClausesZDDs.push_back(clauseSubstitution);

		} 
		// CASE 3: neither pos y nor neg y occurs
		ZDD Z_cl = ClausetoZDD(cnf[i], mgr, maxVar);// clause ZDD
		newClausesZDDs.push_back(Z_cl);
	}

	ZDD substitutedZDD = newClausesZDDs[0];
	for (const ZDD& zdd : newClausesZDDs) {
		substitutedZDD = substitutedZDD.Union(zdd);
	}

	return substitutedZDD;
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
	std::unordered_map <int, int> indexToNodesMap = produceIndicesMap(maxVar);
	
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

	//check realizability
	partialRealizability(unionedZDDs);
	fullRealizability(unionedZDDs, indexToNodesMap, qcnf2);



	// draw the entire CNF's ZDD
	/*std::vector<char*> inames;
 	const std::vector<std::string> variable_labels;
	
	for (auto& nodepair : indexToNodesMap) {

		std::cout << nodepair.first;
		std::cout << " " << nodepair.second << std::endl;
		char* label = (char*)nodepair.first;
		variable_labels.push_back(label);
	}
	for (int i = 0; i < 2*maxVar; ++i) {
		std::string label = variable_labels[i];

		// Return value of label.c_str() is temporary, so need to make a copy
		inames[i] = new char[label.length() + 1]; // need space for '\0' terminator
		strcpy(inames[i], label.c_str());
	}
	for (auto& c : inames) {
		std::cout << c;
	}

	std::cout << "maxVar = " << maxVar << std::endl;
	*/
	ZDDtoDot(mgr, zdds, "ZDD.dot", NULL,NULL);
	
	// resolve on y variables and output the ZDD as .dot and .png
	//ZDD ResolvedZDD = Resolution(unionedZDDs, qcnf2.existential_vars, "resolved.dot", indexToNodesMap);
	ZDD ResolvedZDD = Resolution(unionedZDDs, qcnf2.existential_vars, indexToNodesMap);
	// core dumped before this line
	std::vector<ZDD> resolvedZdds = {ResolvedZDD};
	ZDDtoDot(mgr, resolvedZdds, "ResolvedZDD.dot", NULL,NULL);



	return;
	

}












