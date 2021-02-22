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
ZDD CNFtoZDDconverter::ClausetoZDD(const CnfClause& cl, Cudd& mgr, int maxRange) const {

	

	// draw ZDD for the clause
	ZDD newZDDofClause = mgr.zddVar(cl[0]);
	//return newZDDofClause;
	std::cout << "Start with Node " << cl[0] << std::endl;
	
	//std::vector<int> subset0list;
	//std::vector<int> changelist;
	
	// eliminate other variables
	for (int i = 0; i <= 2*maxRange; i++) {					
		if (i != cl[0]) {
			newZDDofClause = newZDDofClause.Subset0(i);
			std::cout << "Subset0 with Node " << i << std::endl;
			
		}
	}
	
	

	// append other variables to the clause
	
	for (int i : cl) {
		if (i != cl[0]) {
			newZDDofClause =newZDDofClause.Change(i);	
			std::cout << "Change with Node " << i << std::endl;
		}
	}

	// return the ZDD of the clause
	std::cout << "Done Building ZDD for the clause above." << std::endl;
	
	return newZDDofClause;
}

// helper function: given index->node index
int CNFtoZDDconverter::indexConverter(int g) {
	// example: +10, -10 => 18,19, 
	// example: +1,-1 => 0, 1
	// +n, -n => (2n-2), (2n-1)
	if (g < 0) {
		return (-1)*g*2-1;
	} else {
		return 2*g-2;
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
	std::cout << "File Index\tNode Index" << std::endl;
	for (auto& n : index_map) {
		std::cout << n.first << "\t" << n.second << std::endl;
	}
	return index_map;
}

//draw ZDD
void CNFtoZDDconverter::ZDDtoDot(Cudd& mgr, const std::vector<ZDD> z, const std::string dotfile, char** inames, char** onames) {
	std::cout << "Output ZDD for the CNF above to file " << dotfile << std::endl;
	mgr.DumpDot(z, inames, onames, fopen(dotfile.c_str(), "w"));
}

//resolve a variable
ZDD CNFtoZDDconverter::Resolution(Cudd& mgr, const ZDD& zdd, const std::vector<int> y_vars) {
	ZDD resolvedZDD;
	for (int y : y_vars) {
		std::cout << "Resolving for" << std::endl;
		std::cout << "y posY negY " << std::endl;
		int posY = indexConverter(y);
		int negY = indexConverter((-1)*y);
		std::cout << y << " " << posY << " " << negY << std::endl;
		
		// build ZDDs for f_y^+, f_y^-, f_y'
		std::vector<ZDD> tmpZDDs;
		ZDD f_y_plus = zdd.Subset1(posY);
		
		std::cout << "To get f_y^+ for y = " << y << ", subset1(" << posY << ")." << std::endl; 
		tmpZDDs = {f_y_plus};
		ZDDtoDot(mgr, tmpZDDs, "plusZDD_" + std::to_string(y) + ".dot", NULL, NULL);

		ZDD f_y_minus = zdd.Subset1(negY);
		std::cout << "To get f_y^- for y = " << y << ", subset1(" << negY << ")." << std::endl; 
		tmpZDDs = {f_y_minus};
		ZDDtoDot(mgr, tmpZDDs, "minusZDD_" + std::to_string(y) + ".dot", NULL, NULL);

		ZDD f_y_prime = zdd.Subset0(posY).Subset0(negY);
		std::cout << "To get f_y\' for y = " << y << ", subset0(" << posY << "), subset0(" << negY << ")." << std::endl; 
		tmpZDDs = {f_y_prime};
		ZDDtoDot(mgr, tmpZDDs, "primeZDD_" + std::to_string(y) + ".dot", NULL, NULL);

		std::cout << "Done producing f_y_plus, f_y_minus, f_y_prime for y value above." << std::endl;
		//std::cout << "before going into clauseDistribution function in cuddObj.c" << std::endl;
		// core dumped after this line in first iteration
		
		//std::cout << "after first step of clauseDistribution function in cuddObj.c\nnow manager is: " << (mgr == NULL) << std::endl;
		ZDD f_y_plus_OR_f_y_minus = f_y_plus.ClauseDistribution(f_y_minus);
		std::cout << "To get ZDD of (f_y^- or f_y^+):" << std::endl;
		tmpZDDs = {f_y_plus_OR_f_y_minus};
		ZDDtoDot(mgr, tmpZDDs, "or_ZDD_" + std::to_string(y) + ".dot", NULL, NULL);

		std::cout << "To get ZDD of (f_y^- or f_y^+) and f_y\'" << std::endl;
		resolvedZDD = f_y_plus_OR_f_y_minus.SubSumptionFreeUnion(f_y_prime);
		tmpZDDs = {resolvedZDD};
		ZDDtoDot(mgr, tmpZDDs, "resolvedZDD_" + std::to_string(y) + ".dot", NULL, NULL);
		std::cout << "Done resolving." << std::endl;
		
	}
	// core dumped before this line
	return resolvedZDD;
}

// check partial realizability
bool CNFtoZDDconverter::partialRealizability(Cudd& mgr, const ZDD& zdd,QCnfFormula& qcnf2) {
	std::cout << "Checking Partial Realizability: " << std::endl;
	ZDD resolved = Resolution(mgr, zdd, qcnf2.existential_vars);
	std::cout << "Count = " << resolved.Count() << std::endl;
	// it is confirmed that when empty clause satisfies CNF, Count = 1, when no clauses satisfies CNF, Count = 0
	// so Count() can be used to count the number of path to terminal-1
	// i.e., partial realizability
	if (resolved.Count() > 0) {
		std::cout << "Partial Realizability: YES" << std::endl;
		return 1;
	} else {
		std::cout << "Partial Realizability: NO" << std::endl;
		return 0;
	}
}
// check full realizability
bool CNFtoZDDconverter::fullRealizability(Cudd& mgr, const ZDD& zdd, QCnfFormula& qcnf2 ) {
	ZDD Resolved = Resolution(mgr, zdd, qcnf2.existential_vars);
	
	ZDD zeroTerminal = mgr.zddZero();
	if (Resolved == zeroTerminal) {
		// not fully realizable
		std::cout << "Full Realizability: NO" << std::endl;
		return 0;
	}
	// fully realizable
	std::cout << "Full Realizability: Yes" << std::endl;
	return 1;
	
}

//substitution helper function: cross(z)

ZDD CNFtoZDDconverter::crossZDD(const ZDD& z) const {
	std::cout << "no errors until this line000111" << std::endl;
	Cudd mgr0;

	//??????????????????????????
	// only ZDD parameter, or more parameters like literals?
	std::cout << "no errors until this line000222" << std::endl;
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
			ZDD clauseSubstitution = crossZDD(Z_cl);
			std::cout << "no errors until this line000" << std::endl;
			clauseSubstitution = clauseSubstitution.ClauseDistribution(newClauseZDD);
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

	std::cout << "\n\nQReader reading from file: " << path << std::endl;
	// get variables
	QDimacsReader qreader;
	QCnfFormula qcnf = qreader.Read(path);
	
	std::cout << "Got QCnfFormula, \nUniversal variables are: ";
	for (int i : qcnf.universal_vars) {
		std::cout << " " << i;
	}
	std::cout << "\nExistential variables are:";
	for (int i : qcnf.existential_vars) {
		std::cout << " " << i;
	}
	std::cout << std::endl;

	// get formula
	CnfFormula cnf = qcnf.formula;
	const int nClauses = cnf.size();

	std::cout << "There are " << nClauses << "clauses in the CNF." << std::endl;
	std::cout << "CNF (by File Index) is: " << std::endl;

	// build another CNF with Node Indices
	CnfFormula cnf2;
	for (CnfClause c : cnf) {
		CnfClause cl;
		for (int i : c) {
			std::cout << i << ", ";
			cl |= indexConverter(i);
		}
		std::cout << std::endl;
		cnf2 &= cl;
	}
	std::cout << "End of CNF (by File Index)." << std::endl;
	std::cout << "CNF (by Node Index) is: " << std::endl;	
	for (CnfClause c : cnf2) {
		for (int i : c) {
			std::cout << i << ", ";
		}
		std::cout << std::endl;
	}
	std::cout << "End of CNF (by Node Index)." << std::endl;

	
	
	// get the largest absolute value in given variable indices
	
	int maxVar = maxVarRange(qcnf);
	std::cout << "Noticed largest range " << maxVar << std::endl;
	
	
	// produce map of given indices and node indices
	std::unordered_map <int, int> indexToNodesMap = produceIndicesMap(maxVar);

	// draw ZDDs of the i-th clause
	Cudd mgr;
	
	// initiate a vector of clause-ZDDs
	std::vector<ZDD> clauseZDDs;
	
	int j = 1;
	std::vector<ZDD> tmpZDDvec;
	ZDD Z_cl;
	// iterate over clauses, build ZDDs and add them to Clause_ZDDs
	for (const CnfClause& clause : cnf2) {
		Z_cl = ClausetoZDD(clause, mgr, maxVar);
		// add the ZDD of this clause to the vector of ZDDs
		tmpZDDvec = {Z_cl};
		ZDDtoDot(mgr, tmpZDDvec, "ZDD"+std::to_string(j)+".dot", NULL,NULL);
		j++;
		clauseZDDs.emplace_back(Z_cl);
	}

	// union the clause-zdds into ZDD of the CNF
	if (clauseZDDs.size() <= 0) {
		std::cout << "formula is empty, 0 clause-ZDDs" << std::endl;
		throw EmptyFormulaException(path); 
	}
	std::cout << "Unioning ZDDs of clauses above." << std::endl;
	ZDD unionedZDDs = clauseZDDs[0];
	for (const ZDD& zdd : clauseZDDs) {
		unionedZDDs = unionedZDDs.Union(zdd);
	}
	std::vector<ZDD> zdds = {unionedZDDs};
	ZDDtoDot(mgr, zdds, "ZDD.dot", NULL,NULL);
	

	

	//check realizability
	
	partialRealizability(mgr, unionedZDDs, qcnf);
	fullRealizability(mgr, unionedZDDs,qcnf);

	// resolve on y variables and output the ZDD as .dot and .png
	
	ZDD ResolvedZDD = Resolution(mgr, unionedZDDs, qcnf.existential_vars);
	// core dumped before this line
	
	std::vector<ZDD> resolvedZdds = {ResolvedZDD};
	ZDDtoDot(mgr, resolvedZdds, "ResolvedZDD.dot", NULL,NULL);
	std::cout << "\n\n";
	



	return;
	

}












