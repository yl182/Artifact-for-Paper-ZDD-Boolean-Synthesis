#include <sys/types.h>
#include <sys/time.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <math.h>
#include <stdlib.h>
#include <chrono>
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
CNFtoZDDconverter::CNFtoZDDconverter(bool writeDotFiles, bool printDetails) {
	writeDotFiles_ = writeDotFiles;
	printDetails_ = printDetails;
}


//timer
double CNFtoZDDconverter::timer(const std::chrono::steady_clock::time_point t1, const std::chrono::steady_clock::time_point t2) const {
	std::chrono::steady_clock::duration timespan = t2-t1;
	//std::cout << "timespan.count = " << timespan.count() << std::endl;
	//std::cout << "std::chrono::steady_clock::period::num" << std::chrono::steady_clock::period::num << std::endl;
	//std::cout << "std::chrono::steady_clock::period::den" << std::chrono::steady_clock::period::den << std::endl;
	double timeInSeconds = (double)timespan.count()  *  std::chrono::steady_clock::period::num / std::chrono::steady_clock::period::den;

	return timeInSeconds;
}




//template <typename T>
// notes: overloaded/multiple-signature functions must have equal number of parameters
// if use template: then printToCout(T a, bool newline) const, and
// in calling it must specify printToCout<int>(...) or printToCout<std::string>(...) everytime
void CNFtoZDDconverter::printToCout(std::string a, bool newline) const {
	if (printDetails_) {
		std::cout << a;
		if (newline) {
			std::cout << std::endl;
		}
	}
	return;
}

void CNFtoZDDconverter::printToCout(int a, bool newline) const {
	if (printDetails_) {
		std::cout << a;
		if (newline) {
			std::cout << std::endl;
		}
	}
	return;
}

void CNFtoZDDconverter::printToCout(double a, bool newline) const {
	if (printDetails_) {
		std::cout << a;
		if (newline) {
			std::cout << std::endl;
		}
	}
	return;
}
/*void CNFtoZDDconverter::printToCout(std::string a) const {
	if (printDetails_) {
		std::cout << a;
	}
	return;
}
void CNFtoZDDconverter::printToCout(int a) const {
	if (printDetails_) {
		std::cout << a;
	}
	return;
}*/
std::runtime_error CNFtoZDDconverter::EmptyFormulaException(const std::string& filepath) const {
	return std::runtime_error(filepath + ", formula is empty, 0 clause-ZDDs");
}		

//helper functions: given a reference of a clause, return the ZDD representing the clause
ZDD CNFtoZDDconverter::ClausetoZDD(const CnfClause& cl, Cudd& mgr, int maxRange) const {

	ZDD newZDDofClause = mgr.zddOne(2*maxRange);
	for (int i : cl) {
		newZDDofClause =newZDDofClause.Change(i);				
		printToCout("Change with Node ");
		printToCout(i, 1);
		
	}
// saved version
/*
	// draw ZDD for the clause
	ZDD newZDDofClause = mgr.zddVar(cl[0]);
	//return newZDDofClause;
	printToCout("Start with Node ", 0);
	printToCout(cl[0], 1);
	
	//std::vector<int> subset0list;
	//std::vector<int> changelist;
	
	// eliminate other variables
	for (int i = 0; i <= 2*maxRange-1; i++) {					
		if (i != cl[0]) {
			newZDDofClause = newZDDofClause.Subset0(i);			
			printToCout("Subset0 with Node ", 0);
			printToCout(i, 1);		
		}
	}
	// append other variables to the clause
	
	for (int i : cl) {
		if (i != cl[0]) {
			newZDDofClause =newZDDofClause.Change(i);				
			printToCout("Change with Node ");
			printToCout(i, 1);
		}
	}
*/
	// return the ZDD of the clause
	printToCout("Done Building ZDD for the clause above.", 1);
	
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
	int a=0;
	int b=0;
	if (qcnf.universal_vars.size() > 0) {
		printToCout("universal vars not empty.", 1);
		a = *std::max_element(qcnf.universal_vars.begin(), qcnf.universal_vars.end());
	}
	if (qcnf.existential_vars.size() > 0) {
		printToCout("existential vars not empty.", 1);
		b = *std::max_element(qcnf.existential_vars.begin(), qcnf.existential_vars.end());
	}
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
	printToCout("File Index\tNode Index", 1);
	for (auto& n : index_map) {
		printToCout(n.first);
		printToCout("\t");
		printToCout(n.second, 1);
	}
	return index_map;
}

//draw ZDD
void CNFtoZDDconverter::ZDDtoDot(Cudd& mgr, const std::vector<ZDD> z, const std::string dotfile, char** inames, char** onames) {
	
	
	if (writeDotFiles_) {
		printToCout("Output ZDD for the CNF above to file "+dotfile, 1);
		
		FILE * filepointer;
		filepointer = fopen(dotfile.c_str(), "w");
		if (filepointer != NULL) {
			mgr.DumpDot(z, inames, onames, filepointer);
			fclose(filepointer);
		} else {
			printf("File opening error: %s\n", strerror(errno));
		}
	}
	
	return;
	
	
}

//resolve a variable
ZDD CNFtoZDDconverter::Resolution(Cudd& mgr, const ZDD& zdd, const std::vector<int> y_vars) {
	ZDD resolvedZDD = zdd;
	std::vector<ZDD> tmpZDDs;
	for (int y : y_vars) {
		printToCout("Resolving for", 1);
		printToCout("y posY negY ", 1);
		int posY = indexConverter(y);
		int negY = indexConverter((-1)*y);
		printToCout(y);
		printToCout("\t");
		printToCout(posY);
		printToCout("\t");
		printToCout(negY, 1);
		
		// build ZDDs for f_y^+, f_y^-, f_y'
		
		ZDD f_y_plus = resolvedZDD.Subset1(posY);
		
		printToCout("To get f_y^+ for y = ");
		printToCout(y);
		printToCout(", subset1(");
		printToCout(posY);
		printToCout(").", 1);
		tmpZDDs = {f_y_plus};
		ZDDtoDot(mgr, tmpZDDs, "plusZDD_" + std::to_string(y) + ".dot", NULL, NULL);

		ZDD f_y_minus = resolvedZDD.Subset1(negY);
		printToCout("To get f_y^- for y = ");
		printToCout(y);
		printToCout(", subset1(");
		printToCout(negY);
		printToCout(").", 1); 
		tmpZDDs = {f_y_minus};
		ZDDtoDot(mgr, tmpZDDs, "minusZDD_" + std::to_string(y) + ".dot", NULL, NULL);

		ZDD f_y_prime = resolvedZDD.Subset0(posY).Subset0(negY);
		printToCout("To get f_y\' for y = ");
		printToCout(y);
		printToCout(", subset0(");
		printToCout(posY);
		printToCout("), subset0(");
		printToCout(negY);
		printToCout(").", 1); 
		tmpZDDs = {f_y_prime};
		ZDDtoDot(mgr, tmpZDDs, "primeZDD_" + std::to_string(y) + ".dot", NULL, NULL);

		printToCout("Done producing f_y_plus, f_y_minus, f_y_prime for y value above.", 1);
		
		ZDD f_y_plus_OR_f_y_minus = f_y_plus.ClauseDistribution(f_y_minus);
		printToCout("To get ZDD of (f_y^- or f_y^+):", 1);
		tmpZDDs = {f_y_plus_OR_f_y_minus};
		ZDDtoDot(mgr, tmpZDDs, "or_ZDD_" + std::to_string(y) + ".dot", NULL, NULL);

		printToCout("To get ZDD of (f_y^- or f_y^+) and f_y\'", 1);
		resolvedZDD = f_y_plus_OR_f_y_minus.SubSumptionFreeUnion(f_y_prime);
		tmpZDDs = {resolvedZDD};
		ZDDtoDot(mgr, tmpZDDs, "resolvedZDD_" + std::to_string(y) + ".dot", NULL, NULL);
		printToCout("Done resolving.", 1);
		
	}
	// core dumped before this line
	return resolvedZDD;
}

// check partial realizability
std::vector<std::string> CNFtoZDDconverter::checkFullPartialRealizability(Cudd& mgr, const ZDD& zdd, QCnfFormula& qcnf2, std::vector<double>& timerNoter) {
	std::vector<std::string> fullPartial;

	// check full realizability
	printToCout("Checking Partial Realizability: ", 1);

	// timer set up
	std::chrono::steady_clock::time_point tBeforeRealizability = std::chrono::steady_clock::now();
	printToCout("got tBeforeRealizability time", 1);


	ZDD resolvedYs = Resolution(mgr, zdd, qcnf2.existential_vars);

	// time point after resolving Y's
	std::chrono::steady_clock::time_point tAfterResolvingYs = std::chrono::steady_clock::now();

	// compare ZDD-0 with resolvedY
	std::vector<ZDD> resolvedYsZdds = {resolvedYs};
	ZDDtoDot(mgr, resolvedYsZdds, "ResolvedYsZDD.dot", NULL,NULL);
	ZDD zeroTerminal = mgr.zddZero();

	// judge full realizability
	if (resolvedYs == zeroTerminal) {
		// not fully realizable
		printToCout("Full Realizability: YES", 1);
		fullPartial.emplace_back("YES");
	} else {
		// fully realizable
		printToCout("Full Realizability: NO", 1);
		fullPartial.emplace_back("NO");
	}
	
	// time point after resolving Y's and comparison (full realizability)

	std::chrono::steady_clock::time_point tFullRealizabilityDone = std::chrono::steady_clock::now();
	double tFull = timer(tBeforeRealizability, tFullRealizabilityDone);
	double tResolvingY = timer(tBeforeRealizability, tAfterResolvingYs);
	timerNoter.emplace_back(tFull);

	printToCout("got tAfterResolvingYs time", 1);
	printToCout("Full Realizability time: ", 0);
	printToCout(tFull, 0);
	printToCout(" seconds.", 1);
	

	// time point before resolving X's
	std::chrono::steady_clock::time_point tBeforeResolvingXs = std::chrono::steady_clock::now();

	// check partial realizability
	ZDD resolvedYsXs = Resolution(mgr, resolvedYs, qcnf2.universal_vars);

	// time point after resolving X's
	std::chrono::steady_clock::time_point tAfterResolvingXs = std::chrono::steady_clock::now();
	//double tYandXs = timer(tBeforeRealizability, tAfterResolvingXs);
	//timerNoter.emplace_back(tYandXs);

	std::vector<ZDD> resolvedYsXsZdds = {resolvedYsXs};
	ZDDtoDot(mgr, resolvedYsXsZdds, "ResolvedYsXsZDD.dot", NULL,NULL);
	
	if (resolvedYsXs == zeroTerminal) {
		// partially realizable
		printToCout("Partial Realizability: YES", 1);
		fullPartial.emplace_back("YES");
	} else {
		// partially NOT realizable
		printToCout("Partial Realizability: NO", 1);
		fullPartial.emplace_back("NO");
	}
	// time point after resolving X's and comparison with 0-ZDD (partial realizability done)
	std::chrono::steady_clock::time_point tPartialRealizabilityDone = std::chrono::steady_clock::now();

	// add resolvingXtime + resolvingYtime + comparing = time for checking partial realizability
	double tPartial = timer(tBeforeResolvingXs, tPartialRealizabilityDone)+timer(tBeforeRealizability,tAfterResolvingYs);
	timerNoter.emplace_back(tPartial);
	
	printToCout("got tAfterResolvingXs time", 1);
	printToCout("Partial Realizability time: ", 0);
	printToCout(tPartial, 0);
	printToCout(" seconds.", 1);
	


	return fullPartial;
	
}

//substitution helper function: cross(z)

ZDD CNFtoZDDconverter::crossZDD(const ZDD& z) const {
	printToCout("no errors until this line000111", 1);
	Cudd mgr0;

	//??????????????????????????
	// only ZDD parameter, or more parameters like literals?
	printToCout("no errors until this line000222", 1);
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
			printToCout("after calling crossZDD() the first time in substitution function", 1);
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

	printToCout("\n\nQReader reading from file: "+path, 1);
	std::vector<double> timerNoter;
	std::chrono::steady_clock::time_point tStart = std::chrono::steady_clock::now();
	printToCout("got tStart time", 1);

	// get variables
	QDimacsReader qreader;
	QCnfFormula qcnf = qreader.Read(path);
	
	printToCout("Got QCnfFormula, \nUniversal variables are: ");
	for (int i : qcnf.universal_vars) {
		printToCout(" ");
		printToCout(i);
	}
	printToCout("\nExistential variables are:");
	for (int i : qcnf.existential_vars) {
		printToCout(" ");
		printToCout(i);
	}
	printToCout("", 1);

	// get formula
	CnfFormula cnf = qcnf.formula;
	const int nClauses = cnf.size();

	printToCout("There are ");
	printToCout(nClauses);
	printToCout("clauses in the CNF.", 1);
	printToCout("CNF (by File Index) is: ", 1);

	// build another CNF with Node Indices
	CnfFormula cnf2;
	for (CnfClause c : cnf) {
		CnfClause cl;
		for (int i : c) {
			printToCout(i);
			printToCout(", ");
			cl |= indexConverter(i);
		}
		printToCout("", 1);
		cnf2 &= cl;
	}
	printToCout("End of CNF (by File Index).", 1);
	printToCout("CNF (by Node Index) is: ", 1);
	for (CnfClause c : cnf2) {
		for (int i : c) {
			printToCout(i);
			printToCout(", ");
		}
		printToCout("", 1);
	}
	printToCout("End of CNF (by Node Index).", 1);

	
	
	// get the largest absolute value in given variable indices
	
	int maxVar = maxVarRange(qcnf);
	printToCout("Noticed largest range ");
	printToCout(maxVar, 1);
	
	
	// produce map of given indices and node indices
	//
	//std::unordered_map <int, int> indexToNodesMap = produceIndicesMap(maxVar);

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
		printToCout("formula is empty, 0 clause-ZDDs", 1);
		throw EmptyFormulaException(path); 
	}
	printToCout("Unioning ZDDs of clauses above.", 1);
	ZDD unionedZDDs = clauseZDDs[0];
	for (const ZDD& zdd : clauseZDDs) {
		unionedZDDs = unionedZDDs.Union(zdd);
	}
	std::vector<ZDD> zdds = {unionedZDDs};
	ZDDtoDot(mgr, zdds, "ZDD.dot", NULL,NULL);

	// count compilation time
	std::chrono::steady_clock::time_point tZDDdone = std::chrono::steady_clock::now();
	double timeCompilation = timer(tStart, tZDDdone);
	printToCout("got tZDDdone time", 1);
	printToCout("Compilation time: ", 0);
	printToCout(timeCompilation, 0);
	printToCout(" seconds.", 1);
	timerNoter.emplace_back(timeCompilation);
	

	

	//check realizability
	
	std::vector<std::string> fullPartial = checkFullPartialRealizability(mgr, unionedZDDs, qcnf, timerNoter);
	printToCout("Filename\tFull\tPartial\tCompilationTime\tFullRealizabilityTime\tPartialRealizabilityTime: ", 1);
	printToCout(path+"\t");
	printToCout(fullPartial[0]+"\t"+fullPartial[1] + "\t", 0);
	printToCout(timerNoter[0], 0);
	printToCout(" sec\t", 0);
	printToCout(timerNoter[1], 0);
	printToCout(" sec\t", 0);
	printToCout(timerNoter[2], 0);
	printToCout(" sec\t", 1);


	
	std::ofstream out("results.txt", std::ios_base::app);
	out << "Filename\tFull\tPartial\tCompilationTime\tFullRealizabilityTime\tPartialRealizabilityTime: \n";
	out << path << "\t" << fullPartial[0] << "\t" << fullPartial[1] << "\t" << timerNoter[0] << " sec\t" << timerNoter[1] << " sec\t" << timerNoter[2] << " sec" << std::endl;
	out.close();

	return;
	

}












