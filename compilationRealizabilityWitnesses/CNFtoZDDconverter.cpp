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
#include <unordered_set>
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

/*
ZDD CNFtoZDDconverter::convertToNegative(const ZDD& zdd) {
	

}
*/

// function to construct ZDD for f_y^-
ZDD CNFtoZDDconverter::constructCNFWitness(Cudd& mgr, const ZDD& zdd, int y) {
	
		
		printToCout("Constructing CNF witness f_y^- for y = " + std::to_string(y), 1);
		printToCout("y posY negY ", 1);
		int posY = indexConverter(y);
		int neg_Y = indexConverter((-1)*y);
		printToCout(y);
		printToCout("\t");
		printToCout(posY);
		printToCout("\t");
		printToCout(neg_Y, 1);
		
		// build ZDDs for CNF witness f_y^-
		ZDD witnessCNF = zdd.Subset1(neg_Y);
		std::vector<ZDD> tmpZDDs;
		tmpZDDs = {witnessCNF};
		ZDDtoDot(mgr, tmpZDDs, "CNFwitnessY_" + std::to_string(y) + ".dot", NULL, NULL);
		return witnessCNF;
		
}

// function to construct get ZDD for f_y^+
ZDD CNFtoZDDconverter::constructZDDforFYminus(Cudd& mgr, const ZDD& zdd, int y) {
	
		
		printToCout("Constructing f_y^+ for y = " + std::to_string(y), 1);
		printToCout("y posY negY ", 1);
		int pos_Y = indexConverter(y);
		int neg_Y = indexConverter((-1)*y);
		printToCout(y);
		printToCout("\t");
		printToCout(pos_Y);
		printToCout("\t");
		printToCout(neg_Y, 1);
		
		// build ZDDs for CNF witness f_y^-
		ZDD witnessCNF = zdd.Subset0(pos_Y);
		std::vector<ZDD> tmpZDDs;
		tmpZDDs = {witnessCNF};
		ZDDtoDot(mgr, tmpZDDs, "f_y_plus_helperZDD_" + std::to_string(y) + ".dot", NULL, NULL);
		return witnessCNF;
		
}



// MCS ordering
std::vector<int> CNFtoZDDconverter::MCSordering(const QCnfFormula qcnf) const {
	// CNF by file indices
	CnfFormula cnf = qcnf.formula;
	//const int nClauses = cnf.size();
	std::unordered_map<int, std::unordered_set<int>> MCSmap;
	
	
	
	// insert neighbors into map
	// note: for variables with no neighbors, there are no keys of the same name in MCSmap
	for (CnfClause c : cnf) {
		for (int i : c) {
			for (int j : c) {
				if (j != i) {
					MCSmap[abs(i)].emplace(abs(j));
					printToCout("inserting to MCSmap: KEY: ");
					printToCout(abs(i));
					printToCout(", VALUE: ");
					printToCout(abs(j), 1);
				}
			}
		}
	}


	// print MCSmap
	printToCout("NOW print all K,V pairs", 1);
	for (auto it=MCSmap.begin(); it != MCSmap.end(); it++) {
		printToCout(" KEY: ");
		printToCout(it->first);
		printToCout(", VALUES: ");
		for (int in : it->second){
			printToCout(in);
			printToCout(" ");
		}  
		printToCout("", 1);
	}

	// construct count map
	std::vector<std::pair<int, int>> MCScount;
	

	// add variables without neighbors to MCScount
	for (int u : qcnf.universal_vars) {
		if (MCSmap.count(u) == 0) {
			MCScount.emplace_back(std::make_pair(u, 0));
			printToCout(" KEY: ");
			printToCout(u);
			printToCout(", COUNT: ");
			printToCout(0, 1);
		}
		
	}
	for (int e : qcnf.existential_vars) {
		if (MCSmap.count(e) == 0) {
			MCScount.emplace_back(std::make_pair(e, 0));
			printToCout(" KEY: ");
			printToCout(e);
			printToCout(", COUNT: ");
			printToCout(0, 1);
		}
	}

	// count neighbors in a factor/clause/support
	
	for (auto it=MCSmap.begin(); it != MCSmap.end(); it++) {
		printToCout(" KEY: ");
		printToCout(it->first);
		printToCout(", COUNT: ");
		printToCout((int)it->second.size(), 1);
		MCScount.emplace_back(std::make_pair(it->first, it->second.size() ));
	}
	int tmpMax = 0;
	int maxKey = 0;
	int iterations = 0;
	tmpMax = MCScount.begin()->second;
	
	//return the MCS ordering
	std::vector<int> MCSorderingIndices;
	int initSize = MCScount.size();
	while (iterations < initSize) {
		int i = 0;
		auto tmpIt = MCScount.begin();
		maxKey = 0;
		tmpMax = 0;
		for (auto it = MCScount.begin(); it != MCScount.end(); it++) {
			printToCout("comparing KEY ");
			printToCout(it->first);
			printToCout(" with ");
			printToCout(MCScount[maxKey].first, 1);

			printToCout("VALUE ");
			printToCout(it->second);
			printToCout(" with VALUE ");
			printToCout(MCScount[maxKey].second, 1);
			if (tmpMax < MCScount[i].second) {
				tmpMax = MCScount[i].second;
				maxKey = i;
				tmpIt = it;
				printToCout("update tmpMax=");
				printToCout(MCScount[i].second);
				printToCout(", maxKey=");
				printToCout(maxKey);
				printToCout(", tmpIt points to KEY=");
				printToCout(it->first, 1);
			}
			i++;
		}
		MCSorderingIndices.emplace_back(MCScount[maxKey].first);
		printToCout("push ");
		printToCout(MCScount[maxKey].first);
		printToCout(" back to MCSordering", 1);
		MCScount.erase(tmpIt);
		iterations++;
	}
	
	// printing
	printToCout("MCS ordering: ");
	std::cout << "MCS ordering: ";
	for (int i : MCSorderingIndices) {
		printToCout(i);
		printToCout(" ");
		std::cout << i << " ";
	}
	printToCout("", 1);
	std::cout << std::endl;
	return MCSorderingIndices;
	
}


//timer
double timer(const std::chrono::steady_clock::time_point t1, const std::chrono::steady_clock::time_point t2) {
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
ZDD CNFtoZDDconverter::Resolution(Cudd& mgr, const ZDD& zdd, const std::vector<int>& y_vars, const std::vector<int>& mcsOrder, std::vector<ZDD>& intermediateZDDs, std::vector<int>& resolveOrder) {
	std::cout << "RESOLVING Scope: ";
	for (int y : y_vars) {
		std::cout << y << " ";
	}
	std::cout <<std::endl;
	

	for (int i : mcsOrder) {
		if (find(y_vars.begin(), y_vars.end(), i) != y_vars.end()) {
			resolveOrder.push_back(i);
		}
	}

	ZDD resolvedZDD = zdd;
	std::vector<ZDD> tmpZDDs;
	for (int y : resolveOrder) {
		std::cout << "Resolving for y=" << y << std::endl;
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

		intermediateZDDs.emplace_back(resolvedZDD);
		
	}
	// core dumped before this line
	return resolvedZDD;
}

// check partial realizability
std::vector<std::string> CNFtoZDDconverter::checkFullPartialRealizability(Cudd& mgr, const ZDD& zdd, QCnfFormula& qcnf2, std::vector<double>& timerNoter, std::vector<int>& mcsOrder, std::vector<ZDD>& intermediateZDDs, std::vector<int>& resolvedYsIndices) {
	std::vector<std::string> fullPartial;

	// check full realizability
	printToCout("Checking Partial Realizability: ", 1);

	// timer set up
	std::chrono::steady_clock::time_point tBeforeRealizability = std::chrono::steady_clock::now();
	printToCout("got tBeforeRealizability time", 1);

	ZDD resolvedYs = Resolution(mgr, zdd, qcnf2.existential_vars, mcsOrder, intermediateZDDs, resolvedYsIndices);

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
	std::vector<ZDD> tmp1 = {};
	std::vector<int> tmp2 = {};
	ZDD resolvedYsXs = Resolution(mgr, resolvedYs, qcnf2.universal_vars, mcsOrder, tmp1, tmp2);

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
ZDD CNFtoZDDconverter::crossZDD(const ZDD& z, Cudd& mgr) const {
	int rootIndex = z.NodeReadIndex();
	ZDD zdd0 = mgr.zddZero();
	ZDD zdd1 = mgr.zddOne(5);
	if (zdd0 == z) {
		return zdd1;
	}
	if (z.Count() == 0) {
		return zdd0;
	}
	// 0-child sub-ZDD of z
	ZDD zleft = z.Subset0(rootIndex);
	// 1-child sub-ZDD of z
	ZDD zright = z.Subset1(rootIndex).Change(rootIndex);
	// new z_r = ZDDunion(Z_l, Z_r)
	ZDD z_r = zleft.Union(zright);
	// new z_ll = cross(Z_r)
	ZDD z_ll = crossZDD(z_r, mgr);
	// update z_r = cross(zright)
	z_r = crossZDD(zleft, mgr);
	// new z_hh = nonsup(z_r, z_ll)
	ZDD z_hh = nonsup(mgr, z_r, z_ll);
	// return new z' = newZDD(rootnode, z_ll, z_hh)
	return z.Ite(z_ll, z_hh);


	//std::cout << z.NodeReadIndex() << std::endl;
	//std::cout << z.printRootIndex() << std::endl;
	return z;
	
}
ZDD CNFtoZDDconverter::nonsup(Cudd& mgr, const ZDD& z_this, const ZDD& z) const {
	// implemented as DIFF function (speedup version of nonsup)
	ZDD z0 = mgr.zddZero();
	if (z ==z0) {
		return z_this;
	}
	if ( (z_this == z0) or (z.Count() == 0) or (z_this == z)) {
		return z0;
	}
	// f_v, g_v as indices of rootnodes
	int f_v = z_this.NodeReadIndex();
	int g_v = z.NodeReadIndex();
	ZDD g_l = z.Subset0(g_v);
	ZDD f_l = z_this.Subset0(f_v);
	ZDD f_h = z_this.Subset1(f_v).Change(f_v);
	ZDD g_h = z.Subset1(g_v).Change(g_v);
	ZDD r_l, r_h; // new ZDDs for constructing return value
	if (f_v > g_v) {
		return nonsup(mgr, z_this, g_l);
	} 
	if (f_v < g_v) {
		r_l = nonsup(mgr, f_l, z);
		r_h = f_h;
	} else {
		r_l = nonsup(mgr, f_l, g_l);
		r_h = nonsup(mgr, f_h, g_h);
	}
	return z_this.Ite(r_l, r_h);
}

// function to negate indices (returns the ZDD )
ZDD CNFtoZDDconverter::negateDnfZDD(const ZDD& z, int maxVar, std::vector<int>& ys, Cudd& mgr) {
	int a,b;
	ZDD z1, tmpZ;
	tmpZ = z;
	for (int y : ys) {
		a = indexConverter(y);
		b = indexConverter((-1)*y);
		// replace x+1: 1,3,5,... to 2*maxVar+themselves
		z1 = tmpZ.Subset0(b).SubSumptionFreeUnion(z.Subset1(b).Change(2*maxVar+b)); // since subset1 already removes b from clauses
		// p to not p
		z1 = z1.Subset1(a).Change(b).SubSumptionFreeUnion(z1.Subset0(a));
		// not p to p
		z1 = z1.Subset1(2*maxVar+b).Change(a).SubSumptionFreeUnion(z1.Subset0(2*maxVar+b));
		tmpZ = z1;
	}
	return tmpZ;
}


// substitution function
// actually not calling this function in final version
/*
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
*/
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

	// produce MCS ordering:
	std::vector<int> mcs = MCSordering(qcnf);


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

	// count number of nodes in ZDD of formula
    int ZDDNodeCount = unionedZDDs.nodeCount();


	// count compilation time
	std::chrono::steady_clock::time_point tZDDdone = std::chrono::steady_clock::now();
	double timeCompilation = timer(tStart, tZDDdone);
	printToCout("got tZDDdone time", 1);
	printToCout("Compilation time: ", 0);
	printToCout(timeCompilation, 0);
	printToCout(" seconds.", 1);
	timerNoter.emplace_back(timeCompilation);
	

	//timenoter: 0:compilation, 1:full, 2:partial, 3: realizability, 4:

	//check realizability
	std::vector<ZDD> intermediateZDDs = {};
	std::vector<int> resolvedYsIndices = {};
	std::vector<std::string> fullPartial = checkFullPartialRealizability(mgr, unionedZDDs, qcnf, timerNoter, mcs, intermediateZDDs, resolvedYsIndices);

	// count realizability time
	std::chrono::steady_clock::time_point tEndOfRealizability = std::chrono::steady_clock::now();
	double timeForRealizability = timer(tZDDdone, tEndOfRealizability);
	timerNoter.emplace_back(timeForRealizability);

	

	

	// start construction of witnesses
	// suppose order of y's are MCS ordering
	// intermediateZDDs in order
	// resolvedYsIndices y's in order

	int n = intermediateZDDs.size();
	int n2 = resolvedYsIndices.size();
	printToCout(n, 0);
	printToCout(n2, 0);
	int countSteps;
	
	std::vector<ZDD> witnesses = {};
	std::vector<ZDD> crossWitnesses = {};
	std::vector<int> witnessIndices = {};
	ZDD wCNF, wDNF, neg_wDNF;
	ZDD currentZDD, nextZDD;
	ZDD tmpZDD, tmp2ZDD;
	countSteps = 0;
	while (countSteps < n) {
		currentZDD = intermediateZDDs[n-countSteps-1]; // phi_i, which has only one y_i
		int currentY = resolvedYsIndices[n-countSteps-1];
		//	substitutions for previous positive y's
		for (int i = 0; i < countSteps; i++) {
			// for positive occurrences of y
			// clause distribution between f_y^+ and CNF witness
			// then union 
			tmpZDD = constructZDDforFYminus(mgr, currentZDD, witnessIndices[i]);
			//currentZDD.Subset0(indexy)
			tmp2ZDD = currentZDD.Subset0(indexConverter(currentY));
			// use substitution to update the ZDD
			currentZDD = tmpZDD.ClauseDistribution(witnesses[i]).SubSumptionFreeUnion(tmp2ZDD);
		}
		//substitutions for previous negative y's

		for (int i = 0; i < countSteps; i++) {
			// for negative occurrences of y's
			// 1. cross: CNF witness -> DNF witness
			wDNF = crossWitnesses[i];

			// 2. negate, since occurrences are neg y, by switching the indices to their partner-indices
			neg_wDNF = negateDnfZDD(wDNF, maxVar, resolvedYsIndices,mgr);
			// 3. f_y^- clauseDistribution with witness (result of step 2), and then subsumptionfreeunion with subset0(neg y)
			tmpZDD = currentZDD.Subset1(indexConverter(currentY*(-1)));
			tmp2ZDD = currentZDD.Subset0(indexConverter(currentY*(-1)));
			currentZDD = tmpZDD.ClauseDistribution(wDNF).SubSumptionFreeUnion(tmp2ZDD);
		}
		// now currentZDD up-to-date with only 1 y
		// update witness
		wCNF = constructCNFWitness(mgr, currentZDD, currentY);
		//cross: CNF witness -> DNF witness
		wDNF = crossZDD(wCNF, mgr);

		witnesses.emplace_back(wCNF);
		crossWitnesses.emplace_back(wDNF);
		witnessIndices.emplace_back(currentY);

		countSteps++;
	}
	for (int j = 0; j < n; j++) {
		// note: only output CNF witness
		ZDDtoDot(mgr, {witnesses[j]}, "CNFwitness_"+ std::to_string(witnessIndices[j]) +".dot", NULL, NULL);
		printToCout("Outputting CNF witness for "+std::to_string(witnessIndices[j])+"to ZDD in dotFile.", 1);
	}

	// count time for synthesis
	std::chrono::steady_clock::time_point tEndOfSynthesis = std::chrono::steady_clock::now();
	double timeForSynthesis = timer(tEndOfRealizability, tEndOfSynthesis);
	timerNoter.emplace_back(timeForSynthesis); // timeNoter[4], time for synthesis

	// print out and results
	printToCout("Filename\tFull\tPartial\tCompilationTime\tFullRealizabilityTime\tPartialRealizabilityTime\tRealizabilityTime\tSynthesisTime\tZDDFormulaSize\tPeakNodeCount\tPeakMemoryInUse: ", 1);
	printToCout(path+":\n");//filename
	printToCout(fullPartial[0]+"\t"+fullPartial[1] + "\t", 0);//full partial
	printToCout(timerNoter[0], 0);//compilation time
	printToCout(" sec\t", 0);
	printToCout(timerNoter[1], 0);//full time
	printToCout(" sec\t", 0);
	printToCout(timerNoter[2], 0);//partial time
	printToCout(" sec\t", 0);
	printToCout(timerNoter[3], 0);//Realizability total time
	printToCout(" sec\t", 0);
	printToCout(timerNoter[4], 0);//Synthesis time
	printToCout(" sec\t", 0);
	
	// ZDD Size of Formula
	printToCout(ZDDNodeCount, 0);//ZDD formula size
	printToCout(" nodes\t", 0);
	// peak node count
	printToCout((double)mgr.ReadPeakNodeCount(), 0);//peak node count
	printToCout(" nodes\t", 0);
	// peak memory in use
	printToCout((double)mgr.ReadMemoryInUse(), 0);//peak memory count
	printToCout(" bytes\t", 1);

	
	std::ofstream out("resultsSynthesis.txt", std::ios_base::app);
	//out << "Filename\tFull\tPartial\tCompilationTime(ms)\tFullRealizabilityTime(ms)\tPartialRealizabilityTime(ms)\tRealizabilityTime(ms)\tSynthesisTime(ms)\tZDDFormulaSize(nodes)\tPeakNodeCount(nodes)\tPeakMemoryInUse:(bytes) \n";
	out << path << "\t" << fullPartial[0] << "\t" << fullPartial[1] << "\t" << timerNoter[0]*1000 << " ms\t" << timerNoter[1]*1000 << " ms\t" << timerNoter[2]*1000 << " ms\t" << timerNoter[3]*1000 << " ms\t" << timerNoter[4]*1000 << " ms\t" << ZDDNodeCount << " nodes\t" << (double)mgr.ReadPeakNodeCount() << " nodes\t" << (double)mgr.ReadMemoryInUse() << " bytes" << std::endl;
	out.close();

	std::ofstream outCSV("resultsSynthesis.csv", std::ios_base::app);
	outCSV << path << "," << fullPartial[0] << "," << fullPartial[1] << "," << timerNoter[0]*1000 << "," << timerNoter[1]*1000 << "," << timerNoter[2]*1000 << "," << timerNoter[3]*1000 << "," << timerNoter[4]*1000 << "," << ZDDNodeCount << "," << (double)mgr.ReadPeakNodeCount() << "," << (double)mgr.ReadMemoryInUse() << "," << std::endl;
	outCSV.close();
	return;
	

}












