#ifndef CNF_TO_ZDD_H
#define CNF_TO_ZDD_H

#include <sys/types.h>
#include <sys/time.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <math.h>
#include <stdlib.h>
#include <string>
#include <iostream>
#include <vector>
#include <map>
#include <algorithm>
#include <unordered_map>
#include <stdexcept>
#include "QCnfFormula.hpp"
#include "QDimacsReader.hpp"
#include "CnfFormula.hpp"
#include "cudd.h"
#include "cuddObj.hh"

//CNFtoZDDconverter class

class CNFtoZDDconverter {
	
public:
	//constructors
	CNFtoZDDconverter();

	//helper functions
	std::runtime_error EmptyFormulaException(const std::string& filepath) const;

	ZDD ClausetoZDD(const CnfClause& cl, Cudd& mgr, const int maxRange) const; 
	int indexConverter(int g);
	int maxVarRange(const QCnfFormula& qcnf);	
	std::unordered_map<int, int> produceIndicesMap(int maxvar);
	
	//draw ZDD
	void ZDDtoDot(Cudd& mgr, const std::vector<ZDD> z, const std::string dotfile, char** inames, char** onames);
	
	// check partial realizability
	bool partialRealizability(Cudd& mgr, const ZDD& zdd,QCnfFormula& qcnf2) ;

	// check full realizability
	bool fullRealizability(Cudd& mgr, const ZDD& zdd, QCnfFormula& qcnf2 ) ;

	//resolution
	//ZDD Resolution(const ZDD& zdd, const std::vector<int> y_vars, const std::string& outputpath, std::unordered_map <int, int> index_map) const;
	ZDD Resolution(Cudd& mgr, const ZDD& zdd, const std::vector<int> y_vars);

	// substitution
	ZDD crossZDD(const ZDD& z) const;

	ZDD negCrossZDD(const ZDD& z) const;

	ZDD CNFtoDNF_Substitution(Cudd& mgr, int y, std::unordered_map <int, int>& index_map, int maxVar, const ZDD& z, CnfFormula& cnf, std::vector<ZDD>& Clause_ZDDs);


	//main converter
	void convertCNFtoZDD(const std::string& path);
	

	
};


#endif // CNF_TO_ZDD_H








