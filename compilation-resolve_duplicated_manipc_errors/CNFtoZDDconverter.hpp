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

	ZDD ClausetoZDD(const CnfClause& cl, Cudd& mgr, int maxvar); 
	int indexConverter(int g);
	int maxVarRange(const QCnfFormula& qcnf);	
	std::unordered_map<int, int> produceIndicesMap(int maxvar);
	
	//draw ZDD
	void ZDDtoDot(Cudd& mgr, const std::vector<ZDD> z, const std::string dotfile, char** inames, char** onames);
	
	// check partial realizability
	bool partialRealizability(const ZDD& zdd) const;

	// check full realizability
	bool fullRealizability(const ZDD& zdd,, std::unordered_map <int, int> index_map ) const;

	//resolution
	//ZDD Resolution(const ZDD& zdd, const std::vector<int> y_vars, const std::string& outputpath, std::unordered_map <int, int> index_map) const;
	ZDD Resolution(const ZDD& zdd, const std::vector<int> y_vars, std::unordered_map <int, int> index_map) const;

	//main converter
	void convertCNFtoZDD(const std::string& path);
	

	
};


#endif // CNF_TO_ZDD_H








